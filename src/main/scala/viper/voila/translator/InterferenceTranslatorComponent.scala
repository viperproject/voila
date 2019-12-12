/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.{everywhere, query}
import viper.silver.ast._

import scala.collection.breakOut
import viper.silver.{ast => vpr}
import viper.voila.backends.ViperAstUtils
import viper.voila.frontend._
import viper.voila.translator.TranslatorUtils._

trait InterferenceTranslatorComponent { this: PProgramToViperTranslator =>
  def evaluateInterferenceContext(id: PIdnUse, origin: PExpression): vpr.Exp = {
    val dflt = translateUseOf(id).withSource(origin, overwrite = true)

    extractBoundRegionInstance(id) match {
      case Some((region, inArgs, _)) =>
        interferenceReferenceFunctions
          .application(region, inArgs map translate)
          .withSource(origin, overwrite = true)

      case _ => dflt
    }
  }

  private val interferenceContextFootprints = new LavishFootprintManager[PRegion]
    with RegionManager[vpr.Predicate, vpr.PredicateAccessPredicate]
    with RemoveVersionSelector[PRegion] {
    override val name: String = "interferenceContext"
  }

  val interferenceReferenceFunctions: HeapFunctionManager[PRegion] with RegionManager[vpr.Function, vpr.FuncApp] = {
    val _name = "interferenceReference"
    def _functionType(obj: PRegion): Type = regionStateFunction(obj).typ

    val _triggerManager =
      new DomainFunctionManager[PRegion]
        with RegionManager[vpr.DomainFunc, vpr.DomainFuncApp]
        with SubFullSelector[PRegion] {
        override val name: String = _name
        override def functionTyp(obj: PRegion): Type = vpr.Bool
      }

    collectedDeclarations ++= _triggerManager.collectGlobalDeclarations

    new HeapFunctionManager[PRegion]
        with RegionManager[vpr.Function, vpr.FuncApp]
        with SequenceStabelizeVersionedSelector[PRegion] {

      override val footprintManager: FootprintManager[PRegion] with SubSelector[PRegion] = interferenceContextFootprints
      override val triggerManager: DomainFunctionManager[PRegion] with SubSelector[PRegion] = _triggerManager

      override def functionTyp(obj: PRegion): Type = _functionType(obj)

      override val name: String = _name

      override def havoc(id: PRegion, label: vpr.Label)(wrapper: QuantifierWrapper.Wrapper): Stmt =
        ViperAstUtils.Seqn()(info = vpr.SimpleInfo(Vector("", "havoc performed by other front resource", "")))
    }
  }

  val interferenceSetFunctions: HeapFunctionManager[PRegion] with RegionManager[vpr.Function, vpr.FuncApp] = {
    val _name = "interferenceSet"
    def _functionType(obj: PRegion): Type = vpr.SetType(regionStateFunction(obj).typ)

    val _triggerManager =
      new DomainFunctionManager[PRegion]
        with RegionManager[vpr.DomainFunc, vpr.DomainFuncApp]
        with SubFullSelector[PRegion] {
        override val name: String = _name
        override def functionTyp(obj: PRegion): Type = _functionType(obj)
      }

    collectedDeclarations ++= _triggerManager.collectGlobalDeclarations /* TODO: This could be put into another trait */

    new HeapFunctionManager[PRegion]
        with RegionManager[vpr.Function, vpr.FuncApp]
        with SequenceStabelizeVersionedSelector[PRegion] {

      override val footprintManager: FootprintManager[PRegion] with SubSelector[PRegion] = interferenceContextFootprints
      override val triggerManager: DomainFunctionManager[PRegion] with SubSelector[PRegion] = _triggerManager

      override def functionTyp(obj: PRegion): Type = _functionType(obj)
      override val name: String = _name

      override protected def post(trigger: DomainFuncApp): Vector[vpr.Exp] = {
        val varName = "$_m" /* TODO: Naming convention */
        val varType = trigger.typ match {
          case vpr.SetType(t) => t
          case other => sys.error(s"Unexpectedly found $other (${other.getClass.getSimpleName})")
        }
        val varDecl = vpr.LocalVarDecl(varName, varType)()
        val variable = varDecl.localVar

        val varInResult =
          vpr.AnySetContains(
            variable,
            vpr.Result(trigger.typ)()
          )()

        val varInTrigger =
          vpr.AnySetContains(
            variable,
            trigger
          )()

        val triggerRelation =
          vpr.Forall(
            Vector(varDecl),
            Vector(vpr.Trigger(Vector(varInResult))()),
            vpr.Implies(varInResult, varInTrigger)()
          )()

        val postCondition = vpr.InhaleExhaleExp(
          triggerRelation,
          vpr.TrueLit()()
        )()

        Vector(postCondition)
      }

      override def triggerApplication(id: PRegion, args: Vector[Exp]): Exp = {
        selectArgs(id,args) match {
          case xs :+ m => vpr.AnySetContains(m, triggerManager.application(id, xs))()
        }
      }
    }
  }

  def regionArgumentMapping(region: PRegion, args: Vector[vpr.Exp]): Map[vpr.LocalVar, vpr.Exp] = {
    val inArgsSubst: Map[vpr.LocalVar, vpr.Exp] =
      region.formalInArgs.map(translate(_).localVar)
            .zip(args)
            .map{case (formal, actual) => formal -> actual}(breakOut)

    val outArgsSubst: Map[vpr.LocalVar, vpr.Exp] =
      region.formalOutArgs.map(translate(_).localVar).zipWithIndex.map{ case (f, i) =>
        f -> FuncApp(
          regionOutArgumentFunction(region, i),
          args
        )()
      }(breakOut)

    inArgsSubst ++ outArgsSubst
  }

  def linkInterferenceContext(region: PRegion, args: Vector[vpr.Exp]): vpr.Stmt = {
    var counter = 0
    var stateDependencies: List[(vpr.LocalVarDecl, PRegion, Vector[vpr.Exp])] = Nil

    val mapping = regionArgumentMapping(region, args)

    val state = translateWith(region.state) {
      case exp@ PIdnExp(id) =>
        extractBoundRegionInstance(id) match {
          case Some((innerRegion, inArgs, _)) =>

            val varName = s"$$_m$counter" /* TODO: Naming convention */
            counter += 1

            val regionStateType = translate(semanticAnalyser.typ(innerRegion.state))
            val varDecl = vpr.LocalVarDecl(varName, regionStateType)()
            val variable = varDecl.localVar

            stateDependencies ::= (varDecl, innerRegion, inArgs map (translate(_).replace(mapping)))

            variable

          case _ => translateUseOf(id).withSource(exp, overwrite = true)
        }
    }.replace(mapping)

    val refLabel = freshLabel("transitionPre")

//    var allRegions: List[(PRegion, Vector[vpr.Exp])] = Nil
//
//    translateWith(region.interpretation) {
//      case pred: PPredicateExp if extractableRegionInstance(pred) =>
//        val (innerRegion, inArgs, _) = getRegionPredicateDetails(pred)
//
//        allRegions ::= (innerRegion, inArgs map (translate(_).replace(mapping)))
//
//        translate(pred)
//    }
//
//    println("\n\n[linkInterferenceContext]")
//    println(s"  region = ${region.id.name}\n")
//
//    println("  allRegions = ")
//    allRegions foreach (r => println(s"    ${r._1.id.name}(${r._2.mkString(", ")})"))
//
//    println("\n  attribute approach:")

    var allRegions2 = Vector.empty[(Vector[vpr.Exp], PRegion, Vector[vpr.Exp])]

    everywhere(query[PAstNode] {
      case regionExp: PPredicateExp if extractableRegionInstance(regionExp) =>
//        println(s"    ${semanticAnalyser.pathConditions(regionExp)}  -->  ${regionExp.pretty}")

        val (innerRegion, inArgs, _) =
          getRegionPredicateDetails(regionExp)

        val pcs = semanticAnalyser.pathConditions(regionExp)
        val vprPcs = pcs map (translate(_).replace(mapping))

        allRegions2 = allRegions2 :+ (vprPcs, innerRegion, inArgs map (translate(_).replace(mapping)))
    })(region.interpretation)

//    println("\n  allRegions2 = ")
//    allRegions2 foreach (r => {
//      println(s"    [${r._1.mkString(" && ")}]  -->\n      ${r._2.id.name}(${r._3.mkString(", ")})")
//    })
//
//    println("\n\n")

//    if (allRegions.nonEmpty) {
//      val footprintHavocs = allRegions map { case (innerRegion, innerArgs) =>
    if (allRegions2.nonEmpty) {
      val footprintHavocs = allRegions2 map { case (_, innerRegion, innerArgs) =>
        // We could conditionally havoc interference set functions, by using the path conditions
        // collected as part of `allRegions2`. The additional branches would probably reduce
        // performance, though.

        val wrapper = singleWrapper(innerArgs)
        interferenceSetFunctions.havoc(innerRegion, refLabel)(wrapper)
      }

      val transformStmt =
        if (stateDependencies.nonEmpty) {
          val rhsContainTerms = stateDependencies map { case (decl, innerRegion, innerArgs) =>
            vpr.AnySetContains(
              decl.localVar,
              interferenceSetFunctions.application(innerRegion, innerArgs)
            )()
          }

          val triggerTerms = stateDependencies map { case (decl, innerRegion, innerArgs) =>
            interferenceSetFunctions.triggerApplication(innerRegion, innerArgs :+ decl.localVar)
          }

          val decls = stateDependencies map { case (decl, _, _) => decl }

          val lhsContainTerm =
            vpr.AnySetContains(
              state,
              interferenceSetFunctions.application(region, args)
            )()

          val body = vpr.EqCmp(lhsContainTerm, viper.silicon.utils.ast.BigAnd(rhsContainTerms))()

          /* TODO: Maybe add contains-assertions for better trigger usage */

          vpr.Inhale(
            vpr.Forall(
              decls,
              Vector(vpr.Trigger(triggerTerms)()),
              body
            )()
          )()

        } else {
          ViperAstUtils.Seqn()(info = vpr.SimpleInfo(Vector("", "no additional linking required", "")))
        }

//      val referencePointSelections = allRegions map { case (innerRegion, innerArgs) =>
      val referencePointSelections = allRegions2 map { case (pathConditions, innerRegion, innerArgs) =>
        val wrapper = singleWrapper(innerArgs)
        val prePermissions = vpr.LabelledOld(_: vpr.Exp, refLabel.name)()

        // TODO: @Felix: I [Malte] couldn't figure out how to pass pathConditions to either
        //       referencePointConstraint or interferenceReferenceFunctions.select in a meaningful
        //       way.

        val constraint = referencePointConstraint(innerRegion, prePermissions)

        interferenceReferenceFunctions.select(innerRegion, constraint, refLabel)(wrapper) match {
          // Only constrain the interference set if pathConditions hold.
          // I.e.: given `inhale hf() == old[lbl](hf)`,
          // rewrite it to `inhale pcs ==> hf() == old[lbl](hf)`.
          case seqn @ vpr.Seqn(Seq(vprStmt1, vprInhale @ vpr.Inhale(vprAssertion)), Seq()) =>
            ViperAstUtils.Seqn(
              vprStmt1,
              vpr.Inhale(
                vpr.Implies(
                  viper.silicon.utils.ast.BigAnd(pathConditions),
                  vprAssertion
                )()
              )(vprInhale.pos, vprInhale.info, vprInhale.errT)
            )(seqn.pos, seqn.info, seqn.errT)
          case other =>
            sys.error(s"Unexpectedly found $other (of class ${other.getClass.getName})")
        }
      }

      vpr.Seqn(
        (refLabel +: footprintHavocs) ++
          (transformStmt +: referencePointSelections),
        Vector.empty
      )()

    } else {
      ViperAstUtils.Seqn()(info = vpr.SimpleInfo(Vector("", "no interference context translation needed", "")))
    }
  }

  def referencePointConstraint(region: PRegion, prePermissions: vpr.Exp => vpr.Exp): Constraint = {
    Constraint(args => target =>
      /* target == prePermissions(R_state(args)) */
      TranslatorUtils.QuantifierWrapper.UnitWrapperExt(
        vpr.EqCmp(
          target,
          prePermissions(
            vpr.FuncApp(
              regionStateFunction(region),
              args
            )()
          )
        )()
      )
    )
  }

  def nextStateContainedInInference(region: PRegion): Constraint = {
    Constraint(args => target =>
      /* target in R_X(args) */
      TranslatorUtils.QuantifierWrapper.UnitWrapperExt(
        vpr.AnySetContains(
          target,
          interferenceSetFunctions.application(region, args)
        )()
      )
    )
  }

  def containsAllPossibleNextStatesConstraint(region: PRegion,
                                              possibleNextStateConstraint: Constraint)
                                             : Constraint = {

    def constrain(args: Vector[Exp])(target: Exp): TranslatorUtils.QuantifierWrapper.WrapperExt = {
      val varName = "$_m" /* TODO: Naming convention */
      val varType = regionStateFunction(region).typ
      val varDecl = vpr.LocalVarDecl(varName, varType)()
      val variable = varDecl.localVar

      /* m in X(xs)*/
      val varInInterference =
        vpr.AnySetContains(
          variable,
          target
        )()

      val varIsPossibleNextState: TranslatorUtils.QuantifierWrapper.WrapperExt =
        possibleNextStateConstraint.constrain(args)(variable)

      /* m in X(xs) <==> preState(xs) ~> m */
      varIsPossibleNextState.combine(e =>
        TranslatorUtils.QuantifierWrapper.QuantWrapperExt(
          Vector(varDecl),
          vpr.EqCmp(varInInterference, e)()
        )
      )
    }

    Constraint(constrain, possibleNextStateConstraint.skolemization)
  }

  val atomicityContextFunctions: HeapFunctionManager[PRegion] with RegionManager[vpr.Function, vpr.FuncApp] = {
    val _name = "atomicity_context"
    def _functionType(obj: PRegion): Type = vpr.SetType(regionStateFunction(obj).typ)

    val _footprintManager = new FrugalFootprintManager[PRegion]
      with RegionManager[vpr.Predicate, vpr.PredicateAccessPredicate]
      with SubFullSelector[PRegion] {
      override val name: String = _name
    }

    val _triggerManager =
      new DomainFunctionManager[PRegion]
        with RegionManager[vpr.DomainFunc, vpr.DomainFuncApp]
        with SubFullSelector[PRegion] {
        override val name: String = _name
        override def functionTyp(obj: PRegion): Type = vpr.Bool
      }

    collectedDeclarations ++= _triggerManager.collectGlobalDeclarations /* TODO: This could be put into another trait */

    new HeapFunctionManager[PRegion]
      with RegionManager[vpr.Function, vpr.FuncApp]
      with FrontFullSelector[PRegion] {

      override val footprintManager: FootprintManager[PRegion] with SubSelector[PRegion] = _footprintManager
      override val triggerManager: DomainFunctionManager[PRegion] with SubSelector[PRegion] = _triggerManager

      override def functionTyp(obj: PRegion): Type = _functionType(obj)
      override val name: String = _name
    }
  }

  def atomicityContextAllWrapper(region: PRegion, label: vpr.Label): TranslatorUtils.QuantifierWrapper.Wrapper = {
    /* Arguments as for region R */
    val vprRegionArgumentDecls: Vector[vpr.LocalVarDecl] = region.formalInArgs.map(translate)

    /* Arguments as for region R */
    val vprRegionArguments: Vector[vpr.LocalVar] = vprRegionArgumentDecls map (_.localVar)

    /* π */
    val vprPreHavocAtomicityPermissions =
      atomicityContextFunctions.footprintOldPerm(region, vprRegionArguments, label)

    /* none < π */
    val vprIsAtomicityAccessible =
      vpr.PermLtCmp(
        vpr.NoPerm()(),
        vprPreHavocAtomicityPermissions
      )()

    TranslatorUtils.QuantifierWrapper.QuantWrapper(vprRegionArgumentDecls, vprRegionArguments, vprIsAtomicityAccessible)
  }

  protected def atomicityContextAssignConstraint(region: PRegion): Constraint = {
    Constraint(args => target =>
      TranslatorUtils.QuantifierWrapper.UnitWrapperExt(
        vpr.EqCmp(
          target,
          interferenceSetFunctions.application(region, args)
        )()
      )
    )
  }

  protected def atomicityContextEqualsOldConstraint(region: PRegion, label: vpr.Label): Constraint = {
    Constraint(args => target =>
      TranslatorUtils.QuantifierWrapper.UnitWrapperExt(
        vpr.EqCmp(
          target,
          vpr.LabelledOld(atomicityContextFunctions.application(region, args), label.name)()
        )()
      )
    )
  }

  def atomicityContextWhileConstraint(region: PRegion, label: vpr.Label): Constraint = {
    Constraint(args => target => {
      val varName = "$_m" /* TODO: naming convention */
      val varType = regionStateFunction(region).typ
      val varDecl = vpr.LocalVarDecl(varName, varType)()

      TranslatorUtils.QuantifierWrapper.QuantWrapperExt(
        Vector(varDecl),
        vpr.EqCmp(
          target,
          vpr.LabelledOld(atomicityContextFunctions.application(region, args), label.name)()
        )()
      )
    })
  }

  protected def checkAtomicityNotYetCaptured(region: PRegion, args: Vector[vpr.Exp]): vpr.Assert = {
    val wrapper = singleWrapper(args)
    atomicityContextFunctions.assertNoFootprint(region)(wrapper)
  }

  protected def assignAtomicityContext(region: PRegion, args: Vector[vpr.Exp]): vpr.Stmt = {
    val wrapper = singleWrapper(args)
    val constraint = atomicityContextAssignConstraint(region)
    atomicityContextFunctions.freshSelect(region, constraint)(wrapper)
  }

  protected def assignOldAtomicityContext(region: PRegion, args: Vector[vpr.Exp], label: vpr.Label)
                                         : vpr.Stmt = {

    val wrapper = singleWrapper(args)
    val constraint = atomicityContextEqualsOldConstraint(region, label)
    atomicityContextFunctions.freshSelect(region, constraint)(wrapper)
  }

  protected def deselectAtomicityContext(region: PRegion, args: Vector[vpr.Exp]): vpr.Exhale = {
    val wrapper = singleWrapper(args)
    atomicityContextFunctions.exhaleFootprint(region)(wrapper)
  }
}
