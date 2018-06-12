/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.ast.{Declaration, Exp, Stmt, Trigger}

import scala.collection.mutable
import viper.silver.{ast => vpr}
import viper.voila.backends.ViperAstUtils
import viper.voila.frontend.{PMember, PRegion}
import viper.voila.translator.TranslatorUtils.BetterQuantifierWrapper

object TranslatorUtils {

  // TODO: credit

  trait Observer[S] {
    def receiveUpdate(subject: S)
  }

  trait Subject[S] {

    private var observers: List[Observer[S]] = Nil
    def addObserver(observer: Observer[S]): Unit = observers ::= observer

    def notifyObservers(subject: S): Unit = observers foreach (_.receiveUpdate(subject))
  }

  case class ManagedObject[T](id: T, decls: Vector[vpr.LocalVarDecl])

  trait BaseSelector[T] {

    def selectArgs(id: T, args: Vector[vpr.Exp]): Vector[vpr.Exp]

    def formalArgSelection(obj: ManagedObject[T]): Vector[vpr.LocalVarDecl] = {

      val vars = obj.decls map (_.localVar)
      val selectedVars = selectArgs(obj.id, vars)

      selectedVars.zipWithIndex map {
        case (v: vpr.LocalVar, _) => vpr.LocalVarDecl(v.name, v.typ)()
        case (e, i)                   => vpr.LocalVarDecl(s"$$p$i", e.typ)()
      }
    }
  }

  trait FrontSelector[R] extends BaseSelector[R]
  trait SubSelector[R] extends BaseSelector[R]

  trait EmptySelector[R] extends BaseSelector[R] {
    override def selectArgs(id: R, args: Vector[vpr.Exp]): Vector[vpr.Exp] = Vector.empty
  }

  trait SubEmptySelector[R] extends EmptySelector[R] with SubSelector[R]
  trait FrontEmptySelector[R] extends EmptySelector[R] with FrontSelector[R]

  trait FullSelector[R] extends BaseSelector[R] {
    override def selectArgs(id: R, args: Vector[vpr.Exp]): Vector[vpr.Exp] = args
  }

  trait SubFullSelector[R] extends FullSelector[R] with SubSelector[R]
  trait FrontFullSelector[R] extends FullSelector[R] with FrontSelector[R]

  trait VersionedSelector[R] extends FrontSelector[R] with Observer[Int]{
    private var currentVersion = 0

    override def selectArgs(id: R, args: Vector[vpr.Exp]): Vector[vpr.Exp] =
      vpr.IntLit(currentVersion)().asInstanceOf[vpr.Exp] +: args

    override def receiveUpdate(subject: Int): Unit = currentVersion = subject
  }

  trait RemoveVersionSelector[R] extends SubSelector[R] {
    override def selectArgs(id: R, args: Vector[vpr.Exp]): Vector[vpr.Exp] = args.tail
  }

  trait BasicManager[T, M <: vpr.Declaration, A <: vpr.Exp] {

    this: BaseSelector[T] =>

    val name: String

    protected def idToName(id: T): String

    protected def memberName(objName: String): String

    protected def toMember(obj: ManagedObject[T]): (M, Vector[vpr.Declaration])

    protected val collectedMember = mutable.Map.empty[String, M]

    def collectMember(obj: ManagedObject[T]): Vector[vpr.Declaration] = {
      val (m,ds) = toMember(obj)
      collectedMember += idToName(obj.id) -> m
      m +: ds
    }

    def collectGlobalDeclarations: Vector[vpr.Declaration] = Vector.empty

    def application(id: T, args: Vector[vpr.Exp]): A
  }

  trait BasicManagerWithSimpleApplication[T, M <: vpr.Declaration, A <: vpr.Exp] extends BasicManager[T, M, A] {

    this: BaseSelector[T] =>

    def getID(objName: String): T

    def application(objName: String, args: Vector[vpr.Exp]): A =
      application(getID(objName), args)
  }


  trait FootprintManager[T] extends BasicManager[T, vpr.Predicate, vpr.PredicateAccessPredicate] {

    this: BaseSelector[T] =>

    override protected def memberName(objName: String): String = s"${objName}_${name}_fp"

    override protected def toMember(obj: ManagedObject[T]): (vpr.Predicate, Vector[vpr.Declaration]) =
      (vpr.Predicate(
          name = memberName(idToName(obj.id)),
          formalArgs = formalArgSelection(obj),
          body = None
        )(),
        Vector.empty
      )

    override def application(id: T, args: Vector[vpr.Exp]): vpr.PredicateAccessPredicate =
      accessWithPermission(id, args, vpr.FullPerm()())

    protected def application(id: T, args: Vector[vpr.Exp], label: vpr.Label): vpr.PredicateAccessPredicate =
      accessWithPermission(id, args, oldPerm(id, args, label))

    protected def access(id: T, args: Vector[vpr.Exp]): vpr.PredicateAccess =
      vpr.PredicateAccess(
        predicateName = memberName(idToName(id)),
        args = selectArgs(id, args)
      )()

    protected def accessWithPermission(id: T, args: Vector[vpr.Exp], perm: vpr.Exp): vpr.PredicateAccessPredicate =
      vpr.PredicateAccessPredicate(
        access(id, args),
        perm
      )()

    def oldPerm(id: T, args: Vector[vpr.Exp], label: vpr.Label): vpr.Exp =
      vpr.LabelledOld(currentPerm(id, args), label.name)()

    def currentPerm(id: T, args: Vector[vpr.Exp]): vpr.Exp =
      vpr.CurrentPerm(access(id, args))()

    def initialize(id: T): vpr.Stmt

    def havoc(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Stmt

    def inhaleFootprint(id: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Inhale = {
      val args = wrapper.args
      val transedWrapper = wrapper.transform(selectArgs(id,_))

      /* No trigger yet available */
      vpr.Inhale(transedWrapper.wrapWithoutCondition(application(id, args)))()
    }

    def inhaleFootprint(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Inhale = {
      val args = wrapper.args
      val transedWrapper = wrapper.transform(selectArgs(id,_))

      /* No trigger yet available */
      vpr.Inhale(transedWrapper.wrapWithoutCondition(application(id, args, label)))()
    }

    def exhaleFootprint(id: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Exhale = {
      val args = wrapper.args
      val transedWrapper = wrapper.transform(selectArgs(id,_))

      /* No trigger yet available */
      vpr.Exhale(transedWrapper.wrapWithoutCondition(application(id, args)))()
    }

    def exhaleFootprint(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Exhale = {
      val args = wrapper.args
      val transedWrapper = wrapper.transform(selectArgs(id,_))

      /* No trigger yet available */
      vpr.Exhale(transedWrapper.wrapWithoutCondition(application(id, args, label)))()
    }

    def assertFootprint(id: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Assert = {
      val args = wrapper.args
      val transedWrapper = wrapper.transform(selectArgs(id,_))

      /* No trigger yet available */
      vpr.Assert(transedWrapper.wrapWithoutCondition(application(id, args)))()
    }

    def assertNoFootprint(id: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Assert = {
      val args = wrapper.args
      val transedWrapper = wrapper.transform(selectArgs(id,_))

      vpr.Assert(transedWrapper.wrapWithoutCondition(
        vpr.EqCmp(
          currentPerm(id, args),
          vpr.NoPerm()()
        )()
      ))()
    }
  }

  trait LavishFootprintManager[T] extends FootprintManager[T] {

    this: BaseSelector[T] =>

    override def initialize(id: T): vpr.Stmt = {
      val pred = collectedMember(idToName(id))
      val decls = pred.formalArgs.toVector
      val vars = decls map (_.localVar)

      val access =
        vpr.PredicateAccessPredicate(
          vpr.PredicateAccess(
            predicateName = memberName(idToName(id)),
            args = vars // no selector
          )(),
          vpr.FullPerm()()
        )()

      val result = vpr.Inhale(
        vpr.Forall(
          decls,
          Vector.empty,
          access
        )()
      )()

      ViperAstUtils.sanitizeBoundVariableNames(result)
    }

    override def havoc(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Stmt = {
      vpr.Seqn(
        Vector(exhaleFootprint(id)(wrapper), inhaleFootprint(id)(wrapper)),
        Vector.empty
      )()
    }

  }

  trait FrugalFootprintManager[T] extends FootprintManager[T] {
    this: BaseSelector[T] =>

    override def initialize(id: T): Stmt =
      ViperAstUtils.Seqn()(info = vpr.SimpleInfo(Vector("", "no init required", "")))

    override def havoc(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Stmt = {
      vpr.Seqn(
        Vector(inhaleFootprint(id)(wrapper)),
        Vector.empty
      )()
    }
  }

  trait FunctionManager[T, M <: vpr.Declaration, A <: vpr.Exp] extends BasicManager[T, M, A] {

    this: BaseSelector[T] =>

    def functionTyp(obj: T): vpr.Type
  }

  trait DomainFunctionManager[T] extends FunctionManager[T, vpr.DomainFunc, vpr.DomainFuncApp] {

    this: BaseSelector[T] =>

    override protected def memberName(objName: String): String = s"${objName}_${name}_df"

    private lazy val domainName: String = s"${name}_Domain"

    protected lazy val dfltAxioms: Vector[vpr.DomainAxiom] = Vector.empty

    lazy val domain: vpr.Domain =
      vpr.Domain(
        name = domainName,
        functions = Vector.empty,
        axioms = dfltAxioms,
        typVars = Vector.empty
      )()

    override def collectGlobalDeclarations: Vector[Declaration] = Vector(domain)

    override protected def toMember(obj: ManagedObject[T]): (vpr.DomainFunc, Vector[vpr.Declaration]) =
      (
        vpr.DomainFunc(
          name = memberName(idToName(obj.id)),
          formalArgs = formalArgSelection(obj),
          typ = functionTyp(obj.id)
        )(domainName = domainName),
        Vector.empty
      )

    override def application(id: T, args: Vector[vpr.Exp]): vpr.DomainFuncApp =
      vpr.DomainFuncApp(
        func = collectedMember(idToName(id)),
        args = selectArgs(id, args),
        typVarMap = Map.empty
      )()
  }

  case class Constraint(constrain: Vector[Exp] => vpr.Exp => TranslatorUtils.BetterQuantifierWrapper.WrapperExt,
                        skolemization: Option[Vector[Exp] => vpr.Stmt => vpr.Stmt] = None)

  trait FrontResource[T] {

    def application(id: T, args: Vector[vpr.Exp]): vpr.Exp

    def applyTrigger(id: T, args: Vector[vpr.Exp]): Vector[vpr.Trigger]

    def havoc(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Stmt

    def inhaleFootprint(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Stmt

    def select(id: T, constraint: Constraint, label: vpr.Label)(wrapper: TranslatorUtils.BetterQuantifierWrapper.Wrapper): vpr.Stmt = {

      val args = wrapper.args

      val havocCode = havoc(id, label)(wrapper)

      val selectCondition = constraint.constrain(args)(application(id, args))

      val selectExp = wrapper.wrapExt(selectCondition, applyTrigger(id, _))

      val selectCode = vpr.Inhale(selectExp)()

      val finalizedSelectCode = constraint.skolemization match {
        case None => selectCode
        case Some(skolemize) => skolemize(args)(selectCode)
      }

      val result = vpr.Seqn(
        Vector(havocCode, finalizedSelectCode),
        Vector.empty
      )()

      ViperAstUtils.sanitizeBoundVariableNames(result)
    }

    def refSelect(id: T, constraint: Constraint, label: vpr.Label)(wrapper: TranslatorUtils.BetterQuantifierWrapper.Wrapper): vpr.Stmt = {

      val args = wrapper.args

      val inhaleCode = inhaleFootprint(id, label)(wrapper)

      val selectCondition = constraint.constrain(args)(application(id, args))

      val selectExp = wrapper.wrapExt(selectCondition, applyTrigger(id, _))

      val selectCode = vpr.Inhale(selectExp)()

      val finalizedSelectCode = constraint.skolemization match {
        case None => selectCode
        case Some(skolemize) => skolemize(args)(selectCode)
      }

      val result = vpr.Seqn(
        Vector(inhaleCode, finalizedSelectCode),
        Vector.empty
      )()

      ViperAstUtils.sanitizeBoundVariableNames(result)
    }
  }

  trait FrugalFrontResource[T] extends FrontResource[T] {

    def inhaleFootprint(t: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Stmt

    def exhaleFootprint(t: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Stmt

    def freshSelect(id: T, constraint: Constraint)(wrapper: TranslatorUtils.BetterQuantifierWrapper.Wrapper): vpr.Stmt = {

      val args = wrapper.args

      val inhaleCode = inhaleFootprint(id)(wrapper)

      val selectCondition = constraint.constrain(args)(application(id, args))

      val selectExp = wrapper.wrapExt(selectCondition, applyTrigger(id, _))

      val selectCode = vpr.Inhale(selectExp)()

      val finalizedSelectCode = constraint.skolemization match {
        case None => selectCode
        case Some(skolemize) => skolemize(args)(selectCode)
      }

      val result = vpr.Seqn(
        Vector(inhaleCode, finalizedSelectCode),
        Vector.empty
      )()

      ViperAstUtils.sanitizeBoundVariableNames(result)
    }
  }

  trait HeapFunctionManager[T] extends FunctionManager[T, vpr.Function, vpr.FuncApp] with FrugalFrontResource[T] {

    this: BaseSelector[T] =>

    override protected def memberName(objName: String): String = s"${objName}_${name}_hf"

    val footprintManager: FootprintManager[T] with SubSelector[T]
    val triggerManager: DomainFunctionManager[T] with SubSelector[T]

    protected def post(trigger: vpr.DomainFuncApp): Vector[vpr.Exp] =
      Vector(vpr.InhaleExhaleExp(trigger, vpr.TrueLit()())())

    protected def body(obj: ManagedObject[T]): (Option[vpr.Exp], Option[vpr.DecClause]) =
      (None, None)

    override protected def toMember(obj: ManagedObject[T]): (vpr.Function, Vector[vpr.Declaration]) = {
      val decls = formalArgSelection(obj)
      val vars = decls map (_.localVar)

      val subObj = ManagedObject(obj.id, decls)

      val footprintDecls = footprintManager.collectMember(subObj)
      val triggerDecls = triggerManager.collectMember(subObj)

      val (bodyExp, decs) = body(subObj)

      (
        vpr.Function(
          name = memberName(idToName(obj.id)),
          formalArgs = decls,
          typ = functionTyp(obj.id),
          pres = Vector(footprintManager.application(obj.id,vars)),
          posts = post(triggerManager.application(obj.id, vars)),
          decs = decs,
          body = bodyExp
        )(),
        footprintDecls ++: triggerDecls
      )
    }

    override def application(id: T, args: Vector[vpr.Exp]): vpr.FuncApp =
      vpr.FuncApp(
        func = collectedMember(idToName(id)),
        args = selectArgs(id, args)
      )()

    def triggerApplication(id: T, args: Vector[vpr.Exp]): vpr.Exp =
      triggerManager.application(id, selectArgs(id, args))

    def applyTrigger(id: T, args: Vector[vpr.Exp]): Vector[vpr.Trigger] =
      Vector(vpr.Trigger(Vector(triggerApplication(id, args)))())

    def footprintOldPerm(id: T, args: Vector[vpr.Exp], label: vpr.Label): vpr.Exp =
      footprintManager.oldPerm(id, selectArgs(id, args), label)

    def footprintCurrentPerm(id: T, args: Vector[vpr.Exp]): vpr.Exp =
      footprintManager.currentPerm(id, selectArgs(id, args))

    def havoc(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Stmt =
      footprintManager.havoc(id, label)(wrapper.transform(selectArgs(id,_)))

    def inhaleFootprint(id: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Inhale =
      footprintManager.inhaleFootprint(id)(wrapper.transform(selectArgs(id,_)))

    def inhaleFootprint(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Inhale =
      footprintManager.inhaleFootprint(id, label)(wrapper.transform(selectArgs(id,_)))

    def exhaleFootprint(id: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Exhale =
      footprintManager.exhaleFootprint(id)(wrapper.transform(selectArgs(id,_)))

    def exhaleFootprint(id: T, label: vpr.Label)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Exhale =
      footprintManager.exhaleFootprint(id, label)(wrapper.transform(selectArgs(id,_)))

    def assertFootprint(id: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Assert =
      footprintManager.assertFootprint(id)(wrapper.transform(selectArgs(id,_)))

    def assertNoFootprint(id: T)(wrapper: BetterQuantifierWrapper.Wrapper): vpr.Assert =
      footprintManager.assertNoFootprint(id)(wrapper.transform(selectArgs(id,_)))
  }

  object BetterQuantifierWrapper {

    sealed trait WrapperExt {
      def combine(func: vpr.Exp => WrapperExt): WrapperExt
    }

    case class UnitWrapperExt(exp: Exp) extends WrapperExt {
      override def combine(func: Exp => WrapperExt): WrapperExt = func(exp)
    }

    case class QuantWrapperExt(decls: Vector[vpr.LocalVarDecl], exp: Exp) extends WrapperExt {
      override def combine(func: Exp => WrapperExt): WrapperExt = func(exp) match {
        case UnitWrapperExt(e) => QuantWrapperExt(decls, e)
        case QuantWrapperExt(ds, e) => QuantWrapperExt(decls ++: ds, e)
      }
    }

    sealed trait Wrapper {
      def args: Vector[vpr.Exp]

      def wrapExt(ext: WrapperExt, triggers: Vector[vpr.Exp] => Vector[vpr.Trigger] = xs => Vector.empty): vpr.Exp

      def wrap(exp: vpr.Exp, triggers: Vector[vpr.Exp] => Vector[vpr.Trigger] = xs => Vector.empty): vpr.Exp =
        wrapExt(UnitWrapperExt(exp), triggers)

      def wrapExtWithoutCondition(ext: WrapperExt, triggers: Vector[vpr.Exp] => Vector[vpr.Trigger] = xs => Vector.empty): vpr.Exp

      def wrapWithoutCondition(exp: vpr.Exp, triggers: Vector[vpr.Exp] => Vector[vpr.Trigger] = xs => Vector.empty): vpr.Exp =
        wrapExtWithoutCondition(UnitWrapperExt(exp), triggers)

      def transform(trans: Vector[vpr.Exp] => Vector[vpr.Exp]): Wrapper
    }

    case class UnitWrapper(args: Vector[vpr.Exp]) extends Wrapper {
      override def wrapExt(ext: WrapperExt, triggers: Vector[vpr.Exp] => Vector[vpr.Trigger]): Exp = ext match {
        case UnitWrapperExt(e) => e
        case QuantWrapperExt(ds, e) => vpr.Forall(ds, triggers(args ++: (ds map (_.localVar))), e)(e.pos, e.info, e.errT)
      }

      override def transform(trans: Vector[Exp] => Vector[Exp]): Wrapper =
        UnitWrapper(trans(args))

      override def wrapExtWithoutCondition(exp: WrapperExt, triggers: Vector[vpr.Exp] => Vector[vpr.Trigger]): Exp = wrapExt(exp, triggers)
    }

    case class QuantWrapper(decls: Vector[vpr.LocalVarDecl], args: Vector[vpr.Exp], condition: vpr.Exp) extends Wrapper {
      override def wrapExt(ext: WrapperExt, triggers: Vector[vpr.Exp] => Vector[vpr.Trigger]): Exp = ext match {
        case UnitWrapperExt(e) => vpr.Forall(decls, triggers(decls map (_.localVar)), vpr.Implies(condition, e)())(e.pos, e.info, e.errT)
        case QuantWrapperExt(ds, e) => vpr.Forall(decls ++: ds, triggers((decls ++: ds) map (_.localVar)), vpr.Implies(condition, e)())(e.pos, e.info, e.errT)
      }

      override def transform(trans: Vector[Exp] => Vector[Exp]): Wrapper = {

        val declVars = decls map (_.localVar)
        val transedDeclVars = trans(declVars)

        val transedDecls = transedDeclVars.zipWithIndex map {
          case (v: vpr.LocalVar, _) => vpr.LocalVarDecl(v.name, v.typ)()
          case (e, i)                   => vpr.LocalVarDecl(s"$$p$i", e.typ)()
        }

        if (transedDecls.nonEmpty) {
          QuantWrapper(transedDecls, trans(args), condition)
        } else{
          UnitWrapper(Vector.empty)
        }
      }

      override def wrapExtWithoutCondition(ext: WrapperExt, triggers: Vector[vpr.Exp] => Vector[vpr.Trigger]): Exp = ext match {
        case UnitWrapperExt(e) => vpr.Forall(decls, triggers(decls map (_.localVar)), e)(e.pos, e.info, e.errT)
        case QuantWrapperExt(ds, e) => vpr.Forall(decls ++: ds, triggers((decls ++: ds) map (_.localVar)), e)(e.pos, e.info, e.errT)
      }
    }

  }


  //  trait BasicFeaturedManager[R, F, M, A] extends BasicManager[(R,F),M, A]{
  //
  //    this: BaseSelector[(R,F)] =>
  //
  //    protected def objToName(obj: R): String
  //    protected def featureToName(obj: F): String
  //
  //    override protected def objToName(pair: (R, F)): String =
  //      s"${objToName(pair._1)}_${featureToName(pair._2)}"
  //
  //    def toMember(obj: R, feature: F): M
  //
  //    override def toMember(pair: (R, F)): M = toMember(pair._1, pair._2)
  //
  //    def collectFeatures(obj: R): Vector[F]
  //    def collectMembers(obj: R): Vector[M] = collectFeatures(obj) map (collectMember(obj,_))
  //  }


}
