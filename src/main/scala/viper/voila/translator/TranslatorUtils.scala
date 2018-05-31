/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.ast.{Exp, Trigger}

import scala.collection.mutable
import viper.silver.{ast => vpr}
import viper.voila.frontend.{PMember, PRegion}

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
        case (v: vpr.LocalVarDecl, _) => vpr.LocalVarDecl(v.name, v.typ)()
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
      (
        vpr.Predicate(
          name = memberName(idToName(obj.id)),
          formalArgs = formalArgSelection(obj),
          body = None
        )(),
        Vector.empty
      )

    override def application(id: T, args: Vector[vpr.Exp]): vpr.PredicateAccessPredicate =
      vpr.PredicateAccessPredicate(
        vpr.PredicateAccess(
          predicateName = memberName(idToName(id)),
          args = selectArgs(id, args)
        )(),
        vpr.FullPerm()()
      )()

    def allWrapper(id: T)(transformer: Vector[vpr.Exp] => vpr.Exp):  vpr.Exp = {

      val member = collectedMember(idToName(id))
      val decls = member.formalArgs.toVector
      val vars = decls map (_.localVar)

      vpr.Forall(
        variables = decls,
        triggers = Vector.empty,
        exp = transformer(vars)
      )()
    }

    def singleWrapper(id: T, args: Vector[vpr.Exp])(transformer: Vector[vpr.Exp] => vpr.Exp):  vpr.Exp = {
      transformer(args)
    }

    def inhaleFootprint(id: T)(wrapper: (Vector[vpr.Exp] => vpr.Exp) => vpr.Exp): vpr.Stmt =
      vpr.Inhale(wrapper(application(id,_)))()

    def exhaleFootprint(id: T)(wrapper: (Vector[vpr.Exp] => vpr.Exp) => vpr.Exp): vpr.Stmt =
      vpr.Exhale(wrapper(application(id,_)))()
  }

  trait FunctionManager[T, M <: vpr.Declaration, A <: vpr.Exp] extends BasicManager[T, M, A] {

    this: BaseSelector[T] =>

    def functionTyp(obj: T): vpr.Type
  }

  trait DomainFunctionManager[T] extends FunctionManager[T, vpr.DomainFunc, vpr.DomainFuncApp] {

    this: BaseSelector[T] =>

    override protected def memberName(objName: String): String = s"${objName}_${name}_df"

    private val domainName: String = s"${name}_Domain"

    protected val dfltAxioms: Vector[vpr.DomainAxiom] = Vector.empty

    val domain: vpr.Domain =
      vpr.Domain(
        name = domainName,
        functions = Vector.empty,
        axioms = dfltAxioms,
        typVars = Vector.empty
      )()

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

  trait HeapFunctionManager[T] extends FunctionManager[T, vpr.Function, vpr.FuncApp] {

    this: BaseSelector[T] =>

    override protected def memberName(objName: String): String = s"${objName}_${name}_hf"

    val footprintManager: FootprintManager[T] with SubSelector[T]
    val triggerManager: DomainFunctionManager[T] with SubSelector[T]

    protected def post(trigger: vpr.DomainFuncApp): vpr.Exp =
      vpr.InhaleExhaleExp(
        trigger,
        vpr.TrueLit()()
      )()

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
          posts = Vector(post(triggerManager.application(obj.id, vars))),
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

    def applyTrigger(id: T, args: Vector[vpr.Exp]): vpr.DomainFuncApp =
      triggerManager.application(id, selectArgs(id, args))

    def inhaleFootprint(id: T)(wrapper: (Vector[vpr.Exp] => vpr.Exp) => vpr.Exp): vpr.Stmt =
      footprintManager.inhaleFootprint(id)(wrapper)

    def exhaleFootprint(id: T)(wrapper: (Vector[vpr.Exp] => vpr.Exp) => vpr.Exp): vpr.Stmt =
      footprintManager.exhaleFootprint(id)(wrapper)
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

      def wrap(ext: WrapperExt, triggers: Vector[vpr.Trigger] = Vector.empty): vpr.Exp

      def wrap(exp: vpr.Exp, triggers: Vector[vpr.Trigger] = Vector.empty): vpr.Exp =
        wrap(UnitWrapperExt(exp), triggers)

      def transform(trans: Vector[vpr.Exp] => Vector[vpr.Exp]): Wrapper
    }

    case class UnitWrapper(args: Vector[vpr.Exp]) extends Wrapper {
      override def wrap(ext: WrapperExt, triggers: Vector[Trigger]): Exp = ext match {
        case UnitWrapperExt(e) => e
        case QuantWrapperExt(ds, e) => vpr.Forall(ds, triggers, e)(e.pos, e.info, e.errT)
      }

      override def transform(trans: Vector[Exp] => Vector[Exp]): Wrapper =
        UnitWrapper(trans(args))
    }

    case class QuantWrapper(decls: Vector[vpr.LocalVarDecl], args: Vector[vpr.Exp], condition: vpr.Exp) extends Wrapper {
      override def wrap(ext: WrapperExt, triggers: Vector[Trigger]): Exp = ext match {
        case UnitWrapperExt(e) => vpr.Forall(decls, triggers, e)(e.pos, e.info, e.errT)
        case QuantWrapperExt(ds, e) => vpr.Forall(decls ++: ds, triggers, vpr.Implies(condition, e)())(e.pos, e.info, e.errT)
      }

      override def transform(trans: Vector[Exp] => Vector[Exp]): Wrapper = {

        val declVars = decls map (_.localVar)
        val transedDeclVars = trans(declVars)

        val transedDecls = transedDeclVars.zipWithIndex map {
          case (v: vpr.LocalVarDecl, _) => vpr.LocalVarDecl(v.name, v.typ)()
          case (e, i)                   => vpr.LocalVarDecl(s"$$p$i", e.typ)()
        }

        QuantWrapper(transedDecls, trans(args), condition)
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
