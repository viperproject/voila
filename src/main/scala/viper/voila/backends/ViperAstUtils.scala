/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.backends

import viper.silver.{ast => vpr}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.utility.ViperStrategy

object ViperAstUtils {
  def Seqn(ss: vpr.Stmt*)
          (pos: vpr.Position = vpr.NoPosition,
           info: vpr.Info = vpr.NoInfo,
           errT: vpr.ErrorTrafo = vpr.NoTrafos)
          : vpr.Seqn = {

    vpr.Seqn(ss, Vector.empty)(pos, info, errT)
  }

  def DomainAxiom(name: String, exp: vpr.Exp)
                 (pos: vpr.Position = vpr.NoPosition,
                  info: vpr.Info = vpr.NoInfo,
                  domainName: String,
                  errT: vpr.ErrorTrafo = vpr.NoTrafos)
                 : vpr.NamedDomainAxiom = {

    vpr.NamedDomainAxiom(name, exp)(pos, info, domainName, errT)
  }

  def sanitizeBoundVariableNames[N <: vpr.Node](node: N): N = {
    val rename: String => String = name => s"$$$name"

    val sanitizer =
      ViperStrategy.Context[Seq[String]](
        {
          case (q: vpr.QuantifiedExp, ctx) =>
            val sanitizedQuantExp =
              q.withVariables(
                q.variables map (v => v.copy(name = rename(v.name))(v.pos, v.info, v.errT)))

            val updatedCtx = ctx.updateContext(ctx.c ++ q.variables.map(_.name))

            (sanitizedQuantExp, updatedCtx)
          case (v: vpr.LocalVar, ctx) if ctx.c.contains(v.name) =>
            val sanitizedVar =
              v.copy(name = rename(v.name), v.typ)(v.pos, v.info, v.errT)

            (sanitizedVar, ctx)
        },
        Seq.empty,
        Traverse.TopDown)

    sanitizer.execute[N](node)
  }

  def skolemize[N <: vpr.Node]
               (node: N, substitute: (vpr.LocalVar, Seq[vpr.LocalVar]) => vpr.Exp)
               : N = {

    /* TODO: Can the code handle nested existentials? */

    type Collector =
      /* Pair of universally bound variables (ubvs) and existentially bound variables (ebvs) */
      (Seq[vpr.LocalVar], Seq[vpr.LocalVar])

    val emptyCollector = (Vector.empty, Vector.empty)

    val skolemizer =
      ViperStrategy.Context[Collector](
        {
          case (q: vpr.Exists, ctx) =>
            val (ubvs, ebvs) = ctx.c
            val updatedCtx = ctx.updateContext((ubvs, ebvs ++ q.variables.map(_.localVar)))

            (q.exp, updatedCtx)

          case (q: vpr.QuantifiedExp, ctx) => /* All quantified expressions except existentials */
            val (ubvs, ebvs) = ctx.c
            val updatedCtx = ctx.updateContext((ubvs ++ q.variables.map(_.localVar), ebvs))

            (q, updatedCtx)

          case (v: vpr.LocalVar, ctx) if ctx.c._2.exists(_.name == v.name) =>
            (substitute(v, ctx.c._1), ctx)
        },
        emptyCollector,
        Traverse.TopDown)

    skolemizer.execute[N](node)
  }
}
