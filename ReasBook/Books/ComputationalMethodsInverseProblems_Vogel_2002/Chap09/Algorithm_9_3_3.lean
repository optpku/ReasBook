/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_3.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_20.ReducedHessian

public section

/-!
Algorithm 9.3.3. GPRN.

This item now exposes Algorithm 9.3.3 itself through the source-facing step and
iterate-sequence owners `GPRN.IsStep` and `GPRN.IsIterateSequence` in the
reusable foundation module `Book.Ch9.Algorithm_9_3_3.Iterates`. That module
still keeps the explicit reduced-Hessian-based reduced-Newton direction, the
reduced-Newton stage update, and the backend direction-parameterized recurrence
available as companion API. The intermediate projected-gradient stage points
reuse the canonical projected-gradient update owner `GradientProjection.update`
directly. The reduced-Newton formula still appears explicitly through
`GPRN.IsReducedNewtonDirection`, so singular reduced Hessians are not silently
totalized by mathlib's default matrix inverse. The module continues to reuse
the canonical projected-gradient and reduced-Hessian APIs already present in
the repository.
-/

/-
Algorithm 9.3.3.

The source-facing GPRN owner is the step relation `GPRN.IsStep` together with
the iterate-sequence predicate `GPRN.IsIterateSequence`. The backend recursive
family `GPRN.iterates` and the stage sequence `GPRN.projectedStages` remain as
companion API for explicit trajectory calculations once a reduced-direction
sequence has been supplied.
-/
#check GPRN.IsStep
#check GPRN.IsIterateSequence
#check GPRN.projectedStage
#check GPRN.iterates
#check GPRN.projectedStages

/-
The reduced-Newton stage in Algorithm 9.3.3 is represented by the explicit
one-step direction owner `GPRN.reducedNewtonDirection`, the source-facing
single-stage direction predicate `GPRN.IsReducedNewtonDirection`, the backend
stagewise projection `GPRN.IsReducedDirectionSequence`, the explicit update
`GPRN.reducedNewtonUpdate`, and the backend reduced-stage line-search predicate
`GPRN.IsExactReducedLineSearch`.
-/
#check GPRN.reducedNewtonDirection
#check GPRN.IsReducedNewtonDirection
#check GPRN.IsReducedDirectionSequence
#check GPRN.reducedNewtonUpdate
#check GPRN.IsExactReducedLineSearch

/-
Backend anchor checks for the projected-gradient stage owner, the active set
`𝒜(f_v^GP)`, and the reduced Hessian `H_R` reused by the reduced-Newton
direction rule, together with the ambient gradient owner used in that rule.
-/
#check GradientProjection.iterates
#check ActiveSet.active
#check NonnegativeOrthant.reducedHessian
#check gradient
