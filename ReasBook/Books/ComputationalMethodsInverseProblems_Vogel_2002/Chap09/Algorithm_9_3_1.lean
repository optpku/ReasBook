/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates

public section

/-
Algorithm 9.3.1. Gradient Projection.

To minimize `J f` subject to the external feasible-set constraint `f ≥ 0`, this
item uses the projected-gradient recurrence `GradientProjection.iterates P J τ f0`
as the reusable source-facing owner. The per-step projected line-search clause
is recorded separately by `GradientProjection.IsExactLineSearch P J τ f0`. Both
owners keep the projection map `P` explicit until the Chapter 9 feasible-set
owner is formalized elsewhere in the repository.
-/
#check GradientProjection.iterates

/- Algorithm 9.3.1. Backend owner for the exact projected line-search clause
`τ_v = arg min_{τ > 0} J (P (f_v - τ ∇J(f_v)))`. -/
#check GradientProjection.IsExactLineSearch
