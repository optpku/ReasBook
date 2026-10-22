/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this internal owner file are maintained by hand.

noncomputable section

universe u v

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
  [AddCommMonoid Λ] [Module ℝ Λ]

/- The linear-equality feasible-set owner belongs to the chapter's affine linear-constraint
domain.

Relevant sampled declarations:
* `Set.preimage`
* `LinearMap.ker`
* `Set.univ`

Best owner abstraction:
* `linearEqualityFeasibleSet Q A b`

Primitive data:
* an ambient set `Q`
* a linear map `A`
* a right-hand side `b`

Derived API:
* `mem_linearEqualityFeasibleSet_iff`

This file isolates the primitive feasible-set owner from theorem files that develop richer
subgradient or optimality APIs. The owner itself only needs the intrinsic real-module structure on
the ambient and codomain spaces, so downstream Euclidean or matrix statements specialize to it
directly instead of rebuilding a coordinate-level duplicate.
-/

/-- The feasible set cut out by the ambient constraint `x ∈ Q` and the linear equality
constraint `A x = b`. -/
def linearEqualityFeasibleSet (Q : Set E) (A : E →ₗ[ℝ] Λ) (b : Λ) : Set E :=
  {x | x ∈ Q ∧ A x = b}

/-- Membership in `linearEqualityFeasibleSet Q A b` is exactly ambient feasibility together with
the equality constraint `A x = b`. -/
@[simp] theorem mem_linearEqualityFeasibleSet_iff
    {Q : Set E} {A : E →ₗ[ℝ] Λ} {b : Λ} {x : E} :
    x ∈ linearEqualityFeasibleSet Q A b ↔ x ∈ Q ∧ A x = b :=
  Iff.rfl

end
