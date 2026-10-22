/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module LinearMap

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 6.17 lies in the affine variational-inequality / monotone affine-operator domain.

Sampled owner-style declarations:
- `AffineMap` in mathlib, the canonical owner of an affine operator together with its linear part;
- `LinearMap.BilinForm.IsNonneg` in mathlib, the canonical positivity owner for the bilinear form
  underlying a map `E →ₗ[ℝ] Dual ℝ E`;
- `PrimalConvexMinimizationProblem` in `Definition_6_4`, the chapter pattern of keeping only
  genuinely primitive feasible-set data public and deriving convenience API separately;
- `LinearEqualityConstrainedConvexProblem` in `Chap03/Definition_3_27`, the project pattern of
  extending an owner abstraction rather than restating equivalent lower-level data.

Best owner abstraction:
- source-facing: `AffineVariationalInequalityProblem E`;
- core/canonical: `AffineMap` for the operator and `BilinForm.IsNonneg` for the positivity of its
  linear part;
- bridge/view: the source-facing pointwise inequality `0 ≤ B.linear h h`, derived from the
  bilinear-form owner field.

Primitive data:
- the feasible set `Q` together with boundedness, closedness, and convexity;
- the affine operator `B : E →ᵃ[ℝ] E⋆`;
- nonnegativity of the bilinear form `B.linear`.

Derived API:
- coercion to the affine operator as a function;
- the source-facing pointwise monotonicity theorem `linear_nonnegative`;
- the solution predicate `IsSolution`.
-/

/-- Definition 6.17: an affine variational inequality problem consists of a bounded closed convex
set `Q ⊆ E` and an affine operator `B : E → E*` whose linear part satisfies
`⟪Bh, h⟫ ≥ 0` for every `h ∈ E`. The textbook item specializes this owner to finite-dimensional
real normed spaces. -/
structure AffineVariationalInequalityProblem (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  /-- The feasible set `Q ⊆ E`. -/
  feasibleSet : Set E
  /-- The feasible set `Q` is bounded. -/
  feasibleSet_bounded : Bornology.IsBounded feasibleSet
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The affine operator `B : E → E*`. -/
  operator : E →ᵃ[ℝ] Dual ℝ E
  /-- The bilinear form underlying the linear part of `B` is nonnegative. -/
  operator_linear_isNonneg : BilinForm.IsNonneg operator.linear

namespace AffineVariationalInequalityProblem

/-- An affine variational inequality problem can be evaluated as its canonical affine operator
`B : E → E*`. -/
instance : CoeFun (AffineVariationalInequalityProblem E) (fun _ ↦ E → Dual ℝ E) where
  coe problem := problem.operator

/-- Evaluating an affine variational inequality problem returns its affine operator value. -/
@[simp] theorem coe_apply
    (problem : AffineVariationalInequalityProblem E) (w : E) :
    problem w = problem.operator w :=
  rfl

/-- The linear part of the affine operator satisfies `⟪Bh, h⟫ ≥ 0` for every `h ∈ E`. -/
theorem linear_nonnegative
    (problem : AffineVariationalInequalityProblem E) (h : E) :
    0 ≤ problem.operator.linear h h :=
  problem.operator_linear_isNonneg.nonneg h

/-- A point `wStar` solves `VI(Q, B)` when it lies in `Q` and satisfies the defining variational
inequality against every `w ∈ Q`. -/
def IsSolution (problem : AffineVariationalInequalityProblem E) (wStar : E) : Prop :=
  wStar ∈ problem.feasibleSet ∧ ∀ w ∈ problem.feasibleSet, 0 ≤ problem wStar (w - wStar)

-- Proof sketch: unfold `IsSolution`; the conjunction is exactly feasibility together with the
-- displayed inequality against every feasible comparison point.
/-- A point solves `VI(Q, B)` exactly when it is feasible and satisfies the defining inequality
against every feasible comparison point. -/
theorem isSolution_iff (problem : AffineVariationalInequalityProblem E) (wStar : E) :
    problem.IsSolution wStar ↔
      wStar ∈ problem.feasibleSet ∧
        ∀ w ∈ problem.feasibleSet, 0 ≤ problem wStar (w - wStar) :=
  Iff.rfl

end AffineVariationalInequalityProblem

end
