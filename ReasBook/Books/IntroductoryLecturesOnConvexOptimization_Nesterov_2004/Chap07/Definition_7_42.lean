/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealInnerProductSpace

universe u v

/-
Definition 7.42 lies in the chapter's finite max-inner / log-sum-exp smoothing domain.

Sampled owner-style declarations:
- `η` and `eta_apply` in `Chap06/Proposition_6_23` / `Definition_6_27`, the chapter owner for the
  positive-parameter log-sum-exp potential on a finite score family;
- `logSumExpAbsoluteValueSmoothing` in `Chap06/Definition_6_22`, the nearby chapter owner pattern
  for nonempty finite-family log-sum-exp smoothings;
- `ConvexBody.supportFunctionReal` in `Chap07/Definition_7_24`, an intrinsic Chapter 7 owner that
  replaces a concrete `ℝⁿ` model by a real inner-product space parameter;
- `smoothMaxInnerApproximation_hessian_quadratic_form_le` in `Chap07/Proposition_7_21`, the
  direct downstream theorem using the owner introduced here.

Best owner abstraction:
- source-facing: `smoothMaxInnerApproximation`, since Definition 7.42 introduces the smoothing of
  `x ↦ max_i ⟪a_i, x⟫`;
- core/canonical: the Chapter 6 positive-parameter log-sum-exp owner `η`;
- bridge/view: the score vector `WithLp.toLp 2 (fun i ↦ ⟪a i, x⟫)`.

Primitive data:
- a nonempty finite index type `ι`;
- a family `a : ι → E`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the source-facing smoothing function itself;
- the bridge theorem `smoothMaxInnerApproximation_apply`, obtained by evaluating `η` on the score
  vector `i ↦ ⟪a i, x⟫`.

Source/core/bridge triage:
- source-facing: Definition 7.42's smoothing of the finite max-inner objective;
- core/canonical: `η`;
- bridge/view: the evaluation of `η` on the inner-product score vector.

This file stays at the source-facing layer. The previous version hard-coded the concrete ambient
model `EuclideanSpace ℝ (Fin n)` and the family index `Fin m`; the refined owner keeps the same
mathematical formula but moves to the intrinsic real inner-product / finite-family layer and
exposes Definition 7.42 as a thin specialization of the Chapter 6 owner `η`.
-/

variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 7.42: for vectors `aᵢ ∈ E` in a real inner-product space `E` and a positive
parameter `μ`, the smooth approximation of `x ↦ max_i ⟪aᵢ, x⟫` is the Chapter 6 log-sum-exp owner
`η` applied to the score vector `i ↦ ⟪aᵢ, x⟫`, i.e.
`x ↦ μ log (∑ i, exp (⟪aᵢ, x⟫ / μ))`, for a nonempty finite family indexed by `ι`. -/
def smoothMaxInnerApproximation (a : ι → E) (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  fun x ↦ η μ (WithLp.toLp 2 fun i ↦ ⟪a i, x⟫)

-- Proof sketch: unfold `smoothMaxInnerApproximation`; this is the defining specialization of the
-- Chapter 6 owner `η` to the score family `i ↦ ⟪a i, x⟫`.
omit [Nonempty ι] in
/-- Unfolding `smoothMaxInnerApproximation` gives the Chapter 6 log-sum-exp owner `η` applied to
the score family `i ↦ ⟪a i, x⟫`. -/
@[simp] theorem smoothMaxInnerApproximation_def
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) :
    smoothMaxInnerApproximation a μ =
      fun x ↦ η μ (WithLp.toLp 2 fun i ↦ ⟪a i, x⟫) := by
  -- This is exactly the defining specialization of `η` to the inner-product score family.
  rfl

omit [Nonempty ι] in
-- Proof sketch: evaluate `smoothMaxInnerApproximation_def` at `x`, then rewrite the resulting
-- `η` term with `eta_apply`.
/-- Evaluating `smoothMaxInnerApproximation a μ` at `x` gives the defining log-sum-exp formula
`μ log (∑ i exp (⟪aᵢ, x⟫ / μ))`. -/
@[simp] theorem smoothMaxInnerApproximation_apply
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    smoothMaxInnerApproximation a μ x =
      (μ : ℝ) * Real.log (∑ i : ι, Real.exp (⟪a i, x⟫ / (μ : ℝ))) := by
  -- Evaluate the owner at `x` and rewrite with the Chapter 6 coordinate formula for `η`.
  simpa [smoothMaxInnerApproximation] using
    (eta_apply μ (WithLp.toLp 2 fun i ↦ ⟪a i, x⟫))

-- Proof sketch: apply function extensionality and use
-- `smoothMaxInnerApproximation_apply` pointwise.
omit [Nonempty ι] in
/-- The smoothing map `smoothMaxInnerApproximation a μ` is exactly the textbook log-sum-exp
function `x ↦ μ log (∑ i exp (⟪aᵢ, x⟫ / μ))`. -/
theorem smoothMaxInnerApproximation_eq_logSumExp
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) :
    smoothMaxInnerApproximation a μ =
      fun x ↦
        (μ : ℝ) * Real.log (∑ i : ι, Real.exp (⟪a i, x⟫ / (μ : ℝ))) := by
  -- Pointwise evaluation gives the textbook formula, so extensionality closes the function
  -- equality.
  funext x
  -- The pointwise formula is exactly the required equality at `x`.
  exact smoothMaxInnerApproximation_apply a μ x

end
