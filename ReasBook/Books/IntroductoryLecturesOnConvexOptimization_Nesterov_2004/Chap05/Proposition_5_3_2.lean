/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement

noncomputable section

universe u

section SharedHelpers

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Proposition 5.3.2: completing the square against the Newton step rewrites the
Hessian quadratic form in terms of the barrier expression and the inverse-Hessian pairing. -/
lemma hessian_inverse_gradient_completed_square
    {F : E → ℝ} {x u : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    inner ℝ
        (u - (hessian F x).inverse (∇ F x))
        (hessian F x (u - (hessian F x).inverse (∇ F x))) =
      inner ℝ u (hessian F x u) - 2 * inner ℝ (∇ F x) u +
        inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) := by
  let v := (hessian F x).inverse (∇ F x)
  have hHv : hessian F x v = ∇ F x := hInv.self_apply_inverse (∇ F x)
  have hcross_left : inner ℝ u (hessian F x v) = inner ℝ (∇ F x) u := by
    rw [hHv, real_inner_comm]
  have hcross_right : inner ℝ v (hessian F x u) = inner ℝ (∇ F x) u := by
    calc
      inner ℝ v (hessian F x u) = inner ℝ (hessian F x u) v := by
        rw [real_inner_comm]
      _ = inner ℝ u (hessian F x v) := by
        simpa using hPos.isSymmetric u v
      _ = inner ℝ (∇ F x) u := hcross_left
  have hdiag : inner ℝ v (hessian F x v) = inner ℝ (∇ F x) v := by
    rw [hHv, real_inner_comm]
  -- Expand the shifted quadratic form and then rewrite both cross terms by symmetry and
  -- `hInv.self_apply_inverse`.
  calc
    inner ℝ (u - v) (hessian F x (u - v)) =
        inner ℝ u (hessian F x u) - inner ℝ u (hessian F x v) -
          inner ℝ v (hessian F x u) + inner ℝ v (hessian F x v) := by
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
      ring
    _ = inner ℝ u (hessian F x u) - inner ℝ (∇ F x) u - inner ℝ (∇ F x) u +
          inner ℝ (∇ F x) v := by
      rw [hcross_left, hcross_right, hdiag]
    _ = inner ℝ u (hessian F x u) - 2 * inner ℝ (∇ F x) u +
          inner ℝ (∇ F x) v := by
      ring
    _ = inner ℝ u (hessian F x u) - 2 * inner ℝ (∇ F x) u +
          inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) := by
      rfl

/-- Helper for Proposition 5.3.2: the inverse-Hessian pairing of the gradient with itself is
nonnegative under Hessian positivity. -/
lemma gradient_inverse_hessian_gradient_nonneg
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    0 ≤ inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) := by
  let v := (hessian F x).inverse (∇ F x)
  have hnonneg : 0 ≤ inner ℝ v (hessian F x v) := hPos.inner_nonneg_right v
  have hHv : hessian F x v = ∇ F x := hInv.self_apply_inverse (∇ F x)
  -- Rewrite the nonnegative quadratic form at the Newton step into the target pairing.
  calc
    0 ≤ inner ℝ v (hessian F x v) := hnonneg
    _ = inner ℝ (∇ F x) v := by
      rw [hHv, real_inner_comm]
    _ = inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) := by
      rfl

/-- Helper for Proposition 5.3.2: the barrier inequality is equivalent to bounding the
inverse-Hessian pairing of the gradient with itself. -/
theorem barrier_parameter_bound_iff_inverse_hessian_pairing_le
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) ≤ (ν : ℝ) := by
  constructor
  · intro hbound
    have hstep := hbound ((hessian F x).inverse (∇ F x))
    have hHv : hessian F x ((hessian F x).inverse (∇ F x)) = ∇ F x :=
      hInv.self_apply_inverse (∇ F x)
    -- Evaluate the barrier bound at the Newton step to isolate the inverse-Hessian pairing.
    have hpair : inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) ≤ (ν : ℝ) := by
      have hstep' :
          2 * inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) ≤
            (ν : ℝ) + inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) := by
        simpa [hHv, real_inner_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using hstep
      nlinarith
    exact hpair
  · intro hpair u
    have hnonneg :
        0 ≤ inner ℝ
          (u - (hessian F x).inverse (∇ F x))
          (hessian F x (u - (hessian F x).inverse (∇ F x))) :=
      hPos.inner_nonneg_right (u - (hessian F x).inverse (∇ F x))
    -- Completing the square reduces the reverse implication to the assumed pairing bound.
    rw [hessian_inverse_gradient_completed_square (F := F) (x := x) (u := u) hPos hInv] at hnonneg
    nlinarith

end SharedHelpers

/- This file lies in the Chapter 5 barrier-parameter / Newton-decrement domain.

Sampled owner declarations in this domain:
* `newtonDecrement` and `newtonDecrement_def` in `Definition_5_0_24`, the pointwise owner for the
  Newton decrement from local Hessian positivity and invertibility data;
* `NewtonDecrement.ofPosDefMem` and `NewtonDecrement.ofPosDefMem_def` in `Definition_5_0_24`, the
  positive-definite-Hessian domain bridge obtained from `x ∈ dom`;
* `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem` and
  `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` in `Definition_5_0_23`, the canonical
  way to derive the local Hessian data from domain hypotheses;
* `barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the local-norm-square
  companion reformulation of the same fixed-point inequality.

Best owner abstraction:
* source-facing: the fixed-point barrier inequality in all directions;
* core/canonical: the Chapter 5 Newton decrement owners `λ[F; x | hPos; hInv]` and `λ[F; x | hx]`;
* bridge/view: `newtonDecrement_def` and `NewtonDecrement.ofPosDefMem_def`, which rewrite those
  owner surfaces as the inverse-Hessian gradient pairing.

Primitive data:
* a function `F`, a point `x`, and a barrier parameter `ν`;
* the pointwise Hessian positivity and invertibility data at `x`.

Derived API:
* the pointwise Newton-decrement bound `λ[F; x | hPos; hInv] ≤ √ν`;
* the inverse-Hessian gradient pairing bound as a companion reformulation;
* the domain-level Newton-decrement bound `λ[F; x | hx] ≤ √ν`.

The public surface therefore states Proposition 5.3.2 first on the Chapter 5 pointwise owner
`λ[F; x | hPos; hInv]`, keeps the inverse-Hessian pairing only as a companion reformulation for
duality arguments, and reserves `λ[F; x | hx]` for the separate positive-definite-domain bridge. -/

section PointwiseOwner

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: complete the square with
-- `u - (hessian F x).inverse (∇ F x)` and then rewrite the maximizing value by
-- `newtonDecrement_def`, identifying it with the pointwise Newton decrement
-- `λ[F; x | hPos; hInv]`.
/-- Proposition 5.3.2, pointwise owner form: if the Hessian at `x` is positive and invertible,
then the barrier inequality from Definition 5.3.2 is equivalent to the Chapter 5 pointwise
Newton-decrement bound `λ[F; x | hPos; hInv] ≤ √ν`. -/
theorem barrier_parameter_bound_iff_newtonDecrement_le_sqrt
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      λ[F; x | hPos; hInv] ≤ Real.sqrt (ν : ℝ) := by
  -- Rewrite the pointwise owner into the inverse-Hessian pairing surface from Proposition 5.3.2.
  rw [newtonDecrement_def F x hPos hInv]
  constructor
  · intro hbound
    exact (Real.sqrt_le_sqrt_iff ν.2).2 <|
      (barrier_parameter_bound_iff_inverse_hessian_pairing_le
        (F := F) (ν := ν) (x := x) hPos hInv).1 hbound
  · intro hbound
    exact (barrier_parameter_bound_iff_inverse_hessian_pairing_le
      (F := F) (ν := ν) (x := x) hPos hInv).2 <|
      (Real.sqrt_le_sqrt_iff ν.2).1 hbound

end PointwiseOwner

section PointwiseCompanion

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: complete the square with
-- `u - (hessian F x).inverse (∇ F x)` and use the positive / invertible Hessian supplied by the
-- pointwise hypotheses at `x` to identify the supremum of
-- `2 ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫` with the inverse-Hessian pairing
-- `⟪∇ F(x), (∇² F(x))⁻¹ ∇ F(x)⟫`.
/-- Proposition 5.3.2, companion inverse-Hessian form: if the Hessian at `x` is positive and
invertible, then the barrier inequality from Definition 5.3.2 is equivalent to the
inverse-Hessian pairing bound `⟪∇ F(x), [∇² F(x)]⁻¹ ∇ F(x)⟫ ≤ ν`. -/
theorem barrier_parameter_bound_iff_gradient_inverse_hessian_gradient_le
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) ≤ (ν : ℝ) := by
  -- This companion theorem is exactly the inverse-Hessian-pairing core equivalence above.
  simpa using
    barrier_parameter_bound_iff_inverse_hessian_pairing_le (F := F) (ν := ν) (x := x) hPos hInv

end PointwiseCompanion

section NewtonDecrementBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

-- Proof sketch: apply the pointwise owner theorem
-- `barrier_parameter_bound_iff_newtonDecrement_le_sqrt` to the positive and invertible Hessian
-- witnesses canonically supplied by `HasPositiveDefiniteHessianOn dom F`, then identify the
-- resulting pointwise owner with the domain notation `λ[F; x | hx]`.
/-- Under the positive-definite-Hessian owner hypothesis, the domain-level bridge form of
the fixed-point barrier inequality is equivalently the owner-level Newton-decrement bound
`λ[F; x | hx] ≤ √ν`. -/
theorem barrier_parameter_bound_iff_newtonDecrement_ofPosDefMem_le_sqrt
    {dom : Set E} {F : E → ℝ} {ν : NNReal} [HasPositiveDefiniteHessianOn dom F] {x : E}
    (hx : x ∈ dom) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      λ[F; x | hx] ≤ Real.sqrt (ν : ℝ) := by
  have hPos : (hessian F x).IsPositive :=
    HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  have hInv : (hessian F x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)
  -- Replace the domain-level owner by the pointwise Hessian data canonically supplied by `hx`.
  simpa [newtonDecrement_def, NewtonDecrement.ofPosDefMem_def] using
    (barrier_parameter_bound_iff_newtonDecrement_le_sqrt
      (F := F) (ν := ν) (x := x) hPos hInv)

end NewtonDecrementBridge

end
