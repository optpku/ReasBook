/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section

/-- Helper for Remark 4.15.1: cocoercivity and Cauchy--Schwarz give the textbook product bound. -/
private lemma cocoercive_norm_product_bound
    {D : Set H} {β : ℝ} {T : D → H} (hT : CocoerciveOn β D T) :
    ∀ x y : D, β * ‖T x - T y‖ ^ 2 ≤ ‖(x : H) - y‖ * ‖T x - T y‖ := by
  intro x y
  -- Bound the inner product from above by the product of the norms.
  exact (hT.ineq x y).trans (real_inner_le_norm ((x : H) - y) (T x - T y))

/-- The cocoercivity inequality yields the textbook pointwise `1 / β`-Lipschitz estimate. -/
-- Proof sketch: combine cocoercivity with the Cauchy--Schwarz inequality to get
-- `β * ‖T x - T y‖^2 ≤ ‖T x - T y‖ * ‖x - y‖`; if `T x = T y` the claim is immediate, and
-- otherwise divide by `‖T x - T y‖`.
private theorem norm_sub_le_inv_mul_norm_sub_of_cocoercive
    {D : Set H} {β : ℝ} {T : D → H} (hT : CocoerciveOn β D T) :
    ∀ x y : D, ‖T x - T y‖ ≤ β⁻¹ * ‖(x : H) - y‖ := by
  intro x y
  -- First convert cocoercivity into the textbook norm product inequality.
  have hbound : β * ‖T x - T y‖ ^ 2 ≤ ‖(x : H) - y‖ * ‖T x - T y‖ :=
    cocoercive_norm_product_bound hT x y
  by_cases hxy : T x = T y
  · -- In the degenerate case the left-hand norm is zero.
    have hnonneg : 0 ≤ β⁻¹ * ‖(x : H) - y‖ := by
      exact mul_nonneg (inv_nonneg.mpr hT.pos.le) (norm_nonneg _)
    simpa [hxy] using hnonneg
  · -- Otherwise the common norm factor is positive, so we cancel it.
    have hn_pos : 0 < ‖T x - T y‖ := by
      refine norm_pos_iff.mpr ?_
      exact sub_ne_zero.mpr hxy
    have hmul : β * ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
      exact le_of_mul_le_mul_right (by simpa [pow_two, mul_assoc] using hbound) hn_pos
    have hdiv : ‖T x - T y‖ ≤ ‖(x : H) - y‖ / β := by
      rw [le_div_iff₀ hT.pos]
      simpa [mul_comm] using hmul
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Remark 4.15.1: a `β`-cocoercive map on a subset of a real Hilbert space is Lipschitz with
constant `1 / β`. -/
-- Proof sketch: first derive the textbook norm inequality from cocoercivity and Cauchy--Schwarz,
-- then apply `LipschitzWith.of_dist_le'` and rewrite distances in the subtype domain as norms in
-- `H`.
theorem lipschitzWith_of_cocoercive
    {D : Set H} {β : ℝ} {T : D → H} (hT : CocoerciveOn β D T) :
    LipschitzWith (Real.toNNReal (1 / β)) T := by
  -- Convert the pointwise norm estimate into the metric Lipschitz condition.
  refine LipschitzWith.of_dist_le' ?_
  intro x y
  -- Distances in the subtype domain are ambient distances, hence ambient norms.
  simpa [Subtype.dist_eq, dist_eq_norm, Real.toNNReal_of_nonneg (one_div_nonneg.mpr hT.pos.le),
    one_div, mul_comm, mul_left_comm, mul_assoc] using
    norm_sub_le_inv_mul_norm_sub_of_cocoercive hT x y

end
