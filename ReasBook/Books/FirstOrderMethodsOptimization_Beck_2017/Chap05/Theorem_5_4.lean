/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" => projectionPoint C hC_nonempty hC_closed hC_convex

-- Proof sketch: apply the projection variational inequality to `v` with test point `P_C(w)` and to
-- `w` with test point `P_C(v)`, then add the resulting inequalities and rearrange the inner-product
-- terms to obtain the standard firm nonexpansiveness estimate.
/-- Theorem 5.4 (1): the point projection onto a nonempty closed convex set in a complete real
inner product space, hence in particular in a Euclidean space, is firmly nonexpansive. -/
theorem metricProjection_firmly_nonexpansive (v w : E) :
    inner ℝ (P v - P w) (v - w) ≥ ‖P v - P w‖ ^ 2 := by
  let p := P v
  let q := P w
  have hp : p ∈ C := by
    simpa [p] using projectionPoint_mem C hC_nonempty hC_closed hC_convex v
  have hq : q ∈ C := by
    simpa [q] using projectionPoint_mem C hC_nonempty hC_closed hC_convex w
  have hv : inner ℝ (v - p) (q - p) ≤ 0 := by
    -- The variational inequality at `v` is tested against the feasible point `q = P_C(w)`.
    simpa [p, q] using
      inner_sub_metricProjection_le_zero C hC_nonempty hC_closed hC_convex v q hq
  have hw : inner ℝ (w - q) (p - q) ≤ 0 := by
    -- The symmetric variational inequality at `w` is tested against `p = P_C(v)`.
    simpa [p, q] using
      inner_sub_metricProjection_le_zero C hC_nonempty hC_closed hC_convex w p hp
  have hv' : 0 ≤ inner ℝ (p - q) (v - p) := by
    -- Rewrite the first inequality so both terms involve the same residual `p - q`.
    have hneg : inner ℝ (v - p) (-(p - q)) ≤ 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv
    rw [inner_neg_right] at hneg
    have hcomm : 0 ≤ inner ℝ (v - p) (p - q) := by
      linarith
    rwa [real_inner_comm] at hcomm
  have hw' : inner ℝ (p - q) (w - q) ≤ 0 := by
    rwa [real_inner_comm] at hw
  have hsum : 0 ≤ inner ℝ (p - q) ((v - p) - (w - q)) := by
    -- Adding the two optimality inequalities yields the nonnegative residual pairing.
    rw [inner_sub_right]
    linarith
  have hdiff : (v - p) - (w - q) = (v - w) - (p - q) := by
    abel
  have hrewrite :
      inner ℝ (p - q) ((v - p) - (w - q)) =
        inner ℝ (p - q) (v - w) - ‖p - q‖ ^ 2 := by
    -- Normalize the residual pairing to the firm nonexpansiveness gap.
    rw [hdiff, inner_sub_right, real_inner_self_eq_norm_sq]
  linarith [hsum, hrewrite]

/-- Helper for Theorem 5.4: the point projection is pointwise nonexpansive in norm. -/
lemma projectionPoint_norm_sub_le (x y : E) :
    ‖P x - P y‖ ≤ ‖x - y‖ := by
  have hfirm :
      ‖P x - P y‖ ^ 2 ≤ inner ℝ (P x - P y) (x - y) := by
    simpa using
      metricProjection_firmly_nonexpansive C hC_nonempty hC_closed hC_convex x y
  have hcs : inner ℝ (P x - P y) (x - y) ≤ ‖P x - P y‖ * ‖x - y‖ := by
    -- Cauchy-Schwarz controls the firm nonexpansiveness inner product from above.
    exact real_inner_le_norm _ _
  -- The quadratic bound reduces to the claimed linear norm estimate.
  nlinarith [hfirm, hcs, norm_nonneg (P x - P y), norm_nonneg (x - y)]

-- Proof sketch: combine firm nonexpansiveness with Cauchy-Schwarz:
-- `‖P_C(v) - P_C(w)‖ ^ 2 ≤ ⟪P_C(v) - P_C(w), v - w⟫ ≤ ‖P_C(v) - P_C(w)‖ * ‖v - w‖`, then
-- divide by `‖P_C(v) - P_C(w)‖` in the nontrivial case, and package the conclusion in the
-- canonical `LipschitzWith 1` form.
/-- Theorem 5.4 (2): the point projection onto a nonempty closed convex set in a complete real
inner product space, hence in particular in a Euclidean space, is nonexpansive in the canonical
`LipschitzWith 1` form. -/
theorem metricProjection_nonexpansive :
    LipschitzWith 1 P := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  -- Package the pointwise norm estimate in the canonical metric formulation.
  simpa [dist_eq_norm] using
    projectionPoint_norm_sub_le C hC_nonempty hC_closed hC_convex x y

end
