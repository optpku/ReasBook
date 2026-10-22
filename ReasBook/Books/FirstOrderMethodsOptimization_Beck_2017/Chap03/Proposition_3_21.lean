/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)

local notation "Pₛ" => metricProjection C hC_nonempty hC_closed hC_convex
local notation "P" => fun x ↦ (Pₛ x : E)

/- Proposition 3.21 is `source-facing`: it states the fixed-point property of the metric
projection along the outward ray from `P_C x` through `x`. Its owner abstraction is the chapter
metric projection `metricProjection` from Proposition 3.12, and the only derived ingredient needed
here is the Hilbert-space variational inequality supplied by
`norm_eq_iInf_iff_real_inner_le_zero`. -/

-- Proof sketch: the projection point `P_C x` satisfies the variational inequality
-- `⟪x - P_C x, w - P_C x⟫ ≤ 0` for every `w ∈ C`. Multiplying by `λ ≥ 0` shows the same
-- inequality for `y = P_C x + λ • (x - P_C x)`, so `P_C x` is also a minimizer of the distance
-- from `y` to `C`. Comparing this minimizer with the chosen metric projection `P_C y` and using
-- the same variational inequality for both points forces `P_C y = P_C x`.
/-- Proposition 3.21: if `C` is a nonempty closed convex subset of a complete real inner product
space, then every point on the ray `P_C x + λ (x - P_C x)` with `λ ≥ 0` has the same metric
projection onto `C` as `x`. -/
theorem metricProjection_add_smul_sub_metricProjection_eq (x : E) (lam : ℝ) (hlam : 0 ≤ lam) :
    P (P x + lam • (x - P x)) = P x := by
  let y : E := P x + lam • (x - P x)
  have hPx : P x ∈ C := (Pₛ x).2
  have hy_Px : ∀ w ∈ C, inner ℝ (y - P x) (w - P x) ≤ 0 := by
    intro w hw
    have hx := inner_sub_metricProjection_le_zero C hC_nonempty hC_closed hC_convex x w hw
    have hy : y - P x = lam • (x - P x) := by
      dsimp [y]
      abel
    rw [hy, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos hlam hx
  have hPx_min : ‖y - P x‖ = ⨅ z : C, ‖y - z‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex hPx).2 hy_Px
  have hPy_min : ‖y - P y‖ = ⨅ z : C, ‖y - z‖ := by
    simpa [y] using norm_sub_metricProjection_eq_iInf C hC_nonempty hC_closed hC_convex y
  have hPy : ∀ w ∈ C, inner ℝ (y - P y) (w - P y) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC_convex (Pₛ y).2).1 hPy_min
  have h1 : inner ℝ (y - P y) (P x - P y) ≤ 0 := hPy (P x) hPx
  have h2 : inner ℝ (y - P x) (P y - P x) ≤ 0 := hy_Px (P y) (Pₛ y).2
  have hnorm : ‖P y - P x‖ ^ 2 ≤ 0 := by
    calc
      ‖P y - P x‖ ^ 2 = inner ℝ (P y - P x) (P y - P x) := by
        rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ ((y - P x) - (y - P y)) (P y - P x) := by
        congr 1
        abel
      _ = inner ℝ (y - P x) (P y - P x) - inner ℝ (y - P y) (P y - P x) := by
        rw [inner_sub_left]
      _ ≤ 0 := by
        have h1' : 0 ≤ inner ℝ (y - P y) (P y - P x) := by
          have h1'' : inner ℝ (y - P y) (-(P y - P x)) ≤ 0 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1
          rw [inner_neg_right] at h1''
          linarith
        linarith
  have hzero : ‖P y - P x‖ = 0 := by
    nlinarith [sq_nonneg ‖P y - P x‖, hnorm]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end
