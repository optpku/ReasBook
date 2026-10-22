/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_10.Filters
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section

namespace TikhonovGcv

/-- Helper for Theorem 7.29: on the algebraic singular-value mode
`c * k^{-p}`, the discrete Tikhonov filter is the rational profile with scale
parameter `((n * α) / c) * k^p`. -/
lemma discreteTikhonov_eq_modeProfile
    {n : ℕ} {α c p : ℝ} (h_c : 0 < c) (k : ℕ+) :
    SpectralFilter.discreteTikhonov n α (c * (k : ℝ) ^ (-p)) =
      1 / (1 + (((n : ℝ) * α) / c) * (k : ℝ) ^ p) := by
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast k.2
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  -- Rewrite the negative power as a reciprocal before clearing denominators.
  rw [SpectralFilter.discreteTikhonov_eq, Real.rpow_neg hk_pos.le p]
  field_simp [h_c.ne', hk_ne]

/-- Helper for Theorem 7.29: the squared discrete Tikhonov filter deviation on
the algebraic singular-value mode is a rational function of the scaled mode
parameter. -/
lemma discreteTikhonov_sub_one_sq_eq_modeProfile
    {n : ℕ} {α c p : ℝ} (h_c : 0 < c) (h_alpha : 0 < α) (k : ℕ+) :
    (SpectralFilter.discreteTikhonov n α (c * (k : ℝ) ^ (-p)) - 1) ^ 2 =
      ((((n : ℝ) * α) / c) ^ 2 * (k : ℝ) ^ (2 * p)) /
        (1 + (((n : ℝ) * α) / c) * (k : ℝ) ^ p) ^ 2 := by
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast k.2
  set τ : ℝ := ((n : ℝ) * α) / c
  have hτ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    positivity
  -- First convert the filter to the rational mode profile, then simplify the
  -- squared deviation explicitly.
  rw [discreteTikhonov_eq_modeProfile (h_c := h_c) (k := k)]
  set A : ℝ := τ * (k : ℝ) ^ p
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hden_ne : 1 + A ≠ 0 := by
    positivity
  have hlin :
      1 / (1 + A) - 1 = -(A / (1 + A)) := by
    field_simp [hden_ne]
    ring
  have hsub :
      (1 / (1 + A) - 1) ^ 2 = (A / (1 + A)) ^ 2 := by
    rw [hlin, neg_sq]
  rw [hsub]
  have hsq :
      (A / (1 + A)) ^ 2 = (A ^ 2) / (1 + A) ^ 2 := by
    field_simp [hden_ne]
  rw [hsq]
  change A ^ 2 / (1 + A) ^ 2 = (τ ^ 2 * (k : ℝ) ^ (2 * p)) / (1 + A) ^ 2
  congr 1
  have hkpow : ((k : ℝ) ^ p) ^ 2 = (k : ℝ) ^ (2 * p) := by
    calc
      ((k : ℝ) ^ p) ^ 2 = (k : ℝ) ^ p * (k : ℝ) ^ p := by ring
      _ = (k : ℝ) ^ (p + p) := by
            rw [← Real.rpow_add hk_pos]
      _ = (k : ℝ) ^ (2 * p) := by
            congr 1
            ring
  calc
    A ^ 2 = (τ * (k : ℝ) ^ p) * (τ * (k : ℝ) ^ p) := by
      simp [A, sq]
    _ = τ ^ 2 * ((k : ℝ) ^ p) ^ 2 := by ring
    _ = τ ^ 2 * (k : ℝ) ^ (2 * p) := by rw [hkpow]

/-- Helper for Theorem 7.29: the squared discrete Tikhonov filter deviation,
multiplied by the source-side decay laws `c * k^{-p}` and `b * k^{-q}`, has
the exact power-profile needed for the spectral numerator rewrite. -/
lemma discreteTikhonov_sub_one_sq_mul_decay_eq_modeProfile
    {n : ℕ} {α b c p q : ℝ} (h_c : 0 < c) (h_alpha : 0 < α) (k : ℕ+) :
    (SpectralFilter.discreteTikhonov n α (c * (k : ℝ) ^ (-p)) - 1) ^ 2 *
        (c * (k : ℝ) ^ (-p)) * (b * (k : ℝ) ^ (-q)) =
      (b * ((n : ℝ) * α) ^ 2 / c) * (k : ℝ) ^ (p - q) /
        (1 + (((n : ℝ) * α) / c) * (k : ℝ) ^ p) ^ 2 := by
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast k.2
  -- Use the exact squared-deviation profile and collapse the remaining powers.
  rw [discreteTikhonov_sub_one_sq_eq_modeProfile (h_c := h_c) (h_alpha := h_alpha) (k := k)]
  rw [Real.rpow_neg hk_pos.le p, Real.rpow_neg hk_pos.le q]
  set τ : ℝ := ((n : ℝ) * α) / c
  have hpow :
      (k : ℝ) ^ (2 * p) * (((k : ℝ) ^ p)⁻¹ * ((k : ℝ) ^ q)⁻¹) = (k : ℝ) ^ (p - q) := by
    calc
      (k : ℝ) ^ (2 * p) * (((k : ℝ) ^ p)⁻¹ * ((k : ℝ) ^ q)⁻¹)
          = (k : ℝ) ^ (2 * p) * ((k : ℝ) ^ (-p) * (k : ℝ) ^ (-q)) := by
              rw [← Real.rpow_neg hk_pos.le p, ← Real.rpow_neg hk_pos.le q]
      _ = (k : ℝ) ^ (2 * p + (-p + -q)) := by
            rw [← Real.rpow_add hk_pos, ← Real.rpow_add hk_pos]
      _ = (k : ℝ) ^ (p - q) := by
            congr 1
            ring
  calc
    (τ ^ 2 * (k : ℝ) ^ (2 * p) / (1 + τ * (k : ℝ) ^ p) ^ 2) *
        (c * ((k : ℝ) ^ p)⁻¹) * (b * ((k : ℝ) ^ q)⁻¹)
        =
          (τ ^ 2 * c * b) *
            ((k : ℝ) ^ (2 * p) * (((k : ℝ) ^ p)⁻¹ * ((k : ℝ) ^ q)⁻¹)) /
              (1 + τ * (k : ℝ) ^ p) ^ 2 := by
                ring
    _ =
          (τ ^ 2 * c * b) * (k : ℝ) ^ (p - q) /
            (1 + τ * (k : ℝ) ^ p) ^ 2 := by
              rw [hpow]
    _ =
          (b * ((n : ℝ) * α) ^ 2 / c) * (k : ℝ) ^ (p - q) /
            (1 + τ * (k : ℝ) ^ p) ^ 2 := by
              dsimp [τ]
              field_simp [h_c.ne']
    _ =
          (b * ((n : ℝ) * α) ^ 2 / c) * (k : ℝ) ^ (p - q) /
            (1 + (((n : ℝ) * α) / c) * (k : ℝ) ^ p) ^ 2 := by
              simp [τ]

end TikhonovGcv
