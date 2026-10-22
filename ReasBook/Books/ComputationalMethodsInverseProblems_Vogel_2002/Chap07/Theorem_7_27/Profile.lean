/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19.KernelMoment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section

namespace TikhonovDiscrepancy

/-- Helper for Theorem 7.27: reindex the positive-mode sum over `Finset.Icc`
to the zero-based `Finset.range` form used by `KernelMoment.quadratureSum`. -/
private lemma sum_Icc_one_eq_sumRangeShift
    {α : Type _} [AddCommMonoid α] (f : ℕ → α) :
    ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1)
  | n => by
      -- Convert the closed interval to the matching half-open interval, then
      -- reuse the standard `sum_range` normalization.
      rw [← Finset.Ico_add_one_right_eq_Icc]
      rw [Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]

/-- Helper for Theorem 7.27: rewrite `KernelMoment.quadratureSum` directly as
the zero-based finite series over the rescaled positive modes. -/
lemma quadratureSum_eq_sumRangeSeries_local
    (p : ℝ) (j : ℕ) (s : ℝ) (n : ℕ) (h : ℝ) :
    KernelMoment.quadratureSum p j s n h =
      ∑ k ∈ Finset.range n, h * KernelMoment.integrand p j s (((k + 1 : ℕ) : ℝ) * h) := by
  -- Expand the owner definition once, then apply the reindexing lemma above.
  rw [KernelMoment.quadratureSum_def, Finset.mul_sum, sum_Icc_one_eq_sumRangeShift]

/-- Helper for Theorem 7.27: the rescaled step `h = (α / c) ^ (1 / p)`
recovers the base ratio `α / c` after taking the `p`-th real power. -/
lemma rescaledStep_rpow_eq_ratio
    {α c p : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) :
    (((α / c) ^ (1 / p)) ^ p) = α / c := by
  have hp_ne : p ≠ 0 := by
    linarith
  have hαc_pos : 0 < α / c := by
    exact div_pos hα hc
  -- First merge the two powers, then simplify the exponent `(1 / p) * p`.
  calc
    ((α / c) ^ (1 / p)) ^ p = (α / c) ^ ((1 / p) * p) := by
      rw [← Real.rpow_mul (le_of_lt hαc_pos)]
    _ = (α / c) ^ (1 : ℝ) := by
      congr 2
      field_simp [hp_ne]
    _ = α / c := by
      rw [Real.rpow_one]

/-- Helper for Theorem 7.27: the rescaled mode variable
`((i : ℝ) * (α / c) ^ (1 / p)) ^ p` matches the algebraic ratio
`(i : ℝ) ^ p * (α / c)`. -/
lemma rescaledMode_rpow_eq_ratio
    {α c p : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) (i : ℕ+) :
    (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p) = (i : ℝ) ^ p * (α / c) := by
  have hi_pos : 0 < (i : ℝ) := by
    exact_mod_cast i.2
  have hstep_pos : 0 < ((α / c) ^ (1 / p)) := by
    exact Real.rpow_pos_of_pos (div_pos hα hc) (1 / p)
  -- Rewrite the mode power through `Real.mul_rpow`, then substitute the base
  -- ratio recovered by `rescaledStep_rpow_eq_ratio`.
  calc
    (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)
        = (i : ℝ) ^ p * (((α / c) ^ (1 / p)) ^ p) := by
            rw [Real.mul_rpow hi_pos.le hstep_pos.le]
    _ = (i : ℝ) ^ p * (α / c) := by
          rw [rescaledStep_rpow_eq_ratio hα hc hp]

/-- Helper for Theorem 7.27: the Tikhonov denominator `α + c i^{-p}` factors
through the rescaled mode variable used in the quadrature profile. -/
lemma tikhonovDenominator_eq_rescaledMode
    {α c p : ℝ} (hα : 0 < α) (hc : 0 < c) (hp : 1 < p) (i : ℕ+) :
    α + c * (i : ℝ) ^ (-p) =
      c * (i : ℝ) ^ (-p) *
        (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) := by
  have hi_pos : 0 < (i : ℝ) := by
    exact_mod_cast i.2
  have hi_cancel : (i : ℝ) ^ (-p) * (i : ℝ) ^ p = 1 := by
    rw [← Real.rpow_add hi_pos, neg_add_cancel, Real.rpow_zero]
  have hscale_cancel : c * (α / c) = α := by
    field_simp [hc.ne']
  have hfirst :
      c * (i : ℝ) ^ (-p) * ((i : ℝ) ^ p * (α / c)) = α := by
    -- Pull the `c` and `α / c` terms together, then cancel the mode powers.
    calc
      c * (i : ℝ) ^ (-p) * ((i : ℝ) ^ p * (α / c))
          = (c * (α / c)) * ((i : ℝ) ^ (-p) * (i : ℝ) ^ p) := by ring
      _ = α := by rw [hscale_cancel, hi_cancel, mul_one]
  -- Rewrite the standalone `α` term through the same rescaled mode factor.
  calc
    α + c * (i : ℝ) ^ (-p)
        = c * (i : ℝ) ^ (-p) * ((i : ℝ) ^ p * (α / c)) +
            c * (i : ℝ) ^ (-p) := by
              rw [hfirst]
    _ = c * (i : ℝ) ^ (-p) * (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p) +
          c * (i : ℝ) ^ (-p) := by
            rw [rescaledMode_rpow_eq_ratio hα hc hp i]
    _ = c * (i : ℝ) ^ (-p) *
          (1 + (((i : ℝ) * ((α / c) ^ (1 / p))) ^ p)) := by
            ring

end TikhonovDiscrepancy
