/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

local notation "Process" => NNReal → Ω → ℝ

variable [MeasurableSpace Ω]

section

variable {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W)

local notation "ℱW" => Filtration.natural W hW.stronglyMeasurable
local notation "BrownianSqSubTime" => fun t ω ↦ W t ω ^ 2 - (t : ℝ)
local notation "BrownianSelfIntegral" => fun t ω ↦ BrownianSqSubTime t ω / 2

/-- Helper for Example 25.20: almost-sure replacement preserves covariance. -/
private lemma covariance_eq_of_ae_eq
    {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  -- Rewrite the covariance through the almost-sure equal coordinate functions.
  have hIntX : ∫ ω, X ω ∂μ = ∫ ω, X' ω ∂μ := integral_congr_ae hX
  have hIntY : ∫ ω, Y ω ∂μ = ∫ ω, Y' ω ∂μ := integral_congr_ae hY
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/- Helper for Example 25.20: squaring the Brownian path and subtracting time preserves almost-sure
continuity. -/
/-- Helper for Example 25.20: if a path `t ↦ W t ω` is continuous, then
`t ↦ W t ω ^ 2 - t` is also continuous. -/
private lemma continuous_sqSubTime_path {ω : Ω}
    (hω : Continuous (processPath W ω)) :
    Continuous (processPath BrownianSqSubTime ω) := by
  simpa [processPath, BrownianSqSubTime] using (hω.pow 2).sub NNReal.continuous_coe

/-- Helper for Example 25.20: almost-sure continuity of `W` passes to
`t ↦ W t ω ^ 2 - t`. -/
lemma sqSubTime_hasAlmostSurelyContinuousPaths
    (_hCont : HasAlmostSurelyContinuousPaths μ W) :
    HasAlmostSurelyContinuousPaths μ BrownianSqSubTime :=
  -- Proof comment: square the almost-surely continuous Brownian path and subtract the deterministic
  -- continuous path `t ↦ t`.
  _hCont.mono continuous_sqSubTime_path

-- Proof sketch: use independent centered Brownian increments to prove the martingale property for
-- the natural filtration, and use the Gaussian marginal law at each fixed time to obtain the `L²`
-- condition.
/-- Example 25.20 (1): the Brownian motion itself, viewed as `W_t = ∫_0^t 1 dW_s`, is a
square-integrable martingale for its natural filtration. -/
theorem brownian_isSquareIntegrable_martingale
    : Martingale W ℱW μ ∧
      IsSquareIntegrableProcess W μ :=
  ⟨brownianMartingale_natural hW, fun t ↦ brownianEval_memLp_two_ofBrownianMotion hW t⟩

-- Proof sketch: combine the existing compensated-square martingale theorem for Brownian motion
-- with almost-sure continuity of Brownian paths; squaring and subtracting the deterministic path
-- `t ↦ t` preserve continuity.
/-- Companion to Example 25.20: the compensated square process `(W_t^2 - t)_{t ≥ 0}` is a continuous
martingale for the natural filtration of Brownian motion. -/
theorem brownian_sq_sub_time_continuous_martingale
    : Martingale BrownianSqSubTime ℱW μ ∧
      HasAlmostSurelyContinuousPaths μ BrownianSqSubTime :=
  ⟨brownian_sq_sub_time_martingale hW, sqSubTime_hasAlmostSurelyContinuousPaths hW.continuous_paths⟩

/- Helper for Example 25.20: the explicit Brownian self-integral formula
`t ↦ (W_t^2 - t) / 2` has square-integrable marginals. -/
lemma brownianSelfIntegral_isSquareIntegrable
    (_hW : IsBrownianMotion μ W) :
    IsSquareIntegrableProcess BrownianSelfIntegral μ :=
  fun t ↦
    let hBrownian : IsBrownianMotion μ W := _hW
    let hWt_memLp_four : MemLp (W t) 4 μ :=
      match eq_or_ne t 0 with
      | Or.inl ht =>
          ht ▸ (hBrownian.zero ▸ memLp_const (μ := μ) (p := (4 : ℝ≥0∞)) (0 : ℝ))
      | Or.inr ht =>
          (hBrownian.gaussian_marginal (pos_iff_ne_zero.mpr ht)).hasGaussianLaw.memLp
            ENNReal.ofNat_ne_top
    let hWtSq_memLp_two : MemLp (fun ω ↦ W t ω ^ 2) 2 μ :=
      hWt_memLp_four.norm_rpow_div (2 : ℝ≥0∞)
    let hDiff_memLp_two : MemLp (fun ω ↦ W t ω ^ 2 - (t : ℝ)) 2 μ :=
      hWtSq_memLp_two.sub (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) (t : ℝ))
    -- Then subtract the deterministic time term and divide by `2`.
    hDiff_memLp_two.const_mul ((2 : ℝ)⁻¹)

-- Proof sketch: identify `t ↦ (W_t^2 - t) / 2` with one half of the compensated-square martingale
-- from part (2); scalar multiplication preserves the martingale property and the `L²` condition.
/-- Companion to Example 25.20: the process `M_t = ∫_0^t W_s dW_s`, represented by
`t ↦ (W_t^2 - t) / 2`, is a square-integrable martingale. -/
theorem brownianSelfIntegral_isSquareIntegrable_martingale
    : Martingale BrownianSelfIntegral ℱW μ ∧
      IsSquareIntegrableProcess BrownianSelfIntegral μ :=
  ⟨
    -- Proof comment: part (2) gives a martingale, and scalar multiplication preserves martingales.
    Martingale.smul ((2 : ℝ)⁻¹) (brownian_sq_sub_time_continuous_martingale hW).1,
    brownianSelfIntegral_isSquareIntegrable hW⟩

end

end ProbabilityTheory
