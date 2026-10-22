/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Corollary 21.12: the time-change factor `K²` viewed in `NNReal`. -/
noncomputable def brownianScalingTime (K : ℝ) : NNReal :=
  ⟨K ^ 2, sq_nonneg K⟩

/-- The Brownian scaling transform with factor `K`, given by `t ↦ K⁻¹ B (K² t)`. -/
noncomputable def brownianScaling (B : NNReal → Ω → ℝ) (K : ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ K⁻¹ * B (brownianScalingTime K * t) ω

/-- Helper for Corollary 21.12: evaluating the scaled Brownian path gives the defining formula
`K⁻¹ * B (K² t)`. -/
@[simp] theorem brownianScaling_apply
    (B : NNReal → Ω → ℝ) (K : ℝ) (t : NNReal) (ω : Ω) :
    brownianScaling B K t ω = K⁻¹ * B (brownianScalingTime K * t) ω :=
  rfl

namespace IsBrownianMotion

/-- Helper for Corollary 21.12: scaling a Brownian motion preserves Gaussian finite-dimensional
laws. -/
lemma brownianScaling_isGaussianProcess
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (K : ℝ) :
    IsGaussianProcess (brownianScaling B K) μ := by
  -- Proof comment: first reindex the Brownian process along `t ↦ K² t`, then apply the constant
  -- scalar multiplication `K⁻¹` to each coordinate.
  let hGaussian : IsGaussianProcess B μ := IsBrownianMotion.isGaussianProcess hB
  have hTimeChanged : IsGaussianProcess (fun t ω ↦ B (brownianScalingTime K * t) ω) μ :=
    hGaussian.comp_right (fun t : NNReal ↦ brownianScalingTime K * t)
  simpa [brownianScaling, smul_eq_mul] using
    IsGaussianProcess.smul (fun _ : NNReal ↦ K⁻¹) hTimeChanged

/-- Helper for Corollary 21.12: composing a continuous path with `t ↦ K² t` and multiplying by
`K⁻¹` preserves continuity. -/
lemma continuous_brownianScalingPath_of_continuous
    {f : NNReal → ℝ} (hf : Continuous f) (K : ℝ) :
    Continuous (fun t : NNReal ↦ K⁻¹ * f (brownianScalingTime K * t)) := by
  -- Proof comment: the time dilation is continuous on `NNReal`, and multiplying the resulting
  -- real-valued path by the constant `K⁻¹` keeps continuity.
  have hScale : Continuous (fun t : NNReal ↦ brownianScalingTime K * t) :=
    continuous_const.mul continuous_id
  exact continuous_const.mul (hf.comp hScale)

/-- Helper for Corollary 21.12: Brownian scaling preserves almost-sure continuity of sample paths.
-/
lemma brownianScaling_hasAlmostSurelyContinuousPaths
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (K : ℝ) :
    HasAlmostSurelyContinuousPaths μ (brownianScaling B K) := by
  -- Proof comment: apply the deterministic continuity lemma to each almost-surely continuous
  -- Brownian sample path.
  filter_upwards [hB.continuous_paths] with ω hω
  simpa [HasAlmostSurelyContinuousPaths, processPath, brownianScaling] using
    continuous_brownianScalingPath_of_continuous (f := fun t ↦ B t ω) hω K

/-- Helper for Corollary 21.12: the covariance kernel of the scaled process is still `s ⊓ t`. -/
lemma brownianScaling_covariance_eq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {K : ℝ} (hK : K ≠ 0) (s t : NNReal) :
    cov[brownianScaling B K s, brownianScaling B K t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: order the times, reduce to the Brownian covariance at the scaled times, and
  -- then cancel the factor `(K⁻¹)^2 * K^2`.
  wlog hst : s ≤ t generalizing s t with hswap
  · rw [covariance_comm, inf_comm]
    exact hswap t s (le_of_not_ge hst)
  have hScaled : brownianScalingTime K * s ≤ brownianScalingTime K * t := by
    simpa [mul_comm] using mul_le_mul_right hst (brownianScalingTime K)
  have hCancel : K⁻¹ * (K⁻¹ * (K ^ 2)) = 1 := by
    calc
      K⁻¹ * (K⁻¹ * (K ^ 2)) = (K⁻¹ * K) * (K⁻¹ * K) := by ring
      _ = 1 * 1 := by simp [hK]
      _ = 1 := by ring
  change cov[fun ω ↦ K⁻¹ * B (brownianScalingTime K * s) ω,
    fun ω ↦ K⁻¹ * B (brownianScalingTime K * t) ω; μ] = ((s ⊓ t : NNReal) : ℝ)
  rw [covariance_const_mul_left, covariance_const_mul_right,
    IsBrownianMotion.covariance_eq hB (brownianScalingTime K * s) (brownianScalingTime K * t)]
  calc
    K⁻¹ * (K⁻¹ * ((((brownianScalingTime K * s) ⊓ (brownianScalingTime K * t) : NNReal) : ℝ))) =
        K⁻¹ * (K⁻¹ * (((brownianScalingTime K * s : NNReal) : ℝ))) := by
          rw [inf_eq_left.mpr hScaled]
    _ = K⁻¹ * (K⁻¹ * (((brownianScalingTime K : NNReal) : ℝ) * (s : ℝ))) := by
          simp [NNReal.coe_mul]
    _ = (K⁻¹ * (K⁻¹ * (K ^ 2))) * (s : ℝ) := by
          simp [brownianScalingTime]
          ring
    _ = (1 : ℝ) * (s : ℝ) := by rw [hCancel]
    _ = ((s ⊓ t : NNReal) : ℝ) := by
          simp [inf_eq_left.mpr hst]

-- Proof sketch: verify the Brownian-motion axioms for the rescaled process. The starting value is
-- preserved because `B 0 = 0`; independent and stationary increments are inherited from `B` after
-- the deterministic time change `t ↦ K^2 t`; the Gaussian marginal rescales by
-- `ProbabilityTheory.gaussianReal_const_mul`; and almost-sure continuity is preserved by
-- composition with the continuous time dilation and scalar multiplication.
/-- Corollary 21.12: scaling property of Brownian motion. If `B` is a Brownian motion and
`K ≠ 0`, then the rescaled process `t ↦ K⁻¹ B (K² t)` is again a Brownian motion. -/
theorem scaling
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {K : ℝ} (hK : K ≠ 0) :
    IsBrownianMotion μ (brownianScaling B K) := by
  -- Proof comment: use the centered-Gaussian Brownian characterization and discharge each field
  -- for the scaled process with the dedicated helper lemmas above.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, brownianScaling_isGaussianProcess hB K, ?_,
    brownianScaling_covariance_eq hB hK, brownianScaling_hasAlmostSurelyContinuousPaths hB K⟩
  · -- Proof comment: at time `0`, the scaled process still evaluates to the zero function.
    funext ω
    simp [hB.zero]
  · intro t
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    -- Proof comment: each scaled marginal is a constant multiple of the Brownian marginal at time
    -- `K² t`, so centeredness is inherited from `hB.mean_zero`.
    change ∫ ω, K⁻¹ * B (brownianScalingTime K * t) ω ∂μ = 0
    rw [integral_const_mul, hB.mean_zero (brownianScalingTime K * t)]
    ring

end IsBrownianMotion

end ProbabilityTheory
