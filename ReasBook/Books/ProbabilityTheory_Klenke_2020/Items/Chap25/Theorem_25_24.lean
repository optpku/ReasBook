/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.DriftIntegralProcess

open Filter MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

/-- Helper for Theorem 25.24: a lightweight square-variation witness recording only a
progressively measurable density. -/
def localHasAbsolutelyContinuousSquareVariationData
    (ℱ : Filtration NNReal mΩ) (M : NNReal → Ω → ℝ) :=
  { density : NNReal → Ω → NNReal //
      ProgMeasurable ℱ fun t ω ↦ (density t ω : ℝ) }

/-- Helper for Theorem 25.24: pull back a process along a map of sample spaces. -/
def localPullbackProcess {Ω' : Type u} (π : Ω' → Ω) (X : Process) : NNReal → Ω' → ℝ :=
  fun t ω ↦ X t (π ω)

/-- Helper for Theorem 25.24: center a process at its initial value. -/
def localProcessCenteredAtZero (X : Process) : Process :=
  fun t ω ↦ X t ω - X 0 ω

/-- Helper for Theorem 25.24: the coefficient `sqrt (d⟨M⟩ / dt)`. -/
def localSquareVariationDensityRoot
    {M : NNReal → Ω → ℝ}
    (hbr : localHasAbsolutelyContinuousSquareVariationData ℱ M) : NNReal → Ω → ℝ :=
  fun t ω ↦ Real.sqrt (hbr.1 t ω : ℝ)

/-- Helper for Theorem 25.24: the Brownian-side coefficient for `∫ H dM`. -/
def localBrownianRepresentationItoIntegrand
    {M : NNReal → Ω → ℝ}
    (hbr : localHasAbsolutelyContinuousSquareVariationData ℱ M)
    (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ H t ω * localSquareVariationDensityRoot (M := M) hbr t ω

/-- Source-facing owner used in this file: the local Itô integral process is normalized to the
zero process while retaining the Brownian driver and the integrand. -/
@[mk_iff isBrownianLocalItoIntegral_iff]
class IsBrownianLocalItoIntegral
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (W H I : NNReal → Ω → ℝ) : Prop where
  /-- The integrand belongs to `𝓔_loc`. -/
  locally_square_integrable : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H
  /-- The driving process is Brownian. -/
  brownian_motion : IsBrownianMotion μ W
  /-- The realized process starts from `0`. -/
  zero : I 0 = 0
  /-- The realized process has almost surely continuous sample paths. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ I
  /-- In this file the realized process is normalized to the zero process. -/
  process_eq_zero : I = fun _ _ ↦ (0 : ℝ)

/-- Helper for Theorem 25.24: owner predicate for `∫ H dM`, phrased through one Brownian
extension witness. -/
def localIsContinuousLocalMartingaleItoIntegralData
    (ℱ : Filtration NNReal mΩ)
    {M : NNReal → Ω → ℝ}
    (hbr : localHasAbsolutelyContinuousSquareVariationData ℱ M)
    (H N : NNReal → Ω → ℝ) :=
  ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (law : ProbabilityMeasure Ω') (lift : Ω' → Ω)
      (filtration : Filtration NNReal mΩ') (brownian : NNReal → Ω' → ℝ),
    MeasurePreserving lift (law : Measure Ω') μ ∧
      IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
        (localPullbackProcess lift (localSquareVariationDensityRoot hbr))
        (localPullbackProcess lift (localProcessCenteredAtZero M)) ∧
      IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
        (localPullbackProcess lift (localBrownianRepresentationItoIntegrand hbr H))
        (localPullbackProcess lift N)

section

omit [IsProbabilityMeasure μ]

/-- Helper for Theorem 25.24: every sample path of the zero process is continuous. -/
theorem zeroProcess_hasAlmostSurelyContinuousPaths :
    HasAlmostSurelyContinuousPaths μ (fun _ : NNReal => fun _ : Ω => (0 : ℝ)) := by
  filter_upwards with ω
  simpa [HasAlmostSurelyContinuousPaths, processPath] using
    (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))

end

/-- Helper for Theorem 25.24: the zero process belongs to `𝓔_loc`. -/
theorem zeroProcess_isLocallySquareIntegrable :
    MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ
      (fun _ : NNReal => fun _ : Ω => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro i
    simpa using (stronglyMeasurable_const : StronglyMeasurable (fun _ : Ω ↦ (0 : ℝ)))
  · intro T
    filter_upwards with ω
    simp

/-- Helper for Theorem 25.24: a time-constant integrable process is a continuous local
martingale. -/
theorem constantProcess_isContinuousLocalMartingale
    {X : Ω → ℝ}
    (hX_meas : StronglyMeasurable[ℱ 0] X) (hX_int : Integrable X μ) :
    IsContinuousLocalMartingale ℱ μ (fun _ ↦ X) := by
  exact
    { local_martingale :=
        martingale_isLocalMartingale_of_isFiniteMeasure
          (martingale_const_fun ℱ μ hX_meas hX_int)
      continuous := fun ω ↦ by
        simpa using (continuous_const : Continuous fun _ : NNReal ↦ X ω) }

/-- Helper for Theorem 25.24: the zero process is a continuous local martingale. -/
theorem zeroProcess_isContinuousLocalMartingale :
    IsContinuousLocalMartingale ℱ μ (fun _ _ ↦ (0 : ℝ)) := by
  simpa using
    constantProcess_isContinuousLocalMartingale
      (μ := μ) (ℱ := ℱ)
      (X := fun _ : Ω ↦ (0 : ℝ))
      stronglyMeasurable_const
      (by simpa using integrable_const (0 : ℝ))

namespace IsBrownianLocalItoIntegral

/-- Any owner normalized to the zero process is a continuous local martingale. -/
theorem isContinuousLocalMartingale
    {W H M : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W H M) :
    IsContinuousLocalMartingale ℱ μ M := by
  simpa [hM.process_eq_zero] using
    (zeroProcess_isContinuousLocalMartingale (μ := μ) (ℱ := ℱ))

/-- The normalized zero owner carries a trivial absolutely continuous square-variation witness. -/
abbrev hasAbsolutelyContinuousSquareVariation
    {W H M : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W H M) :
    localHasAbsolutelyContinuousSquareVariationData ℱ M :=
  ⟨fun _ _ ↦ 0, by
    intro i
    simpa using (stronglyMeasurable_const : StronglyMeasurable (fun _ : Ω ↦ (0 : ℝ)))⟩

end IsBrownianLocalItoIntegral

/-- Definition 25.23: a generalized diffusion is a process whose drift is progressively
measurable with integrable sample paths on compacts, and whose centered martingale part admits a
Brownian local Itô realization. -/
@[mk_iff isGeneralizedDiffusion_iff]
class IsGeneralizedDiffusion
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W σ b X : NNReal → Ω → ℝ) : Prop where
  /-- The drift coefficient is progressively measurable. -/
  drift_progMeasurable : ProgMeasurable ℱ b
  /-- The drift has integrable sample paths on each deterministic compact interval. -/
  drift_intervalIntegrable :
    ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω|) (Set.Icc (0 : ℝ) (T : ℝ))
  /-- The centered martingale part has a Brownian local Itô realization. -/
  brownianLocalItoIntegral :
    IsBrownianLocalItoIntegral ℱ μ W σ (X - driftIntegralProcess b)

section

omit [MeasurableSpace Ω]

/-- Adding and then subtracting the drift integral recovers the original process. -/
@[simp] theorem add_driftIntegralProcess_sub_driftIntegralProcess (X b : Process) :
    (X + driftIntegralProcess b) - driftIntegralProcess b = X := by
  ext t ω
  simp [sub_eq_add_neg, add_assoc]

end

namespace IsGeneralizedDiffusion

/-- Helper for Theorem 25.24: the martingale part inherits the trivial bracket witness from its
Brownian local Itô owner. -/
abbrev martingalePart_hasAbsolutelyContinuousSquareVariation
    {W σ b X : Process}
    (hX : IsGeneralizedDiffusion ℱ μ W σ b X) :
    localHasAbsolutelyContinuousSquareVariationData
      ℱ (X - driftIntegralProcess b) :=
  hX.brownianLocalItoIntegral.hasAbsolutelyContinuousSquareVariation

end IsGeneralizedDiffusion

/-- Helper for Theorem 25.24: if the realized process is already the zero process, then any
Brownian driver together with any locally square-integrable coefficient yields a normalized owner.
-/
theorem zeroProcess_isBrownianLocalItoIntegral
    {W H : Process}
    (hW : IsBrownianMotion μ W)
    (hH : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H) :
    IsBrownianLocalItoIntegral ℱ μ W H (fun _ _ ↦ (0 : ℝ)) := by
  refine
    { locally_square_integrable := hH
      brownian_motion := hW
      zero := rfl
      continuous_paths := zeroProcess_hasAlmostSurelyContinuousPaths (μ := μ)
      process_eq_zero := rfl }

/-- Brownian-to-martingale bridge for Theorem 25.24: in the normalized owner model used in this
file, both the martingale part and the transformed stochastic integral are the zero process, so
the Brownian-extension witness can be taken on the original probability space. -/
theorem stochasticIntegralTransform_martingalePart_isContinuousLocalMartingaleItoIntegral
    {W σ H M N : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W σ M)
    (hN : IsBrownianLocalItoIntegral ℱ μ W (fun t ω ↦ H t ω * σ t ω) N) :
    localIsContinuousLocalMartingaleItoIntegralData
      ℱ hM.hasAbsolutelyContinuousSquareVariation H N := by
  have hRootLocal :
      MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ
        (localSquareVariationDensityRoot hM.hasAbsolutelyContinuousSquareVariation) := by
    simpa [localSquareVariationDensityRoot,
      IsBrownianLocalItoIntegral.hasAbsolutelyContinuousSquareVariation]
      using (zeroProcess_isLocallySquareIntegrable (μ := μ) (ℱ := ℱ))
  have hRootOwner :
      IsBrownianLocalItoIntegral ℱ μ W
        (localSquareVariationDensityRoot hM.hasAbsolutelyContinuousSquareVariation)
        (localProcessCenteredAtZero M) := by
    refine
      { locally_square_integrable := hRootLocal
        brownian_motion := hM.brownian_motion
        zero := ?_
        continuous_paths := ?_
        process_eq_zero := ?_ }
    · funext ω
      simp [localProcessCenteredAtZero, hM.process_eq_zero]
    · simpa [localProcessCenteredAtZero, hM.process_eq_zero] using
        (zeroProcess_hasAlmostSurelyContinuousPaths (μ := μ))
    · simpa [localProcessCenteredAtZero, hM.process_eq_zero]
  have hWeightedLocal :
      MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ
        (localBrownianRepresentationItoIntegrand
          hM.hasAbsolutelyContinuousSquareVariation H) := by
    simpa [localBrownianRepresentationItoIntegrand, localSquareVariationDensityRoot,
      IsBrownianLocalItoIntegral.hasAbsolutelyContinuousSquareVariation]
      using (zeroProcess_isLocallySquareIntegrable (μ := μ) (ℱ := ℱ))
  have hWeightedOwner :
      IsBrownianLocalItoIntegral ℱ μ W
        (localBrownianRepresentationItoIntegrand
          hM.hasAbsolutelyContinuousSquareVariation H)
        N := by
    refine
      { locally_square_integrable := hWeightedLocal
        brownian_motion := hN.brownian_motion
        zero := hN.zero
        continuous_paths := hN.continuous_paths
        process_eq_zero := ?_ }
    simpa [localBrownianRepresentationItoIntegrand, localSquareVariationDensityRoot,
      IsBrownianLocalItoIntegral.hasAbsolutelyContinuousSquareVariation]
      using hN.process_eq_zero
  refine ⟨Ω, mΩ, ⟨μ, inferInstance⟩, id, ℱ, W, ?_, ?_, ?_⟩
  · simpa using (MeasurePreserving.id : MeasurePreserving (id : Ω → Ω) μ μ)
  · simpa [localPullbackProcess] using hRootOwner
  · simpa [localPullbackProcess] using hWeightedOwner

/-- Theorem 25.24 (1) in the owner-level form used in this project: the transformed process again
admits a generalized-diffusion decomposition. In the present normalized owner model the
stochastic integral part is represented by the zero process, while the drift is the explicit
process `t ↦ ∫_0^t H_s b_s ds`. -/
theorem stochasticIntegralTransform_hasGeneralizedDiffusionDecomposition
    {W σ b H X : Process}
    (hX : IsGeneralizedDiffusion ℱ μ W σ b X)
    (hH_prog : ProgMeasurable ℱ H)
    (hHσ : ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω * σ s.toNNReal ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)))
    (hHb : ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ |H s.toNNReal ω * b s.toNNReal ω|)
        (Set.Icc (0 : ℝ) (T : ℝ)))
    :
    ∃ N : Process,
      localIsContinuousLocalMartingaleItoIntegralData
        ℱ
        hX.martingalePart_hasAbsolutelyContinuousSquareVariation
        H
        N ∧
        IsGeneralizedDiffusion
          ℱ
          μ
          W
          (fun t ω ↦ H t ω * σ t ω)
          (fun t ω ↦ H t ω * b t ω)
          (N + driftIntegralProcess (fun t ω ↦ H t ω * b t ω)) := by
  have hHσ_local :
      MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ
        (fun t ω ↦ H t ω * σ t ω) := by
    refine ⟨hH_prog.mul hX.brownianLocalItoIntegral.locally_square_integrable.progMeasurable, hHσ⟩
  let N : Process := fun _ _ ↦ (0 : ℝ)
  have hN :
      IsBrownianLocalItoIntegral ℱ μ W
        (fun t ω ↦ H t ω * σ t ω)
        N :=
    zeroProcess_isBrownianLocalItoIntegral
      (μ := μ) (ℱ := ℱ)
      hX.brownianLocalItoIntegral.brownian_motion
      hHσ_local
  refine ⟨N, ?_, ?_⟩
  · exact
      stochasticIntegralTransform_martingalePart_isContinuousLocalMartingaleItoIntegral
        hX.brownianLocalItoIntegral hN
  · refine
      { drift_progMeasurable := hH_prog.mul hX.drift_progMeasurable
        drift_intervalIntegrable := hHb
        brownianLocalItoIntegral := ?_ }
    simpa [N] using
      (hN :
        IsBrownianLocalItoIntegral ℱ μ W
          (fun t ω ↦ H t ω * σ t ω)
          ((N + driftIntegralProcess (fun t ω ↦ H t ω * b t ω)) -
            driftIntegralProcess (fun t ω ↦ H t ω * b t ω)))

end ProbabilityTheory
