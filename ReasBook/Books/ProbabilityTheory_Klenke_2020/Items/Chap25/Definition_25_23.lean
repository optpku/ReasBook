/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.DriftIntegralProcess
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_17

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

section

omit [MeasurableSpace Ω]

/-- Subtracting and then re-adding the drift integral recovers the original process. -/
@[simp] theorem sub_driftIntegralProcess_add_driftIntegralProcess (X b : Process) :
    (X - driftIntegralProcess b) + driftIntegralProcess b = X := by
  ext t ω
  simp [sub_eq_add_neg, add_assoc]

/-- Adding and then subtracting the drift integral recovers the original process. -/
@[simp] theorem add_driftIntegralProcess_sub_driftIntegralProcess (X b : Process) :
    (X + driftIntegralProcess b) - driftIntegralProcess b = X := by
  ext t ω
  simp [sub_eq_add_neg, add_assoc]

end

/-- Definition 25.23: a real-valued process `X` is a generalized diffusion with diffusion
coefficient `σ` and drift `b` if the drift coefficient is progressively measurable with almost
surely integrable paths on each finite time interval and the canonical martingale part
`X_t - ∫_0^t b_s ds` realizes the Brownian local Itô integral `∫_0^t σ_s dW_s` against the
Brownian driver `W`. -/
@[mk_iff isGeneralizedDiffusion_iff]
class IsGeneralizedDiffusion
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ] (W σ b X : Process) : Prop where
  /-- The drift coefficient is progressively measurable. -/
  drift_progMeasurable : ProgMeasurable ℱ b
  /-- Almost every sample path of the drift is integrable on each finite interval. -/
  drift_intervalIntegrable :
    ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω|) (Set.Icc (0 : ℝ) (T : ℝ))
  /-- The canonical martingale part `X - ∫_0^. b_s ds` is the Brownian local Itô integral with
  diffusion coefficient `σ`. -/
  brownianLocalItoIntegral :
    IsBrownianLocalItoIntegral ℱ μ W σ (X - driftIntegralProcess b)

namespace IsGeneralizedDiffusion

/-- A generalized diffusion admits a Brownian local Itô martingale part whose sum with the drift
integral recovers the original process. This is the source-facing decomposition carried by
`IsGeneralizedDiffusion`, exposed as a thin bridge to the canonical owner
`IsBrownianLocalItoIntegral`. -/
theorem exists_decomposition
    {W σ b X : Process} (hX : IsGeneralizedDiffusion ℱ μ W σ b X) :
    ∃ M : Process,
      IsBrownianLocalItoIntegral ℱ μ W σ M ∧
        X = M + driftIntegralProcess b := by
  refine ⟨X - driftIntegralProcess b, hX.brownianLocalItoIntegral, ?_⟩
  simpa using (sub_driftIntegralProcess_add_driftIntegralProcess X b).symm

end IsGeneralizedDiffusion

end ProbabilityTheory
