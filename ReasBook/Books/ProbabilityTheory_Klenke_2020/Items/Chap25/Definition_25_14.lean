/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- A real-valued process is locally square-integrable if it is progressively measurable and its
squared sample paths are integrable on every finite time interval almost surely. -/
def IsLocallySquareIntegrableProcess (ℱ : TimeFiltration) (μ : Measure Ω)
    (H : Process) : Prop :=
  ProgMeasurable ℱ H ∧
    ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ))

/-- Definition 25.14: the textbook space `𝓔_loc` of locally square-integrable real-valued
processes. -/
abbrev LocallySquareIntegrableProcess (ℱ : TimeFiltration) (μ : Measure Ω) :=
  {H : Process // IsLocallySquareIntegrableProcess ℱ μ H}

namespace IsLocallySquareIntegrableProcess

variable {ℱ : TimeFiltration} {μ : Measure Ω} {H : Process}

/-- A locally square-integrable process is progressively measurable. -/
theorem progMeasurable (hH : IsLocallySquareIntegrableProcess ℱ μ H) :
    ProgMeasurable ℱ H :=
  hH.1

/-- For each finite horizon, a locally square-integrable process has almost surely square-
integrable sample paths on that interval. -/
theorem intervalIntegrable
    (hH : IsLocallySquareIntegrableProcess ℱ μ H) (T : NNReal) :
    ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ)) :=
  hH.2 T

end IsLocallySquareIntegrableProcess

/-- Unfolding `IsLocallySquareIntegrableProcess` gives progressive measurability together with
almost-sure square-integrability of the sample paths on each finite interval. -/
theorem isLocallySquareIntegrableProcess_iff
    (ℱ : TimeFiltration) (μ : Measure Ω) (H : Process) :
    IsLocallySquareIntegrableProcess ℱ μ H ↔
      ProgMeasurable ℱ H ∧
        ∀ T : NNReal, ∀ᵐ ω ∂μ,
          IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ)) :=
  Iff.rfl

end MeasureTheory
