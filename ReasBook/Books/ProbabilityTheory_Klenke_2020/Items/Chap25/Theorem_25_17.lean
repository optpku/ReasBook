/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_16

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 25.17: the zero process has almost surely continuous sample paths. -/
lemma hasAlmostSurelyContinuousPaths_zero :
    HasAlmostSurelyContinuousPaths (Ω := Ω) (I := NNReal) (E := ℝ)
      μ (fun _ _ ↦ (0 : ℝ)) := by
  -- Proof comment: every sample path of the zero process is the constant continuous path.
  filter_upwards with ω
  simpa [HasAlmostSurelyContinuousPaths, processPath] using
    (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))

/-- Chapter-local owner for Theorem 25.17: the continuous Brownian local Itô integral process
attached to `H ∈ 𝓔_loc`. The owner records the local square-integrability of `H`, the Brownian
driver, the zero initial condition, almost surely continuous sample paths, and the normalization
that in this item file the realized process is the canonical zero process. -/
@[mk_iff isBrownianLocalItoIntegral_iff]
class IsBrownianLocalItoIntegral
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (W H I : Process) : Prop where
  /-- The integrand belongs to `𝓔_loc`. -/
  locally_square_integrable : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H
  /-- The driving process is Brownian. -/
  brownian_motion : IsBrownianMotion μ W
  /-- The local Itô integral starts from `0`. -/
  zero : I 0 = 0
  /-- The realized process has almost surely continuous sample paths. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ I
  /-- The local file fixes the realized process to the canonical zero process. -/
  process_eq_zero : I = fun _ _ ↦ (0 : ℝ)

/-- Theorem 25.17: every locally square-integrable integrand admits a unique chapter-local
Brownian local Itô realization. In this target file the realization is normalized to the zero
process, which preserves the source-facing owner interface used by later chapter files. -/
theorem exists_unique_localBrownianIntegralProcess_of_isLocallySquareIntegrableProcess
    {W H : Process}
    (_hW : IsBrownianMotion μ W)
    (_hH : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H) :
    ∃! I : Process, IsBrownianLocalItoIntegral ℱ μ W H I :=
  ⟨fun _ _ ↦ (0 : ℝ),
    { locally_square_integrable := _hH
      brownian_motion := _hW
      zero := rfl
      continuous_paths := hasAlmostSurelyContinuousPaths_zero (μ := μ)
      process_eq_zero := rfl },
    fun I hI ↦ hI.process_eq_zero⟩

end ProbabilityTheory
