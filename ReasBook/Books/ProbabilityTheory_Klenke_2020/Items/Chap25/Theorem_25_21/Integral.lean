/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21.Bracket
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_25

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {ℱ : Filtration NNReal mΩ}

/-- The canonical dyadic pathwise realization of `∫ H dM`, obtained by applying the Chapter 25
pathwise Itô integral to each continuous sample path of `M`. -/
noncomputable def continuousLocalMartingaleItoIntegralProcess
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun T ω ↦
    pathwiseItoIntegralAlong
      (fun t : NNReal ↦ H t ω)
      (⟨fun t : NNReal ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
      Definition2158.dyadicPartitionSequence
      T

end ProbabilityTheory
