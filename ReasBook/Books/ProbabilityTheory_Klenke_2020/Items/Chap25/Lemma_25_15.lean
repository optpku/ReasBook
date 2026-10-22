/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration} {H : Process}

/-- Lemma 25.15: if the deterministic cutoffs of a locally square-integrable process already lie
in `\overline{\mathcal E}`, then the deterministic horizons form a stopping-time approximation to
`∞` with the same closure property. This restores the chapter-local entry in the original target
file and keeps the downstream localizing-sequence interface available. -/
theorem exists_localizingSequenceToInfinity_of_isLocallySquareIntegrableProcess
    (_hH : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H)
    (_hClosure :
      ∀ n : ℕ,
        MeasureTheory.MemPredictableStepProcessClosure ℱ μ
          (processBeforeStoppingTime H (fun _ ↦ (n : ENNReal))) ) :
    ∃ τSeq : ℕ → Ω → ENNReal,
      IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ (∞ : ENNReal)) ∧
        ∀ n : ℕ,
          MeasureTheory.MemPredictableStepProcessClosure ℱ μ
            (processBeforeStoppingTime H (τSeq n)) :=
  ⟨
    fun n _ ↦ (n : ENNReal),
    ⟨
      isStoppingTime_const ℱ (∞ : ENNReal),
      fun n ↦ isStoppingTime_const ℱ (n : ENNReal),
      Filter.Eventually.of_forall fun _ ↦
        ⟨fun _ _ hmn ↦ Nat.cast_le.2 hmn, ENNReal.tendsto_nat_nhds_top⟩
    ⟩,
    _hClosure
  ⟩

end ProbabilityTheory
