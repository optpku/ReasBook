/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal ‹MeasurableSpace Ω›

/-- Example 21.69 (i): every martingale is a local martingale. -/
theorem martingale_isLocalMartingale_local
    {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := by
  -- Proof comment: deterministic times `τₙ ≡ n` are stopping times tending to `∞`, and the
  -- corresponding stopped processes are uniformly integrable martingales by Remark 21.67.
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM.stronglyAdapted.adapted, ?_⟩
  let τs : ℕ → Ω → ENNReal := fun n _ ↦ (n : ENNReal)
  refine ⟨τs, (isLocalizingSequence_iff ℱ μ M τs).2 ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [τs] using isStoppingTime_const ℱ (n : NNReal)
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨?_, ?_⟩
    · intro a b hab
      simpa [τs] using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab)
    · simpa [τs] using ENNReal.tendsto_nat_nhds_top
  · intro n
    simpa [τs] using
      martingaleUniformIntegrable_stoppedProcessConstTime (μ := μ) (ℱ := ℱ) hM (n : NNReal)

end ProbabilityTheory
