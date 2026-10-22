/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.ContinuousExpLift
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Exercise_16_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Lemma_16_24
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Remark_16_18.FiniteConverse

-- Remark 16.18 support currently lives in `Remark_16_18/FiniteConverse.lean`.

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

namespace HasLevyKhinchinRepresentation

/-- Remark 16.18: a Lévy--Khinchin representation with finite jump measure is automatically
infinitely divisible. -/
theorem canonicalLevyMeasure_vagueLimit
    {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple} [IsFiniteMeasure τ.ν]
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    IsInfinitelyDivisible μ := by
  -- Proof comment: the target file restores the label-bearing textbook entry by re-exporting the
  -- proved finite-jump converse from the support module.
  exact isInfinitelyDivisible_of_hasLevyKhinchinRepresentation_of_isFiniteMeasure hτ

end HasLevyKhinchinRepresentation

end MeasureTheory.ProbabilityMeasure
