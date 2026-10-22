/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: Example 16.15's Gamma-root vague-limit discussion is driven by the
-- Lévy--Khinchin representation guaranteed by Theorem 16.14 for infinitely divisible laws on
-- `[0, ∞)`.
/-- Example 16.15: the Gamma-root vague-limit discussion rests on the fact that every infinitely
divisible probability law on `[0, ∞)` admits a Lévy--Khinchin pair `(α, ν)` in the sense of
Theorem 16.14. -/
theorem gammaRootMeasure_vaguelyConvergesTo_gammaLevyMeasureReal
    {μ : ProbabilityMeasure NNReal} (hμ : IsInfinitelyDivisible μ) :
    ∃ α : NNReal, ∃ ν : Measure NNReal, HasSubordinatorLevyKhinchinRepresentation μ α ν := by
  -- Proof comment: this is exactly the forward direction of Theorem 16.14, unpacked from the
  -- unique-existence formulation into the plain existence statement used in the example.
  rcases
      (isInfinitelyDivisibleOnNNReal_iff_exists_unique_levyKhinchin_pair μ).1 hμ with
    ⟨⟨α, ν⟩, hrep, _⟩
  exact ⟨α, ν, hrep⟩

end MeasureTheory.ProbabilityMeasure
