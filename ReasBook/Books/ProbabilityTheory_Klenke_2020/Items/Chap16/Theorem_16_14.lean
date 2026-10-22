/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3

-- The previous wrapper imported this module from itself, creating a build cycle.
-- Keep the module on the minimal import spine recovered from the last successful build.

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The log-Laplace transform of a probability measure on `[0, ∞)`. -/
def logLaplaceTransform (μ : ProbabilityMeasure NNReal) (t : NNReal) : ℝ :=
  -Real.log (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal))

/-- The subordinator Lévy--Khinchin representation predicate on `[0, ∞)`. -/
def HasSubordinatorLevyKhinchinRepresentation
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal) : Prop :=
  ν {0} = 0 ∧
    Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν ∧
    ∀ t : NNReal,
      logLaplaceTransform μ t =
        ((α : ℝ) * (t : ℝ)) +
          ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν

/-- Theorem 16.14: label-bearing entry for the Lévy--Khinchin formula on `[0, ∞)`.

The substantive owner-side development for the subordinator Lévy--Khinchin interface currently
lives in the Chapter 16 item/support files; this target restores the canonical textbook theorem
name expected by downstream Chapter 16 items. -/
theorem isInfinitelyDivisibleOnNNReal_iff_exists_unique_levyKhinchin_pair
    (μ : ProbabilityMeasure NNReal) :
    IsInfinitelyDivisible μ ↔
      ∃! pair : NNReal × Measure NNReal,
        HasSubordinatorLevyKhinchinRepresentation μ pair.1 pair.2 := by
  -- The generated source retained only a True-valued placeholder for this core theorem.
  sorry

end MeasureTheory.ProbabilityMeasure
