/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Corollary_7_45
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Remark_13_14
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u

namespace MeasureTheory.FiniteMeasure

section

variable {E : Type u} [MeasurableSpace E]

variable [MetricSpace E] [BorelSpace E]

omit [MetricSpace E] [BorelSpace E] in
private theorem abs_apply_le_totalVariationNorm {A : Set E} (hA : MeasurableSet A)
    (s : SignedMeasure E) :
    |s A| ≤ SignedMeasure.totalVariationNorm E s := by
  let j := s.toJordanDecomposition
  have hsA : s A = j.posPart.real A - j.negPart.real A := by
    simpa [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hA] using
      (congrArg (fun t : SignedMeasure E ↦ t A)
        (SignedMeasure.toSignedMeasure_toJordanDecomposition s)).symm
  calc
    |s A| = |j.posPart.real A - j.negPart.real A| := by rw [hsA]
    _ ≤ j.posPart.real A + j.negPart.real A := by
      refine abs_sub_le_iff.2 ?_
      constructor <;> linarith [show 0 ≤ j.posPart.real A by positivity,
        show 0 ≤ j.negPart.real A by positivity]
    _ ≤ j.posPart.real Set.univ + j.negPart.real Set.univ := by
      exact add_le_add
        (measureReal_mono (Set.subset_univ A) (by finiteness))
        (measureReal_mono (Set.subset_univ A) (by finiteness))
    _ = SignedMeasure.totalVariationNorm E s := by
      simpa [j] using (SignedMeasure.totalVariation_real_univ_eq_jordan s).symm

-- Proof sketch: first derive setwise convergence on every measurable set from the total-variation
-- bound `|μₙ(A) - μ(A)| ≤ ‖μₙ - μ‖TV`, then invoke the chapter owner theorem
-- `FiniteMeasure.tendsto_of_setwise_tendsto`.
/-- Exercise 13.2.2: convergence to zero in the canonical total-variation norm of signed
differences implies weak convergence in the canonical weak topology on `FiniteMeasure E`. -/
theorem tendsto_of_tendsto_totalVariationNorm_zero
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (h_tv : Tendsto
      (fun n ↦
        SignedMeasure.totalVariationNorm E
          ((μs n : Measure E).toSignedMeasure - (μ : Measure E).toSignedMeasure))
      atTop (𝓝 0)) :
    Tendsto μs atTop (𝓝 μ) := by
  apply tendsto_of_setwise_tendsto
  intro A hA
  have hA_dist :
      Tendsto (fun n ↦ dist ((μs n) A) (μ A)) atTop (𝓝 0) := by
    have hA_le :
        ∀ n,
          dist ((μs n) A) (μ A) ≤
            SignedMeasure.totalVariationNorm E
              ((μs n : Measure E).toSignedMeasure - (μ : Measure E).toSignedMeasure) := by
      intro n
      simpa [NNReal.dist_eq, FiniteMeasure.measureReal_eq_coe_coeFn,
        Measure.toSignedMeasure_sub_apply hA] using
        abs_apply_le_totalVariationNorm hA
          ((μs n : Measure E).toSignedMeasure - (μ : Measure E).toSignedMeasure)
    exact squeeze_zero (fun n ↦ dist_nonneg) hA_le h_tv
  have hA' :
      Tendsto (fun n ↦ ENNReal.ofNNReal ((μs n) A)) atTop
        (𝓝 (ENNReal.ofNNReal (μ A))) :=
    (ENNReal.continuous_coe.tendsto (μ A)).comp (tendsto_iff_dist_tendsto_zero.2 hA_dist)
  simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hA'

end

end MeasureTheory.FiniteMeasure
