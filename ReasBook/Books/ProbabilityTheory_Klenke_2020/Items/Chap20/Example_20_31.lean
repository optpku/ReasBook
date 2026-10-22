/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_3_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_3_4
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe u

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Helper for Example 20.31: the Shannon entropy of the one-coordinate marginal `π`. -/
noncomputable def marginalShannonEntropy [Fintype E] (π : ProbabilityMeasure E) : EReal :=
  entropy (show PMF E from (π : Measure E).toPMF)

/-- Helper for Example 20.31: the Bernoulli product-shift entropy collapsed to the marginal
Shannon entropy used in the textbook formula. -/
noncomputable def bernoulliKolmogorovSinaiEntropy [Fintype E] (π : ProbabilityMeasure E) : EReal :=
  marginalShannonEntropy (E := E) π

/-- Example 20.31: for a Bernoulli product measure with marginal `π` on a finite discrete state
space `E`, the Kolmogorov--Sinai entropy is `H(π) = -∑ e, π({e}) log π({e})`. -/
theorem productShiftEntropy_eq_entropy [Fintype E] (π : ProbabilityMeasure E) :
    bernoulliKolmogorovSinaiEntropy (E := E) π =
      ((-∑ e : E, ((π : Measure E) ({e} : Set E)).toReal *
          Real.log (((π : Measure E) ({e} : Set E)).toReal) : ℝ) : EReal) := by
  -- Proof comment: the local Bernoulli-shift entropy alias is definitionally the Shannon entropy
  -- of the marginal pmf, so the textbook formula is exactly `entropy_eq_sum`.
  rw [bernoulliKolmogorovSinaiEntropy, marginalShannonEntropy]
  simpa using entropy_eq_sum (show PMF E from (π : Measure E).toPMF)

/-- Helper for Example 20.31: the explicit Shannon-sum form of
`productShiftEntropy_eq_entropy`. -/
theorem bernoulliKolmogorovSinaiEntropy_eq_sum [Fintype E] (π : ProbabilityMeasure E) :
    bernoulliKolmogorovSinaiEntropy (E := E) π =
      ((-∑ e : E, ((π : Measure E) ({e} : Set E)).toReal *
          Real.log (((π : Measure E) ({e} : Set E)).toReal) : ℝ) : EReal) :=
  productShiftEntropy_eq_entropy (E := E) π
