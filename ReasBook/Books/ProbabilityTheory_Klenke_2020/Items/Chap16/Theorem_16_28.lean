/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_29

namespace MeasureTheory.ProbabilityMeasure

/-- Theorem 16.28: if a real probability law belongs to the domain of attraction of a non-Dirac
law, then it satisfies `(16.29)` for some `α ∈ (0, 2]`; in the Gaussian case the quadratic tail
criterion gives an attracting law; and for `α ∈ (0, 2)` stable attraction is equivalent to the
tail criterion together with the positive-tail-share limit `(16.30)`. -/
theorem stableDomainOfAttractionCriterion (μ : ProbabilityMeasure ℝ) :
    μ.StableDomainOfAttractionCriterionPartI ∧
      μ.StableDomainOfAttractionCriterionPartII ∧
      μ.StableDomainOfAttractionCriterionPartIII := by
  sorry

end MeasureTheory.ProbabilityMeasure
