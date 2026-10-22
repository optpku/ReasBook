/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_36

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

section

variable {I : Type u} {Ω : I → Type v}
variable [∀ i, MeasurableSpace (Ω i)] [∀ i, StandardBorelSpace (Ω i)]

-- Proof sketch: this source-facing countable-index formulation is the countable specialization of
-- the chapter owner theorem `existsUnique_projectiveLimit_of_isProjectiveMeasureFamily`; the
-- probability-measure clause is then derived canonically from
-- `IsProjectiveLimit.isProbabilityMeasure`.
/-- Theorem 14.35: for a countable family of standard Borel coordinate spaces, every consistent
family of finite-dimensional probability measures extends uniquely to a probability measure on the
full product, equivalently to a projective limit with the prescribed finite-coordinate marginals. -/
theorem existsUnique_probabilityMeasure_isProjectiveLimit_of_countable_standardBorel
    [Countable I]
    (P : ∀ J : Finset I, Measure ((j : J) → Ω j)) [∀ J : Finset I, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃! μ : Measure ((i : I) → Ω i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  rcases existsUnique_projectiveLimit_of_isProjectiveMeasureFamily P hP with ⟨μ, hμ, hμ_unique⟩
  refine ⟨μ, ⟨hμ.isProbabilityMeasure, hμ⟩, ?_⟩
  intro ν hν
  exact hμ_unique ν hν.2

end
