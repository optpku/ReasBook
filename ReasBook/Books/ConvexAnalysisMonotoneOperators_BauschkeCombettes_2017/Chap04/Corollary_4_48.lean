/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u ι

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type ι} [Fintype I]
variable {D : Set E}

/-- Corollary 4.48: the finite weighted average of firmly quasinonexpansive operators is firmly
quasinonexpansive whenever the weights lie in `]0, 1]` and sum to `1`. -/
theorem weightedOperatorAverage_firmly_quasinonexpansive_on
    (ω : I → ℝ) (T : I → D → E)
    (hT : ∀ i, IsFirmlyQuasinonexpansiveOn (T i))
    (hω_mem : ∀ i, ω i ∈ Set.Ioc (0 : ℝ) 1) (hω_sum : ∑ i : I, ω i = 1) :
    IsFirmlyQuasinonexpansiveOn (weightedOperatorAverage ω T) := by
  sorry

end
