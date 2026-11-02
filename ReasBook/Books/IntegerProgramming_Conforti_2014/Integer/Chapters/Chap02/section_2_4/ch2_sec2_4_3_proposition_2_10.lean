module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_19.MinimumWeightSet

public section

namespace MinimumWeightSet

variable {n : ℕ}

/-- Proposition 2.10. For a nonempty family `R` of subsets of `{1, ..., n}` and nonnegative
weights `w`, the minimum-weight set problem over `R` admits an optimal solution that is
inclusion-minimal in `R`. The textbook family
`S = {U ∈ R | there is no V ∈ R with V ⊂ U}` is represented by `Minimal (· ∈ R) U`. -/
theorem exists_isOptimal_minimalMember
    (w : Fin n → NNReal) {R : Set (Finset (Fin n))} (hR : R.Nonempty) :
    ∃ U : Finset (Fin n), IsOptimal w R U ∧ Minimal (· ∈ R) U := by
  obtain ⟨S, hS⟩ := exists_isOptimal w hR
  obtain ⟨U, hUS, hU⟩ := (Set.toFinite R).exists_le_minimal hS.mem
  exact ⟨U, hS.of_subset hU.1 hUS, hU⟩

end MinimumWeightSet
