import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_remark_6_36
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_3.ch6_sec6_3_3_lemma_6_33

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma638

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "Zq" => Fin q → ℤ

namespace IsMinimalValidGomoryJohnsonPair

/-- Helper for Lemma 6.38: the singleton mixed point used in the touching argument is feasible for
`M_f`. -/
lemma touchingSingleton_mem_mixedIntegerRelaxation
    {f : Rq}
    (r_star : Rq)
    (z : Zq) :
    (Finsupp.single r_star 1,
        Finsupp.single ((fun i ↦ (z i : ℝ)) - f - r_star) (1 : NNReal)) ∈
      mixed_integer_relaxation_set f := by
  rw [mem_mixed_integer_relaxation_set_iff]
  refine ⟨z, ?_⟩
  -- The singleton integer mass at `r*` and the singleton continuous mass at `z - f - r*`
  -- add up to the integer vector `z`.
  ext i
  simp [Pi.add_apply, Pi.sub_apply]

/-- Helper for Lemma 6.38: a minimal valid Gomory--Johnson pair is, in particular, a minimal
lifting of its continuous component `ψ`. -/
theorem toIsMinimalLiftingOf
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    IsMinimalLiftingOf f π ψ := by
  refine
    { toIsValidGomoryJohnsonPair := hπψ.toIsValidGomoryJohnsonPair
      eq_of_le := ?_ }
  intro π' hπ' hle
  -- Minimality of the pair already compares against competitors with the same `ψ`.
  exact (hπψ.eq_of_le hπ' hle (fun r ↦ le_rfl)).1

/-- Under the touching-sum hypothesis from Lemma 6.38, the `π`- and `ψ`-components agree at
`r*`. -/
theorem pi_eq_psi_of_touching_sum_eq_one
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ)
    (r_star : Rq) (z : Zq)
    (hsum :
      ψ r_star + ψ ((fun i ↦ (z i : ℝ)) - f - r_star) =
        ψ ((fun i ↦ (z i : ℝ)) - f))
    (hone : ψ ((fun i ↦ (z i : ℝ)) - f) = 1) :
    π r_star = ψ r_star := by
  have hone_le :
      1 ≤ π r_star + ψ ((fun i ↦ (z i : ℝ)) - f - r_star) := by
    -- Apply mixed validity to the source witness with one integer atom at `r*` and one
    -- continuous atom at `z - f - r*`.
    simpa using hπψ.one_le (touchingSingleton_mem_mixedIntegerRelaxation r_star z)
  have hpi_le : π r_star ≤ ψ r_star := hπψ.pi_le_psi r_star
  -- The touching equalities squeeze `π r*` between the same lower and upper bounds.
  linarith [hone_le, hpi_le, hsum, hone]

/-- Lemma 6.38. Under the touching-sum hypothesis
`ψ (r*) + ψ (z - f - r*) = ψ (z - f) = 1`, the minimal valid pair satisfies
`π (r*) = trivial_lifting ψ r*`, hence `π (r*) = ψ (r*) = inf_w ψ (r* + w)`. -/
theorem pi_eq_trivial_lifting_of_touching_sum_eq_one
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ)
    (r_star : Rq) (z : Zq)
    (hsum :
      ψ r_star + ψ ((fun i ↦ (z i : ℝ)) - f - r_star) =
        ψ ((fun i ↦ (z i : ℝ)) - f))
    (hone : ψ ((fun i ↦ (z i : ℝ)) - f) = 1) :
    π r_star = trivial_lifting ψ r_star := by
  have hpi_eq_psi : π r_star = ψ r_star :=
    hπψ.pi_eq_psi_of_touching_sum_eq_one r_star z hsum hone
  have hpi_le_trivial : π r_star ≤ trivial_lifting ψ r_star :=
    minimal_lifting_le_trivial_lifting f ψ π hπψ.toIsMinimalLiftingOf r_star
  have htrivial_le_psi : trivial_lifting ψ r_star ≤ ψ r_star := by
    rw [trivial_lifting_apply]
    refine csInf_le ?_ ?_
    · -- The translate set is bounded below by `0` because `ψ` is pointwise nonnegative.
      use 0
      rintro _ ⟨w, rfl⟩
      exact hπψ.psi_nonnegative (fun i ↦ r_star i + (w i : ℝ))
    · -- The zero translate shows that the infimum is no larger than `ψ r*`.
      exact ⟨0, by simp⟩
  -- Part (1) identifies `π r*` with `ψ r*`, so antisymmetry finishes the infimum comparison.
  apply le_antisymm
  · exact hpi_le_trivial
  · rw [hpi_eq_psi]
    exact htrivial_le_psi

end IsMinimalValidGomoryJohnsonPair

/-- Textbook part (1) of Lemma 6.38. Let `(π, ψ)` be a minimal valid function for `M_f`. If
`ψ (r*) + ψ (z - f - r*) = ψ (z - f) = 1` for some `z ∈ ℤ^q`, then `π (r*) = ψ (r*)`. -/
theorem minimal_valid_gomory_johnson_pair_pi_eq_psi_of_touching_sum_eq_one
    (f : Rq) (π ψ : Rq → ℝ) (r_star : Rq) (z : Zq)
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ)
    (hsum :
      ψ r_star + ψ ((fun i ↦ (z i : ℝ)) - f - r_star) =
        ψ ((fun i ↦ (z i : ℝ)) - f))
    (hone : ψ ((fun i ↦ (z i : ℝ)) - f) = 1) :
    π r_star = ψ r_star :=
  hπψ.pi_eq_psi_of_touching_sum_eq_one r_star z hsum hone

/-- Textbook part (2) of Lemma 6.38. Under the same hypotheses,
`π (r*)` is the infimum of the integer translates
`ψ (r* + w)` with `w ∈ ℤ^q`. -/
theorem minimal_valid_gomory_johnson_pair_pi_eq_integer_translate_inf_of_touching_sum_eq_one
    (f : Rq) (π ψ : Rq → ℝ) (r_star : Rq) (z : Zq)
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ)
    (hsum :
      ψ r_star + ψ ((fun i ↦ (z i : ℝ)) - f - r_star) =
        ψ ((fun i ↦ (z i : ℝ)) - f))
    (hone : ψ ((fun i ↦ (z i : ℝ)) - f) = 1) :
    π r_star =
      sInf (Set.range fun w : Zq ↦ ψ (fun i ↦ r_star i + (w i : ℝ))) := by
  simpa [trivial_lifting] using
    hπψ.pi_eq_trivial_lifting_of_touching_sum_eq_one r_star z hsum hone

end Lemma638
