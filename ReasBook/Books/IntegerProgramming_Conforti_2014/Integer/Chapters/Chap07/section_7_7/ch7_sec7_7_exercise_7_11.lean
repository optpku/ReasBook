/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7

open SequenceIndependentLifting

section Exercise711

variable {n : ℕ}

/-- Exercise 7.11 (1). If the Section 7.2.2 lifting profile
`lifting_profile a b C α β` is superadditive on `[0, b]`, then the lifted inequality with
coefficients `lifting_profile a b C α β (a j)` on `N \ C` is valid for the binary knapsack set
`zero_one_knapsack_set a b`, provided the cover weights are nonnegative. -/
theorem exercise_7_11_lifted_inequality_valid
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hbase :
      is_valid_inequality (zero_one_knapsack_set a b) (base_coefficients C α) β)
    (hC_nonneg : ∀ ⦃j : Fin n⦄, j ∈ C → 0 ≤ a j)
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    (hf_super : is_superadditive_on_Icc (lifting_profile a b C α β) b) :
    is_valid_inequality
      (zero_one_knapsack_set a b)
      (lifted_coefficients C α a (lifting_profile a b C α β))
      β := by
  simpa using
    superadditive_lift_valid
      a b C α β (lifting_profile a b C α β)
      hbase hC_nonneg ha hf_super
      (fun {_} _ ↦ le_rfl)

/-- Exercise 7.11 (2). Under the same Section 7.2.2 hypotheses, every valid lifting of the base
inequality has coefficients on `N \ C` bounded above by the lifting profile:
for each `j ∉ C`, one has `α' j ≤ lifting_profile a b C α β (a j)`. -/
theorem exercise_7_11_valid_lifting_coeff_le_lifting_profile
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hbase :
      is_valid_inequality (zero_one_knapsack_set a b) (base_coefficients C α) β)
    (hC_nonneg : ∀ ⦃j : Fin n⦄, j ∈ C → 0 ≤ a j)
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    (hf_super : is_superadditive_on_Icc (lifting_profile a b C α β) b)
    {α' : Fin n → ℝ}
    (hα' :
      is_lifting_of_base_inequality (zero_one_knapsack_set a b) C α β α') :
    ∀ ⦃j : Fin n⦄, j ∉ C → α' j ≤ lifting_profile a b C α β (a j) := by
  have hmax :
      is_unique_maximal_lifting_of_base_inequality
        (zero_one_knapsack_set a b)
        C
        α
        β
        (lifted_coefficients C α a (lifting_profile a b C α β)) :=
    lifting_profile_is_unique_maximal_lifting a b C α β hbase hC_nonneg ha hf_super
  have hle : α' ≤ lifted_coefficients C α a (lifting_profile a b C α β) :=
    hmax.maximal α' hα'
  intro j hj
  simpa [lifted_coefficients_apply_of_not_mem hj] using hle j

end Exercise711
