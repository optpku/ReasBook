import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.KnapsackSet
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith

open scoped Matrix

section Proposition222

/-- The concrete set `S` from Proposition 2.22, defined as the `0/1` knapsack set with weights
`(90,35,26,25)` and capacity `138`. -/
def proposition_2_22_knapsack_set : Set (Fin 4 → ℝ) :=
  zero_one_knapsack_set (![90, 35, 26, 25] : Fin 4 → ℝ) 138

/-- Membership in `proposition_2_22_knapsack_set` is exactly membership in the corresponding
canonical `0/1` knapsack-set owner. -/
theorem mem_proposition_2_22_knapsack_set_iff
    (x : Fin 4 → ℝ) :
    x ∈ proposition_2_22_knapsack_set ↔
      x ∈ zero_one_knapsack_set (![90, 35, 26, 25] : Fin 4 → ℝ) 138 := by
  -- This companion theorem is just the defining equality of the local abbreviation.
  rfl

/-- The four displayed inequalities from Proposition 2.22, without the separate `0/1` condition.
-/
def proposition_2_22_system (x : Fin 4 → ℝ) : Prop :=
  2 * x 0 + x 1 + x 2 + x 3 ≤ 3 ∧
    x 0 + x 1 + x 2 ≤ 2 ∧
    x 0 + x 1 + x 3 ≤ 2 ∧
    x 0 + x 2 + x 3 ≤ 2

/-- The predicate `proposition_2_22_system` is exactly the displayed conjunction of the four
source inequalities. -/
theorem mem_proposition_2_22_system_iff
    (x : Fin 4 → ℝ) :
    proposition_2_22_system x ↔
      2 * x 0 + x 1 + x 2 + x 3 ≤ 3 ∧
        x 0 + x 1 + x 2 ≤ 2 ∧
        x 0 + x 1 + x 3 ≤ 2 ∧
        x 0 + x 2 + x 3 ≤ 2 := by
  -- This companion theorem is the definitional unfolding of the displayed system.
  rfl

/-- Helper for Proposition 2.22: on `0/1` vectors, the original knapsack inequality is
equivalent to the single inequality `2 * x 0 + x 1 + x 2 + x 3 ≤ 3`. -/
private lemma proposition_2_22_knapsack_iff_single_of_zero_one
    {x : Fin 4 → ℝ} (hbin : is_zero_one_vector x) :
    (((90 : ℝ) * x 0 + 35 * x 1 + 26 * x 2 + 25 * x 3 ≤ 138) ↔
      (2 * x 0 + x 1 + x 2 + x 3 ≤ 3)) := by
  -- Split into the sixteen binary assignments and close each branch by linear arithmetic.
  rcases is_zero_one_vector.apply hbin 0 with hx0 | hx0 <;>
    rcases is_zero_one_vector.apply hbin 1 with hx1 | hx1 <;>
    rcases is_zero_one_vector.apply hbin 2 with hx2 | hx2 <;>
    rcases is_zero_one_vector.apply hbin 3 with hx3 | hx3
  all_goals
    constructor
    · intro h
      linarith [h, hx0, hx1, hx2, hx3]
    · intro h
      linarith [h, hx0, hx1, hx2, hx3]

/-- Helper for Proposition 2.22: on `0/1` vectors, the single inequality
`2 * x 0 + x 1 + x 2 + x 3 ≤ 3` is equivalent to the displayed four-inequality system. -/
private lemma proposition_2_22_single_iff_system_of_zero_one
    {x : Fin 4 → ℝ} (hbin : is_zero_one_vector x) :
    ((2 * x 0 + x 1 + x 2 + x 3 ≤ 3) ↔ proposition_2_22_system x) := by
  -- Rewrite the system to its conjunction form, then close each binary branch by linear arithmetic.
  rw [mem_proposition_2_22_system_iff]
  rcases is_zero_one_vector.apply hbin 0 with hx0 | hx0 <;>
    rcases is_zero_one_vector.apply hbin 1 with hx1 | hx1 <;>
    rcases is_zero_one_vector.apply hbin 2 with hx2 | hx2 <;>
    rcases is_zero_one_vector.apply hbin 3 with hx3 | hx3
  all_goals
    constructor
    · intro h
      constructor
      · linarith [h, hx0, hx1, hx2, hx3]
      · constructor
        · linarith [h, hx0, hx1, hx2, hx3]
        · constructor
          · linarith [h, hx0, hx1, hx2, hx3]
          · linarith [h, hx0, hx1, hx2, hx3]
    · intro h
      rcases h with ⟨h0123, h012, h013, h023⟩
      linarith [h0123, h012, h013, h023, hx0, hx1, hx2, hx3]

/-- Part (1) of Proposition 2.22: the concrete set `S` equals the binary set cut out by
`2 * x 0 + x 1 + x 2 + x 3 ≤ 3`. -/
theorem proposition_2_22_eq_single_inequality :
    proposition_2_22_knapsack_set =
      zero_one_knapsack_set (![2, 1, 1, 1] : Fin 4 → ℝ) 3 := by
  -- Compare the two set descriptions pointwise through their binary membership data.
  ext x
  rw [mem_proposition_2_22_knapsack_set_iff, mem_zero_one_knapsack_set_iff,
    mem_zero_one_knapsack_set_iff]
  constructor
  · intro hx
    have hsingle : 2 * x 0 + x 1 + x 2 + x 3 ≤ 3 := by
      -- Normalize the original knapsack inequality, then use the binary equivalence helper.
      have horiginal : (90 : ℝ) * x 0 + 35 * x 1 + 26 * x 2 + 25 * x 3 ≤ 138 := by
        simpa [Fin.sum_univ_four] using hx.2
      exact (proposition_2_22_knapsack_iff_single_of_zero_one hx.1).mp horiginal
    refine ⟨hx.1, ?_⟩
    simpa [Fin.sum_univ_four] using hsingle
  · intro hx
    have horiginal : (90 : ℝ) * x 0 + 35 * x 1 + 26 * x 2 + 25 * x 3 ≤ 138 := by
      -- The simplified inequality implies the original one for the same binary vector.
      have hsingle : 2 * x 0 + x 1 + x 2 + x 3 ≤ 3 := by
        simpa [Fin.sum_univ_four] using hx.2
      exact (proposition_2_22_knapsack_iff_single_of_zero_one hx.1).mpr hsingle
    refine ⟨hx.1, ?_⟩
    simpa [Fin.sum_univ_four] using horiginal

/-- Part (2) of Proposition 2.22: the concrete set `S` equals the binary set cut out by the
displayed four-inequality system. -/
theorem proposition_2_22_eq_redundant_system :
    proposition_2_22_knapsack_set =
      {x : Fin 4 → ℝ | is_zero_one_vector x ∧ proposition_2_22_system x} := by
  -- Factor through the single-inequality description already established in part (1).
  calc
    proposition_2_22_knapsack_set =
        zero_one_knapsack_set (![2, 1, 1, 1] : Fin 4 → ℝ) 3 :=
      proposition_2_22_eq_single_inequality
    _ = {x : Fin 4 → ℝ | is_zero_one_vector x ∧ proposition_2_22_system x} := by
      ext x
      rw [mem_zero_one_knapsack_set_iff, Set.mem_setOf_eq]
      constructor
      · intro hx
        have hsystem : proposition_2_22_system x := by
          -- Convert the normalized single inequality into the displayed redundant system.
          have hsingle : 2 * x 0 + x 1 + x 2 + x 3 ≤ 3 := by
            simpa [Fin.sum_univ_four] using hx.2
          exact (proposition_2_22_single_iff_system_of_zero_one hx.1).mp hsingle
        exact ⟨hx.1, hsystem⟩
      · intro hx
        have hsingle : 2 * x 0 + x 1 + x 2 + x 3 ≤ 3 := by
          -- The displayed system collapses back to the single inequality on binary vectors.
          exact (proposition_2_22_single_iff_system_of_zero_one hx.1).mpr hx.2
        refine ⟨hx.1, ?_⟩
        simpa [Fin.sum_univ_four] using hsingle

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_22.lean.
Proposition 2.22. The concrete set `S` agrees both with the binary knapsack description
`zero_one_knapsack_set (![2, 1, 1, 1] : Fin 4 → ℝ) 3` and with the displayed redundant
four-inequality system. -/
theorem proposition_2_22 :
    proposition_2_22_knapsack_set =
        zero_one_knapsack_set (![2, 1, 1, 1] : Fin 4 → ℝ) 3 ∧
      proposition_2_22_knapsack_set =
        {x : Fin 4 → ℝ | is_zero_one_vector x ∧ proposition_2_22_system x} := by
  -- Package the two established identities into the single labeled proposition entry.
  exact ⟨proposition_2_22_eq_single_inequality, proposition_2_22_eq_redundant_system⟩

end Proposition222
