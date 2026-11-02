module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Card
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.Cover

public section

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- The family used for Exercise 2.3 assigns unit weight to each of the `2m` variables. -/
def exercise_2_3_unit_weight_knapsack_weights (m : ℕ) : Fin (2 * m) → ℕ :=
  fun _ ↦ 1

/-- The family used for Exercise 2.3 has capacity `m - 1`. -/
def exercise_2_3_unit_weight_knapsack_capacity (m : ℕ) : ℕ :=
  m - 1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_3.lean: the sum of the
exercise's unit weights over a finset is its cardinality. -/
lemma exerciseUnitWeights_sum_eq_card
    (m : ℕ) (C : Finset (Fin (2 * m))) :
    C.sum (exercise_2_3_unit_weight_knapsack_weights m) = C.card := by
  -- Replace every unit weight by one and count the elements of the finset.
  simp [exercise_2_3_unit_weight_knapsack_weights]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_3.lean

Exercise 2.3. For the positive-size `0,1` knapsack family with `n = 2m`
unit-weight variables and capacity `m - 1`, the minimal covers are exactly the
subsets of cardinality `m`. -/
theorem exercise_2_3_unit_weight_knapsack_minimal_cover_iff_card
    (m : ℕ) (hm : 0 < m) (C : Finset (Fin (2 * m))) :
    IsMinimalKnapsackCover
        (exercise_2_3_unit_weight_knapsack_weights m)
        (exercise_2_3_unit_weight_knapsack_capacity m)
        C ↔
      C.card = m := by
  -- Express minimality through the total sum and all one-element erasures.
  rw [isMinimalKnapsackCover_iff, isKnapsackCover_iff]
  constructor
  · intro hMinimal
    rcases hMinimal with ⟨hCover, hErase⟩
    -- Unit weights turn the cover condition into the lower bound `m ≤ C.card`.
    rw [exercise_2_3_unit_weight_knapsack_capacity,
      exerciseUnitWeights_sum_eq_card] at hCover
    have hCardLower : m ≤ C.card := by
      omega
    have hCardPos : 0 < C.card := lt_of_lt_of_le hm hCardLower
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hCardPos
    -- Erasing one member supplies the matching upper bound on `C.card`.
    have hEraseLe := hErase i hi
    rw [exerciseUnitWeights_sum_eq_card,
      exercise_2_3_unit_weight_knapsack_capacity,
      Finset.card_erase_of_mem hi] at hEraseLe
    omega
  · intro hCard
    constructor
    · -- A finset of size `m` exceeds the capacity `m - 1` because `m` is positive.
      rw [exercise_2_3_unit_weight_knapsack_capacity,
        exerciseUnitWeights_sum_eq_card, hCard]
      omega
    · intro i hi
      -- Removing any member leaves exactly `m - 1` unit weights.
      rw [exerciseUnitWeights_sum_eq_card,
        exercise_2_3_unit_weight_knapsack_capacity,
        Finset.card_erase_of_mem hi, hCard]

/-- The positive-size explicit family above has `Nat.choose (2 * m) m` minimal
covers, which is exponential in the number `n = 2m` of variables. -/
theorem exercise_2_3_unit_weight_knapsack_minimal_covers_card
    (m : ℕ) (hm : 0 < m) :
    {C : Finset (Fin (2 * m)) |
        IsMinimalKnapsackCover
          (exercise_2_3_unit_weight_knapsack_weights m)
          (exercise_2_3_unit_weight_knapsack_capacity m)
          C}.ncard =
      Nat.choose (2 * m) m := by
  -- Identify the classified covers with the fixed-cardinality powerset of `univ`.
  have hCovers :
      {C : Finset (Fin (2 * m)) |
          IsMinimalKnapsackCover
            (exercise_2_3_unit_weight_knapsack_weights m)
            (exercise_2_3_unit_weight_knapsack_capacity m)
            C} =
        ((Finset.univ : Finset (Fin (2 * m))).powersetCard m :
          Set (Finset (Fin (2 * m)))) := by
    ext C
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_powersetCard,
      Finset.subset_univ, true_and,
      exercise_2_3_unit_weight_knapsack_minimal_cover_iff_card m hm]
  -- Count the fixed-cardinality powerset using the standard binomial formula.
  rw [hCovers, Set.ncard_coe_finset, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

end
