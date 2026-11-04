/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch`, so this file follows the local Chapter 7 minimal-cover and Chapter 5
-- Chvatal-presentation patterns in a small self-contained form.

noncomputable section

section Exercise78

variable {n : ℕ}

/- This `bridge/view` owner keeps the source-facing multiplier presentation specialized to the
natural `0,1` knapsack formulation, rather than replacing it by a more global cutting-plane
owner. -/
/-- `IsKnapsackChvatalPresentation a b coeff rhs` means that the inequality
`coeff ⬝ᵥ x ≤ rhs` is obtained from the natural `0,1` knapsack formulation
`a ⬝ᵥ x ≤ b, x ≤ 1, x ≥ 0` by a single Chvatal rounding step, using one nonnegative multiplier
for the knapsack row, one nonnegative multiplier for each upper bound `x_j ≤ 1`, and one
nonnegative multiplier for each implicit lower bound `x_j ≥ 0`. -/
def IsKnapsackChvatalPresentation
    (a : Fin n → ℕ)
    (b : ℕ)
    (coeff : Fin n → ℝ)
    (rhs : ℕ) : Prop :=
  ∃ u₀ : ℝ, ∃ u v : Fin n → ℝ,
    0 ≤ u₀ ∧
      (∀ j, 0 ≤ u j) ∧
        (∀ j, 0 ≤ v j) ∧
          (fun j ↦ u₀ * (a j : ℝ) + u j - v j) = coeff ∧
            Int.floor (u₀ * (b : ℝ) + Finset.univ.sum u) = rhs

/-- Expanding `IsKnapsackChvatalPresentation a b coeff rhs` recovers the nonnegative
multiplier description of a Chvatal inequality for the natural knapsack formulation. -/
theorem isKnapsackChvatalPresentation_iff
    (a : Fin n → ℕ)
    (b : ℕ)
    (coeff : Fin n → ℝ)
    (rhs : ℕ) :
    IsKnapsackChvatalPresentation a b coeff rhs ↔
      ∃ u₀ : ℝ, ∃ u v : Fin n → ℝ,
        0 ≤ u₀ ∧
          (∀ j, 0 ≤ u j) ∧
            (∀ j, 0 ≤ v j) ∧
              (fun j ↦ u₀ * (a j : ℝ) + u j - v j) = coeff ∧
                Int.floor (u₀ * (b : ℝ) + Finset.univ.sum u) = rhs := Iff.rfl

/-- The coefficient vector in the Exercise 7.8 inequality: it is `1` on the cover `C` and
`⌊a_j / a_h⌋` on the complement. -/
def exercise_7_8_chvatal_coeffs
    (a : Fin n → ℕ) (C : Finset (Fin n)) (h : Fin n) : Fin n → ℝ :=
  fun j ↦ if j ∈ C then 1 else (Int.floor ((a j : ℝ) / (a h : ℝ)) : ℝ)

/-- `exercise_7_8_chvatal_coeffs a C h j` is `1` on `C` and `⌊a_j / a_h⌋` off `C`. -/
theorem exercise_7_8_chvatal_coeffs_apply
    (a : Fin n → ℕ) (C : Finset (Fin n)) (h j : Fin n) :
    exercise_7_8_chvatal_coeffs a C h j =
      if j ∈ C then 1 else (Int.floor ((a j : ℝ) / (a h : ℝ)) : ℝ) :=
  rfl

/-- The nonnegative multipliers placed on the upper-bound rows `x_j ≤ 1` in the Exercise 7.8
Chvatal aggregation. They are `1 - a_j / a_h` on the cover and `0` outside the cover. -/
def exercise_7_8_upper_bound_multipliers
    (a : Fin n → ℕ) (C : Finset (Fin n)) (h : Fin n) : Fin n → ℝ :=
  fun j ↦ if j ∈ C then 1 - (a j : ℝ) / (a h : ℝ) else 0

/-- `exercise_7_8_upper_bound_multipliers a C h j` is `1 - a_j / a_h` on `C` and `0` off `C`.
-/
theorem exercise_7_8_upper_bound_multipliers_apply
    (a : Fin n → ℕ) (C : Finset (Fin n)) (h j : Fin n) :
    exercise_7_8_upper_bound_multipliers a C h j =
      if j ∈ C then 1 - (a j : ℝ) / (a h : ℝ) else 0 :=
  rfl

/-- The nonnegative slack subtracted from the aggregated coefficients on `N \ C` in the Exercise
7.8 Chvatal presentation. This is the fractional part of `a_j / a_h` outside `C` and `0` on
`C`. -/
def exercise_7_8_fractional_slack
    (a : Fin n → ℕ) (C : Finset (Fin n)) (h : Fin n) : Fin n → ℝ :=
  fun j ↦ if j ∈ C then 0 else (a j : ℝ) / (a h : ℝ) - Int.floor ((a j : ℝ) / (a h : ℝ))

/-- `exercise_7_8_fractional_slack a C h j` is `0` on `C` and the fractional part of `a_j / a_h`
off `C`. -/
theorem exercise_7_8_fractional_slack_apply
    (a : Fin n → ℕ) (C : Finset (Fin n)) (h j : Fin n) :
    exercise_7_8_fractional_slack a C h j =
      if j ∈ C then 0 else (a j : ℝ) / (a h : ℝ) - Int.floor ((a j : ℝ) / (a h : ℝ)) :=
  rfl

/-- The displayed multiplier `1 / a_h` together with
`exercise_7_8_upper_bound_multipliers a C h` and `exercise_7_8_fractional_slack a C h`
gives an explicit Chvatal presentation of the Exercise 7.8 inequality whenever the stated
nonnegativity, coefficient, and right-hand-side identities hold. -/
theorem exercise_7_8_explicit_chvatal_certificate
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (h : Fin n)
    (hu₀ : 0 ≤ (1 / (a h : ℝ)))
    (hupper : ∀ j, 0 ≤ exercise_7_8_upper_bound_multipliers a C h j)
    (hslack : ∀ j, 0 ≤ exercise_7_8_fractional_slack a C h j)
    (hcoeff : ∀ j,
      (1 / (a h : ℝ)) * (a j : ℝ) +
          exercise_7_8_upper_bound_multipliers a C h j -
          exercise_7_8_fractional_slack a C h j =
        exercise_7_8_chvatal_coeffs a C h j)
    (hrhs : Int.floor
      ((1 / (a h : ℝ)) * (b : ℝ) +
        Finset.univ.sum (exercise_7_8_upper_bound_multipliers a C h)) =
      Int.ofNat (C.card - 1)) :
    IsKnapsackChvatalPresentation a b (exercise_7_8_chvatal_coeffs a C h) (C.card - 1) := by
  refine ⟨1 / (a h : ℝ), exercise_7_8_upper_bound_multipliers a C h,
    exercise_7_8_fractional_slack a C h, hu₀, hupper, hslack, ?_, hrhs⟩
  funext j
  exact hcoeff j

/-- Helper for Exercise 7.8: minimality at the pivot item bounds the cover excess by `a h`. -/
theorem exercise_7_8_excess_le_pivotWeight
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (h : Fin n)
    (hhC : h ∈ C) :
    C.sum a - b ≤ a h := by
  -- Rewrite the full cover sum as the erased sum plus the pivot weight.
  have hsum_le : C.sum a ≤ b + a h := by
    calc
      C.sum a = (C.erase h).sum a + a h := by
        rw [(Finset.sum_erase_add (s := C) (a := h) (f := a) hhC).symm]
      _ ≤ b + a h := Nat.add_le_add_right (hC.erase_sum_le h hhC) (a h)
  omega

/-- Helper for Exercise 7.8: the chosen maximal cover item has positive weight. -/
theorem exercise_7_8_pivotWeight_pos
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (h : Fin n)
    (hhC : h ∈ C) :
    0 < a h := by
  -- The cover excess is positive for every cover, and minimality bounds it by `a h`.
  have hexcess_pos : 0 < C.sum a - b := Nat.sub_pos_of_lt hC.sum_gt_capacity
  have hexcess_le : C.sum a - b ≤ a h :=
    exercise_7_8_excess_le_pivotWeight a b C hC h hhC
  omega

/-- Helper for Exercise 7.8: the aggregated upper-bound multipliers normalize the Chvatal right-
hand side to `|C| - (∑_{j ∈ C} a_j - b) / a_h`. -/
theorem exercise_7_8_upperBoundMultiplierSum_eq
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (h : Fin n) :
    ((1 / (a h : ℝ)) * (b : ℝ) + Finset.univ.sum (exercise_7_8_upper_bound_multipliers a C h)) =
      (C.card : ℝ) - (((C.sum a - b : ℕ) : ℝ) / (a h : ℝ)) := by
  classical
  have hb_le : b ≤ C.sum a := Nat.le_of_lt hC.sum_gt_capacity
  have hsum_upper :
      Finset.univ.sum (exercise_7_8_upper_bound_multipliers a C h) =
        C.sum (fun j ↦ 1 - (a j : ℝ) / (a h : ℝ)) := by
    -- Outside the cover, the upper-bound multipliers vanish.
    calc
      Finset.univ.sum (exercise_7_8_upper_bound_multipliers a C h) =
          C.sum (exercise_7_8_upper_bound_multipliers a C h) := by
            symm
            refine Finset.sum_subset (Finset.subset_univ C) ?_
            intro j _ hj_not_mem
            simp [exercise_7_8_upper_bound_multipliers, hj_not_mem]
      _ = C.sum (fun j ↦ 1 - (a j : ℝ) / (a h : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [exercise_7_8_upper_bound_multipliers, hj]
  -- Rearrange the sum into the normalized `|C| - excess / a_h` form.
  calc
    ((1 / (a h : ℝ)) * (b : ℝ) + Finset.univ.sum (exercise_7_8_upper_bound_multipliers a C h))
      = (b : ℝ) * ((a h : ℝ)⁻¹) +
          C.sum (fun j ↦ 1 - (a j : ℝ) * ((a h : ℝ)⁻¹)) := by
          rw [hsum_upper]
          simp [div_eq_mul_inv, mul_comm]
    _ = (b : ℝ) * ((a h : ℝ)⁻¹) + (C.card : ℝ) -
          C.sum (fun j ↦ (a j : ℝ) * ((a h : ℝ)⁻¹)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
          ring
    _ = (b : ℝ) * ((a h : ℝ)⁻¹) + (C.card : ℝ) -
          (C.sum (fun j ↦ (a j : ℝ))) * ((a h : ℝ)⁻¹) := by
          rw [Finset.sum_mul]
    _ = (b : ℝ) * ((a h : ℝ)⁻¹) + (C.card : ℝ) - (((C.sum a : ℕ) : ℝ)) * ((a h : ℝ)⁻¹) := by
          congr 2
          rw [Nat.cast_sum]
    _ = (C.card : ℝ) - (((C.sum a - b : ℕ) : ℝ) / (a h : ℝ)) := by
          rw [Nat.cast_sub hb_le]
          simp [div_eq_mul_inv]
          ring

/-- Helper for Exercise 7.8: the normalized Chvatal right-hand side floors to `|C| - 1`. -/
theorem exercise_7_8_rhs_floor_eq
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (h : Fin n)
    (hhC : h ∈ C) :
    Int.floor
      (((1 / (a h : ℝ)) * (b : ℝ)) + Finset.univ.sum (exercise_7_8_upper_bound_multipliers a C h)) =
        Int.ofNat (C.card - 1) := by
  have hpivot_pos : 0 < a h := exercise_7_8_pivotWeight_pos a b C hC h hhC
  have hexcess_pos : 0 < C.sum a - b := Nat.sub_pos_of_lt hC.sum_gt_capacity
  have hexcess_le : C.sum a - b ≤ a h :=
    exercise_7_8_excess_le_pivotWeight a b C hC h hhC
  have hratio_pos :
      0 < ((C.sum a - b : ℕ) : ℝ) / (a h : ℝ) := by
    exact div_pos (show 0 < ((C.sum a - b : ℕ) : ℝ) by exact_mod_cast hexcess_pos)
      (show 0 < (a h : ℝ) by exact_mod_cast hpivot_pos)
  have hratio_le_one :
      ((C.sum a - b : ℕ) : ℝ) / (a h : ℝ) ≤ 1 := by
    rw [div_le_iff₀]
    · simpa using (show ((C.sum a - b : ℕ) : ℝ) ≤ (a h : ℝ) by exact_mod_cast hexcess_le)
    · exact_mod_cast hpivot_pos
  rw [exercise_7_8_upperBoundMultiplierSum_eq a b C hC h]
  -- The normalized right-hand side lies in the interval `[|C| - 1, |C|)`.
  have hcard_pos : 0 < C.card := Finset.card_pos.mpr ⟨h, hhC⟩
  have hcard_one_le : 1 ≤ C.card := Nat.succ_le_of_lt hcard_pos
  refine Int.floor_eq_iff.mpr ?_
  constructor
  · have hcard_minus_one_le :
        (C.card : ℝ) - 1 ≤ (C.card : ℝ) -
          (((C.sum a - b : ℕ) : ℝ) / (a h : ℝ)) := by
      linarith
    simpa [Nat.cast_sub hcard_one_le] using hcard_minus_one_le
  · have hlt_card :
        (C.card : ℝ) - (((C.sum a - b : ℕ) : ℝ) / (a h : ℝ)) < C.card := by
      linarith
    simpa [Nat.cast_sub hcard_one_le, Nat.sub_add_cancel hcard_one_le, add_comm, add_left_comm,
      add_assoc] using hlt_card

/-- Exercise 7.8. For the `0,1` knapsack set `K = ℤ^n ∩ P` with
`P = {x ∈ ℝ^n | ∑ j, a_j x_j ≤ b, 0 ≤ x ≤ 1}`, if `C` is a minimal cover and `h ∈ C` has
maximal weight on `C`, then the inequality
`∑ j ∈ C, x_j + ∑ j ∉ C, ⌊a_j / a_h⌋ x_j ≤ |C| - 1`
is a Chvatal inequality for `P`. -/
theorem exercise_7_8_chvatal_inequality
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (h : Fin n)
    (hhC : h ∈ C)
    (hhmax : ∀ j ∈ C, a j ≤ a h) :
    IsKnapsackChvatalPresentation a b (exercise_7_8_chvatal_coeffs a C h) (C.card - 1) := by
  have hpivot_pos : 0 < a h := exercise_7_8_pivotWeight_pos a b C hC h hhC
  have hu₀ : 0 ≤ (1 / (a h : ℝ)) := by
    -- The knapsack-row multiplier is nonnegative because the pivot weight is positive.
    exact one_div_nonneg.mpr (show 0 ≤ (a h : ℝ) by exact_mod_cast hpivot_pos.le)
  refine exercise_7_8_explicit_chvatal_certificate a b C h hu₀ ?_ ?_ ?_ ?_
  · intro j
    by_cases hj : j ∈ C
    · -- On the cover, maximality of `h` makes the upper-bound multiplier nonnegative.
      have hdiv_le_one : (a j : ℝ) / (a h : ℝ) ≤ 1 := by
        rw [div_le_iff₀]
        · simpa using (show (a j : ℝ) ≤ (a h : ℝ) by exact_mod_cast hhmax j hj)
        · exact_mod_cast hpivot_pos
      simpa [exercise_7_8_upper_bound_multipliers_apply, hj] using sub_nonneg.mpr hdiv_le_one
    · -- Off the cover, the multiplier is exactly `0`.
      simp [exercise_7_8_upper_bound_multipliers_apply, hj]
  · intro j
    by_cases hj : j ∈ C
    · -- On the cover, the fractional slack is defined to be `0`.
      simp [exercise_7_8_fractional_slack_apply, hj]
    · -- Off the cover, the fractional slack is `x - floor x`, which is always nonnegative.
      simp [exercise_7_8_fractional_slack_apply, hj]
  · intro j
    by_cases hj : j ∈ C
    · -- On the cover, the aggregation collapses to the coefficient `1`.
      simp [exercise_7_8_chvatal_coeffs_apply, exercise_7_8_upper_bound_multipliers_apply,
        exercise_7_8_fractional_slack_apply, hj, div_eq_mul_inv]
      ring
    · -- Off the cover, subtracting the fractional part leaves the floor coefficient.
      calc
        (1 / (a h : ℝ)) * (a j : ℝ) +
            exercise_7_8_upper_bound_multipliers a C h j -
            exercise_7_8_fractional_slack a C h j
          = (a j : ℝ) / (a h : ℝ) -
              (((a j : ℝ) / (a h : ℝ)) - Int.floor ((a j : ℝ) / (a h : ℝ))) := by
              have hratio : (1 / (a h : ℝ)) * (a j : ℝ) = (a j : ℝ) / (a h : ℝ) := by
                rw [one_div, div_eq_mul_inv, mul_comm]
              rw [exercise_7_8_upper_bound_multipliers_apply,
                exercise_7_8_fractional_slack_apply]
              rw [if_neg hj, if_neg hj, add_zero, hratio]
        _ = Int.floor ((a j : ℝ) / (a h : ℝ)) := by
            ring
        _ = exercise_7_8_chvatal_coeffs a C h j := by
            simp [exercise_7_8_chvatal_coeffs_apply, hj]
  · -- The aggregated right-hand side floors to `|C| - 1` by the normalized excess bound.
    exact exercise_7_8_rhs_floor_eq a b C hC h hhC

end Exercise78
