/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-- A real matrix whose entries all belong to `{ -1, 0, 1 }`. -/
def has_signed_unit_entries {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, D i j = -1 ∨ D i j = 0 ∨ D i j = 1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean: the `0/1` point attached to
a Boolean pattern. -/
private def boolPatternPoint {n : ℕ} (σ : Fin n → Bool) : Fin n → ℝ :=
  fun i ↦ if σ i then 1 else 0

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean: the signed row coefficients
that separate a Boolean pattern from the other binary points. -/
private def signedSeparatorCoeff {n : ℕ} (σ : Fin n → Bool) : Fin n → ℝ :=
  fun i ↦ if σ i then 1 else -1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean: the sum of the Boolean point
coordinates is the support size of the pattern. -/
private lemma sum_boolPatternPoint_eq_card {n : ℕ} (σ : Fin n → Bool) :
    ∑ i : Fin n, boolPatternPoint σ i =
      ((Finset.univ.filter fun i ↦ σ i).card : ℝ) := by
  -- Replace the Boolean point by its coordinatewise indicator and evaluate the indicator sum.
  unfold boolPatternPoint
  exact Finset.sum_boole (R := ℝ) (fun i : Fin n ↦ σ i) Finset.univ

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean: a `0/1` vector is recovered
from the Boolean pattern recording its `1` coordinates. -/
private lemma boolPatternPoint_eq_self_of_isZeroOne {n : ℕ} {x : Fin n → ℝ}
    (hx : is_zero_one_vector x) :
    boolPatternPoint (fun i ↦ x i = 1) = x := by
  -- Compare coordinates and use the `0/1` dichotomy at each coordinate.
  funext i
  rcases is_zero_one_vector.apply hx i with hxi | hxi
  · simp [boolPatternPoint, hxi]
  · simp [boolPatternPoint, hxi]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean: each separator term is
bounded by the corresponding Boolean-point coordinate. -/
private lemma signedSeparatorTerm_le_indicator {n : ℕ} (σ : Fin n → Bool) {x : Fin n → ℝ}
    (hx : is_zero_one_vector x) (i : Fin n) :
    signedSeparatorCoeff σ i * x i ≤ boolPatternPoint σ i := by
  -- Reduce to the four possible `0/1`-and-Boolean coordinate combinations.
  rcases is_zero_one_vector.apply hx i with hxi | hxi <;>
    by_cases hσ : σ i <;>
    simp [signedSeparatorCoeff, boolPatternPoint, hxi, hσ]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean: at a mismatching coordinate,
the separator term loses one unit compared to the Boolean-point coordinate. -/
private lemma signedSeparatorTerm_le_indicator_sub_one_of_ne {n : ℕ} (σ : Fin n → Bool)
    {x : Fin n → ℝ} (hx : is_zero_one_vector x) {i : Fin n}
    (hneq : x i ≠ boolPatternPoint σ i) :
    signedSeparatorCoeff σ i * x i ≤ boolPatternPoint σ i - 1 := by
  -- The mismatch forces the unique `0/1` value different from the Boolean point.
  by_cases hσ : σ i
  · have hxi : x i = 0 := by
      rcases is_zero_one_vector.apply hx i with hzero | hone
      · exact hzero
      · exfalso
        exact hneq (by simp [boolPatternPoint, hσ, hone])
    simp [signedSeparatorCoeff, boolPatternPoint, hσ, hxi]
  · have hxi : x i = 1 := by
      rcases is_zero_one_vector.apply hx i with hzero | hone
      · exfalso
        exact hneq (by simp [boolPatternPoint, hσ, hzero])
      · exact hone
    simp [signedSeparatorCoeff, boolPatternPoint, hσ, hxi]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean: every binary point distinct
from a Boolean pattern satisfies the corresponding signed separator inequality. -/
private lemma signedSeparatorValue_le_bound_of_ne {n : ℕ} (σ : Fin n → Bool) {x : Fin n → ℝ}
    (hx : is_zero_one_vector x) (hneq : x ≠ boolPatternPoint σ) :
    ∑ i : Fin n, signedSeparatorCoeff σ i * x i ≤
      ((Finset.univ.filter fun i ↦ σ i).card : ℝ) - 1 := by
  -- Pick a mismatching coordinate and spend the missing unit there.
  have hmismatch : ∃ j : Fin n, x j ≠ boolPatternPoint σ j := by
    by_contra hno
    apply hneq
    funext j
    by_contra hj
    exact hno ⟨j, hj⟩
  rcases hmismatch with ⟨j, hj⟩
  have hrest :
      (Finset.univ.erase j).sum (fun i : Fin n ↦ signedSeparatorCoeff σ i * x i) ≤
        (Finset.univ.erase j).sum (fun i : Fin n ↦ boolPatternPoint σ i) := by
    -- Away from the mismatching coordinate, every term is bounded by the Boolean indicator.
    exact Finset.sum_le_sum fun i hi ↦ signedSeparatorTerm_le_indicator σ hx i
  have hj' :
      signedSeparatorCoeff σ j * x j ≤ boolPatternPoint σ j - 1 :=
    signedSeparatorTerm_le_indicator_sub_one_of_ne σ hx hj
  calc
    ∑ i : Fin n, signedSeparatorCoeff σ i * x i
        = (Finset.univ.erase j).sum (fun i : Fin n ↦ signedSeparatorCoeff σ i * x i) +
            signedSeparatorCoeff σ j * x j := by
            symm
            exact Finset.sum_erase_add (s := Finset.univ) (f := fun i : Fin n ↦
              signedSeparatorCoeff σ i * x i) (Finset.mem_univ j)
    _ ≤ (Finset.univ.erase j).sum (fun i : Fin n ↦ boolPatternPoint σ i) +
          (boolPatternPoint σ j - 1) := by
      exact add_le_add hrest hj'
    _ = ((Finset.univ.erase j).sum (fun i : Fin n ↦ boolPatternPoint σ i) +
          boolPatternPoint σ j) - 1 := by
      ring
    _ = ∑ i : Fin n, boolPatternPoint σ i - 1 := by
      rw [Finset.sum_erase_add (s := Finset.univ) (f := boolPatternPoint σ) (Finset.mem_univ j)]
    _ = ((Finset.univ.filter fun i ↦ σ i).card : ℝ) - 1 := by
      rw [sum_boolPatternPoint_eq_card]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean: the separator row attains
its exact support-cardinality value on the Boolean pattern that defines it. -/
private lemma signedSeparatorValue_at_pattern {n : ℕ} (σ : Fin n → Bool) :
    ∑ i : Fin n, signedSeparatorCoeff σ i * boolPatternPoint σ i =
      ((Finset.univ.filter fun i ↦ σ i).card : ℝ) := by
  -- On the defining pattern, every term collapses to the Boolean indicator.
  calc
    ∑ i : Fin n, signedSeparatorCoeff σ i * boolPatternPoint σ i
        = ∑ i : Fin n, boolPatternPoint σ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hσ : σ i <;> simp [signedSeparatorCoeff, boolPatternPoint, hσ]
    _ = ((Finset.univ.filter fun i ↦ σ i).card : ℝ) := by
      rw [sum_boolPatternPoint_eq_card]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_26.lean
Exercise 2.26. Every `0,1` set cut out by a real system `Ax ≤ b` can also be
written using a system `Dx ≤ d` whose matrix entries all lie in `{ -1, 0, 1 }`,
possibly with a different number of inequalities. -/
theorem zero_one_set_has_signed_unit_matrix_representation
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ∃ p : ℕ, ∃ D : Matrix (Fin p) (Fin n) ℝ, ∃ d : Fin p → ℝ,
      has_signed_unit_entries D ∧
        {x : Fin n → ℝ | is_zero_one_vector x ∧ A.mulVec x ≤ b} =
          {x : Fin n → ℝ | is_zero_one_vector x ∧ D.mulVec x ≤ d} := by
  classical
  let BadPattern := {σ : Fin n → Bool // ¬ A.mulVec (boolPatternPoint σ) ≤ b}
  let p : ℕ := Fintype.card BadPattern
  let e : BadPattern ≃ Fin p := Fintype.equivFin BadPattern
  let D : Matrix (Fin p) (Fin n) ℝ := fun i j ↦ signedSeparatorCoeff (e.symm i).1 j
  let d : Fin p → ℝ := fun i ↦ ((Finset.univ.filter fun j ↦ (e.symm i).1 j).card : ℝ) - 1
  refine ⟨p, D, d, ?_, ?_⟩
  · -- Every row entry is one of the two signed separator coefficients.
    intro i j
    by_cases hσ : (e.symm i).1 j
    · right
      right
      simp [D, signedSeparatorCoeff, hσ]
    · left
      simp [D, signedSeparatorCoeff, hσ]
  · -- Prove the two set inclusions using the bad-pattern rows.
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx01, hAx⟩
      refine ⟨hx01, ?_⟩
      intro i
      let σ : BadPattern := e.symm i
      have hneq : x ≠ boolPatternPoint σ.1 := by
        -- Equality with a bad pattern would contradict the assumed feasibility of `x`.
        intro hEq
        exact σ.2 (by simpa [σ, hEq] using hAx)
      have hsep :
          ∑ j : Fin n, signedSeparatorCoeff σ.1 j * x j ≤
            ((Finset.univ.filter fun j ↦ σ.1 j).card : ℝ) - 1 :=
        signedSeparatorValue_le_bound_of_ne σ.1 hx01 hneq
      -- Expand the selected row of `D.mulVec x` to the separator sum.
      simpa [D, d, Matrix.mulVec, dotProduct, σ] using hsep
    · intro hx
      rcases hx with ⟨hx01, hDx⟩
      refine ⟨hx01, ?_⟩
      by_contra hAx
      let σx : Fin n → Bool := fun i ↦ x i = 1
      have hxPattern : boolPatternPoint σx = x :=
        boolPatternPoint_eq_self_of_isZeroOne hx01
      let σbad : BadPattern := ⟨σx, by simpa [σx, hxPattern] using hAx⟩
      have hrow :
          ∑ j : Fin n, signedSeparatorCoeff σx j * x j ≤
            ((Finset.univ.filter fun j ↦ σx j).card : ℝ) - 1 := by
        -- Read the inequality corresponding to the bad pattern extracted from `x`.
        simpa [D, d, Matrix.mulVec, dotProduct, σx, σbad] using hDx (e σbad)
      have hself :
          ∑ j : Fin n, signedSeparatorCoeff σx j * x j =
            ((Finset.univ.filter fun j ↦ σx j).card : ℝ) := by
        -- Reconstructing the Boolean pattern turns the row evaluation into its exact self-value.
        simpa [σx, hxPattern] using signedSeparatorValue_at_pattern σx
      linarith
