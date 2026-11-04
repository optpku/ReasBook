/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_2

open LinearEquiv
open scoped Matrix

-- Exercise 5.7 is kept in the concrete pair model `(ℝ × ℝ)`, but its mixed-integer and
-- Chvátal notions are specialized from the Chapter 5 `Fin 2 → ℝ` owners through the canonical
-- mathlib equivalence `LinearEquiv.finTwoArrow ℝ ℝ`.

section Exercise57

/-- The matrix describing the system
`-2 x + y ≤ 0`, `2 x + y ≤ 2`, and `-y ≤ 0` from Exercise 5.7. -/
def exercise_5_7_matrix : Matrix (Fin 3) (Fin 2) ℝ :=
  ![![-(2 : ℝ), 1], ![2, 1], ![0, -(1 : ℝ)]]

/-- The right-hand side vector for the matrix description of Exercise 5.7. -/
def exercise_5_7_rhs : Fin 3 → ℝ :=
  ![0, 2, 0]

/-- The integer-variable index set `I = {x}` from Exercise 5.7. -/
def exercise_5_7_integer_indices : Finset (Fin 2) :=
  {0}

/-- The polyhedron `P = {(x, y) ∈ ℝ² | 2 x ≥ y, 2 x + y ≤ 2, y ≥ 0}` from Exercise 5.7. -/
def exercise_5_7_polyhedron : Set (ℝ × ℝ) :=
  (finTwoArrow ℝ ℝ).symm ⁻¹' polyhedron_le_set exercise_5_7_matrix exercise_5_7_rhs

/-- Membership in `exercise_5_7_polyhedron` is exactly the displayed inequality system of
Exercise 5.7. -/
theorem mem_exercise_5_7_polyhedron_iff
    {xy : ℝ × ℝ} :
    xy ∈ exercise_5_7_polyhedron ↔
      xy.2 ≤ 2 * xy.1 ∧ 2 * xy.1 + xy.2 ≤ 2 ∧ 0 ≤ xy.2 := by
  rw [exercise_5_7_polyhedron, Set.mem_preimage, mem_polyhedron_le_set_iff]
  constructor
  · intro hxy
    -- Read the three row inequalities in the concrete `(x, y)` coordinates.
    have h0 : -2 * xy.1 + xy.2 ≤ 0 := by
      simpa [exercise_5_7_matrix, exercise_5_7_rhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, LinearEquiv.finTwoArrow] using hxy 0
    have h1 : 2 * xy.1 + xy.2 ≤ 2 := by
      simpa [exercise_5_7_matrix, exercise_5_7_rhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, LinearEquiv.finTwoArrow] using hxy 1
    have h2 : -xy.2 ≤ 0 := by
      simpa [exercise_5_7_matrix, exercise_5_7_rhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, LinearEquiv.finTwoArrow] using hxy 2
    refine ⟨?_, h1, ?_⟩
    · linarith
    · linarith
  · rintro ⟨hy_le, hsum_le, hy_nonneg⟩ i
    -- Reassemble the owner-side matrix inequality row by row.
    fin_cases i
    · have h0 : -2 * xy.1 + xy.2 ≤ 0 := by
        linarith
      simpa [exercise_5_7_matrix, exercise_5_7_rhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, LinearEquiv.finTwoArrow] using h0
    · simpa [exercise_5_7_matrix, exercise_5_7_rhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, LinearEquiv.finTwoArrow] using hsum_le
    · have h2 : -xy.2 ≤ 0 := by
        linarith
      simpa [exercise_5_7_matrix, exercise_5_7_rhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, LinearEquiv.finTwoArrow] using h2

/-- The mixed-integer set `S := P ∩ (ℤ × ℝ)` from Exercise 5.7, viewed through the canonical
owner `mixed_integer_feasible_set`. -/
def exercise_5_7_mixed_integer_set : Set (ℝ × ℝ) :=
  (finTwoArrow ℝ ℝ).symm ⁻¹'
    mixed_integer_feasible_set
      exercise_5_7_matrix
      exercise_5_7_rhs
      exercise_5_7_integer_indices

/-- Membership in `exercise_5_7_mixed_integer_set` means feasibility in `P` together with
integrality of the first coordinate. -/
theorem mem_exercise_5_7_mixed_integer_set_iff
    {xy : ℝ × ℝ} :
    xy ∈ exercise_5_7_mixed_integer_set ↔
      xy ∈ exercise_5_7_polyhedron ∧ ∃ z : ℤ, xy.1 = (z : ℝ) := by
  rw [exercise_5_7_mixed_integer_set, Set.mem_preimage, mem_mixed_integer_feasible_set_iff]
  constructor
  · rintro ⟨hxy, hint⟩
    refine ⟨?_, ?_⟩
    · -- The owner-side feasibility condition is exactly pair-model membership in `P`.
      change (finTwoArrow ℝ ℝ).symm xy ∈
        polyhedron_le_set exercise_5_7_matrix exercise_5_7_rhs
      exact (mem_polyhedron_le_set_iff).2 hxy
    · simpa [LinearEquiv.finTwoArrow] using
        hint 0 (by simp [exercise_5_7_integer_indices])
  · rintro ⟨hxy, ⟨z, hz⟩⟩
    refine ⟨?_, ?_⟩
    · -- Repackage pair-model feasibility into the owner-side inequality data.
      have hxy' : (finTwoArrow ℝ ℝ).symm xy ∈
          polyhedron_le_set exercise_5_7_matrix exercise_5_7_rhs := by
        simpa [exercise_5_7_polyhedron] using hxy
      exact (mem_polyhedron_le_set_iff).1 hxy'
    · intro j hj
      fin_cases j
      · simpa [LinearEquiv.finTwoArrow, exercise_5_7_integer_indices] using ⟨z, hz⟩
      · simp [exercise_5_7_integer_indices] at hj

/-- The fractional vertex `(1 / 2, 1)` of the triangle `P`. -/
noncomputable def exercise_5_7_fractional_vertex : ℝ × ℝ :=
  ((1 : ℝ) / 2, (1 : ℝ))

/-- The point `(1 / 2, 1)` belongs to the polyhedron of Exercise 5.7. -/
theorem exercise_5_7_fractional_vertex_mem_polyhedron :
    exercise_5_7_fractional_vertex ∈ exercise_5_7_polyhedron := by
  -- Check the three defining inequalities directly at the displayed vertex.
  rw [exercise_5_7_fractional_vertex, mem_exercise_5_7_polyhedron_iff]
  norm_num

/-- The Chvátal closure of Exercise 5.7 in the concrete pair model is the pair-view of the
canonical Chapter 5 mixed-integer Chvátal closure. -/
def exercise_5_7_chvatal_closure : Set (ℝ × ℝ) :=
  (finTwoArrow ℝ ℝ).symm ⁻¹'
    chvatalClosure
      exercise_5_7_matrix
      exercise_5_7_rhs
      exercise_5_7_integer_indices

/-- Membership in `exercise_5_7_chvatal_closure` is exactly membership in the Chapter 5
mixed-integer Chvátal closure for the matrix model of Exercise 5.7. -/
theorem mem_exercise_5_7_chvatal_closure_iff
    {xy : ℝ × ℝ} :
    xy ∈ exercise_5_7_chvatal_closure ↔
      (finTwoArrow ℝ ℝ).symm xy ∈
        chvatalClosure
          exercise_5_7_matrix
          exercise_5_7_rhs
          exercise_5_7_integer_indices :=
  Iff.rfl

/-- Helper for Exercise 5.7: every point of `P` satisfies the interval bound `0 ≤ x ≤ 1`. -/
lemma exercise_5_7_xBounds_of_mem_polyhedron
    {xy : ℝ × ℝ}
    (hxy : xy ∈ exercise_5_7_polyhedron) :
    0 ≤ xy.1 ∧ xy.1 ≤ 1 := by
  -- Combine `y ≤ 2x`, `2x + y ≤ 2`, and `0 ≤ y` to trap the first coordinate.
  rcases (mem_exercise_5_7_polyhedron_iff.mp hxy) with ⟨hy_le, hsum_le, hy_nonneg⟩
  constructor <;> linarith

/-- Helper for Exercise 5.7: every mixed-integer feasible point lies on the axis `y = 0`. -/
lemma exercise_5_7_mixed_integer_second_eq_zero
    {xy : ℝ × ℝ}
    (hxy : xy ∈ exercise_5_7_mixed_integer_set) :
    xy.2 = 0 := by
  -- The integral first coordinate lies in `[0, 1]`, so only the cases `x = 0` and `x = 1`
  -- remain, and both force `y = 0` from the defining inequalities of `P`.
  rcases (mem_exercise_5_7_mixed_integer_set_iff.mp hxy) with ⟨hpoly, ⟨z, hz⟩⟩
  have hx_bounds := exercise_5_7_xBounds_of_mem_polyhedron hpoly
  have hz_nonneg_real : 0 ≤ (z : ℝ) := by
    simpa [hz] using hx_bounds.1
  have hz_le_one_real : (z : ℝ) ≤ 1 := by
    simpa [hz] using hx_bounds.2
  have hz_nonneg : 0 ≤ z := by
    exact_mod_cast hz_nonneg_real
  have hz_le_one : z ≤ 1 := by
    exact_mod_cast hz_le_one_real
  rcases (mem_exercise_5_7_polyhedron_iff.mp hpoly) with ⟨hy_le, hsum_le, hy_nonneg⟩
  interval_cases z
  · have hx_zero : xy.1 = 0 := by
      simpa using hz
    have hy_nonpos : xy.2 ≤ 0 := by
      linarith
    linarith
  · have hx_one : xy.1 = 1 := by
      simpa using hz
    have hy_nonpos : xy.2 ≤ 0 := by
      linarith
    linarith

/-- Helper for Exercise 5.7: the convex hull of the mixed-integer feasible set stays on the axis
`y = 0`. -/
lemma exercise_5_7_convexHull_mixed_integer_set_subset_axis :
    convexHull ℝ exercise_5_7_mixed_integer_set ⊆
      {xy : ℝ × ℝ | xy.2 = 0} := by
  -- Every generator lies on the axis, and that axis is convex.
  have hsubset : exercise_5_7_mixed_integer_set ⊆ {xy : ℝ × ℝ | xy.2 = 0} := by
    intro xy hxy
    exact exercise_5_7_mixed_integer_second_eq_zero hxy
  have haxis_convex : Convex ℝ {xy : ℝ × ℝ | xy.2 = 0} := by
    intro x hx y hy a b ha hb hab
    have hx0 : x.2 = 0 := hx
    have hy0 : y.2 = 0 := hy
    change (a • x + b • y).2 = 0
    simp [hx0, hy0]
  intro xy hxy
  exact convexHull_min hsubset haxis_convex hxy

/-- Helper for Exercise 5.7: every admissible Chvátal multiplier produces an integral
`x`-coefficient already bounded by the floored right-hand side. -/
lemma exercise_5_7_xCoeff_le_floor_rhs
    {u : Fin 3 → ℝ}
    (hu_nonneg : ∀ i : Fin 3, 0 ≤ u i)
    (hu_int : ∃ z : ℤ, (u ᵥ* exercise_5_7_matrix) 0 = (z : ℝ)) :
    (u ᵥ* exercise_5_7_matrix) 0 ≤
      (((⌊u ⬝ᵥ exercise_5_7_rhs⌋ : ℤ) : ℝ)) := by
  rcases hu_int with ⟨z, hz⟩
  have hxcoeff_le : (u ᵥ* exercise_5_7_matrix) 0 ≤ 2 * u 1 := by
    -- Expand the `x`-coefficient and discard the nonpositive contribution `-2 * u 0`.
    have hcoeff : (u ᵥ* exercise_5_7_matrix) 0 = -2 * u 0 + 2 * u 1 := by
      calc
        (u ᵥ* exercise_5_7_matrix) 0 = -(u 0 * 2) + u 1 * 2 := by
          simp [exercise_5_7_matrix, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
        _ = -2 * u 0 + 2 * u 1 := by
          ring
    rw [hcoeff]
    nlinarith [hu_nonneg 0]
  have hz_le_floor_rhs_int : z ≤ ⌊u ⬝ᵥ exercise_5_7_rhs⌋ := by
    -- The coefficient is integral, so it suffices to compare it with the unfloored right-hand
    -- side and then invoke `Int.le_floor`.
    apply Int.le_floor.mpr
    calc
      (z : ℝ) = (u ᵥ* exercise_5_7_matrix) 0 := by
        rw [hz]
      _ ≤ 2 * u 1 := hxcoeff_le
      _ = u ⬝ᵥ exercise_5_7_rhs := by
        calc
          2 * u 1 = u 1 * 2 := by
            ring
          _ = u ⬝ᵥ exercise_5_7_rhs := by
            simp [exercise_5_7_rhs, dotProduct, Fin.sum_univ_three]
  have hz_le_floor_rhs_real :
      (z : ℝ) ≤ (((⌊u ⬝ᵥ exercise_5_7_rhs⌋ : ℤ) : ℝ)) := by
    exact_mod_cast hz_le_floor_rhs_int
  calc
    (u ᵥ* exercise_5_7_matrix) 0 = (z : ℝ) := hz
    _ ≤ (((⌊u ⬝ᵥ exercise_5_7_rhs⌋ : ℤ) : ℝ)) := hz_le_floor_rhs_real

/-- First conclusion of Exercise 5.7: for
`P := {(x, y) ∈ ℝ² | 2 x ≥ y, 2 x + y ≤ 2, y ≥ 0}` and
`S := P ∩ (ℤ × ℝ)`, the convex hull `conv(S)` is not equal to `P`. -/
theorem exercise_5_7_convexHull_mixed_integer_set_ne_polyhedron :
    convexHull ℝ exercise_5_7_mixed_integer_set ≠ exercise_5_7_polyhedron := by
  intro hEq
  -- The fractional vertex belongs to `P`, but the mixed-integer hull stays on the axis `y = 0`.
  have hvertex_hull :
      exercise_5_7_fractional_vertex ∈ convexHull ℝ exercise_5_7_mixed_integer_set := by
    rw [hEq]
    exact exercise_5_7_fractional_vertex_mem_polyhedron
  have haxis : exercise_5_7_fractional_vertex.2 = 0 :=
    exercise_5_7_convexHull_mixed_integer_set_subset_axis hvertex_hull
  norm_num [exercise_5_7_fractional_vertex] at haxis

/-- Exercise 5.7 (2). The Chvátal closure of
`P := {(x, y) ∈ ℝ² | 2 x ≥ y, 2 x + y ≤ 2, y ≥ 0}` is `P` itself. -/
theorem exercise_5_7_chvatal_closure_eq_polyhedron :
    exercise_5_7_chvatal_closure = exercise_5_7_polyhedron := by
  ext xy
  constructor
  · intro hxy
    rw [mem_exercise_5_7_chvatal_closure_iff] at hxy
    -- Every Chvátal closure sits inside the original polyhedron.
    have hpoly :
        (finTwoArrow ℝ ℝ).symm xy ∈
          polyhedron_le_set exercise_5_7_matrix exercise_5_7_rhs :=
      chvatalClosure_subset_polyhedron
        exercise_5_7_matrix
        exercise_5_7_rhs
        exercise_5_7_integer_indices
        hxy
    simpa [exercise_5_7_polyhedron] using hpoly
  · intro hxy
    rw [mem_exercise_5_7_chvatal_closure_iff, mem_chvatalClosure_expanded_iff]
    refine ⟨?_, ?_⟩
    · -- Start from the ambient polyhedron membership.
      simpa [exercise_5_7_polyhedron] using hxy
    · intro u hu_nonneg hu_int hu_zero
      -- The continuous-coordinate condition kills the `y` coefficient, leaving a one-dimensional
      -- cut in `x`.
      let a : ℝ := (u ᵥ* exercise_5_7_matrix) 0
      have hcontinuous : (u ᵥ* exercise_5_7_matrix) 1 = 0 := by
        exact hu_zero 1 (by simp [exercise_5_7_integer_indices])
      have hx_bounds := exercise_5_7_xBounds_of_mem_polyhedron hxy
      have ha_floor :
          a ≤ (((⌊u ⬝ᵥ exercise_5_7_rhs⌋ : ℤ) : ℝ)) := by
        dsimp [a]
        exact exercise_5_7_xCoeff_le_floor_rhs hu_nonneg
          (hu_int 0 (by simp [exercise_5_7_integer_indices]))
      have hdot :
          (u ᵥ* exercise_5_7_matrix) ⬝ᵥ (finTwoArrow ℝ ℝ).symm xy = a * xy.1 := by
        -- After the `y`-coefficient vanishes, the dot product keeps only the `x` term.
        dsimp [a]
        simp [dotProduct, Fin.sum_univ_two, hcontinuous]
      by_cases ha_nonneg : 0 ≤ a
      · have hax : a * xy.1 ≤ a := by
          nlinarith [ha_nonneg, hx_bounds.2]
        calc
          (u ᵥ* exercise_5_7_matrix) ⬝ᵥ (finTwoArrow ℝ ℝ).symm xy = a * xy.1 := hdot
          _ ≤ a := hax
          _ ≤ (((⌊u ⬝ᵥ exercise_5_7_rhs⌋ : ℤ) : ℝ)) := ha_floor
      · have ha_nonpos : a ≤ 0 := le_of_not_ge ha_nonneg
        have hax : a * xy.1 ≤ 0 := by
          nlinarith [ha_nonpos, hx_bounds.1]
        have hfloor_nonneg : 0 ≤ (((⌊u ⬝ᵥ exercise_5_7_rhs⌋ : ℤ) : ℝ)) := by
          -- The right-hand side is `2 * u₁`, so its floor is nonnegative.
          have hrhs_nonneg : 0 ≤ u ⬝ᵥ exercise_5_7_rhs := by
            calc
              0 ≤ 2 * u 1 := by
                nlinarith [hu_nonneg 1]
              _ = u ⬝ᵥ exercise_5_7_rhs := by
                calc
                  2 * u 1 = u 1 * 2 := by
                    ring
                  _ = u ⬝ᵥ exercise_5_7_rhs := by
                    simp [exercise_5_7_rhs, dotProduct, Fin.sum_univ_three]
          exact_mod_cast Int.floor_nonneg.mpr hrhs_nonneg
        calc
          (u ᵥ* exercise_5_7_matrix) ⬝ᵥ (finTwoArrow ℝ ℝ).symm xy = a * xy.1 := hdot
          _ ≤ 0 := hax
          _ ≤ (((⌊u ⬝ᵥ exercise_5_7_rhs⌋ : ℤ) : ℝ)) := hfloor_nonneg

end Exercise57
