/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4.ch5_sec5_4_definition_5_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped Matrix LovaszSchrijverNotation

-- Primary domain: coordinate lift-and-project and Lovasz-Schrijver operators on subsets of
-- `ℝ^n`.
-- Owner abstractions reused here:
-- * `coordinate_lift_project_hull` from Chapter 5 for the source-facing coordinate split hulls
-- * `lovasz_schrijver_N` and `IsLovaszSchrijverMatrix` from Section 10.3 for the canonical
--   one-step linear Lovasz-Schrijver operator

section Exercise109

variable {n : ℕ}

/-- The matrix `A` for the explicit `Ax ≥ b` counterexample used in Exercise 10.9. -/
def exercise_10_9_counterexample_matrix : Matrix (Fin 7) (Fin 3) ℝ :=
  !![(1 : ℝ), 2, 2;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1;
    -1, 0, 0;
    0, -1, 0;
    0, 0, -1]

/-- The right-hand side vector `b` for the explicit `Ax ≥ b` counterexample used in
Exercise 10.9. -/
def exercise_10_9_counterexample_rhs : Fin 7 → ℝ :=
  ![(3 : ℝ), 0, 0, 0, -1, -1, -1]

/-- The explicit polyhedron
`P = {x ∈ ℝ_+^3 : exercise_10_9_counterexample_matrix * x ≥ exercise_10_9_counterexample_rhs}`
used in the Exercise 10.9 counterexample. The last three rows encode `x_j ≤ 1`. -/
def exercise_10_9_counterexample_polyhedron : Set (Fin 3 → ℝ) :=
  polyhedron_le_set (-exercise_10_9_counterexample_matrix) (-exercise_10_9_counterexample_rhs)

/-- Membership in `exercise_10_9_counterexample_polyhedron` is exactly the conjunction
`x₀ + 2 x₁ + 2 x₂ ≥ 3` and `0 ≤ x_j ≤ 1` for `j = 0, 1, 2`. -/
theorem mem_exercise_10_9_counterexample_polyhedron_iff
    (x : Fin 3 → ℝ) :
    x ∈ exercise_10_9_counterexample_polyhedron ↔
      3 ≤ x 0 + 2 * x 1 + 2 * x 2 ∧
        0 ≤ x 0 ∧
        0 ≤ x 1 ∧
        0 ≤ x 2 ∧
        x 0 ≤ 1 ∧
        x 1 ≤ 1 ∧
        x 2 ≤ 1 := by
  -- Rewrite the matrix presentation row-by-row into the scalar feasibility conditions.
  rw [exercise_10_9_counterexample_polyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    have h4 := hx 4
    have h5 := hx 5
    have h6 := hx 6
    norm_num [exercise_10_9_counterexample_matrix, exercise_10_9_counterexample_rhs,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2 h3 h4 h5 h6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h0' : -(2 * x 1) + -x 0 + 3 ≤ 2 * x 2 := by
        simpa using h0
      nlinarith [h0']
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4
    · simpa using h5
    · simpa using h6
  · rintro ⟨hmain, hx0_nonneg, hx1_nonneg, hx2_nonneg, hx0_le, hx1_le, hx2_le⟩
    intro i
    fin_cases i
    · have h0 : -(2 * x 1) + -x 0 + 3 ≤ 2 * x 2 := by
        nlinarith
      simpa [exercise_10_9_counterexample_matrix, exercise_10_9_counterexample_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
    · simpa [exercise_10_9_counterexample_matrix, exercise_10_9_counterexample_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hx0_nonneg
    · simpa [exercise_10_9_counterexample_matrix, exercise_10_9_counterexample_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hx1_nonneg
    · simpa [exercise_10_9_counterexample_matrix, exercise_10_9_counterexample_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hx2_nonneg
    · simpa [exercise_10_9_counterexample_matrix, exercise_10_9_counterexample_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hx0_le
    · simpa [exercise_10_9_counterexample_matrix, exercise_10_9_counterexample_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hx1_le
    · simpa [exercise_10_9_counterexample_matrix, exercise_10_9_counterexample_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hx2_le

/-- Helper for Exercise 10.9: the explicit counterexample polyhedron sits inside `[0, 1]^3`. -/
lemma exercise_10_9_counterexample_polyhedron_subset_unit_box :
    exercise_10_9_counterexample_polyhedron ⊆ prefix_unit_box (Nat.le_refl 3) := by
  intro x hx
  -- Read the coordinatewise bounds directly from the explicit membership characterization.
  rcases (mem_exercise_10_9_counterexample_polyhedron_iff x).1 hx with
    ⟨-, hx0_nonneg, hx1_nonneg, hx2_nonneg, hx0_le, hx1_le, hx2_le⟩
  rw [mem_prefix_unit_box_iff]
  intro j
  fin_cases j
  · simpa using And.intro hx0_nonneg hx0_le
  · simpa using And.intro hx1_nonneg hx1_le
  · simpa using And.intro hx2_nonneg hx2_le

/-- Helper for Exercise 10.9: every matrix polyhedron `polyhedron_le_set A b` is convex. -/
lemma polyhedronLeSet_convex
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  intro x hx y hy a c ha hc hac
  -- Rewrite convex combinations through the defining matrix inequalities.
  rw [mem_polyhedron_le_set_iff] at hx hy ⊢
  intro i
  calc
    (A *ᵥ (a • x + c • y)) i = a * (A *ᵥ x) i + c * (A *ᵥ y) i := by
      simp [Matrix.mulVec_add, Matrix.mulVec_smul]
    _ ≤ a * b i + c * b i := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hc)
    _ = b i := by rw [← add_mul, hac, one_mul]

/-- Helper for Exercise 10.9: a positive-height point of `homogenized_cone P` over a convex set
dehomogenizes to a point of `P`. -/
lemma normalizeMemOfMemHomogenizedConeOfConvex
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    (hP_convex : Convex ℝ P)
    {y : Fin (n + 1) → ℝ}
    (hy : y ∈ homogenized_cone P)
    (hy0_pos : 0 < y 0) :
    ∃ x : Fin n → ℝ, x ∈ P ∧ y = y 0 • homogenized_point x := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  have hxP : x ∈ P := by
    -- Collapse the convex hull witness because the base set is already convex.
    rwa [convexHull_eq_self.2 hP_convex] at hxHull
  refine ⟨x, hxP, ?_⟩
  -- The cone height is exactly the top coordinate of the homogenized vector.
  simp [homogenized_point]

/-- Helper for Exercise 10.9: the tail coordinates of `homogenized_point z` are exactly the
coordinates of `z`. -/
lemma homogenized_point_succ_apply
    {n : ℕ}
    (z : Fin n → ℝ)
    (i : Fin n) :
    homogenized_point z i.succ = z i :=
  rfl

/-- The explicit point `(1/3, 2/3, 2/3)` used to witness strictness in Exercise 10.9. -/
def exercise_10_9_counterexample_point : Fin 3 → ℝ :=
  ![(((1 : ℚ) / 3 : ℚ) : ℝ), (((2 : ℚ) / 3 : ℚ) : ℝ), (((2 : ℚ) / 3 : ℚ) : ℝ)]

/-- Helper for Exercise 10.9: a feasible point with second coordinate `0` is forced onto the
zero-face vertex `(1, 0, 1)`. -/
lemma counterexample_polyhedron_eq_one_zero_one_of_second_zero
    {x : Fin 3 → ℝ}
    (hx : x ∈ exercise_10_9_counterexample_polyhedron)
    (hx1 : x 1 = 0) :
    x = ![(1 : ℝ), 0, 1] := by
  rcases (mem_exercise_10_9_counterexample_polyhedron_iff x).1 hx with
    ⟨hmain, hx0_nonneg, -, hx2_nonneg, hx0_le, -, hx2_le⟩
  have hx0_eq : x 0 = 1 := by
    nlinarith [hmain, hx2_le]
  have hx2_eq : x 2 = 1 := by
    nlinarith [hmain, hx0_le]
  funext i
  fin_cases i
  · simp [hx0_eq]
  · simp [hx1]
  · simp [hx2_eq]

/-- Helper for Exercise 10.9: a feasible point with third coordinate `0` is forced onto the
zero-face vertex `(1, 1, 0)`. -/
lemma counterexample_polyhedron_eq_one_one_zero_of_third_zero
    {x : Fin 3 → ℝ}
    (hx : x ∈ exercise_10_9_counterexample_polyhedron)
    (hx2 : x 2 = 0) :
    x = ![(1 : ℝ), 1, 0] := by
  rcases (mem_exercise_10_9_counterexample_polyhedron_iff x).1 hx with
    ⟨hmain, hx0_nonneg, hx1_nonneg, -, hx0_le, hx1_le, -⟩
  have hx0_eq : x 0 = 1 := by
    nlinarith [hmain, hx1_le]
  have hx1_eq : x 1 = 1 := by
    nlinarith [hmain, hx0_le]
  funext i
  fin_cases i
  · simp [hx0_eq]
  · simp [hx1_eq]
  · simp [hx2]

/-- Helper for Exercise 10.9: on the face `x 0 = 1`, feasibility implies `1 ≤ x 1 + x 2`. -/
lemma counterexample_polyhedron_tail_sum_ge_one_of_first_one
    {x : Fin 3 → ℝ}
    (hx : x ∈ exercise_10_9_counterexample_polyhedron)
    (hx0 : x 0 = 1) :
    1 ≤ x 1 + x 2 := by
  rcases (mem_exercise_10_9_counterexample_polyhedron_iff x).1 hx with
    ⟨hmain, -, -, -, -, -, -⟩
  nlinarith [hmain, hx0]

/-- The point `exercise_10_9_counterexample_point` lies in every coordinate lift-and-project hull
of `exercise_10_9_counterexample_polyhedron`, equivalently in its full-coordinate
lift-project closure. -/
theorem exercise_10_9_counterexample_point_mem_lift_project_closure :
    exercise_10_9_counterexample_point ∈
      lift_project_closure exercise_10_9_counterexample_polyhedron Finset.univ := by
  rw [mem_lift_project_closure_iff]
  intro j hj
  fin_cases j
  · -- Split on the first coordinate using feasible points on the faces `x 0 = 0` and `x 0 = 1`.
    rw [coordinate_lift_project_hull_def]
    let xZero : Fin 3 → ℝ := ![(0 : ℝ), (1 : ℝ) / 2, 1]
    let xOne : Fin 3 → ℝ := ![(1 : ℝ), 1, 0]
    have hxZero :
        xZero ∈
          exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 0 = 0} := by
      refine ⟨?_, by simp [xZero]⟩
      rw [mem_exercise_10_9_counterexample_polyhedron_iff]
      change
        3 ≤ (0 : ℝ) + 2 * ((1 : ℝ) / 2) + 2 * 1 ∧
          0 ≤ (0 : ℝ) ∧
          0 ≤ (1 : ℝ) / 2 ∧
          0 ≤ (1 : ℝ) ∧
          (0 : ℝ) ≤ 1 ∧
          (1 : ℝ) / 2 ≤ 1 ∧
          (1 : ℝ) ≤ 1
      norm_num
    have hxOne :
        xOne ∈
          exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 0 = 1} := by
      refine ⟨?_, by simp [xOne]⟩
      rw [mem_exercise_10_9_counterexample_polyhedron_iff]
      change
        3 ≤ (1 : ℝ) + 2 * (1 : ℝ) + 2 * (0 : ℝ) ∧
          0 ≤ (1 : ℝ) ∧
          0 ≤ (1 : ℝ) ∧
          0 ≤ (0 : ℝ) ∧
          (1 : ℝ) ≤ 1 ∧
          (1 : ℝ) ≤ 1 ∧
          (0 : ℝ) ≤ 1
      norm_num
    have hline :
        AffineMap.lineMap xZero xOne (((1 : ℚ) / 3 : ℚ) : ℝ) =
          exercise_10_9_counterexample_point := by
      funext i
      fin_cases i <;> norm_num [AffineMap.lineMap_apply, xZero, xOne,
        exercise_10_9_counterexample_point]
    have hseg : exercise_10_9_counterexample_point ∈ segment ℝ xZero xOne := by
      rw [← hline]
      exact lineMap_mem_segment ℝ xZero xOne (by
        change ((((1 : ℚ) / 3 : ℚ) : ℝ)) ∈ Set.Icc (0 : ℝ) 1
        norm_num)
    let S : Set (Fin 3 → ℝ) :=
      (exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 0 = 0}) ∪
        (exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 0 = 1})
    have hxZero' : xZero ∈ S := Or.inl hxZero
    have hxOne' : xOne ∈ S := Or.inr hxOne
    exact (segment_subset_convexHull hxZero' hxOne') hseg
  · -- Split on the second coordinate using a segment between the `x 1 = 0` and `x 1 = 1` faces.
    rw [coordinate_lift_project_hull_def]
    let xZero : Fin 3 → ℝ := ![(1 : ℝ), 0, 1]
    let xOne : Fin 3 → ℝ := ![(0 : ℝ), 1, (1 : ℝ) / 2]
    have hxZero :
        xZero ∈
          exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 1 = 0} := by
      refine ⟨?_, by simp [xZero]⟩
      rw [mem_exercise_10_9_counterexample_polyhedron_iff]
      change
        3 ≤ (1 : ℝ) + 2 * (0 : ℝ) + 2 * (1 : ℝ) ∧
          0 ≤ (1 : ℝ) ∧
          0 ≤ (0 : ℝ) ∧
          0 ≤ (1 : ℝ) ∧
          (1 : ℝ) ≤ 1 ∧
          (0 : ℝ) ≤ 1 ∧
          (1 : ℝ) ≤ 1
      norm_num
    have hxOne :
        xOne ∈
          exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 1 = 1} := by
      refine ⟨?_, by simp [xOne]⟩
      rw [mem_exercise_10_9_counterexample_polyhedron_iff]
      change
        3 ≤ (0 : ℝ) + 2 * (1 : ℝ) + 2 * ((1 : ℝ) / 2) ∧
          0 ≤ (0 : ℝ) ∧
          0 ≤ (1 : ℝ) ∧
          0 ≤ (1 : ℝ) / 2 ∧
          (0 : ℝ) ≤ 1 ∧
          (1 : ℝ) ≤ 1 ∧
          (1 : ℝ) / 2 ≤ 1
      norm_num
    have hline :
        AffineMap.lineMap xZero xOne (((2 : ℚ) / 3 : ℚ) : ℝ) =
          exercise_10_9_counterexample_point := by
      funext i
      fin_cases i <;> norm_num [AffineMap.lineMap_apply, xZero, xOne,
        exercise_10_9_counterexample_point]
    have hseg : exercise_10_9_counterexample_point ∈ segment ℝ xZero xOne := by
      rw [← hline]
      exact lineMap_mem_segment ℝ xZero xOne (by
        change ((((2 : ℚ) / 3 : ℚ) : ℝ)) ∈ Set.Icc (0 : ℝ) 1
        norm_num)
    let S : Set (Fin 3 → ℝ) :=
      (exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 1 = 0}) ∪
        (exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 1 = 1})
    have hxZero' : xZero ∈ S := Or.inl hxZero
    have hxOne' : xOne ∈ S := Or.inr hxOne
    exact (segment_subset_convexHull hxZero' hxOne') hseg
  · -- The third coordinate uses the symmetric pair of feasible face points.
    rw [coordinate_lift_project_hull_def]
    let xZero : Fin 3 → ℝ := ![(1 : ℝ), 1, 0]
    let xOne : Fin 3 → ℝ := ![(0 : ℝ), (1 : ℝ) / 2, 1]
    have hxZero :
        xZero ∈
          exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 2 = 0} := by
      refine ⟨?_, by simp [xZero]⟩
      rw [mem_exercise_10_9_counterexample_polyhedron_iff]
      change
        3 ≤ (1 : ℝ) + 2 * (1 : ℝ) + 2 * (0 : ℝ) ∧
          0 ≤ (1 : ℝ) ∧
          0 ≤ (1 : ℝ) ∧
          0 ≤ (0 : ℝ) ∧
          (1 : ℝ) ≤ 1 ∧
          (1 : ℝ) ≤ 1 ∧
          (0 : ℝ) ≤ 1
      norm_num
    have hxOne :
        xOne ∈
          exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 2 = 1} := by
      refine ⟨?_, by simp [xOne]⟩
      rw [mem_exercise_10_9_counterexample_polyhedron_iff]
      change
        3 ≤ (0 : ℝ) + 2 * ((1 : ℝ) / 2) + 2 * (1 : ℝ) ∧
          0 ≤ (0 : ℝ) ∧
          0 ≤ (1 : ℝ) / 2 ∧
          0 ≤ (1 : ℝ) ∧
          (0 : ℝ) ≤ 1 ∧
          (1 : ℝ) / 2 ≤ 1 ∧
          (1 : ℝ) ≤ 1
      norm_num
    have hline :
        AffineMap.lineMap xZero xOne (((2 : ℚ) / 3 : ℚ) : ℝ) =
          exercise_10_9_counterexample_point := by
      funext i
      fin_cases i <;> norm_num [AffineMap.lineMap_apply, xZero, xOne,
        exercise_10_9_counterexample_point]
    have hseg : exercise_10_9_counterexample_point ∈ segment ℝ xZero xOne := by
      rw [← hline]
      exact lineMap_mem_segment ℝ xZero xOne (by
        change ((((2 : ℚ) / 3 : ℚ) : ℝ)) ∈ Set.Icc (0 : ℝ) 1
        norm_num)
    let S : Set (Fin 3 → ℝ) :=
      (exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 2 = 0}) ∪
        (exercise_10_9_counterexample_polyhedron ∩ {x : Fin 3 → ℝ | x 2 = 1})
    have hxZero' : xZero ∈ S := Or.inl hxZero
    have hxOne' : xOne ∈ S := Or.inr hxOne
    exact (segment_subset_convexHull hxZero' hxOne') hseg

/-- The point `exercise_10_9_counterexample_point` lies in every coordinate lift-and-project hull
of `exercise_10_9_counterexample_polyhedron`. -/
theorem exercise_10_9_counterexample_point_mem_iInter_coordinate_lift_project_hull :
    exercise_10_9_counterexample_point ∈
      ⋂ j : Fin 3, coordinate_lift_project_hull exercise_10_9_counterexample_polyhedron j := by
  simpa [lift_project_closure_univ_eq_iInter_coordinate_lift_project_hull] using
    exercise_10_9_counterexample_point_mem_lift_project_closure

/-- Helper for Exercise 10.9: the complementary lifted column for the second coordinate forces the
off-diagonal entries `Y 1 2` and `Y 3 2`. -/
lemma counterexample_complementarySecondColumnEntries
    {Y : Matrix (Fin 4) (Fin 4) ℝ}
    (hY : IsLovaszSchrijverMatrix exercise_10_9_counterexample_polyhedron Y)
    (hcol0 : Y *ᵥ lifted_basis 0 = homogenized_point exercise_10_9_counterexample_point) :
    Y 1 2 = 0 ∧
      Y 3 2 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
  -- Route correction: instead of normalizing several complementary columns at once, isolate the
  -- `(e₀ - e₂)` column and only read off the two scalar entries needed later.
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hsymm, -, hrest, hdiag⟩
  have hsymmEntry : ∀ i j : Fin 4, Y i j = Y j i := by
    intro i j
    simpa using congr_fun (congr_fun hsymm j) i
  have hconvex : Convex ℝ exercise_10_9_counterexample_polyhedron := by
    simpa [exercise_10_9_counterexample_polyhedron] using
      polyhedronLeSet_convex
        (-exercise_10_9_counterexample_matrix) (-exercise_10_9_counterexample_rhs)
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 0
  have hY10 : Y 1 0 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 1
  have hY20 : Y 2 0 = (((2 : ℚ) / 3 : ℚ) : ℝ) := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 2
  have hY30 : Y 3 0 = (((2 : ℚ) / 3 : ℚ) : ℝ) := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 3
  have hY02 : Y 0 2 = (((2 : ℚ) / 3 : ℚ) : ℝ) := by
    rw [hsymmEntry 0 2]
    exact hY20
  have hdiag1 : Y 2 2 = Y 2 0 := by
    simpa using hdiag (1 : Fin 3)
  have hcompCone :
      Y *ᵥ (lifted_basis 0 - lifted_basis 2) ∈
        homogenized_cone exercise_10_9_counterexample_polyhedron := by
    simpa using (hrest (1 : Fin 3)).2
  have hcompTop :
      (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 0 =
        (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    norm_num [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY02]
  have hcompTopPos : 0 < (Y *ᵥ (lifted_basis 0 - lifted_basis 2)) 0 := by
    rw [hcompTop]
    norm_num
  -- Dehomogenize the complementary column and force the normalized point onto the `x₁ = 0` face.
  rcases normalizeMemOfMemHomogenizedConeOfConvex hconvex hcompCone hcompTopPos with
    ⟨u, huP, huEq⟩
  have huEq' :
      Y *ᵥ (lifted_basis 0 - lifted_basis 2) =
        ((((1 : ℚ) / 3 : ℚ) : ℝ)) • homogenized_point u := by
    simpa [hcompTop] using huEq
  have huSecondZero : u 1 = 0 := by
    have hcoord := congr_fun huEq' 2
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, homogenized_point, hdiag1, hY20] at hcoord
    simpa [homogenized_point] using hcoord
  have huVertex : u = ![(1 : ℝ), 0, 1] :=
    counterexample_polyhedron_eq_one_zero_one_of_second_zero huP huSecondZero
  rw [huVertex] at huEq'
  -- Read the two coordinates needed later from the explicit scaled vertex equality.
  have hcoord1 := congr_fun huEq' 1
  have hcoord3 := congr_fun huEq' 3
  have hY12 : Y 1 2 = 0 := by
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, homogenized_point, hY10] at hcoord1
    nlinarith
  have hY32 : Y 3 2 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, homogenized_point, hY30] at hcoord3
    nlinarith
  exact ⟨hY12, hY32⟩

/-- Helper for Exercise 10.9: the complementary lifted column for the third coordinate forces the
off-diagonal entries `Y 1 3` and `Y 2 3`. -/
lemma counterexample_complementaryThirdColumnEntries
    {Y : Matrix (Fin 4) (Fin 4) ℝ}
    (hY : IsLovaszSchrijverMatrix exercise_10_9_counterexample_polyhedron Y)
    (hcol0 : Y *ᵥ lifted_basis 0 = homogenized_point exercise_10_9_counterexample_point) :
    Y 1 3 = 0 ∧
      Y 2 3 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
  -- Route correction: run the same dehomogenization only for `(e₀ - e₃)` so the proof ends at
  -- the scalar readout actually consumed by the contradiction.
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hsymm, -, hrest, hdiag⟩
  have hsymmEntry : ∀ i j : Fin 4, Y i j = Y j i := by
    intro i j
    simpa using congr_fun (congr_fun hsymm j) i
  have hconvex : Convex ℝ exercise_10_9_counterexample_polyhedron := by
    simpa [exercise_10_9_counterexample_polyhedron] using
      polyhedronLeSet_convex
        (-exercise_10_9_counterexample_matrix) (-exercise_10_9_counterexample_rhs)
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 0
  have hY10 : Y 1 0 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 1
  have hY20 : Y 2 0 = (((2 : ℚ) / 3 : ℚ) : ℝ) := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 2
  have hY30 : Y 3 0 = (((2 : ℚ) / 3 : ℚ) : ℝ) := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 3
  have hdiag2 : Y 3 3 = Y 3 0 := by
    simpa using hdiag (2 : Fin 3)
  have hY03 : Y 0 3 = (((2 : ℚ) / 3 : ℚ) : ℝ) := by
    rw [hsymmEntry 0 3]
    exact hY30
  have hcompCone :
      Y *ᵥ (lifted_basis 0 - lifted_basis 3) ∈
        homogenized_cone exercise_10_9_counterexample_polyhedron := by
    simpa using (hrest (2 : Fin 3)).2
  have hcompTop :
      (Y *ᵥ (lifted_basis 0 - lifted_basis 3)) 0 =
        (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    norm_num [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY03]
  have hcompTopPos : 0 < (Y *ᵥ (lifted_basis 0 - lifted_basis 3)) 0 := by
    rw [hcompTop]
    norm_num
  -- Dehomogenize the complementary column and force the normalized point onto the `x₂ = 0` face.
  rcases normalizeMemOfMemHomogenizedConeOfConvex hconvex hcompCone hcompTopPos with
    ⟨u, huP, huEq⟩
  have huEq' :
      Y *ᵥ (lifted_basis 0 - lifted_basis 3) =
        ((((1 : ℚ) / 3 : ℚ) : ℝ)) • homogenized_point u := by
    simpa [hcompTop] using huEq
  have huThirdZero : u 2 = 0 := by
    have hcoord := congr_fun huEq' 3
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, homogenized_point, hdiag2, hY30] at hcoord
    simpa [homogenized_point] using hcoord
  have huVertex : u = ![(1 : ℝ), 1, 0] :=
    counterexample_polyhedron_eq_one_one_zero_of_third_zero huP huThirdZero
  rw [huVertex] at huEq'
  -- Read the two coordinates needed later from the explicit scaled vertex equality.
  have hcoord1 := congr_fun huEq' 1
  have hcoord2 := congr_fun huEq' 2
  have hY13 : Y 1 3 = 0 := by
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, homogenized_point, hY10] at hcoord1
    nlinarith
  have hY23 : Y 2 3 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    simp [Matrix.mulVec_sub, mulVec_lifted_basis, homogenized_point, hY20] at hcoord2
    nlinarith
  exact ⟨hY13, hY23⟩

/-- Helper for Exercise 10.9: any Lovász-Schrijver witness for the explicit point forces the
off-diagonal entries `Y 1 2`, `Y 1 3`, and `Y 2 3`. -/
lemma exercise_10_9_forcedCrossTerms_of_lovaszSchrijverWitness
    {Y : Matrix (Fin 4) (Fin 4) ℝ}
    (hY : IsLovaszSchrijverMatrix exercise_10_9_counterexample_polyhedron Y)
    (hcol0 : Y *ᵥ lifted_basis 0 = homogenized_point exercise_10_9_counterexample_point) :
    Y 1 2 = 0 ∧
      Y 1 3 = 0 ∧
      Y 2 3 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
  -- Route correction: the witness analysis now ends in two concrete complementary-column lemmas,
  -- so this wrapper only assembles their scalar outputs.
  rcases counterexample_complementarySecondColumnEntries hY hcol0 with ⟨hY12, -⟩
  rcases counterexample_complementaryThirdColumnEntries hY hcol0 with ⟨hY13, hY23⟩
  exact ⟨hY12, hY13, hY23⟩

/-- Helper for Exercise 10.9: the lifted column for the first coordinate forces the lower bound
`1 / 3 ≤ Y 2 1 + Y 3 1`. -/
lemma counterexample_firstCoordinateColumnTailSumLowerBound
    {Y : Matrix (Fin 4) (Fin 4) ℝ}
    (hY : IsLovaszSchrijverMatrix exercise_10_9_counterexample_polyhedron Y)
    (hcol0 : Y *ᵥ lifted_basis 0 = homogenized_point exercise_10_9_counterexample_point) :
    (((1 : ℚ) / 3 : ℚ) : ℝ) ≤ Y 2 1 + Y 3 1 := by
  -- Route correction: normalize only the positive column `e₁`, force the face `x₀ = 1`, and
  -- transport the resulting tail-sum inequality back to the witness entries.
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hsymm, -, hrest, hdiag⟩
  have hsymmEntry : ∀ i j : Fin 4, Y i j = Y j i := by
    intro i j
    simpa using congr_fun (congr_fun hsymm j) i
  have hconvex : Convex ℝ exercise_10_9_counterexample_polyhedron := by
    simpa [exercise_10_9_counterexample_polyhedron] using
      polyhedronLeSet_convex
        (-exercise_10_9_counterexample_matrix) (-exercise_10_9_counterexample_rhs)
  have hY10 : Y 1 0 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    simpa [mulVec_lifted_basis, homogenized_point, exercise_10_9_counterexample_point] using
      congr_fun hcol0 1
  have hY01 : Y 0 1 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    rw [hsymmEntry 0 1]
    exact hY10
  have hdiag0 : Y 1 1 = Y 1 0 := by
    simpa using hdiag (0 : Fin 3)
  have hcolCone :
      Y *ᵥ lifted_basis 1 ∈ homogenized_cone exercise_10_9_counterexample_polyhedron := by
    simpa using (hrest (0 : Fin 3)).1
  have hcolTop : (Y *ᵥ lifted_basis 1) 0 = (((1 : ℚ) / 3 : ℚ) : ℝ) := by
    simpa [mulVec_lifted_basis] using hY01
  have hcolTopPos : 0 < (Y *ᵥ lifted_basis 1) 0 := by
    rw [hcolTop]
    norm_num
  -- Dehomogenize the first lifted column and use the diagonal equality to land on the face
  -- `x₀ = 1`.
  rcases normalizeMemOfMemHomogenizedConeOfConvex hconvex hcolCone hcolTopPos with
    ⟨u, huP, huEq⟩
  have huEq' :
      Y *ᵥ lifted_basis 1 =
        ((((1 : ℚ) / 3 : ℚ) : ℝ)) • homogenized_point u := by
    simpa [hcolTop] using huEq
  have huFirstOne : u 0 = 1 := by
    have hcoord := congr_fun huEq' 1
    simp [mulVec_lifted_basis, homogenized_point, hdiag0, hY10] at hcoord
    nlinarith
  have htail : 1 ≤ u 1 + u 2 :=
    counterexample_polyhedron_tail_sum_ge_one_of_first_one huP huFirstOne
  -- The normalized tail coordinates are exactly `Y 2 1` and `Y 3 1` after rescaling.
  have hcoord2' : Y 2 1 = (((1 : ℚ) / 3 : ℚ) : ℝ) * u 1 := by
    have hcoord2 := congr_fun huEq' 2
    simpa [mulVec_lifted_basis, homogenized_point] using hcoord2
  have hcoord3' : Y 3 1 = (((1 : ℚ) / 3 : ℚ) : ℝ) * u 2 := by
    have hcoord3 := congr_fun huEq' 3
    simpa [mulVec_lifted_basis, homogenized_point] using hcoord3
  nlinarith

/-- The point `exercise_10_9_counterexample_point` does not belong to the Lovasz-Schrijver
relaxation of `exercise_10_9_counterexample_polyhedron`. -/
theorem exercise_10_9_counterexample_point_not_mem_lovasz_schrijver_N :
    exercise_10_9_counterexample_point ∉
      N(exercise_10_9_counterexample_polyhedron) := by
  -- Route correction: the contradiction now uses one lower-bound helper and one cross-term
  -- helper, rather than reopening several column normalizations inside the final theorem.
  intro hx
  rw [mem_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  rcases exercise_10_9_forcedCrossTerms_of_lovaszSchrijverWitness hY hcol0 with
    ⟨hY12, hY13, -⟩
  have hlower := counterexample_firstCoordinateColumnTailSumLowerBound hY hcol0
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hsymm, -, -, -⟩
  have hsymmEntry : ∀ i j : Fin 4, Y i j = Y j i := by
    intro i j
    simpa using congr_fun (congr_fun hsymm j) i
  have hY21 : Y 2 1 = 0 := by
    rw [hsymmEntry 2 1]
    exact hY12
  have hY31 : Y 3 1 = 0 := by
    rw [hsymmEntry 3 1]
    exact hY13
  -- The first-column lower bound contradicts the forced vanishing of both tail entries.
  nlinarith

/-- Helper for Exercise 10.9: every point of the one-step Lovász-Schrijver relaxation already
lies in each coordinate lift-and-project hull of the explicit counterexample polyhedron. -/
lemma counterexample_memCoordinateHull_of_memLovaszSchrijverN
    {x : Fin 3 → ℝ}
    (hx : x ∈ N(exercise_10_9_counterexample_polyhedron))
    (j : Fin 3) :
    x ∈ coordinate_lift_project_hull exercise_10_9_counterexample_polyhedron j := by
  -- Route correction: keep the proof coordinate-local and split into boundary and interior cases,
  -- so each branch only normalizes the two lifted columns attached to the chosen coordinate.
  rw [mem_lovasz_schrijver_N_iff] at hx
  rcases hx with ⟨Y, hY, hcol0⟩
  have hconvex : Convex ℝ exercise_10_9_counterexample_polyhedron := by
    simpa [exercise_10_9_counterexample_polyhedron] using
      polyhedronLeSet_convex
        (-exercise_10_9_counterexample_matrix) (-exercise_10_9_counterexample_rhs)
  have hxP : x ∈ exercise_10_9_counterexample_polyhedron := by
    exact lovasz_schrijver_N_subset exercise_10_9_counterexample_polyhedron hconvex
      ((mem_lovasz_schrijver_N_iff _ _).2 ⟨Y, hY, hcol0⟩)
  have hxBox := exercise_10_9_counterexample_polyhedron_subset_unit_box hxP
  rw [mem_prefix_unit_box_iff] at hxBox
  have hxj_nonneg : 0 ≤ x j := (hxBox j).1
  have hxj_le_one : x j ≤ 1 := (hxBox j).2
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hsymm, -, hrest, hdiag⟩
  have hsymmEntry : ∀ i k : Fin 4, Y i k = Y k i := by
    intro i k
    simpa using congr_fun (congr_fun hsymm k) i
  have hY00 : Y 0 0 = 1 := by
    simpa [mulVec_lifted_basis, homogenized_point] using congr_fun hcol0 0
  have hYj0 : Y j.succ 0 = x j := by
    simpa [mulVec_lifted_basis, homogenized_point_succ_apply] using congr_fun hcol0 j.succ
  have hY0j : Y 0 j.succ = x j := by
    rw [hsymmEntry 0 j.succ]
    exact hYj0
  by_cases hxj_zero : x j = 0
  · -- Boundary case `x j = 0`: the point already belongs to the left face.
    rw [coordinate_lift_project_hull_def]
    exact subset_convexHull ℝ _ (Or.inl ⟨hxP, hxj_zero⟩)
  by_cases hxj_one : x j = 1
  · -- Boundary case `x j = 1`: the point already belongs to the right face.
    rw [coordinate_lift_project_hull_def]
    exact subset_convexHull ℝ _ (Or.inr ⟨hxP, hxj_one⟩)
  · -- Interior case: dehomogenize the positive column and its complement, then reassemble `x`
    -- as a segment point between the `x j = 0` and `x j = 1` faces.
    have hxj_pos : 0 < x j := by
      refine lt_of_le_of_ne hxj_nonneg ?_
      intro hzero
      exact hxj_zero hzero.symm
    have hone_sub_pos : 0 < 1 - x j := by
      refine lt_of_le_of_ne (sub_nonneg.mpr hxj_le_one) ?_
      intro hzero
      apply hxj_one
      linarith
    have hdiagj : Y j.succ j.succ = Y j.succ 0 := hdiag j
    have hcolCone :
        Y *ᵥ lifted_basis j.succ ∈
          homogenized_cone exercise_10_9_counterexample_polyhedron := (hrest j).1
    have hcompCone :
        Y *ᵥ (lifted_basis 0 - lifted_basis j.succ) ∈
          homogenized_cone exercise_10_9_counterexample_polyhedron := (hrest j).2
    rcases normalizeMemOfMemHomogenizedConeOfConvex hconvex hcolCone (by
      simpa [mulVec_lifted_basis, hY0j] using hxj_pos) with
      ⟨xOne, hxOneP, hcolEq⟩
    rcases normalizeMemOfMemHomogenizedConeOfConvex hconvex hcompCone (by
      simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY0j] using hone_sub_pos) with
      ⟨xZero, hxZeroP, hcompEq⟩
    have hcolEq' :
        Y *ᵥ lifted_basis j.succ = (x j) • homogenized_point xOne := by
      simpa [mulVec_lifted_basis, hY0j] using hcolEq
    have hcompEq' :
        Y *ᵥ (lifted_basis 0 - lifted_basis j.succ) =
          (1 - x j) • homogenized_point xZero := by
      simpa [Matrix.mulVec_sub, mulVec_lifted_basis, hY00, hY0j] using hcompEq
    have hxOneFace : xOne j = 1 := by
      have hcoord := congr_fun hcolEq' j.succ
      simp [mulVec_lifted_basis, homogenized_point, hdiagj, hYj0] at hcoord
      nlinarith
    have hxZeroFace : xZero j = 0 := by
      have hcoord : 1 - x j = 0 ∨ xZero j = 0 := by
        have hcoord := congr_fun hcompEq' j.succ
        simpa [Matrix.mulVec_sub, mulVec_lifted_basis, homogenized_point, hdiagj, hYj0]
          using hcoord
      rcases hcoord with hfac | hzero
      · have hxj_eq_one : x j = 1 := by
          linarith
        exact False.elim (hxj_one hxj_eq_one)
      · exact hzero
    have hsumCols :
        Y *ᵥ lifted_basis j.succ + Y *ᵥ (lifted_basis 0 - lifted_basis j.succ) =
          Y *ᵥ lifted_basis 0 := by
      ext k
      simp [Matrix.mulVec_sub, mulVec_lifted_basis]
    have hsumVec :
        homogenized_point x =
          (x j) • homogenized_point xOne + (1 - x j) • homogenized_point xZero := by
      calc
        homogenized_point x = Y *ᵥ lifted_basis 0 := hcol0.symm
        _ = Y *ᵥ lifted_basis j.succ + Y *ᵥ (lifted_basis 0 - lifted_basis j.succ) := by
          symm
          exact hsumCols
        _ = (x j) • homogenized_point xOne + (1 - x j) • homogenized_point xZero := by
          rw [hcolEq', hcompEq']
    have hline : AffineMap.lineMap xZero xOne (x j) = x := by
      funext i
      have hcoord := congr_fun hsumVec i.succ
      have hcoord' : x i = x j * xOne i + (1 - x j) * xZero i := by
        simpa [homogenized_point] using hcoord
      calc
        AffineMap.lineMap xZero xOne (x j) i = x j * (xOne i - xZero i) + xZero i := by
          simp [AffineMap.lineMap_apply]
        _ = x j * xOne i + (1 - x j) * xZero i := by
          ring
        _ = x i := by
          linarith
    have hxSeg : x ∈ segment ℝ xZero xOne := by
      rw [← hline]
      exact lineMap_mem_segment ℝ xZero xOne ⟨hxj_nonneg, hxj_le_one⟩
    rw [coordinate_lift_project_hull_def]
    let S : Set (Fin 3 → ℝ) :=
      (exercise_10_9_counterexample_polyhedron ∩ {y : Fin 3 → ℝ | y j = 0}) ∪
        (exercise_10_9_counterexample_polyhedron ∩ {y : Fin 3 → ℝ | y j = 1})
    have hxZero' : xZero ∈ S := Or.inl ⟨hxZeroP, hxZeroFace⟩
    have hxOne' : xOne ∈ S := Or.inr ⟨hxOneP, hxOneFace⟩
    exact (segment_subset_convexHull hxZero' hxOne') hxSeg

/-- Helper for Exercise 10.9: the one-step Lovász-Schrijver relaxation of the explicit
counterexample polyhedron is contained in its full-coordinate lift-project closure. -/
lemma exercise_10_9_lovaszSchrijverSubsetLiftProjectClosure :
    N(exercise_10_9_counterexample_polyhedron) ⊆
      lift_project_closure exercise_10_9_counterexample_polyhedron Finset.univ := by
  -- Route correction: prove coordinate-hull membership once in a local helper, then discharge the
  -- full closure by the owner characterization `mem_lift_project_closure_iff`.
  intro x hx
  rw [mem_lift_project_closure_iff]
  intro j hj
  exact counterexample_memCoordinateHull_of_memLovaszSchrijverN hx j

/-- Exercise 10.9. For the explicit polyhedron
`P = {x ∈ [0, 1]^3 | x₀ + 2 x₁ + 2 x₂ ≥ 3}`, encoded by
`exercise_10_9_counterexample_matrix` and `exercise_10_9_counterexample_rhs`, the
Lovasz-Schrijver relaxation `N(P)` is strictly contained in the full-coordinate
lift-project closure of `P`. -/
theorem exercise_10_9_lovasz_schrijver_N_ssubset_lift_project_closure :
    N(exercise_10_9_counterexample_polyhedron) ⊂
      lift_project_closure exercise_10_9_counterexample_polyhedron Finset.univ := by
  refine ⟨exercise_10_9_lovaszSchrijverSubsetLiftProjectClosure, ?_⟩
  intro hclosure
  exact exercise_10_9_counterexample_point_not_mem_lovasz_schrijver_N
    (hclosure exercise_10_9_counterexample_point_mem_lift_project_closure)

/-- Exercise 10.9. For the explicit polyhedron
`P = {x ∈ [0, 1]^3 | x₀ + 2 x₁ + 2 x₂ ≥ 3}`, encoded by
`exercise_10_9_counterexample_matrix` and `exercise_10_9_counterexample_rhs`, the inclusion
`N(P) ⊆ ⋂_{j=1}^3 conv ((P ∩ {x_j = 0}) ∪ (P ∩ {x_j = 1}))` is strict. -/
theorem exercise_10_9_lovasz_schrijver_N_ssubset_iInter_coordinate_lift_project_hull :
    N(exercise_10_9_counterexample_polyhedron) ⊂
      ⋂ j : Fin 3, coordinate_lift_project_hull exercise_10_9_counterexample_polyhedron j := by
  simpa [lift_project_closure_univ_eq_iInter_coordinate_lift_project_hull] using
    exercise_10_9_lovasz_schrijver_N_ssubset_lift_project_closure

end Exercise109
