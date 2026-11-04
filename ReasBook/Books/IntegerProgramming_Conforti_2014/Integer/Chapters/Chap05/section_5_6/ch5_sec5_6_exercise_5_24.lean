/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: Chapter 5 lift-and-project and Chvátal closures for concrete polyhedra in
--   `Fin 2 → ℝ`;
-- * core/canonical owners sampled upstream: `polyhedron_le_set`, `prefix_unit_box`,
--   `zero_one_points`, `lift_project_closure`, and `pure_integer_chvatal_closure`;
-- * source-facing layer kept here: the two concrete Exercise 5.24 polytopes;
-- * bridge/view layer kept here: explicit descriptions of the corresponding zero-one hulls and
--   closure relaxations.

section Exercise524

/-- Helper for Exercise 5.24: membership in the two-dimensional unit box is coordinatewise. -/
theorem mem_prefix_unit_box_two_iff
    (x : Fin 2 → ℝ) :
    x ∈ prefix_unit_box (Nat.le_refl 2) ↔
      0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 := by
  constructor
  · intro hx
    rw [mem_prefix_unit_box_iff] at hx
    exact ⟨(hx 0).1, (hx 0).2, (hx 1).1, (hx 1).2⟩
  · rintro ⟨hx0_nonneg, hx0_le, hx1_nonneg, hx1_le⟩
    rw [mem_prefix_unit_box_iff]
    intro j
    fin_cases j
    · exact ⟨hx0_nonneg, hx0_le⟩
    · exact ⟨hx1_nonneg, hx1_le⟩

/-- Helper for Exercise 5.24: the two-dimensional unit box is the interval `[0, 1]^2`. -/
theorem prefix_unit_box_two_eq_Icc :
    prefix_unit_box (Nat.le_refl 2) = Set.Icc (0 : Fin 2 → ℝ) 1 := by
  ext x
  constructor
  · intro hx
    rw [mem_prefix_unit_box_two_iff] at hx
    rcases hx with ⟨hx0_nonneg, hx0_le, hx1_nonneg, hx1_le⟩
    rw [Set.mem_Icc, Pi.le_def]
    constructor
    · intro i
      fin_cases i
      · simpa using hx0_nonneg
      · simpa using hx1_nonneg
    · intro i
      fin_cases i
      · simpa using hx0_le
      · simpa using hx1_le
  · intro hx
    rw [Set.mem_Icc, Pi.le_def] at hx
    rcases hx with ⟨hx_nonneg, hx_le⟩
    exact (mem_prefix_unit_box_two_iff x).2 ⟨by simpa using hx_nonneg 0,
      by simpa using hx_le 0, by simpa using hx_nonneg 1, by simpa using hx_le 1⟩

/-- Helper for Exercise 5.24: the case-1 triangle
`[0, 1]^2 ∩ {x | x 0 + x 1 ≤ 1}` is convex. -/
theorem exercise524Case1TriangleExplicitConvex :
    Convex ℝ (prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | x 0 + x 1 ≤ 1}) := by
  let L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ x 0 + x 1
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro a x
        simp [mul_add] }
  -- Keep the box and the sum inequality as separate convex factors.
  have hbox : Convex ℝ (prefix_unit_box (Nat.le_refl 2)) := by
    simpa [prefix_unit_box_two_eq_Icc] using (convex_Icc (0 : Fin 2 → ℝ) 1)
  have hsum : Convex ℝ {x : Fin 2 → ℝ | x 0 + x 1 ≤ 1} := by
    simpa [L] using (convex_Iic (1 : ℝ)).linear_preimage L
  exact hbox.inter hsum

/-- Helper for Exercise 5.24: the case-2 segment
`[0, 1]^2 ∩ {x | x 1 = 0}` is convex. -/
theorem exercise524Case2SegmentExplicitConvex :
    Convex ℝ (prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | x 1 = 0}) := by
  let L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) 1
  -- The segment is the box intersected with the hyperplane `x 1 = 0`.
  have hbox : Convex ℝ (prefix_unit_box (Nat.le_refl 2)) := by
    simpa [prefix_unit_box_two_eq_Icc] using (convex_Icc (0 : Fin 2 → ℝ) 1)
  have hline : Convex ℝ {x : Fin 2 → ℝ | x 1 = 0} := by
    simpa [L] using ((convex_singleton (0 : ℝ)).linear_preimage L)
  exact hbox.inter hline

/-- Helper for Exercise 5.24: the explicit case-2 Chvátal relaxation region
`[0, 1]^2 ∩ {x | x 1 ≤ x 0 ∧ x 0 + x 1 ≤ 1}` is convex. -/
theorem exercise524Case2RelaxationExplicitConvex :
    Convex ℝ (prefix_unit_box (Nat.le_refl 2) ∩
      {x : Fin 2 → ℝ | x 1 ≤ x 0 ∧ x 0 + x 1 ≤ 1}) := by
  let Ldiff : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ x 1 - x 0
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro a x
        simp [mul_sub] }
  let Lsum : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ x 0 + x 1
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro a x
        simp [mul_add] }
  -- Intersect the box with the two defining halfspaces.
  have hbox : Convex ℝ (prefix_unit_box (Nat.le_refl 2)) := by
    simpa [prefix_unit_box_two_eq_Icc] using (convex_Icc (0 : Fin 2 → ℝ) 1)
  have hdiffSub : Convex ℝ {x : Fin 2 → ℝ | x 1 - x 0 ≤ 0} := by
    have hpreimage : Convex ℝ (Ldiff ⁻¹' Set.Iic (0 : ℝ)) := by
      exact (convex_Iic (0 : ℝ)).linear_preimage Ldiff
    simpa [Ldiff, Set.preimage] using hpreimage
  have hdiff : Convex ℝ {x : Fin 2 → ℝ | x 1 ≤ x 0} := by
    simpa [sub_nonpos] using hdiffSub
  have hsum : Convex ℝ {x : Fin 2 → ℝ | x 0 + x 1 ≤ 1} := by
    simpa [Lsum] using (convex_Iic (1 : ℝ)).linear_preimage Lsum
  simpa [Set.inter_assoc] using
    hbox.inter (hdiff.inter hsum)

/-- A matrix presentation of the first polytope from Exercise 5.24. -/
def exercise_5_24_case_1_A : Matrix (Fin 5) (Fin 2) ℝ :=
  ![![1, 0],
    ![0, 1],
    ![-1, 0],
    ![0, -1],
    ![2, 2]]

/-- The right-hand side vector for `exercise_5_24_case_1_A`. -/
def exercise_5_24_case_1_b : Fin 5 → ℝ :=
  ![(1 : ℝ), 1, 0, 0, 3]

/-- The first polytope from Exercise 5.24, kept on the canonical Chapter 3 polyhedron owner. -/
def exercise_5_24_case_1_polytope : Set (Fin 2 → ℝ) :=
  polyhedron_le_set exercise_5_24_case_1_A exercise_5_24_case_1_b

/-- The first polytope from Exercise 5.24 is exactly
`P = {x ∈ [0, 1]^2 | 2 x₁ + 2 x₂ ≤ 3}`. -/
theorem exercise_5_24_case_1_polytope_eq_explicit :
    exercise_5_24_case_1_polytope =
      prefix_unit_box (Nat.le_refl 2) ∩ {x | 2 * x 0 + 2 * x 1 ≤ 3} := by
  ext x
  constructor
  · intro hx
    rw [exercise_5_24_case_1_polytope, mem_polyhedron_le_set_iff] at hx
    -- Read the matrix system row by row to recover the box bounds and the main inequality.
    have hx0_le : x 0 ≤ 1 := by
      simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using hx 0
    have hx1_le : x 1 ≤ 1 := by
      simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using hx 1
    have hx0_nonneg : 0 ≤ x 0 := by
      have hx2 : -x 0 ≤ 0 := by
        simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using hx 2
      linarith
    have hx1_nonneg : 0 ≤ x 1 := by
      have hx3 : -x 1 ≤ 0 := by
        simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using hx 3
      linarith
    refine ⟨(mem_prefix_unit_box_two_iff x).2 ⟨hx0_nonneg, hx0_le, hx1_nonneg, hx1_le⟩, ?_⟩
    simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using hx 4
  · rintro ⟨hxBox, hmain⟩
    rw [exercise_5_24_case_1_polytope, mem_polyhedron_le_set_iff]
    rw [mem_prefix_unit_box_two_iff] at hxBox
    rcases hxBox with ⟨hx0_nonneg, hx0_le, hx1_nonneg, hx1_le⟩
    -- Reassemble the five original inequalities from the explicit box-and-sum description.
    intro i
    fin_cases i
    · simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using hx0_le
    · simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using hx1_le
    · have : -x 0 ≤ 0 := by linarith
      simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using this
    · have : -x 1 ≤ 0 := by linarith
      simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using this
    · simpa [exercise_5_24_case_1_A, exercise_5_24_case_1_b, Matrix.mulVec, dotProduct] using hmain

/-- The computed lift-and-project closure for the first polytope, namely the unit square together
with the two inequalities `2 x₁ + x₂ ≤ 2` and `x₁ + 2 x₂ ≤ 2`. -/
def exercise_5_24_case_1_lift_project_relaxation : Set (Fin 2 → ℝ) :=
  prefix_unit_box (Nat.le_refl 2) ∩
    {x | 2 * x 0 + x 1 ≤ 2 ∧ x 0 + 2 * x 1 ≤ 2}

/-- The zero-one hull of the first polytope. -/
def exercise_5_24_case_1_zero_one_hull : Set (Fin 2 → ℝ) :=
  convexHull ℝ (zero_one_points (Nat.le_refl 2) exercise_5_24_case_1_polytope)

/-- The canonical zero-one hull of the first polytope is exactly
`[0, 1]^2 ∩ {x | x₁ + x₂ ≤ 1}`. -/
theorem exercise_5_24_case_1_zero_one_hull_eq_explicit :
    exercise_5_24_case_1_zero_one_hull =
      prefix_unit_box (Nat.le_refl 2) ∩ {x | x 0 + x 1 ≤ 1} := by
  ext x
  constructor
  · intro hx
    rw [exercise_5_24_case_1_zero_one_hull] at hx
    -- Every binary feasible point is one of the three triangle vertices.
    refine (convexHull_min ?_ exercise524Case1TriangleExplicitConvex) hx
    intro y hy
    rw [mem_zero_one_points_iff] at hy
    have hyP := hy.1
    rw [exercise_5_24_case_1_polytope_eq_explicit] at hyP
    refine ⟨hyP.1, ?_⟩
    change y 0 + y 1 ≤ 1
    have hy0 : y 0 = 0 ∨ y 0 = 1 := by simpa using hy.2 0
    have hy1 : y 1 = 0 ∨ y 1 = 1 := by simpa using hy.2 1
    rcases hy0 with hy0 | hy0 <;> rcases hy1 with hy1 | hy1
    · nlinarith [hyP.2, hy0, hy1]
    · nlinarith [hyP.2, hy0, hy1]
    · nlinarith [hyP.2, hy0, hy1]
    · exfalso
      have hnot : ¬ 2 * y 0 + 2 * y 1 ≤ 3 := by
        rw [hy0, hy1]
        norm_num
      exact hnot hyP.2
  · rintro ⟨hxBox, hsum⟩
    change x 0 + x 1 ≤ 1 at hsum
    rw [exercise_5_24_case_1_zero_one_hull]
    let w : Fin 3 → ℝ
      | 0 => 1 - x 0 - x 1
      | 1 => x 0
      | _ => x 1
    have hxBox' := (mem_prefix_unit_box_two_iff x).1 hxBox
    have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
      intro i
      fin_cases i
      · simp [w]
        nlinarith
      · simp [w]
        linarith
      · simp [w]
        linarith
    have hw_sum : ∑ i, w i = 1 := by
      simp [w, Fin.sum_univ_three]
      ring
    -- Use the standard barycentric decomposition in the triangle `{(0,0), (1,0), (0,1)}`.
    refine mem_convexHull_of_exists_fintype w
      (fun i : Fin 3 ↦
        match i with
        | 0 => ![(0 : ℝ), 0]
        | 1 => ![(1 : ℝ), 0]
        | _ => ![(0 : ℝ), 1])
      hw_nonneg hw_sum ?_ ?_
    · intro i
      fin_cases i
      · rw [mem_zero_one_points_iff, exercise_5_24_case_1_polytope_eq_explicit]
        constructor
        · refine ⟨?_, by norm_num⟩
          simp [mem_prefix_unit_box_two_iff]
        · intro j
          fin_cases j <;> simp
      · rw [mem_zero_one_points_iff, exercise_5_24_case_1_polytope_eq_explicit]
        constructor
        · refine ⟨?_, by norm_num⟩
          simp [mem_prefix_unit_box_two_iff]
        · intro j
          fin_cases j <;> simp
      · rw [mem_zero_one_points_iff, exercise_5_24_case_1_polytope_eq_explicit]
        constructor
        · refine ⟨?_, by norm_num⟩
          simp [mem_prefix_unit_box_two_iff]
        · intro j
          fin_cases j <;> simp
    · ext j
      fin_cases j
      · simp [w, Fin.sum_univ_three]
      · simp [w, Fin.sum_univ_three]

/-- A matrix presentation of the second polytope from Exercise 5.24. -/
def exercise_5_24_case_2_A : Matrix (Fin 6) (Fin 2) ℝ :=
  ![![1, 0],
    ![0, 1],
    ![-1, 0],
    ![0, -1],
    ![2, 1],
    ![-2, 1]]

/-- The right-hand side vector for `exercise_5_24_case_2_A`. -/
def exercise_5_24_case_2_b : Fin 6 → ℝ :=
  ![(1 : ℝ), 1, 0, 0, 2, 0]

/-- The second polytope from Exercise 5.24, kept on the canonical Chapter 3 polyhedron owner. -/
def exercise_5_24_case_2_polytope : Set (Fin 2 → ℝ) :=
  polyhedron_le_set exercise_5_24_case_2_A exercise_5_24_case_2_b

/-- The second polytope from Exercise 5.24 is exactly
`P = {x ∈ [0, 1]^2 | 2 x₁ + x₂ ≤ 2, x₂ ≤ 2 x₁}`. -/
theorem exercise_5_24_case_2_polytope_eq_explicit :
    exercise_5_24_case_2_polytope =
      prefix_unit_box (Nat.le_refl 2) ∩
        {x | 2 * x 0 + x 1 ≤ 2 ∧ x 1 ≤ 2 * x 0} := by
  ext x
  constructor
  · intro hx
    rw [exercise_5_24_case_2_polytope, mem_polyhedron_le_set_iff] at hx
    -- Again unpack the box rows first and keep the two structural inequalities separate.
    have hx0_le : x 0 ≤ 1 := by
      simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hx 0
    have hx1_le : x 1 ≤ 1 := by
      simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hx 1
    have hx0_nonneg : 0 ≤ x 0 := by
      have hx2 : -x 0 ≤ 0 := by
        simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hx 2
      linarith
    have hx1_nonneg : 0 ≤ x 1 := by
      have hx3 : -x 1 ≤ 0 := by
        simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hx 3
      linarith
    refine
      ⟨(mem_prefix_unit_box_two_iff x).2 ⟨hx0_nonneg, hx0_le, hx1_nonneg, hx1_le⟩, ?_⟩
    constructor
    · simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hx 4
    · have : -2 * x 0 + x 1 ≤ 0 := by
        simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hx 5
      linarith
  · rintro ⟨hxBox, hmain, hside⟩
    rw [exercise_5_24_case_2_polytope, mem_polyhedron_le_set_iff]
    rw [mem_prefix_unit_box_two_iff] at hxBox
    rcases hxBox with ⟨hx0_nonneg, hx0_le, hx1_nonneg, hx1_le⟩
    -- Convert the explicit inequalities back to the six-row matrix system.
    intro i
    fin_cases i
    · simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hx0_le
    · simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hx1_le
    · have : -x 0 ≤ 0 := by linarith
      simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using this
    · have : -x 1 ≤ 0 := by linarith
      simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using this
    · simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using hmain
    · have : -2 * x 0 + x 1 ≤ 0 := by linarith
      simpa [exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.mulVec, dotProduct] using this

/-- The zero-one hull of the second polytope. -/
def exercise_5_24_case_2_zero_one_hull : Set (Fin 2 → ℝ) :=
  convexHull ℝ (zero_one_points (Nat.le_refl 2) exercise_5_24_case_2_polytope)

/-- The canonical zero-one hull of the second polytope is exactly the segment `[0, 1] × {0}`. -/
theorem exercise_5_24_case_2_zero_one_hull_eq_explicit :
    exercise_5_24_case_2_zero_one_hull =
      prefix_unit_box (Nat.le_refl 2) ∩ {x | x 1 = 0} := by
  ext x
  constructor
  · intro hx
    rw [exercise_5_24_case_2_zero_one_hull] at hx
    -- The binary feasible points collapse to the two endpoints `(0,0)` and `(1,0)`.
    refine (convexHull_min ?_ exercise524Case2SegmentExplicitConvex) hx
    intro y hy
    rw [mem_zero_one_points_iff] at hy
    have hyP := hy.1
    rw [exercise_5_24_case_2_polytope_eq_explicit] at hyP
    refine ⟨hyP.1, ?_⟩
    change y 1 = 0
    have hy0 : y 0 = 0 ∨ y 0 = 1 := by simpa using hy.2 0
    have hy1 : y 1 = 0 ∨ y 1 = 1 := by simpa using hy.2 1
    rcases hy0 with hy0 | hy0 <;> rcases hy1 with hy1 | hy1
    · exact hy1
    · exfalso
      nlinarith [hyP.2.2, hy0, hy1]
    · exact hy1
    · exfalso
      nlinarith [hyP.2.1, hy0, hy1]
  · rintro ⟨hxBox, hx1_zero⟩
    change x 1 = 0 at hx1_zero
    rw [exercise_5_24_case_2_zero_one_hull]
    let w : Fin 2 → ℝ
      | 0 => 1 - x 0
      | _ => x 0
    have hxBox' := (mem_prefix_unit_box_two_iff x).1 hxBox
    have hw_nonneg : ∀ i : Fin 2, 0 ≤ w i := by
      intro i
      fin_cases i
      · simp [w]
        linarith
      · simp [w]
        linarith
    have hw_sum : ∑ i, w i = 1 := by
      simp [w, Fin.sum_univ_two]
    -- Parametrize the horizontal segment by the coordinate `x 0`.
    refine mem_convexHull_of_exists_fintype w
      (fun i : Fin 2 ↦
        match i with
        | 0 => ![(0 : ℝ), 0]
        | _ => ![(1 : ℝ), 0])
      hw_nonneg hw_sum ?_ ?_
    · intro i
      fin_cases i
      · rw [mem_zero_one_points_iff, exercise_5_24_case_2_polytope_eq_explicit]
        constructor
        · refine ⟨?_, ?_⟩
          · simp [mem_prefix_unit_box_two_iff]
          · constructor <;> norm_num
        · intro j
          fin_cases j <;> simp
      · rw [mem_zero_one_points_iff, exercise_5_24_case_2_polytope_eq_explicit]
        constructor
        · refine ⟨?_, ?_⟩
          · simp [mem_prefix_unit_box_two_iff]
          · constructor <;> norm_num
        · intro j
          fin_cases j <;> simp
    · ext j
      fin_cases j
      · simp [w, Fin.sum_univ_two]
      · simp [w, hx1_zero, Fin.sum_univ_two]

/-- The computed Chvátal closure for the second polytope, namely the unit square together with
the Chvátal cuts `x₂ ≤ x₁` and `x₁ + x₂ ≤ 1`. -/
def exercise_5_24_case_2_chvatal_relaxation : Set (Fin 2 → ℝ) :=
  prefix_unit_box (Nat.le_refl 2) ∩ {x | x 1 ≤ x 0 ∧ x 0 + x 1 ≤ 1}

/-- Helper for Exercise 5.24: the coordinate hull obtained by splitting on `x₁`
is exactly the box together with the cut `x₁ + 2 x₂ ≤ 2`. -/
theorem exercise524Case1FirstCoordinateHullEq :
    coordinate_lift_project_hull exercise_5_24_case_1_polytope 0 =
      prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | x 0 + 2 * x 1 ≤ 2} := by
  ext x
  constructor
  · intro hx
    rw [coordinate_lift_project_hull_def] at hx
    let L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y ↦ y 0 + 2 * y 1
        map_add' := by
          intro y z
          simp
          ring
        map_smul' := by
          intro a y
          simp
          ring }
    -- Keep the box and the lifted split inequality as separate convex constraints.
    have htarget_convex :
        Convex ℝ (prefix_unit_box (Nat.le_refl 2) ∩ {y : Fin 2 → ℝ | y 0 + 2 * y 1 ≤ 2}) := by
      have hbox : Convex ℝ (prefix_unit_box (Nat.le_refl 2)) := by
        simpa [prefix_unit_box_two_eq_Icc] using (convex_Icc (0 : Fin 2 → ℝ) 1)
      have hineq : Convex ℝ {y : Fin 2 → ℝ | y 0 + 2 * y 1 ≤ 2} := by
        simpa [L] using (convex_Iic (2 : ℝ)).linear_preimage L
      exact hbox.inter hineq
    -- Every generator lies either on the `x₁ = 0` slice or on the `x₁ = 1` slice, and both
    -- slices satisfy the explicit inequality.
    refine (convexHull_min ?_ htarget_convex) hx
    intro y hy
    rcases hy with ⟨hyP, hy0⟩ | ⟨hyP, hy0⟩
    · rw [exercise_5_24_case_1_polytope_eq_explicit] at hyP
      refine ⟨hyP.1, ?_⟩
      change y 0 + 2 * y 1 ≤ 2
      have hyBox := (mem_prefix_unit_box_two_iff y).1 hyP.1
      have hy0_zero : y 0 = 0 := hy0
      nlinarith [hyBox.2.2]
    · rw [exercise_5_24_case_1_polytope_eq_explicit] at hyP
      refine ⟨hyP.1, ?_⟩
      change y 0 + 2 * y 1 ≤ 2
      have hy0_one : y 0 = 1 := hy0
      have hyMain : 2 + 2 * y 1 ≤ 3 := by
        simpa [hy0_one] using hyP.2
      have hyBound : 1 + 2 * y 1 ≤ 2 := by
        linarith
      simpa [hy0_one] using hyBound
  · rintro ⟨hxBox, hineq⟩
    change x 0 + 2 * x 1 ≤ 2 at hineq
    rw [coordinate_lift_project_hull_def]
    have hxBox' := (mem_prefix_unit_box_two_iff x).1 hxBox
    by_cases hlower : x 0 + x 1 ≤ 1
    · let w : Fin 3 → ℝ
        | 0 => 1 - x 0 - x 1
        | 1 => x 0
        | _ => x 1
      have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
        intro i
        fin_cases i
        · simp [w]
          nlinarith [hlower]
        · simp [w]
          linarith
        · simp [w]
          linarith
      have hw_sum : ∑ i, w i = 1 := by
        simp [w, Fin.sum_univ_three]
        ring
      -- Route correction: use the lower triangle `conv{(0,0),(1,0),(0,1)}` instead of trying to
      -- normalize the whole quadrilateral at once.
      refine mem_convexHull_of_exists_fintype w
        (fun i : Fin 3 ↦
          match i with
          | 0 => ![(0 : ℝ), 0]
          | 1 => ![(1 : ℝ), 0]
          | _ => ![(0 : ℝ), 1])
        hw_nonneg hw_sum ?_ ?_
      · intro i
        fin_cases i
        · exact Or.inl <| by
            have hbox : ![(0 : ℝ), 0] ∈ prefix_unit_box (Nat.le_refl 2) := by
              rw [mem_prefix_unit_box_two_iff]
              norm_num
            have hmain : 2 * (![(0 : ℝ), 0] 0) + 2 * (![(0 : ℝ), 0] 1) ≤ 3 := by
              norm_num
            have hvertex :
                ![(0 : ℝ), 0] ∈
                  prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | 2 * x 0 + 2 * x 1 ≤ 3} :=
              ⟨hbox, hmain⟩
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            simpa using hvertex
        · exact Or.inr <| by
            have hbox : ![(1 : ℝ), 0] ∈ prefix_unit_box (Nat.le_refl 2) := by
              rw [mem_prefix_unit_box_two_iff]
              norm_num
            have hmain : 2 * (![(1 : ℝ), 0] 0) + 2 * (![(1 : ℝ), 0] 1) ≤ 3 := by
              norm_num
            have hvertex :
                ![(1 : ℝ), 0] ∈
                  prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | 2 * x 0 + 2 * x 1 ≤ 3} :=
              ⟨hbox, hmain⟩
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            simpa using hvertex
        · exact Or.inl <| by
            have hbox : ![(0 : ℝ), 1] ∈ prefix_unit_box (Nat.le_refl 2) := by
              rw [mem_prefix_unit_box_two_iff]
              norm_num
            have hmain : 2 * (![(0 : ℝ), 1] 0) + 2 * (![(0 : ℝ), 1] 1) ≤ 3 := by
              norm_num
            have hvertex :
                ![(0 : ℝ), 1] ∈
                  prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | 2 * x 0 + 2 * x 1 ≤ 3} :=
              ⟨hbox, hmain⟩
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            simpa using hvertex
      · ext j
        fin_cases j
        · simp [w, Fin.sum_univ_three]
        · simp [w, Fin.sum_univ_three]
    · have hupper : 1 ≤ x 0 + x 1 := by linarith
      let w : Fin 3 → ℝ
        | 0 => 2 - x 0 - 2 * x 1
        | 1 => 2 * (x 0 + x 1 - 1)
        | _ => 1 - x 0
      have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
        intro i
        fin_cases i
        · simp [w]
          nlinarith [hineq]
        · simp [w]
          linarith
        · simp [w]
          linarith
      have hw_sum : ∑ i, w i = 1 := by
        simp [w, Fin.sum_univ_three]
        ring
      -- The upper region is the triangle `conv{(1,0),(1,1/2),(0,1)}`.
      refine mem_convexHull_of_exists_fintype w
        (fun i : Fin 3 ↦
          match i with
          | 0 => ![(1 : ℝ), 0]
          | 1 => ![(1 : ℝ), (1 / 2 : ℝ)]
          | _ => ![(0 : ℝ), 1])
        hw_nonneg hw_sum ?_ ?_
      · intro i
        fin_cases i
        · exact Or.inr <| by
            have hbox : ![(1 : ℝ), 0] ∈ prefix_unit_box (Nat.le_refl 2) := by
              rw [mem_prefix_unit_box_two_iff]
              norm_num
            have hmain : 2 * (![(1 : ℝ), 0] 0) + 2 * (![(1 : ℝ), 0] 1) ≤ 3 := by
              norm_num
            have hvertex :
                ![(1 : ℝ), 0] ∈
                  prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | 2 * x 0 + 2 * x 1 ≤ 3} :=
              ⟨hbox, hmain⟩
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            simpa using hvertex
        · exact Or.inr <| by
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            norm_num [mem_prefix_unit_box_two_iff]
        · exact Or.inl <| by
            have hbox : ![(0 : ℝ), 1] ∈ prefix_unit_box (Nat.le_refl 2) := by
              rw [mem_prefix_unit_box_two_iff]
              norm_num
            have hmain : 2 * (![(0 : ℝ), 1] 0) + 2 * (![(0 : ℝ), 1] 1) ≤ 3 := by
              norm_num
            have hvertex :
                ![(0 : ℝ), 1] ∈
                  prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | 2 * x 0 + 2 * x 1 ≤ 3} :=
              ⟨hbox, hmain⟩
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            simpa using hvertex
      · ext j
        fin_cases j
        · simp [w, Fin.sum_univ_three]
          ring
        · simp [w, Fin.sum_univ_three]
          ring

/-- Helper for Exercise 5.24: the coordinate hull obtained by splitting on `x₂`
is exactly the box together with the cut `2 x₁ + x₂ ≤ 2`. -/
theorem exercise524Case1SecondCoordinateHullEq :
    coordinate_lift_project_hull exercise_5_24_case_1_polytope 1 =
      prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | 2 * x 0 + x 1 ≤ 2} := by
  ext x
  constructor
  · intro hx
    rw [coordinate_lift_project_hull_def] at hx
    let L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y ↦ 2 * y 0 + y 1
        map_add' := by
          intro y z
          simp
          ring
        map_smul' := by
          intro a y
          simp
          ring }
    -- Keep the box and the lifted split inequality as separate convex constraints.
    have htarget_convex :
        Convex ℝ (prefix_unit_box (Nat.le_refl 2) ∩ {y : Fin 2 → ℝ | 2 * y 0 + y 1 ≤ 2}) := by
      have hbox : Convex ℝ (prefix_unit_box (Nat.le_refl 2)) := by
        simpa [prefix_unit_box_two_eq_Icc] using (convex_Icc (0 : Fin 2 → ℝ) 1)
      have hineq : Convex ℝ {y : Fin 2 → ℝ | 2 * y 0 + y 1 ≤ 2} := by
        simpa [L] using (convex_Iic (2 : ℝ)).linear_preimage L
      exact hbox.inter hineq
    -- Every generator lies either on the `x₂ = 0` slice or on the `x₂ = 1` slice, and both
    -- slices satisfy the explicit inequality.
    refine (convexHull_min ?_ htarget_convex) hx
    intro y hy
    rcases hy with ⟨hyP, hy1⟩ | ⟨hyP, hy1⟩
    · rw [exercise_5_24_case_1_polytope_eq_explicit] at hyP
      refine ⟨hyP.1, ?_⟩
      change 2 * y 0 + y 1 ≤ 2
      have hyBox := (mem_prefix_unit_box_two_iff y).1 hyP.1
      have hy1_zero : y 1 = 0 := hy1
      nlinarith [hyBox.2.1]
    · rw [exercise_5_24_case_1_polytope_eq_explicit] at hyP
      refine ⟨hyP.1, ?_⟩
      change 2 * y 0 + y 1 ≤ 2
      have hy1_one : y 1 = 1 := hy1
      have hyMain : 2 * y 0 + 2 ≤ 3 := by
        simpa [hy1_one] using hyP.2
      have hyBound : 2 * y 0 + 1 ≤ 2 := by
        linarith
      simpa [hy1_one] using hyBound
  · rintro ⟨hxBox, hineq⟩
    change 2 * x 0 + x 1 ≤ 2 at hineq
    rw [coordinate_lift_project_hull_def]
    have hxBox' := (mem_prefix_unit_box_two_iff x).1 hxBox
    by_cases hlower : x 0 + x 1 ≤ 1
    · let w : Fin 3 → ℝ
        | 0 => 1 - x 0 - x 1
        | 1 => x 0
        | _ => x 1
      have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
        intro i
        fin_cases i
        · simp [w]
          nlinarith [hlower]
        · simp [w]
          linarith
        · simp [w]
          linarith
      have hw_sum : ∑ i, w i = 1 := by
        simp [w, Fin.sum_univ_three]
        ring
      -- The lower triangle is again `conv{(0,0),(1,0),(0,1)}`.
      refine mem_convexHull_of_exists_fintype w
        (fun i : Fin 3 ↦
          match i with
          | 0 => ![(0 : ℝ), 0]
          | 1 => ![(1 : ℝ), 0]
          | _ => ![(0 : ℝ), 1])
        hw_nonneg hw_sum ?_ ?_
      · intro i
        fin_cases i
        · exact Or.inl <| by
            have hbox : ![(0 : ℝ), 0] ∈ prefix_unit_box (Nat.le_refl 2) := by
              rw [mem_prefix_unit_box_two_iff]
              norm_num
            have hmain : 2 * (![(0 : ℝ), 0] 0) + 2 * (![(0 : ℝ), 0] 1) ≤ 3 := by
              norm_num
            have hvertex :
                ![(0 : ℝ), 0] ∈
                  prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | 2 * x 0 + 2 * x 1 ≤ 3} :=
              ⟨hbox, hmain⟩
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            simpa using hvertex
        · exact Or.inl <| by
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            norm_num [mem_prefix_unit_box_two_iff]
        · exact Or.inr <| by
            have hbox : ![(0 : ℝ), 1] ∈ prefix_unit_box (Nat.le_refl 2) := by
              rw [mem_prefix_unit_box_two_iff]
              norm_num
            have hmain : 2 * (![(0 : ℝ), 1] 0) + 2 * (![(0 : ℝ), 1] 1) ≤ 3 := by
              norm_num
            have hvertex :
                ![(0 : ℝ), 1] ∈
                  prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | 2 * x 0 + 2 * x 1 ≤ 3} :=
              ⟨hbox, hmain⟩
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            simpa using hvertex
      · ext j
        fin_cases j
        · simp [w, Fin.sum_univ_three]
        · simp [w, Fin.sum_univ_three]
    · have hupper : 1 ≤ x 0 + x 1 := by linarith
      let w : Fin 3 → ℝ
        | 0 => 1 - x 1
        | 1 => 2 * (x 0 + x 1 - 1)
        | _ => 2 - 2 * x 0 - x 1
      have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
        intro i
        fin_cases i
        · simp [w]
          nlinarith [hineq]
        · simp [w]
          linarith
        · simp [w]
          linarith
      have hw_sum : ∑ i, w i = 1 := by
        simp [w, Fin.sum_univ_three]
        ring
      -- The upper region is the triangle `conv{(1,0),(1/2,1),(0,1)}`.
      refine mem_convexHull_of_exists_fintype w
        (fun i : Fin 3 ↦
          match i with
          | 0 => ![(1 : ℝ), 0]
          | 1 => ![((1 / 2 : ℝ)), (1 : ℝ)]
          | _ => ![(0 : ℝ), 1])
        hw_nonneg hw_sum ?_ ?_
      · intro i
        fin_cases i
        · exact Or.inl <| by
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            norm_num [mem_prefix_unit_box_two_iff]
        · exact Or.inr <| by
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            norm_num [mem_prefix_unit_box_two_iff]
        · exact Or.inr <| by
            rw [exercise_5_24_case_1_polytope_eq_explicit]
            norm_num [mem_prefix_unit_box_two_iff]
      · ext j
        fin_cases j
        · simp [w, Fin.sum_univ_three]
          ring
        · simp [w, Fin.sum_univ_three]
          ring

/-- Helper for Exercise 5.24: the midpoint `(1/2, 1/2)` satisfies every rounded valid integer
inequality of the second polytope. -/
theorem exercise524Case2MidpointMemPureIntegerChvatalClosure :
    ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))] ∈
      pure_integer_chvatal_closure exercise_5_24_case_2_polytope := by
  rw [mem_pure_integer_chvatal_closure_iff]
  have hmidP : ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))] ∈ exercise_5_24_case_2_polytope := by
    rw [exercise_5_24_case_2_polytope_eq_explicit]
    constructor
    · rw [mem_prefix_unit_box_two_iff]
      norm_num
    · constructor <;> norm_num
  refine ⟨hmidP, ?_⟩
  intro c d hvalid
  have h00 : (0 : ℝ) ≤ d := by
    have h :=
      hvalid (x := ![(0 : ℝ), 0]) (by
        rw [exercise_5_24_case_2_polytope_eq_explicit]
        constructor
        · rw [mem_prefix_unit_box_two_iff]
          norm_num
        · constructor <;> norm_num)
    simp [dotProduct] at h
    simpa using h
  have h10 : (c 0 : ℝ) ≤ d := by
    have h :=
      hvalid (x := ![(1 : ℝ), 0]) (by
        rw [exercise_5_24_case_2_polytope_eq_explicit]
        constructor
        · rw [mem_prefix_unit_box_two_iff]
          norm_num
        · constructor <;> norm_num)
    simp [dotProduct] at h
    simpa using h
  have hhalfOne : (c 0 : ℝ) / 2 + (c 1 : ℝ) ≤ d := by
    have h :=
      hvalid (x := ![((1 / 2 : ℝ)), (1 : ℝ)]) (by
        rw [exercise_5_24_case_2_polytope_eq_explicit]
        constructor
        · rw [mem_prefix_unit_box_two_iff]
          norm_num
        · constructor <;> norm_num)
    simp [dotProduct] at h
    simpa using h
  let s : ℤ := c 0 + c 1
  have hmid_expr :
      (fun i ↦ (c i : ℝ)) ⬝ᵥ ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))] = ((s : ℤ) : ℝ) / 2 := by
    simp [s, dotProduct]
    ring
  by_cases hs_nonpos : s ≤ 0
  · have hfloor_nonneg : (0 : ℝ) ≤ ((Int.floor d : ℤ) : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr h00
    have hs_nonposR : ((s : ℤ) : ℝ) / 2 ≤ 0 := by
      have hsR : ((s : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hs_nonpos
      nlinarith
    -- Negative or zero midpoint values are controlled by the trivial valid bound at `(0,0)`.
    calc
      (fun i ↦ (c i : ℝ)) ⬝ᵥ ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))]
          = ((s : ℤ) : ℝ) / 2 := hmid_expr
      _ ≤ ((Int.floor d : ℤ) : ℝ) := le_trans hs_nonposR hfloor_nonneg
  · have hs_pos : 0 < s := by omega
    rcases Int.even_or_odd s with hs_even | hs_odd
    · rcases hs_even with ⟨k, hk⟩
      by_cases hcmp : c 1 ≤ c 0
      · have hk_le_c0 : k ≤ c 0 := by
          omega
        have hk_le_d : (k : ℝ) ≤ d := by
          have hk_le_c0R : (k : ℝ) ≤ (c 0 : ℝ) := by exact_mod_cast hk_le_c0
          linarith
        have hk_le_floor : (k : ℝ) ≤ ((Int.floor d : ℤ) : ℝ) := by
          exact_mod_cast (Int.le_floor.mpr hk_le_d)
        -- In the even-sum branch, the midpoint value is the integer `k`.
        calc
          (fun i ↦ (c i : ℝ)) ⬝ᵥ ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))]
              = (k : ℝ) := by
                  rw [hmid_expr]
                  have hkR : ((s : ℤ) : ℝ) = (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
                  nlinarith
          _ ≤ ((Int.floor d : ℤ) : ℝ) := hk_le_floor
      · have hcmp' : c 0 < c 1 := by omega
        have hk_le_d : (k : ℝ) ≤ d := by
          have hint : (2 : ℝ) * (((k + 1 : ℤ) : ℝ)) ≤ (c 0 : ℝ) + 2 * (c 1 : ℝ) := by
            exact_mod_cast (show (2 : ℤ) * (k + 1) ≤ c 0 + 2 * c 1 by omega)
          have hk1_le_halfOne : (((k + 1 : ℤ) : ℝ)) ≤ (c 0 : ℝ) / 2 + (c 1 : ℝ) := by
            nlinarith
          have hk1_le_d : (((k + 1 : ℤ) : ℝ)) ≤ d := by
            nlinarith [hk1_le_halfOne, hhalfOne]
          have hk1_le_d' : (k : ℝ) + 1 ≤ d := by simpa using hk1_le_d
          nlinarith
        have hk_le_floor : (k : ℝ) ≤ ((Int.floor d : ℤ) : ℝ) := by
          exact_mod_cast (Int.le_floor.mpr hk_le_d)
        -- The upper slanted facet gives enough margin when the second coefficient dominates.
        calc
          (fun i ↦ (c i : ℝ)) ⬝ᵥ ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))]
              = (k : ℝ) := by
                  rw [hmid_expr]
                  have hkR : ((s : ℤ) : ℝ) = (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
                  nlinarith
          _ ≤ ((Int.floor d : ℤ) : ℝ) := hk_le_floor
    · rcases hs_odd with ⟨k, hk⟩
      by_cases hc1_nonpos : c 1 ≤ 0
      · have hk1_le_c0 : k + 1 ≤ c 0 := by
          omega
        have hk1_le_d : ((k + 1 : ℤ) : ℝ) ≤ d := by
          have hk1_le_c0R : (((k + 1 : ℤ) : ℝ)) ≤ (c 0 : ℝ) := by
            exact_mod_cast hk1_le_c0
          linarith
        have hk1_le_floor : (((k + 1 : ℤ) : ℝ)) ≤ ((Int.floor d : ℤ) : ℝ) := by
          exact_mod_cast (Int.le_floor.mpr hk1_le_d)
        -- When `c₂ ≤ 0`, the bound at `(1,0)` is at least a half-unit above the midpoint value.
        have hmid_le : ((s : ℤ) : ℝ) / 2 ≤ (((k + 1 : ℤ) : ℝ) : ℝ) := by
          have hmid_eq : ((s : ℤ) : ℝ) / 2 = (k : ℝ) + (1 / 2 : ℝ) := by
            have hkR : ((s : ℤ) : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
            nlinarith
          rw [hmid_eq]
          norm_num
        calc
          (fun i ↦ (c i : ℝ)) ⬝ᵥ ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))]
              = ((s : ℤ) : ℝ) / 2 := hmid_expr
          _ ≤ ((Int.floor d : ℤ) : ℝ) := le_trans hmid_le hk1_le_floor
      · have hc1_pos : 0 < c 1 := by omega
        have hk1_le_d : ((k + 1 : ℤ) : ℝ) ≤ d := by
          have hint : (2 : ℝ) * (((k + 1 : ℤ) : ℝ)) ≤ (c 0 : ℝ) + 2 * (c 1 : ℝ) := by
            exact_mod_cast (show (2 : ℤ) * (k + 1) ≤ c 0 + 2 * c 1 by omega)
          have hk1_le_halfOne : (((k + 1 : ℤ) : ℝ)) ≤ (c 0 : ℝ) / 2 + (c 1 : ℝ) := by
            nlinarith
          nlinarith [hk1_le_halfOne, hhalfOne]
        have hk1_le_floor : (((k + 1 : ℤ) : ℝ)) ≤ ((Int.floor d : ℤ) : ℝ) := by
          exact_mod_cast (Int.le_floor.mpr hk1_le_d)
        -- When `c₂ > 0`, the bound at `(1/2,1)` supplies the missing half-unit.
        have hmid_le : ((s : ℤ) : ℝ) / 2 ≤ (((k + 1 : ℤ) : ℝ) : ℝ) := by
          have hmid_eq : ((s : ℤ) : ℝ) / 2 = (k : ℝ) + (1 / 2 : ℝ) := by
            have hkR : ((s : ℤ) : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
            nlinarith
          rw [hmid_eq]
          norm_num
        calc
          (fun i ↦ (c i : ℝ)) ⬝ᵥ ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))]
              = ((s : ℤ) : ℝ) / 2 := hmid_expr
          _ ≤ ((Int.floor d : ℤ) : ℝ) := le_trans hmid_le hk1_le_floor

/-- Exercise 5.24 (1). For `P = {x ∈ [0, 1]^2 | 2 x₁ + 2 x₂ ≤ 3}`, the lift-and-project
closure is exactly `[0, 1]^2 ∩ {x | 2 x₁ + x₂ ≤ 2, x₁ + 2 x₂ ≤ 2}`. -/
theorem exercise_5_24_case_1_lift_project_closure_eq_relaxation :
    lift_project_closure exercise_5_24_case_1_polytope Finset.univ =
      exercise_5_24_case_1_lift_project_relaxation := by
  ext x
  constructor
  · intro hx
    rw [mem_lift_project_closure_iff] at hx
    have hx0 :
        x ∈ prefix_unit_box (Nat.le_refl 2) ∩ {y : Fin 2 → ℝ | y 0 + 2 * y 1 ≤ 2} := by
      simpa [exercise524Case1FirstCoordinateHullEq] using hx 0 (by simp)
    have hx1 :
        x ∈ prefix_unit_box (Nat.le_refl 2) ∩ {y : Fin 2 → ℝ | 2 * y 0 + y 1 ≤ 2} := by
      simpa [exercise524Case1SecondCoordinateHullEq] using hx 1 (by simp)
    -- Intersect the two coordinate hull descriptions to recover the claimed relaxation.
    exact ⟨hx0.1, hx1.2, hx0.2⟩
  · rintro ⟨hxBox, hcut10, hcut01⟩
    rw [mem_lift_project_closure_iff]
    intro j hj
    fin_cases j
    · -- The first coordinate hull is the box together with `x₁ + 2 x₂ ≤ 2`.
      simpa [exercise524Case1FirstCoordinateHullEq] using
        (show x ∈ prefix_unit_box (Nat.le_refl 2) ∩ {y : Fin 2 → ℝ | y 0 + 2 * y 1 ≤ 2} from
          ⟨hxBox, hcut01⟩)
    · -- The second coordinate hull is the box together with `2 x₁ + x₂ ≤ 2`.
      simpa [exercise524Case1SecondCoordinateHullEq] using
        (show x ∈ prefix_unit_box (Nat.le_refl 2) ∩ {y : Fin 2 → ℝ | 2 * y 0 + y 1 ≤ 2} from
          ⟨hxBox, hcut10⟩)

/-- Exercise 5.24 (2). For `P = {x ∈ [0, 1]^2 | 2 x₁ + 2 x₂ ≤ 3}`, the Chvátal closure is the
zero-one hull `conv (zero_one_points (Nat.le_refl 2) P)`, equivalently
`[0, 1]^2 ∩ {x | x₁ + x₂ ≤ 1}`. -/
theorem exercise_5_24_case_1_chvatal_closure_eq_zero_one_hull :
    pure_integer_chvatal_closure exercise_5_24_case_1_polytope =
      exercise_5_24_case_1_zero_one_hull := by
  ext x
  constructor
  · intro hx
    rw [exercise_5_24_case_1_zero_one_hull_eq_explicit]
    rw [mem_pure_integer_chvatal_closure_iff] at hx
    have hxP : x ∈ exercise_5_24_case_1_polytope := hx.1
    rw [exercise_5_24_case_1_polytope_eq_explicit] at hxP
    -- Use the rounded valid inequality `(1,1) x ≤ floor(3/2)`.
    have hcut : x 0 + x 1 ≤ 1 := by
      have hvalid : is_valid_inequality exercise_5_24_case_1_polytope
          (fun _ : Fin 2 ↦ ((1 : ℤ) : ℝ)) (3 / 2 : ℝ) := by
        intro y hy
        rw [exercise_5_24_case_1_polytope_eq_explicit] at hy
        have hySum : y 0 + y 1 ≤ (3 / 2 : ℝ) := by
          have hyMain : 2 * y 0 + 2 * y 1 ≤ 3 := hy.2
          nlinarith [hyMain]
        simpa [dotProduct] using hySum
      have hxCut := hx.2 (fun _ : Fin 2 ↦ (1 : ℤ)) (3 / 2 : ℝ) hvalid
      norm_num at hxCut
      simpa [dotProduct] using hxCut
    exact ⟨hxP.1, hcut⟩
  · intro hx
    rw [exercise_5_24_case_1_zero_one_hull_eq_explicit] at hx
    rcases hx with ⟨hxBox, hsum⟩
    change x 0 + x 1 ≤ 1 at hsum
    rw [mem_pure_integer_chvatal_closure_iff]
    have hxP : x ∈ exercise_5_24_case_1_polytope := by
      rw [exercise_5_24_case_1_polytope_eq_explicit]
      refine ⟨hxBox, ?_⟩
      have hxMain : 2 * x 0 + 2 * x 1 ≤ 3 := by
        nlinarith [hsum]
      exact hxMain
    refine ⟨hxP, ?_⟩
    intro c d hvalid
    let w : Fin 3 → ℝ
      | 0 => 1 - x 0 - x 1
      | 1 => x 0
      | _ => x 1
    have hxBox := (mem_prefix_unit_box_two_iff x).1 hxBox
    have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
      intro i
      fin_cases i
      · simp [w]
        nlinarith [hsum]
      · simp [w]
        linarith
      · simp [w]
        linarith
    have hw_sum : ∑ i, w i = 1 := by
      simp [w, Fin.sum_univ_three]
      ring
    have h00 : (0 : ℝ) ≤ d := by
      have h :=
        hvalid (x := ![(0 : ℝ), 0]) (by
          rw [exercise_5_24_case_1_polytope_eq_explicit]
          refine ⟨?_, ?_⟩
          · simp [mem_prefix_unit_box_two_iff]
          · norm_num)
      simpa [dotProduct] using h
    have h10 : (c 0 : ℝ) ≤ d := by
      have h :=
        hvalid (x := ![(1 : ℝ), 0]) (by
          rw [exercise_5_24_case_1_polytope_eq_explicit]
          refine ⟨?_, ?_⟩
          · simp [mem_prefix_unit_box_two_iff]
          · norm_num)
      simpa [dotProduct] using h
    have h01 : (c 1 : ℝ) ≤ d := by
      have h :=
        hvalid (x := ![(0 : ℝ), 1]) (by
          rw [exercise_5_24_case_1_polytope_eq_explicit]
          refine ⟨?_, ?_⟩
          · simp [mem_prefix_unit_box_two_iff]
          · norm_num)
      simpa [dotProduct] using h
    have h00_floor : (0 : ℝ) ≤ ((Int.floor d : ℤ) : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr h00
    have h10_floor : (c 0 : ℝ) ≤ ((Int.floor d : ℤ) : ℝ) := by
      exact_mod_cast (Int.le_floor.mpr h10)
    have h01_floor : (c 1 : ℝ) ≤ ((Int.floor d : ℤ) : ℝ) := by
      exact_mod_cast (Int.le_floor.mpr h01)
    -- Evaluate the cut on the barycentric decomposition by the three integer vertices.
    calc
      (fun i ↦ (c i : ℝ)) ⬝ᵥ x
          = w 0 * 0 + w 1 * (c 0 : ℝ) + w 2 * (c 1 : ℝ) := by
              simp [w, dotProduct, Fin.sum_univ_two]
              ring
      _ ≤ w 0 * (((Int.floor d : ℤ) : ℝ)) +
            w 1 * (((Int.floor d : ℤ) : ℝ)) +
            w 2 * (((Int.floor d : ℤ) : ℝ)) := by
              nlinarith [hw_nonneg 0, hw_nonneg 1, hw_nonneg 2,
                h00_floor, h10_floor, h01_floor]
      _ = ((Int.floor d : ℤ) : ℝ) := by
            have hw012 : w 0 + w 1 + w 2 = 1 := by
              simpa [Fin.sum_univ_three] using hw_sum
            nlinarith

/-- Exercise 5.24 (3). In the first polytope, the Chvátal closure is the tighter relaxation:
it is a strict subset of the lift-and-project closure. -/
theorem exercise_5_24_case_1_chvatal_closure_tighter :
    pure_integer_chvatal_closure exercise_5_24_case_1_polytope ⊂
      lift_project_closure exercise_5_24_case_1_polytope Finset.univ := by
  rw [exercise_5_24_case_1_chvatal_closure_eq_zero_one_hull,
    exercise_5_24_case_1_zero_one_hull_eq_explicit,
    exercise_5_24_case_1_lift_project_closure_eq_relaxation]
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · rintro x ⟨hxBox, hsum⟩
    change x 0 + x 1 ≤ 1 at hsum
    -- The Chvátal cut `x₁ + x₂ ≤ 1` implies both lift-and-project inequalities.
    have hxBox' := (mem_prefix_unit_box_two_iff x).1 hxBox
    refine ⟨hxBox, ?_, ?_⟩ <;> nlinarith [hsum, hxBox'.2.1, hxBox'.2.2]
  · intro hEq
    have hwitness_mem :
        ![((2 / 3 : ℝ)), ((2 / 3 : ℝ))] ∈ exercise_5_24_case_1_lift_project_relaxation := by
      refine ⟨?_, ?_, ?_⟩
      · norm_num [mem_prefix_unit_box_two_iff]
      · norm_num
      · norm_num
    have hwitness_zero_one :
        ![((2 / 3 : ℝ)), ((2 / 3 : ℝ))] ∈
          prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | x 0 + x 1 ≤ 1} := by
      simpa [hEq] using hwitness_mem
    have hwitness_sum : ![((2 / 3 : ℝ)), ((2 / 3 : ℝ))] 0 +
        ![((2 / 3 : ℝ)), ((2 / 3 : ℝ))] 1 ≤ 1 := hwitness_zero_one.2
    norm_num at hwitness_sum

/-- Exercise 5.24 (4). For
`P = {x ∈ [0, 1]^2 | 2 x₁ + x₂ ≤ 2, x₂ ≤ 2 x₁}`, the lift-and-project closure is the zero-one
hull `conv (zero_one_points (Nat.le_refl 2) P)`, equivalently `[0, 1] × {0}`. -/
theorem exercise_5_24_case_2_lift_project_closure_eq_zero_one_hull :
    lift_project_closure exercise_5_24_case_2_polytope Finset.univ =
      exercise_5_24_case_2_zero_one_hull := by
  rw [exercise_5_24_case_2_zero_one_hull_eq_explicit]
  ext x
  constructor
  · intro hx
    rw [mem_lift_project_closure_iff] at hx
    have hx0 : x ∈ coordinate_lift_project_hull exercise_5_24_case_2_polytope 0 := hx 0 (by simp)
    rw [coordinate_lift_project_hull_def] at hx0
    -- The `x 0 = 0` and `x 0 = 1` slices both force `x 1 = 0`.
    refine (convexHull_min ?_ exercise524Case2SegmentExplicitConvex) hx0
    intro y hy
    rcases hy with ⟨hyP, hy0⟩ | ⟨hyP, hy0⟩
    · rw [exercise_5_24_case_2_polytope_eq_explicit] at hyP
      refine ⟨hyP.1, ?_⟩
      have hy1_zero : y 1 = 0 := by
        have hy0_zero : y 0 = 0 := hy0
        have hyBox := (mem_prefix_unit_box_two_iff y).1 hyP.1
        have hySide : y 1 ≤ 2 * y 0 := by simpa using hyP.2.2
        nlinarith [hySide, hy0_zero, hyBox.2.1]
      exact hy1_zero
    · rw [exercise_5_24_case_2_polytope_eq_explicit] at hyP
      refine ⟨hyP.1, ?_⟩
      have hy1_zero : y 1 = 0 := by
        have hy0_one : y 0 = 1 := hy0
        have hyBox := (mem_prefix_unit_box_two_iff y).1 hyP.1
        have hyMain : 2 * y 0 + y 1 ≤ 2 := by simpa using hyP.2.1
        nlinarith [hyMain, hy0_one, hyBox.2.1]
      exact hy1_zero
  · rintro ⟨hxBox, hx1_zero⟩
    change x 1 = 0 at hx1_zero
    have hxBox' := (mem_prefix_unit_box_two_iff x).1 hxBox
    have hxP : x ∈ exercise_5_24_case_2_polytope := by
      rw [exercise_5_24_case_2_polytope_eq_explicit]
      refine ⟨hxBox, ?_⟩
      constructor
      · nlinarith [hxBox'.2.1]
      · nlinarith [hxBox'.1]
    rw [mem_lift_project_closure_iff]
    intro j hj
    fin_cases j
    · rw [coordinate_lift_project_hull_def]
      let w : Fin 2 → ℝ
        | 0 => 1 - x 0
        | _ => x 0
      have hw_nonneg : ∀ i : Fin 2, 0 ≤ w i := by
        intro i
        fin_cases i
        · simp [w]
          linarith
        · simp [w]
          linarith
      have hw_sum : ∑ i, w i = 1 := by
        simp [w, Fin.sum_univ_two]
      -- Reuse the horizontal segment between the two `x 0`-slices.
      refine mem_convexHull_of_exists_fintype w
        (fun i : Fin 2 ↦
          match i with
          | 0 => ![(0 : ℝ), 0]
          | _ => ![(1 : ℝ), 0])
        hw_nonneg hw_sum ?_ ?_
      · intro i
        fin_cases i
        · exact Or.inl <| by
            rw [exercise_5_24_case_2_polytope_eq_explicit]
            norm_num [mem_prefix_unit_box_two_iff]
        · exact Or.inr <| by
            rw [exercise_5_24_case_2_polytope_eq_explicit]
            norm_num [mem_prefix_unit_box_two_iff]
      · ext k
        fin_cases k
        · simp [w, Fin.sum_univ_two]
        · simp [w, hx1_zero, Fin.sum_univ_two]
    · rw [coordinate_lift_project_hull_def]
      -- Points on the segment already lie on the lower `x 1 = 0` slice.
      exact subset_convexHull ℝ _ (Or.inl ⟨hxP, hx1_zero⟩)

/-- Exercise 5.24 (5). For
`P = {x ∈ [0, 1]^2 | 2 x₁ + x₂ ≤ 2, x₂ ≤ 2 x₁}`, the Chvátal closure is exactly
`[0, 1]^2 ∩ {x | x₂ ≤ x₁, x₁ + x₂ ≤ 1}`. -/
theorem exercise_5_24_case_2_chvatal_closure_eq_relaxation :
    pure_integer_chvatal_closure exercise_5_24_case_2_polytope =
      exercise_5_24_case_2_chvatal_relaxation := by
  ext x
  constructor
  · intro hx
    have hx' :
        x ∈ pure_integer_chvatal_closure (polyhedron_le_set exercise_5_24_case_2_A
          exercise_5_24_case_2_b) := by
      simpa [exercise_5_24_case_2_polytope] using hx
    rw [mem_pure_integer_chvatal_closure_polyhedron_le_set_iff
      exercise_5_24_case_2_A exercise_5_24_case_2_b, mem_chvatalClosure_iff] at hx'
    have hxP : x ∈ exercise_5_24_case_2_polytope := by
      simpa [exercise_5_24_case_2_polytope] using hx'.1
    rw [exercise_5_24_case_2_polytope_eq_explicit] at hxP
    let uDiff : Fin 6 → ℝ := ![(0 : ℝ), 0, 0, 0, 1 / 4, 3 / 4]
    have huDiff : IsChvatalMultiplier exercise_5_24_case_2_A Finset.univ uDiff := by
      rw [isChvatalMultiplier_univ_iff]
      constructor
      · intro i
        fin_cases i <;> norm_num [uDiff]
      · intro j
        fin_cases j
        · refine ⟨-1, ?_⟩
          simp [uDiff, exercise_5_24_case_2_A, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
          norm_num
        · refine ⟨1, ?_⟩
          simp [uDiff, exercise_5_24_case_2_A, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
          norm_num
    have hdiff : x 1 ≤ x 0 := by
      have huCut := hx'.2 uDiff huDiff
      simp [uDiff, exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.vecMul, dotProduct,
        Fin.sum_univ_succ] at huCut
      nlinarith
    let uSum : Fin 6 → ℝ := ![(0 : ℝ), 1 / 2, 0, 0, 1 / 2, 0]
    have huSum : IsChvatalMultiplier exercise_5_24_case_2_A Finset.univ uSum := by
      rw [isChvatalMultiplier_univ_iff]
      constructor
      · intro i
        fin_cases i <;> norm_num [uSum]
      · intro j
        fin_cases j
        · refine ⟨1, ?_⟩
          norm_num [uSum, exercise_5_24_case_2_A, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
        · refine ⟨1, ?_⟩
          norm_num [uSum, exercise_5_24_case_2_A, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    have hsum : x 0 + x 1 ≤ 1 := by
      have huCut := hx'.2 uSum huSum
      simp [uSum, exercise_5_24_case_2_A, exercise_5_24_case_2_b, Matrix.vecMul, dotProduct,
        Fin.sum_univ_succ] at huCut
      nlinarith
    -- The original polytope bounds persist, and the two explicit multipliers yield the missing
    -- Chvátal cuts.
    exact ⟨hxP.1, hdiff, hsum⟩
  · rintro ⟨hxBox, hdiff, hsum⟩
    rw [mem_pure_integer_chvatal_closure_iff]
    have hxBox' := (mem_prefix_unit_box_two_iff x).1 hxBox
    have hxP : x ∈ exercise_5_24_case_2_polytope := by
      rw [exercise_5_24_case_2_polytope_eq_explicit]
      refine ⟨hxBox, ?_⟩
      constructor
      · nlinarith [hxBox'.2.1, hsum]
      · nlinarith
    refine ⟨hxP, ?_⟩
    intro c d hvalid
    let w : Fin 3 → ℝ
      | 0 => 1 - x 0 - x 1
      | 1 => x 0 - x 1
      | _ => 2 * x 1
    have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
      intro i
      fin_cases i
      · simp [w]
        nlinarith [hsum]
      · simp [w]
        linarith
      · simp [w]
        linarith
    have hw_sum : ∑ i, w i = 1 := by
      simp [w, Fin.sum_univ_three]
      ring
    have h00 : (0 : ℝ) ≤ d := by
      have h :=
        hvalid (x := ![(0 : ℝ), 0]) (by
          rw [exercise_5_24_case_2_polytope_eq_explicit]
          refine ⟨?_, ?_⟩
          · simp [mem_prefix_unit_box_two_iff]
          · constructor <;> norm_num)
      simpa using h
    have h10 : (c 0 : ℝ) ≤ ((Int.floor d : ℤ) : ℝ) := by
      have h :=
        hvalid (x := ![(1 : ℝ), 0]) (by
          rw [exercise_5_24_case_2_polytope_eq_explicit]
          refine ⟨?_, ?_⟩
          · simp [mem_prefix_unit_box_two_iff]
          · constructor <;> norm_num)
      have h' : (c 0 : ℝ) ≤ d := by
        simpa [dotProduct] using h
      exact_mod_cast (Int.le_floor.mpr h')
    have hmid :
        ((fun i ↦ (c i : ℝ)) ⬝ᵥ ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))]) ≤
          ((Int.floor d : ℤ) : ℝ) := by
      have hmidMem := exercise524Case2MidpointMemPureIntegerChvatalClosure
      rw [mem_pure_integer_chvatal_closure_iff] at hmidMem
      exact hmidMem.2 c d hvalid
    -- Evaluate the cut on the triangle decomposition `conv{(0,0),(1,0),(1/2,1/2)}`.
    calc
      (fun i ↦ (c i : ℝ)) ⬝ᵥ x
          = w 0 * 0 + w 1 * (c 0 : ℝ) +
              w 2 * ((fun i ↦ (c i : ℝ)) ⬝ᵥ ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))]) := by
              simp [w, dotProduct, Fin.sum_univ_two]
              ring
      _ ≤ w 0 * (((Int.floor d : ℤ) : ℝ)) +
            w 1 * (((Int.floor d : ℤ) : ℝ)) +
            w 2 * (((Int.floor d : ℤ) : ℝ)) := by
              have h00_floor : (0 : ℝ) ≤ ((Int.floor d : ℤ) : ℝ) := by
                exact_mod_cast Int.floor_nonneg.mpr h00
              nlinarith [hw_nonneg 0, hw_nonneg 1, hw_nonneg 2, h00_floor, h10, hmid]
      _ = ((Int.floor d : ℤ) : ℝ) := by
            have hw012 : w 0 + w 1 + w 2 = 1 := by
              simpa [Fin.sum_univ_three] using hw_sum
            nlinarith

/-- Exercise 5.24 (6). In the second polytope, the lift-and-project closure is the tighter
relaxation: it is a strict subset of the Chvátal closure. -/
theorem exercise_5_24_case_2_lift_project_closure_tighter :
    lift_project_closure exercise_5_24_case_2_polytope Finset.univ ⊂
      pure_integer_chvatal_closure exercise_5_24_case_2_polytope := by
  rw [exercise_5_24_case_2_lift_project_closure_eq_zero_one_hull,
    exercise_5_24_case_2_zero_one_hull_eq_explicit,
    exercise_5_24_case_2_chvatal_closure_eq_relaxation]
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    rcases hx with ⟨hxBox, hx1_zero⟩
    change x 1 = 0 at hx1_zero
    -- Points on the zero-one hull segment satisfy both Chvátal cuts immediately.
    refine ⟨hxBox, ?_, ?_⟩
    · have hxBox' := (mem_prefix_unit_box_two_iff _).1 hxBox
      nlinarith [hxBox'.1, hx1_zero]
    · have hxBox' := (mem_prefix_unit_box_two_iff _).1 hxBox
      nlinarith [hx1_zero, hxBox'.2.1]
  · intro hEq
    have hmid_mem :
        ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))] ∈
          pure_integer_chvatal_closure exercise_5_24_case_2_polytope :=
      exercise524Case2MidpointMemPureIntegerChvatalClosure
    have hmid_relax :
        ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))] ∈ exercise_5_24_case_2_chvatal_relaxation := by
      simpa [exercise_5_24_case_2_chvatal_closure_eq_relaxation] using hmid_mem
    have hmid_segment :
        ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))] ∈
          prefix_unit_box (Nat.le_refl 2) ∩ {x : Fin 2 → ℝ | x 1 = 0} := by
      simpa [hEq] using hmid_relax
    have hmid_zero : ![((1 / 2 : ℝ)), ((1 / 2 : ℝ))] 1 = 0 := hmid_segment.2
    norm_num at hmid_zero

end Exercise524
