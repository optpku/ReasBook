/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped Matrix

section Example105

/-- The polytope `P = {x ∈ [0, 1]^4 | x₁ - 2 x₂ + 4 x₃ + 5 x₄ ≥ 3}` from Example 10.5. -/
def lovasz_schrijver_example_10_5_polytope : Set (Fin 4 → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3 ≥ 3}

/-- In Example 10.5, the canonical pure-integer points of `P` are exactly its `0/1` points,
because `P ⊆ [0, 1]^4`. -/
theorem lovasz_schrijver_example_10_5_pure_integer_points_eq_zero_one_points :
    pure_integer_points lovasz_schrijver_example_10_5_polytope =
      zero_one_points (Nat.le_refl 4) lovasz_schrijver_example_10_5_polytope := by
  ext x
  constructor
  · intro hx
    -- Unpack the integer point and use the box constraints
    -- to force each coordinate to be `0` or `1`.
    rw [mem_pure_integer_points_iff] at hx
    rcases hx with ⟨hxP, hxInt⟩
    rw [mem_zero_one_points_iff]
    refine ⟨hxP, ?_⟩
    rcases (mem_integerVectors_iff (x := x)).1 (by simpa [integerVectors] using hxInt) with ⟨z, rfl⟩
    intro i
    have hzi_bounds : 0 ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ 1 := by
      simpa [Function.comp] using hxP.1 i
    have hzi_nonneg : 0 ≤ z i := by
      exact_mod_cast hzi_bounds.1
    have hzi_le_one : z i ≤ 1 := by
      exact_mod_cast hzi_bounds.2
    have hzi_zero_or_one : z i = 0 ∨ z i = 1 := by
      omega
    rcases hzi_zero_or_one with hzi | hzi
    · left
      simp [Function.comp, hzi]
    · right
      simp [Function.comp, hzi]
  · intro hx
    -- Every binary feasible point is visibly integral, so it lies in the pure-integer slice.
    rw [mem_zero_one_points_iff] at hx
    rcases hx with ⟨hxP, hx01raw⟩
    rw [mem_pure_integer_points_iff]
    refine ⟨hxP, ?_⟩
    -- Normalize the coordinate statement so the integer witness talks about `x i` directly.
    have hx01 : ∀ i : Fin 4, x i = 0 ∨ x i = 1 := by
      simpa using hx01raw
    have hxInt : x ∈ integerVectors 4 := by
      -- Build the integer witness coordinatewise from the normalized `0/1` alternatives.
      refine (mem_integerVectors_iff (x := x)).2 ?_
      refine ⟨fun i ↦ if x i = 0 then 0 else 1, ?_⟩
      funext i
      rcases hx01 i with hxi | hxi
      · simp [hxi]
      · simp [hxi]
    simpa [integerVectors] using hxInt

/-- The lifted matrix `Y` appearing in the semidefinite constraint for Example 10.5. The matrix is
indexed by `0, 1, 2, 3, 4`, where `0` is the homogenizing coordinate and the remaining indices
correspond to `x₁, x₂, x₃, x₄`. -/
def lovasz_schrijver_example_10_5_Y
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(1 : ℝ), x 0, x 1, x 2, x 3;
    x 0, x 0, y12, y13, y14;
    x 1, y12, x 1, y23, y24;
    x 2, y13, y23, x 2, y34;
    x 3, y14, y24, y34, x 3]

/-- The eight inequalities obtained by linearizing
`xᵢ (x₁ - 2 x₂ + 4 x₃ + 5 x₄ - 3) ≥ 0` and
`(1 - xᵢ) (x₁ - 2 x₂ + 4 x₃ + 5 x₄ - 3) ≥ 0` in Example 10.5. -/
def lovasz_schrijver_example_10_5_primary_linearization
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) : Prop :=
  -2 * x 0 - 2 * y12 + 4 * y13 + 5 * y14 ≥ 0 ∧
    3 * x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3 + 2 * y12 - 4 * y13 - 5 * y14 ≥ 3 ∧
      -5 * x 1 + y12 + 4 * y23 + 5 * y24 ≥ 0 ∧
        x 0 + 3 * x 1 + 4 * x 2 + 5 * x 3 - y12 - 4 * y23 - 5 * y24 ≥ 3 ∧
          x 2 + y13 - 2 * y23 + 5 * y34 ≥ 0 ∧
            x 0 - 2 * x 1 + 3 * x 2 + 5 * x 3 - y13 + 2 * y23 - 5 * y34 ≥ 3 ∧
              2 * x 3 + y14 - 2 * y24 + 4 * y34 ≥ 0 ∧
                x 0 - 2 * x 1 + 4 * x 2 + 3 * x 3 - y14 + 2 * y24 - 4 * y34 ≥ 3

/-- The pairwise McCormick linearization inequalities for
`yᵢⱼ = xᵢ xⱼ`, together with the upper bounds `xᵢ ≤ 1`, in Example 10.5. -/
def lovasz_schrijver_example_10_5_pairwise_linearization
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) : Prop :=
  1 - x 0 - x 1 + y12 ≥ 0 ∧
    y12 ≤ x 0 ∧
      y12 ≤ x 1 ∧
        0 ≤ y12 ∧
          1 - x 0 - x 2 + y13 ≥ 0 ∧
            y13 ≤ x 0 ∧
              y13 ≤ x 2 ∧
                0 ≤ y13 ∧
                  1 - x 0 - x 3 + y14 ≥ 0 ∧
                    y14 ≤ x 0 ∧
                      y14 ≤ x 3 ∧
                        0 ≤ y14 ∧
                          1 - x 1 - x 2 + y23 ≥ 0 ∧
                            y23 ≤ x 1 ∧
                              y23 ≤ x 2 ∧
                                0 ≤ y23 ∧
                                  1 - x 1 - x 3 + y24 ≥ 0 ∧
                                    y24 ≤ x 1 ∧
                                      y24 ≤ x 3 ∧
                                        0 ≤ y24 ∧
                                          1 - x 2 - x 3 + y34 ≥ 0 ∧
                                            y34 ≤ x 2 ∧
                                              y34 ≤ x 3 ∧
                                                0 ≤ y34 ∧
                                                  x 0 ≤ 1 ∧
                                                    x 1 ≤ 1 ∧ x 2 ≤ 1 ∧ x 3 ≤ 1

/-- Helper for Example 10.5: the example polytope is convex because it is the unit cube
intersected with one affine halfspace. -/
lemma lovasz_schrijver_example_10_5_polytope_convex :
    Convex ℝ lovasz_schrijver_example_10_5_polytope := by
  let f : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj 0 - 2 • LinearMap.proj 1 + 4 • LinearMap.proj 2 + 5 • LinearMap.proj 3
  -- Rewrite the set as a box intersected with a linear halfspace.
  have hrewrite :
      lovasz_schrijver_example_10_5_polytope =
        Set.Icc (0 : Fin 4 → ℝ) 1 ∩ f ⁻¹' Set.Ici (3 : ℝ) := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · exact ⟨fun i ↦ (hx.1 i).1, fun i ↦ (hx.1 i).2⟩
      · simpa [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx.2
    · rintro ⟨hxBox, hxHalfspace⟩
      refine ⟨?_, ?_⟩
      · intro i
        exact ⟨hxBox.1 i, hxBox.2 i⟩
      · simpa [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hxHalfspace
  rw [hrewrite]
  exact (convex_Icc (0 : Fin 4 → ℝ) 1).inter <| (convex_Ici (3 : ℝ)).linear_preimage f

/-- A fixed feasible point of the polytope from Example 10.5, used to witness the zero vector in
the homogenized cone. -/
def lovasz_schrijver_example_10_5_reference_point : Fin 4 → ℝ :=
  ![1, 0, 1, 0]

/-- Helper for Example 10.5: the reference point `(1, 0, 1, 0)` lies in the example polytope. -/
lemma lovasz_schrijver_example_10_5_reference_point_mem_polytope :
    lovasz_schrijver_example_10_5_reference_point ∈ lovasz_schrijver_example_10_5_polytope := by
  -- Check the box constraints and the defining row inequality coordinatewise.
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp [lovasz_schrijver_example_10_5_reference_point]
  · have hrow :
        lovasz_schrijver_example_10_5_reference_point 0 -
            2 * lovasz_schrijver_example_10_5_reference_point 1 +
              4 * lovasz_schrijver_example_10_5_reference_point 2 +
                5 * lovasz_schrijver_example_10_5_reference_point 3 ≥
          3 := by
      change (1 : ℝ) - 2 * 0 + 4 * 1 + 5 * 0 ≥ 3
      norm_num
    simpa using hrow

/-- Helper for Example 10.5: dividing a coordinate by a positive homogenizing scale preserves the
unit interval bounds and reconstructs the original coordinate. -/
lemma lovasz_schrijver_example_10_5_positive_scale_coordinate_data
    (t u : ℝ) (ht : 0 < t) (hu_nonneg : 0 ≤ u) (hu_le : u ≤ t) :
    0 ≤ u / t ∧ u / t ≤ 1 ∧ u = t * (u / t) := by
  -- Package the three arithmetic facts needed in the positive-scale cone branch once.
  refine ⟨div_nonneg hu_nonneg ht.le, ?_, ?_⟩
  · field_simp [ht.ne']
    exact hu_le
  · simpa [mul_comm] using (div_mul_cancel₀ u ht.ne').symm

/-- Helper for Example 10.5: membership in the homogenized cone of the example polytope is
exactly the scaled box constraints together with the scaled row inequality. -/
lemma mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff
    (z : Fin 5 → ℝ) :
    z ∈ homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      0 ≤ z 0 ∧
        (0 ≤ z 1 ∧ z 1 ≤ z 0) ∧
        (0 ≤ z 2 ∧ z 2 ≤ z 0) ∧
        (0 ≤ z 3 ∧ z 3 ≤ z 0) ∧
        (0 ≤ z 4 ∧ z 4 ≤ z 0) ∧
        z 1 - 2 * z 2 + 4 * z 3 + 5 * z 4 ≥ 3 * z 0 := by
  rw [mem_homogenized_cone_iff]
  constructor
  · rintro ⟨t, ht_nonneg, x, hxHull, rfl⟩
    have hx :
        x ∈ lovasz_schrijver_example_10_5_polytope := by
      rwa [convexHull_eq_self.2 lovasz_schrijver_example_10_5_polytope_convex] at hxHull
    -- Rewrite the scaled homogenized point coordinatewise and transfer the box inequalities.
    refine ⟨by simpa [homogenized_point] using ht_nonneg, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · simpa [homogenized_point] using mul_nonneg ht_nonneg (hx.1 0).1
      · simpa [homogenized_point] using mul_le_mul_of_nonneg_left (hx.1 0).2 ht_nonneg
    · constructor
      · simpa [homogenized_point] using mul_nonneg ht_nonneg (hx.1 1).1
      · simpa [homogenized_point] using mul_le_mul_of_nonneg_left (hx.1 1).2 ht_nonneg
    · constructor
      · simpa [homogenized_point] using mul_nonneg ht_nonneg (hx.1 2).1
      · simpa [homogenized_point] using mul_le_mul_of_nonneg_left (hx.1 2).2 ht_nonneg
    · constructor
      · simpa [homogenized_point] using mul_nonneg ht_nonneg (hx.1 3).1
      · simpa [homogenized_point] using mul_le_mul_of_nonneg_left (hx.1 3).2 ht_nonneg
    · -- The defining row inequality scales linearly with the homogenizing coordinate.
      have hz0 :
          (t • homogenized_point x) 0 = t := by
        simp [homogenized_point]
      have hz1 :
          (t • homogenized_point x) 1 = t * x 0 := by
        simp [homogenized_point]
      have hz2' :
          (t • homogenized_point x) 2 = t * x 1 := by
        rfl
      have hz3' :
          (t • homogenized_point x) 3 = t * x 2 := by
        rfl
      have hz4' :
          (t • homogenized_point x) 4 = t * x 3 := by
        rfl
      nlinarith [hx.2, ht_nonneg, hz0, hz1, hz2', hz3', hz4']
  · rintro ⟨hz0_nonneg, hz1, hz2, hz3, hz4, hrow⟩
    by_cases hz0_zero : z 0 = 0
    · have hz1_zero : z 1 = 0 := by linarith
      have hz2_zero : z 2 = 0 := by linarith
      have hz3_zero : z 3 = 0 := by linarith
      have hz4_zero : z 4 = 0 := by linarith
      have href_hull :
          lovasz_schrijver_example_10_5_reference_point ∈
            convexHull ℝ lovasz_schrijver_example_10_5_polytope := by
        rw [convexHull_eq_self.2 lovasz_schrijver_example_10_5_polytope_convex]
        exact lovasz_schrijver_example_10_5_reference_point_mem_polytope
      refine ⟨0, le_rfl, lovasz_schrijver_example_10_5_reference_point, href_hull, ?_⟩
      -- When the homogenizing coordinate vanishes, every scaled coordinate vanishes as well.
      calc
        z = 0 := by
          ext i
          fin_cases i
          · simp [hz0_zero]
          · simp [hz1_zero]
          · simp [hz2_zero]
          · simp [hz3_zero]
          · simp [hz4_zero]
        _ = (0 : ℝ) • homogenized_point lovasz_schrijver_example_10_5_reference_point := by
          simp
    · let x : Fin 4 → ℝ := fun i ↦ z i.succ / z 0
      have hz0_pos : 0 < z 0 := lt_of_le_of_ne hz0_nonneg (Ne.symm hz0_zero)
      have hx0_data :
          0 ≤ x 0 ∧ x 0 ≤ 1 ∧ z 1 = z 0 * x 0 := by
        simpa [x] using
          lovasz_schrijver_example_10_5_positive_scale_coordinate_data
            (z 0) (z 1) hz0_pos hz1.1 hz1.2
      have hx1_data :
          0 ≤ x 1 ∧ x 1 ≤ 1 ∧ z 2 = z 0 * x 1 := by
        simpa [x] using
          lovasz_schrijver_example_10_5_positive_scale_coordinate_data
            (z 0) (z 2) hz0_pos hz2.1 hz2.2
      have hx2_data :
          0 ≤ x 2 ∧ x 2 ≤ 1 ∧ z 3 = z 0 * x 2 := by
        simpa [x] using
          lovasz_schrijver_example_10_5_positive_scale_coordinate_data
            (z 0) (z 3) hz0_pos hz3.1 hz3.2
      have hx3_data :
          0 ≤ x 3 ∧ x 3 ≤ 1 ∧ z 4 = z 0 * x 3 := by
        simpa [x] using
          lovasz_schrijver_example_10_5_positive_scale_coordinate_data
            (z 0) (z 4) hz0_pos hz4.1 hz4.2
      have hx_mem : x ∈ lovasz_schrijver_example_10_5_polytope := by
        refine ⟨?_, ?_⟩
        · intro i
          fin_cases i
          · exact ⟨hx0_data.1, hx0_data.2.1⟩
          · exact ⟨hx1_data.1, hx1_data.2.1⟩
          · exact ⟨hx2_data.1, hx2_data.2.1⟩
          · exact ⟨hx3_data.1, hx3_data.2.1⟩
        · have hscaled :
              z 0 * (x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3) =
                z 1 - 2 * z 2 + 4 * z 3 + 5 * z 4 := by
            calc
              z 0 * (x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3) =
                  z 0 * x 0 - 2 * (z 0 * x 1) + 4 * (z 0 * x 2) + 5 * (z 0 * x 3) := by
                ring
              _ = z 1 - 2 * z 2 + 4 * z 3 + 5 * z 4 := by
                rw [hx0_data.2.2, hx1_data.2.2, hx2_data.2.2, hx3_data.2.2]
          nlinarith [hrow, hscaled, hz0_pos]
      have hx_hull :
          x ∈ convexHull ℝ lovasz_schrijver_example_10_5_polytope := by
        rw [convexHull_eq_self.2 lovasz_schrijver_example_10_5_polytope_convex]
        exact hx_mem
      refine ⟨z 0, hz0_nonneg, x, hx_hull, ?_⟩
      -- Rebuild the lifted vector from the recovered normalized coordinates.
      ext i
      fin_cases i
      · simp [homogenized_point]
      · simpa [x, homogenized_point, mul_comm] using hx0_data.2.2
      · simpa [x, homogenized_point, mul_comm] using hx1_data.2.2
      · simpa [x, homogenized_point, mul_comm] using hx2_data.2.2
      · simpa [x, homogenized_point, mul_comm] using hx3_data.2.2

/-- The explicit matrix of Example 10.5 has first column `(1, x)`. -/
theorem lovasz_schrijver_example_10_5_Y_mulVec_lifted_basis_zero
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) :
    lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 0 =
      homogenized_point x := by
  have hbasis0 : lifted_basis (0 : Fin 5) = Pi.single 0 (1 : ℝ) := by
    funext i
    fin_cases i <;> simp [lifted_basis]
  -- Rewrite the lifted basis vector as the standard basis vector and read off the first column.
  calc
    lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 0 =
    lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ Pi.single 0 (1 : ℝ) := by
      rw [hbasis0]
    _ = (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34).col 0 := by
      exact Matrix.mulVec_single_one
        (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34) 0
    _ = homogenized_point x := by
      ext i
      fin_cases i <;> rfl

/-- Helper for Example 10.5: a lifted basis vector at a nonzero index is the corresponding
standard `Pi.single` vector. -/
lemma lovasz_schrijver_example_10_5_lifted_basis_succ_eq_single
    (i : Fin 4) :
    lifted_basis i.succ = Pi.single i.succ (1 : ℝ) := by
  -- Read the lifted basis vector coordinatewise and split on whether the coordinate matches.
  funext j
  by_cases h : j = i.succ
  · subst h
    simp [lifted_basis]
  · simp [lifted_basis, h]

/-- Helper for Example 10.5: each nonzero lifted basis vector extracts the corresponding explicit
column of the specialized matrix. -/
lemma lovasz_schrijver_example_10_5_column_vector_eq
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) (i : Fin 4) :
    lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis i.succ =
      match i.1 with
      | 0 => ![x 0, x 0, y12, y13, y14]
      | 1 => ![x 1, y12, x 1, y23, y24]
      | 2 => ![x 2, y13, y23, x 2, y34]
      | _ => ![x 3, y14, y24, y34, x 3] := by
  -- Normalize the matrix product to an explicit column before entering cone arithmetic.
  fin_cases i
  · rw [lovasz_schrijver_example_10_5_lifted_basis_succ_eq_single]
    calc
      lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ Pi.single 1 (1 : ℝ) =
          (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34).col 1 := by
        exact Matrix.mulVec_single_one
          (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34) 1
      _ = ![x 0, x 0, y12, y13, y14] := by
        ext j
        fin_cases j <;> rfl
  · rw [lovasz_schrijver_example_10_5_lifted_basis_succ_eq_single]
    calc
      lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ Pi.single 2 (1 : ℝ) =
          (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34).col 2 := by
        exact Matrix.mulVec_single_one
          (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34) 2
      _ = ![x 1, y12, x 1, y23, y24] := by
        ext j
        fin_cases j <;> rfl
  · rw [lovasz_schrijver_example_10_5_lifted_basis_succ_eq_single]
    calc
      lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ Pi.single 3 (1 : ℝ) =
          (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34).col 3 := by
        exact Matrix.mulVec_single_one
          (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34) 3
      _ = ![x 2, y13, y23, x 2, y34] := by
        ext j
        fin_cases j <;> rfl
  · rw [lovasz_schrijver_example_10_5_lifted_basis_succ_eq_single]
    calc
      lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ Pi.single 4 (1 : ℝ) =
          (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34).col 4 := by
        exact Matrix.mulVec_single_one
          (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34) 4
      _ = ![x 3, y14, y24, y34, x 3] := by
        ext j
        fin_cases j <;> rfl

/-- Helper for Example 10.5: the complementary lifted columns come from subtracting the explicit
column vectors from the first column `(1, x)`. -/
lemma lovasz_schrijver_example_10_5_difference_column_vector_eq
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) (i : Fin 4) :
    lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
        (lifted_basis 0 - lifted_basis i.succ) =
      match i.1 with
      | 0 => ![1 - x 0, 0, x 1 - y12, x 2 - y13, x 3 - y14]
      | 1 => ![1 - x 1, x 0 - y12, 0, x 2 - y23, x 3 - y24]
      | 2 => ![1 - x 2, x 0 - y13, x 1 - y23, 0, x 3 - y34]
      | _ => ![1 - x 3, x 0 - y14, x 1 - y24, x 2 - y34, 0] := by
  -- Route correction: use `mulVec_sub` plus the already normalized columns instead of expanding
  -- `Y.col` and subtraction inside the cone goal.
  fin_cases i
  · have hcol :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 1 =
          ![x 0, x 0, y12, y13, y14] := by
      simpa using
        lovasz_schrijver_example_10_5_column_vector_eq x y12 y13 y14 y23 y24 y34 (0 : Fin 4)
    calc
      lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
          (lifted_basis 0 - lifted_basis 1) =
          lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 0 -
            lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 1 := by
        simp [Matrix.mulVec_sub]
      _ = homogenized_point x - ![x 0, x 0, y12, y13, y14] := by
        rw [lovasz_schrijver_example_10_5_Y_mulVec_lifted_basis_zero, hcol]
      _ = ![1 - x 0, 0, x 1 - y12, x 2 - y13, x 3 - y14] := by
        ext j
        fin_cases j
        · simp [homogenized_point]
        · simp [homogenized_point]
        · change x 1 - y12 = x 1 - y12
          rfl
        · change x 2 - y13 = x 2 - y13
          rfl
        · change x 3 - y14 = x 3 - y14
          rfl
  · have hcol :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 2 =
          ![x 1, y12, x 1, y23, y24] := by
      simpa using
        lovasz_schrijver_example_10_5_column_vector_eq x y12 y13 y14 y23 y24 y34 (1 : Fin 4)
    calc
      lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
          (lifted_basis 0 - lifted_basis 2) =
          lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 0 -
            lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 2 := by
        simp [Matrix.mulVec_sub]
      _ = homogenized_point x - ![x 1, y12, x 1, y23, y24] := by
        rw [lovasz_schrijver_example_10_5_Y_mulVec_lifted_basis_zero, hcol]
      _ = ![1 - x 1, x 0 - y12, 0, x 2 - y23, x 3 - y24] := by
        ext j
        fin_cases j
        · simp [homogenized_point]
        · simp [homogenized_point]
        · change x 1 - x 1 = 0
          ring
        · change x 2 - y23 = x 2 - y23
          rfl
        · change x 3 - y24 = x 3 - y24
          rfl
  · have hcol :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 3 =
          ![x 2, y13, y23, x 2, y34] := by
      simpa using
        lovasz_schrijver_example_10_5_column_vector_eq x y12 y13 y14 y23 y24 y34 (2 : Fin 4)
    calc
      lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
          (lifted_basis 0 - lifted_basis 3) =
          lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 0 -
            lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 3 := by
        simp [Matrix.mulVec_sub]
      _ = homogenized_point x - ![x 2, y13, y23, x 2, y34] := by
        rw [lovasz_schrijver_example_10_5_Y_mulVec_lifted_basis_zero, hcol]
      _ = ![1 - x 2, x 0 - y13, x 1 - y23, 0, x 3 - y34] := by
        ext j
        fin_cases j
        · simp [homogenized_point]
        · simp [homogenized_point]
        · change x 1 - y23 = x 1 - y23
          rfl
        · change x 2 - x 2 = 0
          ring
        · change x 3 - y34 = x 3 - y34
          rfl
  · have hcol :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 4 =
          ![x 3, y14, y24, y34, x 3] := by
      simpa using
        lovasz_schrijver_example_10_5_column_vector_eq x y12 y13 y14 y23 y24 y34 (3 : Fin 4)
    calc
      lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
          (lifted_basis 0 - lifted_basis 4) =
          lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 0 -
            lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 4 := by
        simp [Matrix.mulVec_sub]
      _ = homogenized_point x - ![x 3, y14, y24, y34, x 3] := by
        rw [lovasz_schrijver_example_10_5_Y_mulVec_lifted_basis_zero, hcol]
      _ = ![1 - x 3, x 0 - y14, x 1 - y24, x 2 - y34, 0] := by
        ext j
        fin_cases j
        · simp [homogenized_point]
        · simp [homogenized_point]
        · change x 1 - y24 = x 1 - y24
          rfl
        · change x 2 - y34 = x 2 - y34
          rfl
        · change x 3 - x 3 = 0
          ring

/-- Helper for Example 10.5: the first explicit lifted column packages the first primary
inequality and the three incident pairwise bounds. -/
lemma lovasz_schrijver_example_10_5_first_lifted_column_cone_iff
    (x : Fin 4 → ℝ) (y12 y13 y14 : ℝ) :
    ![x 0, x 0, y12, y13, y14] ∈ homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      -2 * x 0 - 2 * y12 + 4 * y13 + 5 * y14 ≥ 0 ∧
        y12 ≤ x 0 ∧ 0 ≤ y12 ∧ y13 ≤ x 0 ∧ 0 ≤ y13 ∧ y14 ≤ x 0 ∧ 0 ≤ y14 := by
  -- Rewrite cone membership into scalar inequalities for this explicit first lifted column.
  rw [mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
  constructor
  · rintro ⟨_, _, hy12, hy13, hy14, hrow⟩
    have hrow_scaled : x 0 - 2 * y12 + 4 * y13 + 5 * y14 ≥ 3 * x 0 := by
      simpa using hrow
    have hrow' : -2 * x 0 - 2 * y12 + 4 * y13 + 5 * y14 ≥ 0 := by
      linarith [hrow_scaled]
    exact ⟨hrow', hy12.2, hy12.1, hy13.2, hy13.1, hy14.2, hy14.1⟩
  · rintro ⟨hrow, hy12_le, hy12_nonneg, hy13_le, hy13_nonneg, hy14_le, hy14_nonneg⟩
    -- Recover the hidden nonnegativity of `x 0` from one incident pair variable.
    have hx0_nonneg : 0 ≤ x 0 := by
      linarith
    have hrow' : x 0 - 2 * y12 + 4 * y13 + 5 * y14 ≥ 3 * x 0 := by
      linarith
    refine ⟨hx0_nonneg, ⟨hx0_nonneg, le_rfl⟩, ⟨hy12_nonneg, hy12_le⟩, ⟨hy13_nonneg, hy13_le⟩,
      ⟨hy14_nonneg, hy14_le⟩, ?_⟩
    simpa using hrow'

/-- Helper for Example 10.5: the second explicit lifted column packages the second primary
inequality and the three incident pairwise bounds. -/
lemma lovasz_schrijver_example_10_5_second_lifted_column_cone_iff
    (x : Fin 4 → ℝ) (y12 y23 y24 : ℝ) :
    ![x 1, y12, x 1, y23, y24] ∈ homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      -5 * x 1 + y12 + 4 * y23 + 5 * y24 ≥ 0 ∧
        y12 ≤ x 1 ∧ 0 ≤ y12 ∧ y23 ≤ x 1 ∧ 0 ≤ y23 ∧ y24 ≤ x 1 ∧ 0 ≤ y24 := by
  -- Rewrite cone membership into scalar inequalities for this explicit second lifted column.
  rw [mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
  constructor
  · rintro ⟨_, hy12, _, hy23, hy24, hrow⟩
    have hrow_scaled : y12 - 2 * x 1 + 4 * y23 + 5 * y24 ≥ 3 * x 1 := by
      simpa using hrow
    have hrow' : -5 * x 1 + y12 + 4 * y23 + 5 * y24 ≥ 0 := by
      linarith [hrow_scaled]
    exact ⟨hrow', hy12.2, hy12.1, hy23.2, hy23.1, hy24.2, hy24.1⟩
  · rintro ⟨hrow, hy12_le, hy12_nonneg, hy23_le, hy23_nonneg, hy24_le, hy24_nonneg⟩
    -- Recover the hidden nonnegativity of `x 1` from one incident pair variable.
    have hx1_nonneg : 0 ≤ x 1 := by
      linarith
    have hrow' : y12 - 2 * x 1 + 4 * y23 + 5 * y24 ≥ 3 * x 1 := by
      linarith
    refine ⟨hx1_nonneg, ⟨hy12_nonneg, hy12_le⟩, ⟨hx1_nonneg, le_rfl⟩, ⟨hy23_nonneg, hy23_le⟩,
      ⟨hy24_nonneg, hy24_le⟩, ?_⟩
    simpa using hrow'

/-- Helper for Example 10.5: the third explicit lifted column packages the third primary
inequality and the three incident pairwise bounds. -/
lemma lovasz_schrijver_example_10_5_third_lifted_column_cone_iff
    (x : Fin 4 → ℝ) (y13 y23 y34 : ℝ) :
    ![x 2, y13, y23, x 2, y34] ∈ homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      x 2 + y13 - 2 * y23 + 5 * y34 ≥ 0 ∧
        y13 ≤ x 2 ∧ 0 ≤ y13 ∧ y23 ≤ x 2 ∧ 0 ≤ y23 ∧ y34 ≤ x 2 ∧ 0 ≤ y34 := by
  -- Rewrite cone membership into scalar inequalities for this explicit third lifted column.
  rw [mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
  constructor
  · rintro ⟨_, hy13, hy23, _, hy34, hrow⟩
    have hrow_scaled : y13 - 2 * y23 + 4 * x 2 + 5 * y34 ≥ 3 * x 2 := by
      simpa using hrow
    have hrow' : x 2 + y13 - 2 * y23 + 5 * y34 ≥ 0 := by
      linarith [hrow_scaled]
    exact ⟨hrow', hy13.2, hy13.1, hy23.2, hy23.1, hy34.2, hy34.1⟩
  · rintro ⟨hrow, hy13_le, hy13_nonneg, hy23_le, hy23_nonneg, hy34_le, hy34_nonneg⟩
    -- Recover the hidden nonnegativity of `x 2` from one incident pair variable.
    have hx2_nonneg : 0 ≤ x 2 := by
      linarith
    have hrow' : y13 - 2 * y23 + 4 * x 2 + 5 * y34 ≥ 3 * x 2 := by
      linarith
    refine ⟨hx2_nonneg, ⟨hy13_nonneg, hy13_le⟩, ⟨hy23_nonneg, hy23_le⟩, ⟨hx2_nonneg, le_rfl⟩,
      ⟨hy34_nonneg, hy34_le⟩, ?_⟩
    simpa using hrow'

/-- Helper for Example 10.5: the fourth explicit lifted column packages the fourth primary
inequality and the three incident pairwise bounds. -/
lemma lovasz_schrijver_example_10_5_fourth_lifted_column_cone_iff
    (x : Fin 4 → ℝ) (y14 y24 y34 : ℝ) :
    ![x 3, y14, y24, y34, x 3] ∈ homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      2 * x 3 + y14 - 2 * y24 + 4 * y34 ≥ 0 ∧
        y14 ≤ x 3 ∧ 0 ≤ y14 ∧ y24 ≤ x 3 ∧ 0 ≤ y24 ∧ y34 ≤ x 3 ∧ 0 ≤ y34 := by
  -- Rewrite cone membership into scalar inequalities for this explicit fourth lifted column.
  rw [mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
  constructor
  · rintro ⟨_, hy14, hy24, hy34, _, hrow⟩
    have hrow_scaled : y14 - 2 * y24 + 4 * y34 + 5 * x 3 ≥ 3 * x 3 := by
      simpa using hrow
    have hrow' : 2 * x 3 + y14 - 2 * y24 + 4 * y34 ≥ 0 := by
      linarith [hrow_scaled]
    exact ⟨hrow', hy14.2, hy14.1, hy24.2, hy24.1, hy34.2, hy34.1⟩
  · rintro ⟨hrow, hy14_le, hy14_nonneg, hy24_le, hy24_nonneg, hy34_le, hy34_nonneg⟩
    -- Recover the hidden nonnegativity of `x 3` from one incident pair variable.
    have hx3_nonneg : 0 ≤ x 3 := by
      linarith
    have hrow' : y14 - 2 * y24 + 4 * y34 + 5 * x 3 ≥ 3 * x 3 := by
      linarith
    refine ⟨hx3_nonneg, ⟨hy14_nonneg, hy14_le⟩, ⟨hy24_nonneg, hy24_le⟩, ⟨hy34_nonneg, hy34_le⟩,
      ⟨hx3_nonneg, le_rfl⟩, ?_⟩
    simpa using hrow'

/-- Helper for Example 10.5: the first explicit complementary column packages the first
complementary primary inequality and its three shifted McCormick constraints. -/
lemma lovasz_schrijver_example_10_5_first_complementary_column_cone_iff
    (x : Fin 4 → ℝ) (y12 y13 y14 : ℝ) :
    ![1 - x 0, 0, x 1 - y12, x 2 - y13, x 3 - y14] ∈
        homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      3 * x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3 + 2 * y12 - 4 * y13 - 5 * y14 ≥ 3 ∧
        y12 ≤ x 1 ∧ 1 - x 0 - x 1 + y12 ≥ 0 ∧
          y13 ≤ x 2 ∧ 1 - x 0 - x 2 + y13 ≥ 0 ∧
            y14 ≤ x 3 ∧ 1 - x 0 - x 3 + y14 ≥ 0 := by
  -- Rewrite cone membership into scalar inequalities for this explicit first complementary
  -- column and package the source-faithful shifted McCormick bounds.
  rw [mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
  constructor
  · rintro ⟨hx0, _, hz12, hz13, hz14, hrow⟩
    have hx0_nonneg : 0 ≤ 1 - x 0 := by
      simpa using hx0
    have hz12_nonneg : 0 ≤ x 1 - y12 := by
      simpa using hz12.1
    have hz12_le : x 1 - y12 ≤ 1 - x 0 := by
      simpa using hz12.2
    have hz13_nonneg : 0 ≤ x 2 - y13 := by
      simpa using hz13.1
    have hz13_le : x 2 - y13 ≤ 1 - x 0 := by
      simpa using hz13.2
    have hz14_nonneg : 0 ≤ x 3 - y14 := by
      simpa using hz14.1
    have hz14_le : x 3 - y14 ≤ 1 - x 0 := by
      simpa using hz14.2
    have hrow_scaled : -2 * (x 1 - y12) + 4 * (x 2 - y13) + 5 * (x 3 - y14) ≥ 3 * (1 - x 0) := by
      simpa using hrow
    have hrow' : 3 * x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3 + 2 * y12 - 4 * y13 - 5 * y14 ≥ 3 := by
      linarith [hrow_scaled]
    have hy12_le : y12 ≤ x 1 := by
      linarith
    have h12_shift : 1 - x 0 - x 1 + y12 ≥ 0 := by
      linarith
    have hy13_le : y13 ≤ x 2 := by
      linarith
    have h13_shift : 1 - x 0 - x 2 + y13 ≥ 0 := by
      linarith
    have hy14_le : y14 ≤ x 3 := by
      linarith
    have h14_shift : 1 - x 0 - x 3 + y14 ≥ 0 := by
      linarith
    exact ⟨hrow', hy12_le, h12_shift, hy13_le, h13_shift, hy14_le, h14_shift⟩
  · rintro ⟨hrow, hy12_le, h12_shift, hy13_le, h13_shift, hy14_le, h14_shift⟩
    -- Recover the omitted nonnegativity of `1 - x 0` from one shifted McCormick block.
    have hz12_nonneg : 0 ≤ x 1 - y12 := by
      linarith
    have hz12_le : x 1 - y12 ≤ 1 - x 0 := by
      linarith
    have hz13_nonneg : 0 ≤ x 2 - y13 := by
      linarith
    have hz13_le : x 2 - y13 ≤ 1 - x 0 := by
      linarith
    have hz14_nonneg : 0 ≤ x 3 - y14 := by
      linarith
    have hz14_le : x 3 - y14 ≤ 1 - x 0 := by
      linarith
    have hx0_nonneg : 0 ≤ 1 - x 0 := by
      linarith
    have hrow' : -2 * (x 1 - y12) + 4 * (x 2 - y13) + 5 * (x 3 - y14) ≥ 3 * (1 - x 0) := by
      linarith
    refine ⟨hx0_nonneg, ⟨le_rfl, hx0_nonneg⟩, ⟨hz12_nonneg, hz12_le⟩, ⟨hz13_nonneg, hz13_le⟩,
      ⟨hz14_nonneg, hz14_le⟩, ?_⟩
    simpa using hrow'

/-- Helper for Example 10.5: the second explicit complementary column packages the second
complementary primary inequality and its three shifted McCormick constraints. -/
lemma lovasz_schrijver_example_10_5_second_complementary_column_cone_iff
    (x : Fin 4 → ℝ) (y12 y23 y24 : ℝ) :
    ![1 - x 1, x 0 - y12, 0, x 2 - y23, x 3 - y24] ∈
        homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      x 0 + 3 * x 1 + 4 * x 2 + 5 * x 3 - y12 - 4 * y23 - 5 * y24 ≥ 3 ∧
        y12 ≤ x 0 ∧ 1 - x 0 - x 1 + y12 ≥ 0 ∧
          y23 ≤ x 2 ∧ 1 - x 1 - x 2 + y23 ≥ 0 ∧
            y24 ≤ x 3 ∧ 1 - x 1 - x 3 + y24 ≥ 0 := by
  -- Rewrite cone membership into scalar inequalities for this explicit second complementary
  -- column and package the source-faithful shifted McCormick bounds.
  rw [mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
  constructor
  · rintro ⟨hx1, hz12, _, hz23, hz24, hrow⟩
    have hx1_nonneg : 0 ≤ 1 - x 1 := by
      simpa using hx1
    have hz12_nonneg : 0 ≤ x 0 - y12 := by
      simpa using hz12.1
    have hz12_le : x 0 - y12 ≤ 1 - x 1 := by
      simpa using hz12.2
    have hz23_nonneg : 0 ≤ x 2 - y23 := by
      simpa using hz23.1
    have hz23_le : x 2 - y23 ≤ 1 - x 1 := by
      simpa using hz23.2
    have hz24_nonneg : 0 ≤ x 3 - y24 := by
      simpa using hz24.1
    have hz24_le : x 3 - y24 ≤ 1 - x 1 := by
      simpa using hz24.2
    have hrow_scaled : x 0 - y12 + 4 * (x 2 - y23) + 5 * (x 3 - y24) ≥ 3 * (1 - x 1) := by
      simpa using hrow
    have hrow' : x 0 + 3 * x 1 + 4 * x 2 + 5 * x 3 - y12 - 4 * y23 - 5 * y24 ≥ 3 := by
      linarith [hrow_scaled]
    have hy12_le : y12 ≤ x 0 := by
      linarith
    have h12_shift : 1 - x 0 - x 1 + y12 ≥ 0 := by
      linarith
    have hy23_le : y23 ≤ x 2 := by
      linarith
    have h23_shift : 1 - x 1 - x 2 + y23 ≥ 0 := by
      linarith
    have hy24_le : y24 ≤ x 3 := by
      linarith
    have h24_shift : 1 - x 1 - x 3 + y24 ≥ 0 := by
      linarith
    exact ⟨hrow', hy12_le, h12_shift, hy23_le, h23_shift, hy24_le, h24_shift⟩
  · rintro ⟨hrow, hy12_le, h12_shift, hy23_le, h23_shift, hy24_le, h24_shift⟩
    -- Recover the omitted nonnegativity of `1 - x 1` from one shifted McCormick block.
    have hz12_nonneg : 0 ≤ x 0 - y12 := by
      linarith
    have hz12_le : x 0 - y12 ≤ 1 - x 1 := by
      linarith
    have hz23_nonneg : 0 ≤ x 2 - y23 := by
      linarith
    have hz23_le : x 2 - y23 ≤ 1 - x 1 := by
      linarith
    have hz24_nonneg : 0 ≤ x 3 - y24 := by
      linarith
    have hz24_le : x 3 - y24 ≤ 1 - x 1 := by
      linarith
    have hx1_nonneg : 0 ≤ 1 - x 1 := by
      linarith
    have hrow' : x 0 - y12 + 4 * (x 2 - y23) + 5 * (x 3 - y24) ≥ 3 * (1 - x 1) := by
      linarith
    refine ⟨hx1_nonneg, ⟨hz12_nonneg, hz12_le⟩, ⟨le_rfl, hx1_nonneg⟩, ⟨hz23_nonneg, hz23_le⟩,
      ⟨hz24_nonneg, hz24_le⟩, ?_⟩
    simpa using hrow'

/-- Helper for Example 10.5: the third explicit complementary column packages the third
complementary primary inequality and its three shifted McCormick constraints. -/
lemma lovasz_schrijver_example_10_5_third_complementary_column_cone_iff
    (x : Fin 4 → ℝ) (y13 y23 y34 : ℝ) :
    ![1 - x 2, x 0 - y13, x 1 - y23, 0, x 3 - y34] ∈
        homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      x 0 - 2 * x 1 + 3 * x 2 + 5 * x 3 - y13 + 2 * y23 - 5 * y34 ≥ 3 ∧
        y13 ≤ x 0 ∧ 1 - x 0 - x 2 + y13 ≥ 0 ∧
          y23 ≤ x 1 ∧ 1 - x 1 - x 2 + y23 ≥ 0 ∧
            y34 ≤ x 3 ∧ 1 - x 2 - x 3 + y34 ≥ 0 := by
  -- Rewrite cone membership into scalar inequalities for this explicit third complementary
  -- column and package the source-faithful shifted McCormick bounds.
  rw [mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
  constructor
  · rintro ⟨hx2, hz13, hz23, _, hz34, hrow⟩
    have hx2_nonneg : 0 ≤ 1 - x 2 := by
      simpa using hx2
    have hz13_nonneg : 0 ≤ x 0 - y13 := by
      simpa using hz13.1
    have hz13_le : x 0 - y13 ≤ 1 - x 2 := by
      simpa using hz13.2
    have hz23_nonneg : 0 ≤ x 1 - y23 := by
      simpa using hz23.1
    have hz23_le : x 1 - y23 ≤ 1 - x 2 := by
      simpa using hz23.2
    have hz34_nonneg : 0 ≤ x 3 - y34 := by
      simpa using hz34.1
    have hz34_le : x 3 - y34 ≤ 1 - x 2 := by
      simpa using hz34.2
    have hrow_scaled : x 0 - y13 - 2 * (x 1 - y23) + 5 * (x 3 - y34) ≥ 3 * (1 - x 2) := by
      simpa using hrow
    have hrow' : x 0 - 2 * x 1 + 3 * x 2 + 5 * x 3 - y13 + 2 * y23 - 5 * y34 ≥ 3 := by
      linarith [hrow_scaled]
    have hy13_le : y13 ≤ x 0 := by
      linarith
    have h13_shift : 1 - x 0 - x 2 + y13 ≥ 0 := by
      linarith
    have hy23_le : y23 ≤ x 1 := by
      linarith
    have h23_shift : 1 - x 1 - x 2 + y23 ≥ 0 := by
      linarith
    have hy34_le : y34 ≤ x 3 := by
      linarith
    have h34_shift : 1 - x 2 - x 3 + y34 ≥ 0 := by
      linarith
    exact ⟨hrow', hy13_le, h13_shift, hy23_le, h23_shift, hy34_le, h34_shift⟩
  · rintro ⟨hrow, hy13_le, h13_shift, hy23_le, h23_shift, hy34_le, h34_shift⟩
    -- Recover the omitted nonnegativity of `1 - x 2` from one shifted McCormick block.
    have hz13_nonneg : 0 ≤ x 0 - y13 := by
      linarith
    have hz13_le : x 0 - y13 ≤ 1 - x 2 := by
      linarith
    have hz23_nonneg : 0 ≤ x 1 - y23 := by
      linarith
    have hz23_le : x 1 - y23 ≤ 1 - x 2 := by
      linarith
    have hz34_nonneg : 0 ≤ x 3 - y34 := by
      linarith
    have hz34_le : x 3 - y34 ≤ 1 - x 2 := by
      linarith
    have hx2_nonneg : 0 ≤ 1 - x 2 := by
      linarith
    have hrow' : x 0 - y13 - 2 * (x 1 - y23) + 5 * (x 3 - y34) ≥ 3 * (1 - x 2) := by
      linarith
    refine ⟨hx2_nonneg, ⟨hz13_nonneg, hz13_le⟩, ⟨hz23_nonneg, hz23_le⟩, ⟨le_rfl, hx2_nonneg⟩,
      ⟨hz34_nonneg, hz34_le⟩, ?_⟩
    simpa using hrow'

/-- Helper for Example 10.5: the fourth explicit complementary column packages the fourth
complementary primary inequality and its three shifted McCormick constraints. -/
lemma lovasz_schrijver_example_10_5_fourth_complementary_column_cone_iff
    (x : Fin 4 → ℝ) (y14 y24 y34 : ℝ) :
    ![1 - x 3, x 0 - y14, x 1 - y24, x 2 - y34, 0] ∈
        homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      x 0 - 2 * x 1 + 4 * x 2 + 3 * x 3 - y14 + 2 * y24 - 4 * y34 ≥ 3 ∧
        y14 ≤ x 0 ∧ 1 - x 0 - x 3 + y14 ≥ 0 ∧
          y24 ≤ x 1 ∧ 1 - x 1 - x 3 + y24 ≥ 0 ∧
            y34 ≤ x 2 ∧ 1 - x 2 - x 3 + y34 ≥ 0 := by
  -- Rewrite cone membership into scalar inequalities for this explicit fourth complementary
  -- column and package the source-faithful shifted McCormick bounds.
  rw [mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
  constructor
  · rintro ⟨hx3, hz14, hz24, hz34, _, hrow⟩
    have hx3_nonneg : 0 ≤ 1 - x 3 := by
      simpa using hx3
    have hz14_nonneg : 0 ≤ x 0 - y14 := by
      simpa using hz14.1
    have hz14_le : x 0 - y14 ≤ 1 - x 3 := by
      simpa using hz14.2
    have hz24_nonneg : 0 ≤ x 1 - y24 := by
      simpa using hz24.1
    have hz24_le : x 1 - y24 ≤ 1 - x 3 := by
      simpa using hz24.2
    have hz34_nonneg : 0 ≤ x 2 - y34 := by
      simpa using hz34.1
    have hz34_le : x 2 - y34 ≤ 1 - x 3 := by
      simpa using hz34.2
    have hrow_scaled : x 0 - y14 - 2 * (x 1 - y24) + 4 * (x 2 - y34) ≥ 3 * (1 - x 3) := by
      simpa using hrow
    have hrow' : x 0 - 2 * x 1 + 4 * x 2 + 3 * x 3 - y14 + 2 * y24 - 4 * y34 ≥ 3 := by
      linarith [hrow_scaled]
    have hy14_le : y14 ≤ x 0 := by
      linarith
    have h14_shift : 1 - x 0 - x 3 + y14 ≥ 0 := by
      linarith
    have hy24_le : y24 ≤ x 1 := by
      linarith
    have h24_shift : 1 - x 1 - x 3 + y24 ≥ 0 := by
      linarith
    have hy34_le : y34 ≤ x 2 := by
      linarith
    have h34_shift : 1 - x 2 - x 3 + y34 ≥ 0 := by
      linarith
    exact ⟨hrow', hy14_le, h14_shift, hy24_le, h24_shift, hy34_le, h34_shift⟩
  · rintro ⟨hrow, hy14_le, h14_shift, hy24_le, h24_shift, hy34_le, h34_shift⟩
    -- Recover the omitted nonnegativity of `1 - x 3` from one shifted McCormick block.
    have hz14_nonneg : 0 ≤ x 0 - y14 := by
      linarith
    have hz14_le : x 0 - y14 ≤ 1 - x 3 := by
      linarith
    have hz24_nonneg : 0 ≤ x 1 - y24 := by
      linarith
    have hz24_le : x 1 - y24 ≤ 1 - x 3 := by
      linarith
    have hz34_nonneg : 0 ≤ x 2 - y34 := by
      linarith
    have hz34_le : x 2 - y34 ≤ 1 - x 3 := by
      linarith
    have hx3_nonneg : 0 ≤ 1 - x 3 := by
      linarith
    have hrow' : x 0 - y14 - 2 * (x 1 - y24) + 4 * (x 2 - y34) ≥ 3 * (1 - x 3) := by
      linarith
    refine ⟨hx3_nonneg, ⟨hz14_nonneg, hz14_le⟩, ⟨hz24_nonneg, hz24_le⟩, ⟨hz34_nonneg, hz34_le⟩,
      ⟨le_rfl, hx3_nonneg⟩, ?_⟩
    simpa using hrow'

/-- Helper for Example 10.5: each explicit lifted column lies in the homogenized cone exactly
when the matching primary inequality and incident lower/upper McCormick bounds hold. -/
lemma lovasz_schrijver_example_10_5_column_cone_block_iff
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) (i : Fin 4) :
    lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis i.succ ∈
        homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      match i.1 with
      | 0 =>
          -2 * x 0 - 2 * y12 + 4 * y13 + 5 * y14 ≥ 0 ∧
            y12 ≤ x 0 ∧ 0 ≤ y12 ∧ y13 ≤ x 0 ∧ 0 ≤ y13 ∧ y14 ≤ x 0 ∧ 0 ≤ y14
      | 1 =>
          -5 * x 1 + y12 + 4 * y23 + 5 * y24 ≥ 0 ∧
            y12 ≤ x 1 ∧ 0 ≤ y12 ∧ y23 ≤ x 1 ∧ 0 ≤ y23 ∧ y24 ≤ x 1 ∧ 0 ≤ y24
      | 2 =>
          x 2 + y13 - 2 * y23 + 5 * y34 ≥ 0 ∧
            y13 ≤ x 2 ∧ 0 ≤ y13 ∧ y23 ≤ x 2 ∧ 0 ≤ y23 ∧ y34 ≤ x 2 ∧ 0 ≤ y34
      | _ =>
          2 * x 3 + y14 - 2 * y24 + 4 * y34 ≥ 0 ∧
            y14 ≤ x 3 ∧ 0 ≤ y14 ∧ y24 ≤ x 3 ∧ 0 ≤ y24 ∧ y34 ≤ x 3 ∧ 0 ≤ y34 := by
  -- Route correction: dispatch to the concrete explicit-column lemmas instead of proving
  -- arithmetic through the indexed `match` layer.
  fin_cases i
  · have hvec :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 1 =
          ![x 0, x 0, y12, y13, y14] := by
      simpa using
        lovasz_schrijver_example_10_5_column_vector_eq x y12 y13 y14 y23 y24 y34 (0 : Fin 4)
    simpa [hvec] using lovasz_schrijver_example_10_5_first_lifted_column_cone_iff x y12 y13 y14
  · have hvec :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 2 =
          ![x 1, y12, x 1, y23, y24] := by
      simpa using
        lovasz_schrijver_example_10_5_column_vector_eq x y12 y13 y14 y23 y24 y34 (1 : Fin 4)
    simpa [hvec] using lovasz_schrijver_example_10_5_second_lifted_column_cone_iff x y12 y23 y24
  · have hvec :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 3 =
          ![x 2, y13, y23, x 2, y34] := by
      simpa using
        lovasz_schrijver_example_10_5_column_vector_eq x y12 y13 y14 y23 y24 y34 (2 : Fin 4)
    simpa [hvec] using lovasz_schrijver_example_10_5_third_lifted_column_cone_iff x y13 y23 y34
  · have hvec :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ lifted_basis 4 =
          ![x 3, y14, y24, y34, x 3] := by
      simpa using
        lovasz_schrijver_example_10_5_column_vector_eq x y12 y13 y14 y23 y24 y34 (3 : Fin 4)
    simpa [hvec] using lovasz_schrijver_example_10_5_fourth_lifted_column_cone_iff x y14 y24 y34

/-- Helper for Example 10.5: each complementary lifted column lies in the homogenized cone exactly
when the matching complementary primary inequality and incident McCormick constraints hold. -/
lemma lovasz_schrijver_example_10_5_difference_column_cone_block_iff
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) (i : Fin 4) :
    lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
        (lifted_basis 0 - lifted_basis i.succ) ∈
          homogenized_cone lovasz_schrijver_example_10_5_polytope ↔
      match i.1 with
      | 0 =>
          3 * x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3 + 2 * y12 - 4 * y13 - 5 * y14 ≥ 3 ∧
            y12 ≤ x 1 ∧ 1 - x 0 - x 1 + y12 ≥ 0 ∧
              y13 ≤ x 2 ∧ 1 - x 0 - x 2 + y13 ≥ 0 ∧
                y14 ≤ x 3 ∧ 1 - x 0 - x 3 + y14 ≥ 0
      | 1 =>
          x 0 + 3 * x 1 + 4 * x 2 + 5 * x 3 - y12 - 4 * y23 - 5 * y24 ≥ 3 ∧
            y12 ≤ x 0 ∧ 1 - x 0 - x 1 + y12 ≥ 0 ∧
              y23 ≤ x 2 ∧ 1 - x 1 - x 2 + y23 ≥ 0 ∧
                y24 ≤ x 3 ∧ 1 - x 1 - x 3 + y24 ≥ 0
      | 2 =>
          x 0 - 2 * x 1 + 3 * x 2 + 5 * x 3 - y13 + 2 * y23 - 5 * y34 ≥ 3 ∧
            y13 ≤ x 0 ∧ 1 - x 0 - x 2 + y13 ≥ 0 ∧
              y23 ≤ x 1 ∧ 1 - x 1 - x 2 + y23 ≥ 0 ∧
                y34 ≤ x 3 ∧ 1 - x 2 - x 3 + y34 ≥ 0
      | _ =>
          x 0 - 2 * x 1 + 4 * x 2 + 3 * x 3 - y14 + 2 * y24 - 4 * y34 ≥ 3 ∧
            y14 ≤ x 0 ∧ 1 - x 0 - x 3 + y14 ≥ 0 ∧
              y24 ≤ x 1 ∧ 1 - x 1 - x 3 + y24 ≥ 0 ∧
                y34 ≤ x 2 ∧ 1 - x 2 - x 3 + y34 ≥ 0 := by
  -- Route correction: dispatch to the concrete explicit complementary-column lemmas instead of
  -- proving arithmetic through the indexed `match` layer.
  fin_cases i
  · have hvec :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
            (lifted_basis 0 - lifted_basis 1) =
          ![1 - x 0, 0, x 1 - y12, x 2 - y13, x 3 - y14] := by
      simpa using
        lovasz_schrijver_example_10_5_difference_column_vector_eq x y12 y13 y14 y23 y24 y34
          (0 : Fin 4)
    simpa [hvec] using
      lovasz_schrijver_example_10_5_first_complementary_column_cone_iff x y12 y13 y14
  · have hvec :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
            (lifted_basis 0 - lifted_basis 2) =
          ![1 - x 1, x 0 - y12, 0, x 2 - y23, x 3 - y24] := by
      simpa using
        lovasz_schrijver_example_10_5_difference_column_vector_eq x y12 y13 y14 y23 y24 y34
          (1 : Fin 4)
    simpa [hvec] using
      lovasz_schrijver_example_10_5_second_complementary_column_cone_iff x y12 y23 y24
  · have hvec :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
            (lifted_basis 0 - lifted_basis 3) =
          ![1 - x 2, x 0 - y13, x 1 - y23, 0, x 3 - y34] := by
      simpa using
        lovasz_schrijver_example_10_5_difference_column_vector_eq x y12 y13 y14 y23 y24 y34
          (2 : Fin 4)
    simpa [hvec] using
      lovasz_schrijver_example_10_5_third_complementary_column_cone_iff x y13 y23 y34
  · have hvec :
        lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34 *ᵥ
            (lifted_basis 0 - lifted_basis 4) =
          ![1 - x 3, x 0 - y14, x 1 - y24, x 2 - y34, 0] := by
      simpa using
        lovasz_schrijver_example_10_5_difference_column_vector_eq x y12 y13 y14 y23 y24 y34
          (3 : Fin 4)
    simpa [hvec] using
      lovasz_schrijver_example_10_5_fourth_complementary_column_cone_iff x y14 y24 y34

/-- The explicit matrix of Example 10.5 is a Lovasz-Schrijver lift for the example polytope
exactly when the hand-written linearized inequalities hold. This is the bridge from the source
coordinates to the canonical Section 10.3 owner `IsLovaszSchrijverMatrix`. -/
theorem lovasz_schrijver_example_10_5_isLovaszSchrijverMatrix_iff
    (x : Fin 4 → ℝ) (y12 y13 y14 y23 y24 y34 : ℝ) :
    IsLovaszSchrijverMatrix lovasz_schrijver_example_10_5_polytope
      (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34) ↔
        lovasz_schrijver_example_10_5_primary_linearization x y12 y13 y14 y23 y24 y34 ∧
          lovasz_schrijver_example_10_5_pairwise_linearization x y12 y13 y14 y23 y24 y34 := by
  -- Route correction: the matrix proof now passes only through the concrete column packages.
  rw [isLovaszSchrijverMatrix_iff]
  constructor
  · rintro ⟨_, _, hcols, _⟩
    -- Read off the four lifted and four complementary cone blocks.
    have hcol0 :
        -2 * x 0 - 2 * y12 + 4 * y13 + 5 * y14 ≥ 0 ∧
          y12 ≤ x 0 ∧ 0 ≤ y12 ∧ y13 ≤ x 0 ∧ 0 ≤ y13 ∧ y14 ≤ x 0 ∧ 0 ≤ y14 := by
      simpa using
        (lovasz_schrijver_example_10_5_column_cone_block_iff x y12 y13 y14 y23 y24 y34 0).1
          ((hcols 0).1)
    have hdiff0 :
        3 * x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3 + 2 * y12 - 4 * y13 - 5 * y14 ≥ 3 ∧
          y12 ≤ x 1 ∧ 1 - x 0 - x 1 + y12 ≥ 0 ∧
            y13 ≤ x 2 ∧ 1 - x 0 - x 2 + y13 ≥ 0 ∧
              y14 ≤ x 3 ∧ 1 - x 0 - x 3 + y14 ≥ 0 := by
      simpa using
        (lovasz_schrijver_example_10_5_difference_column_cone_block_iff
          x y12 y13 y14 y23 y24 y34 0).1 ((hcols 0).2)
    have hcol1 :
        -5 * x 1 + y12 + 4 * y23 + 5 * y24 ≥ 0 ∧
          y12 ≤ x 1 ∧ 0 ≤ y12 ∧ y23 ≤ x 1 ∧ 0 ≤ y23 ∧ y24 ≤ x 1 ∧ 0 ≤ y24 := by
      simpa using
        (lovasz_schrijver_example_10_5_column_cone_block_iff x y12 y13 y14 y23 y24 y34 1).1
          ((hcols 1).1)
    have hdiff1 :
        x 0 + 3 * x 1 + 4 * x 2 + 5 * x 3 - y12 - 4 * y23 - 5 * y24 ≥ 3 ∧
          y12 ≤ x 0 ∧ 1 - x 0 - x 1 + y12 ≥ 0 ∧
            y23 ≤ x 2 ∧ 1 - x 1 - x 2 + y23 ≥ 0 ∧
              y24 ≤ x 3 ∧ 1 - x 1 - x 3 + y24 ≥ 0 := by
      simpa using
        (lovasz_schrijver_example_10_5_difference_column_cone_block_iff
          x y12 y13 y14 y23 y24 y34 1).1 ((hcols 1).2)
    have hcol2 :
        x 2 + y13 - 2 * y23 + 5 * y34 ≥ 0 ∧
          y13 ≤ x 2 ∧ 0 ≤ y13 ∧ y23 ≤ x 2 ∧ 0 ≤ y23 ∧ y34 ≤ x 2 ∧ 0 ≤ y34 := by
      simpa using
        (lovasz_schrijver_example_10_5_column_cone_block_iff x y12 y13 y14 y23 y24 y34 2).1
          ((hcols 2).1)
    have hdiff2 :
        x 0 - 2 * x 1 + 3 * x 2 + 5 * x 3 - y13 + 2 * y23 - 5 * y34 ≥ 3 ∧
          y13 ≤ x 0 ∧ 1 - x 0 - x 2 + y13 ≥ 0 ∧
            y23 ≤ x 1 ∧ 1 - x 1 - x 2 + y23 ≥ 0 ∧
              y34 ≤ x 3 ∧ 1 - x 2 - x 3 + y34 ≥ 0 := by
      simpa using
        (lovasz_schrijver_example_10_5_difference_column_cone_block_iff
          x y12 y13 y14 y23 y24 y34 2).1 ((hcols 2).2)
    have hcol3 :
        2 * x 3 + y14 - 2 * y24 + 4 * y34 ≥ 0 ∧
          y14 ≤ x 3 ∧ 0 ≤ y14 ∧ y24 ≤ x 3 ∧ 0 ≤ y24 ∧ y34 ≤ x 3 ∧ 0 ≤ y34 := by
      simpa using
        (lovasz_schrijver_example_10_5_column_cone_block_iff x y12 y13 y14 y23 y24 y34 3).1
          ((hcols 3).1)
    have hdiff3 :
        x 0 - 2 * x 1 + 4 * x 2 + 3 * x 3 - y14 + 2 * y24 - 4 * y34 ≥ 3 ∧
          y14 ≤ x 0 ∧ 1 - x 0 - x 3 + y14 ≥ 0 ∧
            y24 ≤ x 1 ∧ 1 - x 1 - x 3 + y24 ≥ 0 ∧
              y34 ≤ x 2 ∧ 1 - x 2 - x 3 + y34 ≥ 0 := by
      simpa using
        (lovasz_schrijver_example_10_5_difference_column_cone_block_iff
          x y12 y13 y14 y23 y24 y34 3).1 ((hcols 3).2)
    rcases hcol0 with ⟨hp1, h12_x0, h12_nonneg, h13_x0, h13_nonneg, h14_x0, h14_nonneg⟩
    rcases hdiff0 with ⟨hp2, h12_x1, h12_shift, h13_x2, h13_shift, h14_x3, h14_shift⟩
    rcases hcol1 with ⟨hp3, _, _, h23_x1, h23_nonneg, h24_x1, h24_nonneg⟩
    rcases hdiff1 with ⟨hp4, _, _, h23_x2, h23_shift, h24_x3, h24_shift⟩
    rcases hcol2 with ⟨hp5, h13_x2', _, h23_x2', _, h34_x2, h34_nonneg⟩
    rcases hdiff2 with ⟨hp6, h13_x0', h13_shift', h23_x1', h23_shift', h34_x3, h34_shift⟩
    rcases hcol3 with ⟨hp7, h14_x3', _, h24_x3', _, h34_x3', _⟩
    rcases hdiff3 with ⟨hp8, h14_x0', h14_shift', h24_x1', h24_shift', h34_x2', h34_shift'⟩
    -- Recover the four box upper bounds from the complementary blocks, as in the source route.
    have hx0_le_one : x 0 ≤ 1 := by
      linarith
    have hx1_le_one : x 1 ≤ 1 := by
      linarith
    have hx2_le_one : x 2 ≤ 1 := by
      linarith
    have hx3_le_one : x 3 ≤ 1 := by
      linarith
    refine
      ⟨⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩,
        h12_shift, h12_x0, h12_x1, h12_nonneg, h13_shift, h13_x0', h13_x2', h13_nonneg,
        h14_shift, h14_x0', h14_x3', h14_nonneg, h23_shift, h23_x1', h23_x2', h23_nonneg,
        h24_shift, h24_x1', h24_x3', h24_nonneg, h34_shift, h34_x2', h34_x3, h34_nonneg,
        hx0_le_one, hx1_le_one, hx2_le_one, hx3_le_one⟩
  · rintro ⟨hprimary, hpairwise⟩
    rcases hprimary with ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩
    rcases hpairwise with
      ⟨h12_shift, h12_x0, h12_x1, h12_nonneg, h13_shift, h13_x0, h13_x2, h13_nonneg,
        h14_shift, h14_x0, h14_x3, h14_nonneg, h23_shift, h23_x1, h23_x2, h23_nonneg,
        h24_shift, h24_x1, h24_x3, h24_nonneg, h34_shift, h34_x2, h34_x3, h34_nonneg,
        hx0_le_one, hx1_le_one, hx2_le_one, hx3_le_one⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The specialized matrix is symmetric by inspection of its entries.
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · -- The first column is the homogenized point, so the cone test reduces to the original box
      -- and row inequalities for `x`.
      rw [lovasz_schrijver_example_10_5_Y_mulVec_lifted_basis_zero,
        mem_homogenized_cone_lovasz_schrijver_example_10_5_polytope_iff]
      have hx0_nonneg : 0 ≤ x 0 := by
        linarith
      have hx1_nonneg : 0 ≤ x 1 := by
        linarith
      have hx2_nonneg : 0 ≤ x 2 := by
        linarith
      have hx3_nonneg : 0 ≤ x 3 := by
        linarith
      have hrow : x 0 - 2 * x 1 + 4 * x 2 + 5 * x 3 ≥ 3 := by
        linarith
      refine ⟨zero_le_one, ⟨hx0_nonneg, hx0_le_one⟩, ⟨hx1_nonneg, hx1_le_one⟩,
        ⟨hx2_nonneg, hx2_le_one⟩, ⟨hx3_nonneg, hx3_le_one⟩, ?_⟩
      simpa [homogenized_point] using hrow
    · -- Dispatch the four lifted and four complementary cone clauses to the concrete wrappers.
      intro i
      fin_cases i
      · constructor
        · simpa using
            (lovasz_schrijver_example_10_5_column_cone_block_iff x y12 y13 y14 y23 y24 y34 0).2
              ⟨hp1, h12_x0, h12_nonneg, h13_x0, h13_nonneg, h14_x0, h14_nonneg⟩
        · simpa using
            (lovasz_schrijver_example_10_5_difference_column_cone_block_iff
              x y12 y13 y14 y23 y24 y34 0).2
              ⟨hp2, h12_x1, h12_shift, h13_x2, h13_shift, h14_x3, h14_shift⟩
      · constructor
        · simpa using
            (lovasz_schrijver_example_10_5_column_cone_block_iff x y12 y13 y14 y23 y24 y34 1).2
              ⟨hp3, h12_x1, h12_nonneg, h23_x1, h23_nonneg, h24_x1, h24_nonneg⟩
        · simpa using
            (lovasz_schrijver_example_10_5_difference_column_cone_block_iff
              x y12 y13 y14 y23 y24 y34 1).2
              ⟨hp4, h12_x0, h12_shift, h23_x2, h23_shift, h24_x3, h24_shift⟩
      · constructor
        · simpa using
            (lovasz_schrijver_example_10_5_column_cone_block_iff x y12 y13 y14 y23 y24 y34 2).2
              ⟨hp5, h13_x2, h13_nonneg, h23_x2, h23_nonneg, h34_x2, h34_nonneg⟩
        · simpa using
            (lovasz_schrijver_example_10_5_difference_column_cone_block_iff
              x y12 y13 y14 y23 y24 y34 2).2
              ⟨hp6, h13_x0, h13_shift, h23_x1, h23_shift, h34_x3, h34_shift⟩
      · constructor
        · simpa using
            (lovasz_schrijver_example_10_5_column_cone_block_iff x y12 y13 y14 y23 y24 y34 3).2
              ⟨hp7, h14_x3, h14_nonneg, h24_x3, h24_nonneg, h34_x3, h34_nonneg⟩
        · simpa using
            (lovasz_schrijver_example_10_5_difference_column_cone_block_iff
              x y12 y13 y14 y23 y24 y34 3).2
              ⟨hp8, h14_x0, h14_shift, h24_x1, h24_shift, h34_x2, h34_shift⟩
    · -- The diagonal entries coincide with the first-column coordinates by construction.
      intro i
      fin_cases i <;> rfl

/-- Helper for Example 10.5: a canonical witness matrix is determined by its first column,
symmetry, and the diagonal-equals-first-column conditions. -/
lemma lovasz_schrijver_example_10_5_Y_eq_of_canonical_data
    (x : Fin 4 → ℝ) (Y : Matrix (Fin 5) (Fin 5) ℝ)
    (hsymm : Yᵀ = Y)
    (hfirst : Y *ᵥ lifted_basis 0 = homogenized_point x)
    (hdiag : ∀ i : Fin 4, Y i.succ i.succ = Y i.succ 0) :
    Y = lovasz_schrijver_example_10_5_Y x (Y 1 2) (Y 1 3) (Y 1 4) (Y 2 3) (Y 2 4) (Y 3 4) := by
  have hbasis0 : lifted_basis (0 : Fin 5) = Pi.single 0 (1 : ℝ) := by
    funext i
    fin_cases i <;> simp [lifted_basis]
  have hfirst_col : Y.col 0 = homogenized_point x := by
    simpa [hbasis0] using
      (show Y *ᵥ lifted_basis 0 = homogenized_point x from hfirst)
  have hcol0_apply (i : Fin 5) : Y i 0 = (homogenized_point x) i := by
    simpa using congrFun hfirst_col i
  have hsymm_apply (i j : Fin 5) : Y i j = Y j i := by
    have hij := congrFun (congrFun hsymm i) j
    simpa [Matrix.transpose_apply] using hij.symm
  have h00 : Y 0 0 = 1 := by
    simpa [homogenized_point] using hcol0_apply 0
  have h10 : Y 1 0 = x 0 := by
    simpa [homogenized_point] using hcol0_apply 1
  have h20 : Y 2 0 = x 1 := by
    simpa [homogenized_point] using hcol0_apply 2
  have h30 : Y 3 0 = x 2 := by
    simpa [homogenized_point] using hcol0_apply 3
  have h40 : Y 4 0 = x 3 := by
    simpa [homogenized_point] using hcol0_apply 4
  have h02 : Y 0 2 = x 1 := by
    simpa [h20] using hsymm_apply 0 2
  have h03 : Y 0 3 = x 2 := by
    simpa [h30] using hsymm_apply 0 3
  have h04 : Y 0 4 = x 3 := by
    simpa [h40] using hsymm_apply 0 4
  have h11 : Y 1 1 = x 0 := by
    have hdiag0 : Y 1 1 = Y 1 0 := by
      simpa using hdiag 0
    exact hdiag0.trans h10
  have h22 : Y 2 2 = x 1 := by
    have hdiag1 : Y 2 2 = Y 2 0 := by
      simpa using hdiag 1
    exact hdiag1.trans h20
  have h33 : Y 3 3 = x 2 := by
    have hdiag2 : Y 3 3 = Y 3 0 := by
      simpa using hdiag 2
    exact hdiag2.trans h30
  have h44 : Y 4 4 = x 3 := by
    have hdiag3 : Y 4 4 = Y 4 0 := by
      simpa using hdiag 3
    exact hdiag3.trans h40
  -- Finite extensionality reduces the reconstruction to checking each entry by cases.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lovasz_schrijver_example_10_5_Y, hsymm_apply, h00, h10, h02, h03, h04,
      h11, h22, h33, h44]

/-- Example 10.5. Membership in the canonical Lovasz-Schrijver relaxation `N₊(P)` is exactly the
existence of off-diagonal variables `yᵢⱼ` making the specialized linearized inequalities and
positive-semidefinite constraint hold for the explicit lifted matrix `Y`. -/
theorem mem_lovasz_schrijver_example_10_5_N_plus_iff
    (x : Fin 4 → ℝ) :
    x ∈ lovasz_schrijver_N_plus lovasz_schrijver_example_10_5_polytope ↔
      ∃ y12 y13 y14 y23 y24 y34 : ℝ,
        lovasz_schrijver_example_10_5_primary_linearization x y12 y13 y14 y23 y24 y34 ∧
          lovasz_schrijver_example_10_5_pairwise_linearization x y12 y13 y14 y23 y24 y34 ∧
            (lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34).PosSemidef := by
  rw [mem_lovasz_schrijver_N_plus_iff]
  constructor
  · rintro ⟨Y, hY, hpsd, hfirst⟩
    rcases (isLovaszSchrijverMatrix_iff _ Y).1 hY with ⟨hsymm, _, _, hdiag⟩
    have hY_eq :
        Y = lovasz_schrijver_example_10_5_Y x (Y 1 2) (Y 1 3) (Y 1 4) (Y 2 3) (Y 2 4) (Y 3 4) := by
      exact lovasz_schrijver_example_10_5_Y_eq_of_canonical_data x Y hsymm hfirst hdiag
    have hY_explicit :
        IsLovaszSchrijverMatrix lovasz_schrijver_example_10_5_polytope
          (lovasz_schrijver_example_10_5_Y x (Y 1 2) (Y 1 3) (Y 1 4) (Y 2 3) (Y 2 4) (Y 3 4)) := by
      rw [← hY_eq]
      exact hY
    have hlin :
        lovasz_schrijver_example_10_5_primary_linearization x (Y 1 2) (Y 1 3) (Y 1 4) (Y 2 3)
            (Y 2 4) (Y 3 4) ∧
          lovasz_schrijver_example_10_5_pairwise_linearization x (Y 1 2) (Y 1 3) (Y 1 4) (Y 2 3)
            (Y 2 4) (Y 3 4) := by
      exact
        (lovasz_schrijver_example_10_5_isLovaszSchrijverMatrix_iff x (Y 1 2) (Y 1 3) (Y 1 4)
          (Y 2 3) (Y 2 4) (Y 3 4)).1 hY_explicit
    have hpsd_explicit :
        (lovasz_schrijver_example_10_5_Y x (Y 1 2) (Y 1 3) (Y 1 4) (Y 2 3) (Y 2 4)
          (Y 3 4)).PosSemidef := by
      rw [← hY_eq]
      exact hpsd
    exact ⟨Y 1 2, Y 1 3, Y 1 4, Y 2 3, Y 2 4, Y 3 4, hlin.1, hlin.2, hpsd_explicit⟩
  · rintro ⟨y12, y13, y14, y23, y24, y34, hprimary, hpairwise, hpsd⟩
    refine ⟨lovasz_schrijver_example_10_5_Y x y12 y13 y14 y23 y24 y34, ?_, hpsd, ?_⟩
    · exact
        (lovasz_schrijver_example_10_5_isLovaszSchrijverMatrix_iff x y12 y13 y14 y23 y24 y34).2
          ⟨hprimary, hpairwise⟩
    · exact lovasz_schrijver_example_10_5_Y_mulVec_lifted_basis_zero x y12 y13 y14 y23 y24 y34

/-- Lemma 10.7 applied to Example 10.5: the canonical pure-integer hull `P_I` is contained in
the Lovasz-Schrijver semidefinite relaxation `N₊(P)`. -/
theorem lovasz_schrijver_example_10_5_pure_integer_hull_subset_N_plus :
    pure_integer_hull lovasz_schrijver_example_10_5_polytope ⊆
      lovasz_schrijver_N_plus lovasz_schrijver_example_10_5_polytope := by
  -- Rewrite the integer hull through the freshly identified `0/1` points.
  rw [pure_integer_hull, lovasz_schrijver_example_10_5_pure_integer_points_eq_zero_one_points]
  exact convexHull_zero_one_points_subset_lovasz_schrijver_N_plus
    lovasz_schrijver_example_10_5_polytope

end Example105
