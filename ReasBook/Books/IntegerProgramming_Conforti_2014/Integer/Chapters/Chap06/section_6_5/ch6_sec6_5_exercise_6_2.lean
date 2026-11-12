/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_example_6_3

open scoped BigOperators

-- This file is a bridge/view: Exercise 6.2 reads the Example 6.3 corner polyhedron in the
-- nonbasic coordinates `(x₄, x₆, x₈)`, so the owner remains the specialized Example 6.3 corner
-- polyhedron and this file records its projected coordinate description.

section Exercise62

/-- The displayed corner polyhedron for Exercise 6.2. In the nonbasic coordinates
`(x₄, x₆, x₈)` corresponding to the basis `(x₁, x₂, x₃, x₅, x₇)`, the corner polyhedron of
Example 6.3 is cut out by the minimal system `x₄ ≥ 0`, `x₆ ≥ 0`, `x₈ ≥ 0`, `x₄ + x₈ ≥ 1`, and
`x₄ + x₆ + x₈ ≥ 3`. -/
def exercise_6_2_corner : Set (Fin 3 → ℝ) :=
  {x |
    0 ≤ x 0 ∧
    0 ≤ x 1 ∧
    0 ≤ x 2 ∧
    1 ≤ x 0 + x 2 ∧
    3 ≤ x 0 + x 1 + x 2}

/-- Membership in `exercise_6_2_corner` is exactly the displayed minimal system of inequalities
for the `(x₄, x₆, x₈)` corner polyhedron. -/
theorem mem_exercise_6_2_corner_iff (x : Fin 3 → ℝ) :
    x ∈ exercise_6_2_corner ↔
      0 ≤ x 0 ∧
      0 ≤ x 1 ∧
      0 ≤ x 2 ∧
      1 ≤ x 0 + x 2 ∧
      3 ≤ x 0 + x 1 + x 2 :=
  Iff.rfl

/-- Helper for Exercise 6.2: the tableau point determined by the three integral basic variables
`(x₁, x₂, x₃) = (a, b, c)` in the basis realization of Example 6.3. -/
def exercise_6_2_tableauPoint (a b c : ℤ) : Fin 8 → ℝ :=
  ![
    (a : ℝ),
    (b : ℝ),
    (c : ℝ),
    (2 * a - c : ℤ),
    (2 - 2 * a - c : ℤ),
    (2 - a - b - c : ℤ),
    (2 * b - c : ℤ),
    (1 + a - b - c : ℤ)
  ]

/-- Helper for Exercise 6.2: the projected nonbasic lattice points are exactly the explicit
integer-parameter family obtained from the first three basic coordinates. -/
def exercise_6_2_projectedLattice : Set (Fin 3 → ℝ) :=
  {y |
    0 ≤ y 0 ∧
    0 ≤ y 1 ∧
    0 ≤ y 2 ∧
    ∃ a b c : ℤ,
      y = ![
        ((2 - a - b - c : ℤ) : ℝ),
        ((2 * b - c : ℤ) : ℝ),
        ((1 + a - b - c : ℤ) : ℝ)
      ]}

/-- Helper for Exercise 6.2: any integer triple `(a,b,c)` whose projected coordinates are
nonnegative contributes the corresponding point to `exercise_6_2_projectedLattice`. -/
lemma exercise_6_2_mem_projectedLattice_of_witness
    {a b c : ℤ}
    (hy0 : 0 ≤ (2 - a - b - c : ℤ))
    (hy1 : 0 ≤ (2 * b - c : ℤ))
    (hy2 : 0 ≤ (1 + a - b - c : ℤ)) :
    ![
      ((2 - a - b - c : ℤ) : ℝ),
      ((2 * b - c : ℤ) : ℝ),
      ((1 + a - b - c : ℤ) : ℝ)
    ] ∈ exercise_6_2_projectedLattice := by
  -- The three displayed coordinates are nonnegative and are witnessed by the same integer triple.
  refine ⟨?_, ?_, ?_, a, b, c, rfl⟩
  · simpa using (show (0 : ℝ) ≤ ((2 - a - b - c : ℤ) : ℝ) from by exact_mod_cast hy0)
  · simpa using (show (0 : ℝ) ≤ ((2 * b - c : ℤ) : ℝ) from by exact_mod_cast hy1)
  · simpa using (show (0 : ℝ) ≤ ((1 + a - b - c : ℤ) : ℝ) from by exact_mod_cast hy2)

/-- Helper for Exercise 6.2: the tableau point attached to `(a, b, c)` projects to the expected
nonbasic coordinate triple `(x₄, x₆, x₈)`. -/
lemma exercise_6_2_nonbasic_projection_tableauPoint (a b c : ℤ) :
    example_6_3_nonbasic_projection (exercise_6_2_tableauPoint a b c) =
      ![
        ((2 - a - b - c : ℤ) : ℝ),
        ((2 * b - c : ℤ) : ℝ),
        ((1 + a - b - c : ℤ) : ℝ)
      ] := by
  -- The nonbasic projection just reads off coordinates `5`, `6`, and `7`.
  ext i
  fin_cases i <;> simp [exercise_6_2_tableauPoint, example_6_3_nonbasic_projection]

/-- Helper for Exercise 6.2: whenever the nonbasic coordinates are nonnegative, the explicit
tableau point lies in Gomory's relaxation for Example 6.3. -/
lemma exercise_6_2_tableauPoint_mem_gomoryCornerRelaxation
    {a b c : ℤ}
    (hy0 : 0 ≤ (2 - a - b - c : ℤ))
    (hy1 : 0 ≤ (2 * b - c : ℤ))
    (hy2 : 0 ≤ (1 + a - b - c : ℤ)) :
    exercise_6_2_tableauPoint a b c ∈
      gomory_corner_relaxation (by decide : 5 ≤ 8) Finset.univ
        example_6_3_barA example_6_3_barb := by
  -- Expand the relaxation membership into the tableau equations, integrality, and nonbasic
  -- nonnegativity obligations.
  have hN :
      corner_nonbasic_indices (by decide : 5 ≤ 8) Finset.univ =
        ({5, 6, 7} : Finset (Fin 8)) := by
    ext j
    fin_cases j <;> decide
  rw [mem_gomory_corner_relaxation_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Each tableau row is a direct computation in the explicit Example 6.3 matrix.
    intro i hi
    rw [hN]
    fin_cases i <;>
      simp [exercise_6_2_tableauPoint, example_6_3_barA, example_6_3_barb] <;>
      linarith
  · -- The first five coordinates are integer by construction.
    intro i
    fin_cases i
    · exact ⟨a, by simp [exercise_6_2_tableauPoint]⟩
    · exact ⟨b, by simp [exercise_6_2_tableauPoint]⟩
    · exact ⟨c, by simp [exercise_6_2_tableauPoint]⟩
    · exact ⟨2 * a - c, by simp [exercise_6_2_tableauPoint]⟩
    · exact ⟨2 - 2 * a - c, by simp [exercise_6_2_tableauPoint]⟩
  · -- Only coordinates `5`, `6`, and `7` are constrained to be nonnegative.
    intro j hj
    rw [hN] at hj
    fin_cases j
    · simp at hj
    · simp at hj
    · simp at hj
    · simp at hj
    · simp at hj
    · simpa [exercise_6_2_tableauPoint] using
        (show (0 : ℝ) ≤ ((2 - a - b - c : ℤ) : ℝ) from by exact_mod_cast hy0)
    · simpa [exercise_6_2_tableauPoint] using
        (show (0 : ℝ) ≤ ((2 * b - c : ℤ) : ℝ) from by exact_mod_cast hy1)
    · simpa [exercise_6_2_tableauPoint] using
        (show (0 : ℝ) ≤ ((1 + a - b - c : ℤ) : ℝ) from by exact_mod_cast hy2)

/-- Helper for Exercise 6.2: the nonbasic image of Gomory's relaxation is exactly the explicit
projected lattice set determined by the integer basic coordinates. -/
lemma exercise_6_2_nonbasicImage_gomoryRelaxation_eq_projectedLattice :
    example_6_3_nonbasic_projection ''
        gomory_corner_relaxation (by decide : 5 ≤ 8) Finset.univ example_6_3_barA
          example_6_3_barb =
      exercise_6_2_projectedLattice := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_gomory_corner_relaxation_iff] at hx
    rcases hx with ⟨hx_eq, hx_int, hx_nonneg⟩
    have hN :
        corner_nonbasic_indices (by decide : 5 ≤ 8) Finset.univ =
          ({5, 6, 7} : Finset (Fin 8)) := by
      ext j
      fin_cases j <;> decide
    rcases hx_int 0 with ⟨a, ha⟩
    rcases hx_int 1 with ⟨b, hb⟩
    rcases hx_int 2 with ⟨c, hc⟩
    have ha0 : x 0 = (a : ℝ) := by
      simpa using ha
    have hb1 : x 1 = (b : ℝ) := by
      simpa using hb
    have hc2 : x 2 = (c : ℝ) := by
      simpa using hc
    have hy0 : 0 ≤ x 5 := hx_nonneg 5 (by decide)
    have hy1 : 0 ≤ x 6 := hx_nonneg 6 (by decide)
    have hy2 : 0 ≤ x 7 := hx_nonneg 7 (by decide)
    have hrow0 :
        x 0 = (1 / 2 : ℝ) - ((1 / 2 : ℝ) * x 5 + -((1 / 2 : ℝ) * x 7)) := by
      simpa [hN, example_6_3_barA, example_6_3_barb] using hx_eq 0 (by simp)
    have hrow0' :
        x 0 = (1 / 2 : ℝ) - (1 / 2 : ℝ) * x 5 + (1 / 2 : ℝ) * x 7 := by
      linarith
    have hrow1 :
        x 1 =
          (1 / 2 : ℝ) -
            ((1 / 6 : ℝ) * x 5 + (-((1 / 3 : ℝ) * x 6) + (1 / 6 : ℝ) * x 7)) := by
      simpa [hN, example_6_3_barA, example_6_3_barb] using hx_eq 1 (by simp)
    have hrow1' :
        x 1 =
          (1 / 2 : ℝ) - (1 / 6 : ℝ) * x 5 + (1 / 3 : ℝ) * x 6 - (1 / 6 : ℝ) * x 7 := by
      linarith
    have hrow2 :
        x 2 =
          (1 : ℝ) - ((1 / 3 : ℝ) * x 5 + ((1 / 3 : ℝ) * x 6 + (1 / 3 : ℝ) * x 7)) := by
      simpa [hN, example_6_3_barA, example_6_3_barb] using hx_eq 2 (by simp)
    have hrow2' :
        x 2 =
          (1 : ℝ) - (1 / 3 : ℝ) * x 5 - (1 / 3 : ℝ) * x 6 - (1 / 3 : ℝ) * x 7 := by
      linarith
    have hrow0z : x 7 = 2 * (a : ℝ) + x 5 - 1 := by
      nlinarith [ha0, hrow0']
    have hrow1z : 6 * (b : ℝ) = 3 - x 5 + 2 * x 6 - x 7 := by
      nlinarith [hb1, hrow1']
    have hrow2z : x 6 = 3 - 3 * (c : ℝ) - x 5 - x 7 := by
      nlinarith [hc2, hrow2']
    have hx5R : x 5 = 2 - (a : ℝ) - (b : ℝ) - (c : ℝ) := by
      linarith [hrow0z, hrow1z, hrow2z]
    have hx7R : x 7 = 1 + (a : ℝ) - (b : ℝ) - (c : ℝ) := by
      linarith [hrow0z, hx5R]
    have hx6R : x 6 = 2 * (b : ℝ) - (c : ℝ) := by
      linarith [hrow2z, hx5R, hx7R]
    have hx5 : x 5 = ((2 - a - b - c : ℤ) : ℝ) := by
      calc
        x 5 = 2 - (a : ℝ) - (b : ℝ) - (c : ℝ) := hx5R
        _ = ((2 - a - b - c : ℤ) : ℝ) := by
              norm_num
    have hx6 : x 6 = ((2 * b - c : ℤ) : ℝ) := by
      calc
        x 6 = 2 * (b : ℝ) - (c : ℝ) := hx6R
        _ = ((2 * b - c : ℤ) : ℝ) := by
              norm_num
    have hx7 : x 7 = ((1 + a - b - c : ℤ) : ℝ) := by
      calc
        x 7 = 1 + (a : ℝ) - (b : ℝ) - (c : ℝ) := hx7R
        _ = ((1 + a - b - c : ℤ) : ℝ) := by
              norm_num
    refine ⟨?_, ?_, ?_, a, b, c, ?_⟩
    · simpa [example_6_3_nonbasic_projection] using hy0
    · simpa [example_6_3_nonbasic_projection] using hy1
    · simpa [example_6_3_nonbasic_projection] using hy2
    · ext i
      fin_cases i <;> simp [example_6_3_nonbasic_projection, hx5, hx6, hx7]
  · intro hy
    rcases hy with ⟨hy0, hy1, hy2, a, b, c, rfl⟩
    have hy0R : (0 : ℝ) ≤ ((2 - a - b - c : ℤ) : ℝ) := by
      simpa using hy0
    have hy1R : (0 : ℝ) ≤ ((2 * b - c : ℤ) : ℝ) := by
      simpa using hy1
    have hy2R : (0 : ℝ) ≤ ((1 + a - b - c : ℤ) : ℝ) := by
      simpa using hy2
    have hy0Z : 0 ≤ (2 - a - b - c : ℤ) := by
      exact_mod_cast hy0R
    have hy1Z : 0 ≤ (2 * b - c : ℤ) := by
      exact_mod_cast hy1R
    have hy2Z : 0 ≤ (1 + a - b - c : ℤ) := by
      exact_mod_cast hy2R
    refine ⟨exercise_6_2_tableauPoint a b c, ?_, ?_⟩
    · exact exercise_6_2_tableauPoint_mem_gomoryCornerRelaxation hy0Z hy1Z hy2Z
    · exact exercise_6_2_nonbasic_projection_tableauPoint a b c

/-- Helper for Exercise 6.2: moving the convex-hull definition of the tableau corner through the
nonbasic projection leaves the convex hull of the projected lattice set. -/
lemma exercise_6_2_nonbasicProjection_image_tableauCorner_eq_convexHull_projectedLattice :
    example_6_3_nonbasic_projection '' example_6_3_tableau_corner =
      convexHull ℝ exercise_6_2_projectedLattice := by
  -- Repackage the coordinate projection as a linear map so the image passes through `convexHull`.
  let proj : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := example_6_3_nonbasic_projection
      map_add' := by
        intro x z
        ext i
        fin_cases i <;> simp [example_6_3_nonbasic_projection]
      map_smul' := by
        intro t x
        ext i
        fin_cases i <;> simp [example_6_3_nonbasic_projection] }
  calc
    example_6_3_nonbasic_projection '' example_6_3_tableau_corner
        = proj '' convexHull ℝ
            (gomory_corner_relaxation (by decide : 5 ≤ 8) Finset.univ example_6_3_barA
              example_6_3_barb) := by
              simp [example_6_3_tableau_corner, proj, corner_polyhedron_eq_convexHull]
    _ = convexHull ℝ
          (proj ''
            gomory_corner_relaxation (by decide : 5 ≤ 8) Finset.univ example_6_3_barA
              example_6_3_barb) := by
              simpa using
                (LinearMap.image_convexHull proj
                  (gomory_corner_relaxation (by decide : 5 ≤ 8) Finset.univ example_6_3_barA
                    example_6_3_barb))
    _ = convexHull ℝ exercise_6_2_projectedLattice := by
          have himage :
              proj ''
                  gomory_corner_relaxation (by decide : 5 ≤ 8) Finset.univ example_6_3_barA
                    example_6_3_barb =
                exercise_6_2_projectedLattice := by
            simpa [proj] using exercise_6_2_nonbasicImage_gomoryRelaxation_eq_projectedLattice
          rw [himage]

/-- Helper for Exercise 6.2: every projected lattice point satisfies the displayed inequality
system, so its convex hull lies inside the claimed corner polyhedron. -/
lemma exercise_6_2_projectedLattice_subset_corner :
    exercise_6_2_projectedLattice ⊆ exercise_6_2_corner := by
  intro y hy
  rcases hy with ⟨hy0, hy1, hy2, a, b, c, rfl⟩
  have hy0R : (0 : ℝ) ≤ ((2 - a - b - c : ℤ) : ℝ) := by
    simpa using hy0
  have hy1R : (0 : ℝ) ≤ ((2 * b - c : ℤ) : ℝ) := by
    simpa using hy1
  have hy2R : (0 : ℝ) ≤ ((1 + a - b - c : ℤ) : ℝ) := by
    simpa using hy2
  have hy0Z : 0 ≤ (2 - a - b - c : ℤ) := by
    exact_mod_cast hy0R
  have hy1Z : 0 ≤ (2 * b - c : ℤ) := by
    exact_mod_cast hy1R
  have hy2Z : 0 ≤ (1 + a - b - c : ℤ) := by
    exact_mod_cast hy2R
  have hsumZ : 3 ≤ (3 - 3 * c : ℤ) := by
    omega
  have hbridgeZ : 1 ≤ (3 - 2 * b - 2 * c : ℤ) := by
    omega
  -- The displayed inequalities reduce to linear arithmetic on the integer parameters.
  refine ⟨hy0, hy1, hy2, ?_, ?_⟩
  · have hpairR :
        1 ≤ (((2 - a - b - c : ℤ) : ℝ) + ((1 + a - b - c : ℤ) : ℝ)) := by
      rw [show
        (((2 - a - b - c : ℤ) : ℝ) + ((1 + a - b - c : ℤ) : ℝ)) =
          ((3 - 2 * b - 2 * c : ℤ) : ℝ) by
            norm_num
            ring]
      exact_mod_cast hbridgeZ
    simpa using hpairR
  · have hsumR :
        3 ≤
          (((2 - a - b - c : ℤ) : ℝ) + ((2 * b - c : ℤ) : ℝ) +
            ((1 + a - b - c : ℤ) : ℝ)) := by
      rw [show
        (((2 - a - b - c : ℤ) : ℝ) + ((2 * b - c : ℤ) : ℝ) +
            ((1 + a - b - c : ℤ) : ℝ)) =
          ((3 - 3 * c : ℤ) : ℝ) by
            norm_num
            ring]
      exact_mod_cast hsumZ
    simpa [add_assoc] using hsumR

/-- Helper for Exercise 6.2: the two non-axis vertices on the `3n`-slice come directly from
explicit projected-lattice witnesses. -/
lemma exercise_6_2_threeSliceUpperVertices_mem_projectedLattice
    {n : ℕ} (hn : 0 < n) :
    ![1, (3 * n : ℝ) - 1, 0] ∈ exercise_6_2_projectedLattice ∧
      ![0, (3 * n : ℝ) - 1, 1] ∈ exercise_6_2_projectedLattice := by
  constructor
  · -- The witness `(a,b,c) = (0,n,1-n)` produces the left upper vertex.
    have hmem :=
      exercise_6_2_mem_projectedLattice_of_witness
        (a := 0) (b := (n : ℤ)) (c := (1 - n : ℤ))
        (by omega) (by omega) (by omega)
    have hvec :
        ![1, (3 * n : ℝ) - 1, 0] =
          ![
            ((2 - (0 : ℤ) - (n : ℤ) - (1 - n : ℤ) : ℤ) : ℝ),
            ((2 * (n : ℤ) - (1 - n : ℤ) : ℤ) : ℝ),
            ((1 + (0 : ℤ) - (n : ℤ) - (1 - n : ℤ) : ℤ) : ℝ)
          ] := by
      ext i
      fin_cases i
      · norm_num
      · simp
        ring_nf
      · norm_num
    rw [hvec]
    exact hmem
  · -- The witness `(a,b,c) = (1,n,1-n)` produces the right upper vertex.
    have hmem :=
      exercise_6_2_mem_projectedLattice_of_witness
        (a := 1) (b := (n : ℤ)) (c := (1 - n : ℤ))
        (by omega) (by omega) (by omega)
    have hvec :
        ![0, (3 * n : ℝ) - 1, 1] =
          ![
            ((2 - (1 : ℤ) - (n : ℤ) - (1 - n : ℤ) : ℤ) : ℝ),
            ((2 * (n : ℤ) - (1 - n : ℤ) : ℤ) : ℝ),
            ((1 + (1 : ℤ) - (n : ℤ) - (1 - n : ℤ) : ℤ) : ℝ)
          ] := by
      ext i
      fin_cases i
      · norm_num
      · simp
        ring_nf
      · norm_num
    rw [hvec]
    exact hmem

/-- Helper for Exercise 6.2: the odd `3`-level axis vertices are actual projected-lattice
points. -/
lemma exercise_6_2_threeSliceOddAxisVertices_mem_projectedLattice
    (m : ℕ) :
    ![(6 * m + 3 : ℝ), 0, 0] ∈ exercise_6_2_projectedLattice ∧
      ![0, 0, (6 * m + 3 : ℝ)] ∈ exercise_6_2_projectedLattice := by
  constructor
  · -- The witness `(-3m-1,-m,-2m)` lands on the first axis vertex.
    have hmem :=
      exercise_6_2_mem_projectedLattice_of_witness
        (a := (-((3 * m : ℤ)) - 1 : ℤ)) (b := (-(m : ℤ))) (c := (-(2 * m : ℤ)))
        (by omega) (by omega) (by omega)
    have hvec :
        ![(6 * m + 3 : ℝ), 0, 0] =
          ![
            ((2 - (-((3 * m : ℤ)) - 1 : ℤ) - (-(m : ℤ)) - (-(2 * m : ℤ)) : ℤ) : ℝ),
            ((2 * (-(m : ℤ)) - (-(2 * m : ℤ)) : ℤ) : ℝ),
            ((1 + (-((3 * m : ℤ)) - 1 : ℤ) - (-(m : ℤ)) - (-(2 * m : ℤ)) : ℤ) : ℝ)
          ] := by
      ext i
      fin_cases i <;> norm_num <;> ring
    rw [hvec]
    exact hmem
  · -- The witness `(3m+2,-m,-2m)` lands on the third-coordinate axis vertex.
    have hmem :=
      exercise_6_2_mem_projectedLattice_of_witness
        (a := ((3 * m : ℤ) + 2 : ℤ)) (b := (-(m : ℤ))) (c := (-(2 * m : ℤ)))
        (by omega) (by omega) (by omega)
    have hvec :
        ![0, 0, (6 * m + 3 : ℝ)] =
          ![
            ((2 - ((3 * m : ℤ) + 2 : ℤ) - (-(m : ℤ)) - (-(2 * m : ℤ)) : ℤ) : ℝ),
            ((2 * (-(m : ℤ)) - (-(2 * m : ℤ)) : ℤ) : ℝ),
            ((1 + ((3 * m : ℤ) + 2 : ℤ) - (-(m : ℤ)) - (-(2 * m : ℤ)) : ℤ) : ℝ)
          ] := by
      ext i
      fin_cases i <;> norm_num <;> ring
    rw [hvec]
    exact hmem

/-- Helper for Exercise 6.2: every even `3n` axis vertex is the midpoint of its two neighboring
odd axis vertices, so it already lies in the convex hull of the projected lattice. -/
lemma exercise_6_2_evenAxisVertices_mem_convexHull_projectedLattice
    {m : ℕ} (hm : 0 < m) :
    ![(6 * m : ℝ), 0, 0] ∈ convexHull ℝ exercise_6_2_projectedLattice ∧
      ![0, 0, (6 * m : ℝ)] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
  rcases exercise_6_2_threeSliceOddAxisVertices_mem_projectedLattice (m - 1) with
    ⟨hlowAxis, hlowLifted⟩
  rcases exercise_6_2_threeSliceOddAxisVertices_mem_projectedLattice m with
    ⟨hhighAxis, hhighLifted⟩
  have hcombine :
      ∀ {u v : Fin 3 → ℝ},
        u ∈ convexHull ℝ exercise_6_2_projectedLattice →
        v ∈ convexHull ℝ exercise_6_2_projectedLattice →
        (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v ∈ convexHull ℝ exercise_6_2_projectedLattice := by
    intro u v hu hv
    -- Convexity of the hull closes any midpoint combination of two hull points.
    exact
      (convex_iff_add_mem.mp (convex_convexHull ℝ exercise_6_2_projectedLattice))
        hu hv (by norm_num) (by norm_num) (by norm_num)
  constructor
  · -- The first axis vertex is the midpoint of the adjacent odd first-axis vertices.
    have hmid :
        (1 / 2 : ℝ) • ![6 * ((m - 1 : ℕ) : ℝ) + 3, 0, 0] +
            (1 / 2 : ℝ) • ![(6 * m + 3 : ℝ), 0, 0] ∈
          convexHull ℝ exercise_6_2_projectedLattice := by
      exact
        hcombine
          (subset_convexHull ℝ exercise_6_2_projectedLattice hlowAxis)
          (subset_convexHull ℝ exercise_6_2_projectedLattice hhighAxis)
    have hrepr :
        ![(6 * m : ℝ), 0, 0] =
          (1 / 2 : ℝ) • ![6 * ((m - 1 : ℕ) : ℝ) + 3, 0, 0] +
            (1 / 2 : ℝ) • ![(6 * m + 3 : ℝ), 0, 0] := by
      ext i
      fin_cases i <;> simp
      have hm_pred_nat : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
      have hm_pred : (((m - 1 : ℕ) : ℝ) + 1) = m := by
        exact_mod_cast hm_pred_nat
      nlinarith [hm_pred]
    rw [hrepr]
    exact hmid
  · -- The third-axis vertex is the midpoint of the adjacent odd third-axis vertices.
    have hmid :
        (1 / 2 : ℝ) • ![0, 0, 6 * ((m - 1 : ℕ) : ℝ) + 3] +
            (1 / 2 : ℝ) • ![0, 0, (6 * m + 3 : ℝ)] ∈
          convexHull ℝ exercise_6_2_projectedLattice := by
      exact
        hcombine
          (subset_convexHull ℝ exercise_6_2_projectedLattice hlowLifted)
          (subset_convexHull ℝ exercise_6_2_projectedLattice hhighLifted)
    have hrepr :
        ![0, 0, (6 * m : ℝ)] =
          (1 / 2 : ℝ) • ![0, 0, 6 * ((m - 1 : ℕ) : ℝ) + 3] +
            (1 / 2 : ℝ) • ![0, 0, (6 * m + 3 : ℝ)] := by
      ext i
      fin_cases i <;> simp
      have hm_pred_nat : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
      have hm_pred : (((m - 1 : ℕ) : ℝ) + 1) = m := by
        exact_mod_cast hm_pred_nat
      nlinarith [hm_pred]
    rw [hrepr]
    exact hmid

/-- Helper for Exercise 6.2: every positive `3n` axis vertex belongs to the convex hull of the
projected lattice. Odd levels are direct lattice points, and even levels are midpoints of their
odd neighbors. -/
lemma exercise_6_2_threeSliceAxisVertices_mem_convexHull_projectedLattice
    {n : ℕ} (hn : 0 < n) :
    ![(3 * n : ℝ), 0, 0] ∈ convexHull ℝ exercise_6_2_projectedLattice ∧
      ![0, 0, (3 * n : ℝ)] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨m, rfl⟩
    have hm : 0 < m := by omega
    rcases exercise_6_2_evenAxisVertices_mem_convexHull_projectedLattice hm with
      ⟨haxis, hlifted⟩
    constructor
    · -- The even `3n` case is exactly the midpoint bridge established above.
      convert haxis using 1
      ext i
      fin_cases i
      · simp
        ring_nf
      · simp
      · simp
    · -- The same midpoint bridge handles the third-axis vertex.
      convert hlifted using 1
      ext i
      fin_cases i
      · simp
      · simp
      · simp
        ring_nf
  · rcases hOdd with ⟨m, rfl⟩
    rcases exercise_6_2_threeSliceOddAxisVertices_mem_projectedLattice m with
      ⟨haxis, hlifted⟩
    constructor
    · -- Odd `3n` levels are already lattice points, hence belong to the hull.
      have haxis' :
          ![3 * ((2 * m + 1 : ℕ) : ℝ), 0, 0] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
        convert (subset_convexHull ℝ exercise_6_2_projectedLattice haxis) using 1
        ext i
        fin_cases i
        · simp
          ring_nf
        · simp
        · simp
      exact haxis'
    · -- The third-axis odd case is identical.
      have hlifted' :
          ![0, 0, 3 * ((2 * m + 1 : ℕ) : ℝ)] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
        have hvec :
            ![0, 0, 3 * ((2 * m + 1 : ℕ) : ℝ)] = ![0, 0, (6 * m + 3 : ℝ)] := by
          ext i
          fin_cases i
          · simp
          · simp
          · simp
            ring_nf
        rw [hvec]
        exact subset_convexHull ℝ exercise_6_2_projectedLattice hlifted
      exact hlifted'

/-- Helper for Exercise 6.2: every vertex of the `σ`-slice quadrilateral lies in the convex hull
once `σ` sits between two adjacent `3n` levels. -/
lemma exercise_6_2_sliceVertices_mem_convexHull_of_adjacentThreeLevels
    {σ : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hleft : (3 * n : ℝ) ≤ σ)
    (hright : σ ≤ (3 * (n + 1) : ℝ)) :
    ![σ, 0, 0] ∈ convexHull ℝ exercise_6_2_projectedLattice ∧
      ![1, σ - 1, 0] ∈ convexHull ℝ exercise_6_2_projectedLattice ∧
      ![0, σ - 1, 1] ∈ convexHull ℝ exercise_6_2_projectedLattice ∧
      ![0, 0, σ] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
  let a : ℝ := ((3 * (n + 1) : ℝ) - σ) / 3
  let b : ℝ := (σ - (3 * n : ℝ)) / 3
  have ha_nonneg : 0 ≤ a := by
    -- The left strip inequality makes the lower-level coefficient nonnegative.
    dsimp [a]
    nlinarith
  have hb_nonneg : 0 ≤ b := by
    -- The right strip inequality makes the upper-level coefficient nonnegative.
    dsimp [b]
    nlinarith
  have hab : a + b = 1 := by
    -- The two strip coefficients form a convex pair.
    dsimp [a, b]
    ring
  have hcombine :
      ∀ {u v : Fin 3 → ℝ},
        u ∈ convexHull ℝ exercise_6_2_projectedLattice →
        v ∈ convexHull ℝ exercise_6_2_projectedLattice →
        a • u + b • v ∈ convexHull ℝ exercise_6_2_projectedLattice := by
    intro u v hu hv
    -- All four slice vertices are obtained from one adjacent-level convex combination pattern.
    exact
      (convex_iff_add_mem.mp (convex_convexHull ℝ exercise_6_2_projectedLattice))
        hu hv ha_nonneg hb_nonneg hab
  rcases exercise_6_2_threeSliceAxisVertices_mem_convexHull_projectedLattice hn with
    ⟨haxisLower, hliftedLower⟩
  rcases
      exercise_6_2_threeSliceAxisVertices_mem_convexHull_projectedLattice (Nat.succ_pos n) with
    ⟨haxisUpper, hliftedUpper⟩
  rcases exercise_6_2_threeSliceUpperVertices_mem_projectedLattice hn with
    ⟨hupperLower, hupperLiftedLower⟩
  rcases
      exercise_6_2_threeSliceUpperVertices_mem_projectedLattice (Nat.succ_pos n) with
    ⟨hupperUpper, hupperLiftedUpper⟩
  have haxisUpper' :
      ![(3 * (n + 1) : ℝ), 0, 0] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
    simpa using haxisUpper
  have hliftedUpper' :
      ![0, 0, (3 * (n + 1) : ℝ)] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
    simpa using hliftedUpper
  have hupperUpper' :
      ![1, (3 * (n + 1) : ℝ) - 1, 0] ∈ exercise_6_2_projectedLattice := by
    simpa using hupperUpper
  have hupperLiftedUpper' :
      ![0, (3 * (n + 1) : ℝ) - 1, 1] ∈ exercise_6_2_projectedLattice := by
    simpa using hupperLiftedUpper
  have hσAxis :
      ![σ, 0, 0] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
    -- Interpolate the first-axis endpoints directly in `Fin 3 → ℝ`.
    have hcomboAxis :
        a • ![(3 * n : ℝ), 0, 0] + b • ![(3 * (n + 1) : ℝ), 0, 0] ∈
          convexHull ℝ exercise_6_2_projectedLattice := by
      exact hcombine haxisLower haxisUpper'
    have hrepr :
        ![σ, 0, 0] =
          a • ![(3 * n : ℝ), 0, 0] + b • ![(3 * (n + 1) : ℝ), 0, 0] := by
      ext i
      fin_cases i <;> dsimp [a, b] <;> ring
    simpa [hrepr] using hcomboAxis
  have hσUpper :
      ![1, σ - 1, 0] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
    -- The upper-left vertex uses the same coefficients on the adjacent `3n` upper vertices.
    have hcomboUpper :
        a • ![1, (3 * n : ℝ) - 1, 0] + b • ![1, (3 * (n + 1) : ℝ) - 1, 0] ∈
          convexHull ℝ exercise_6_2_projectedLattice := by
      exact
        hcombine
          (subset_convexHull ℝ exercise_6_2_projectedLattice hupperLower)
          (subset_convexHull ℝ exercise_6_2_projectedLattice hupperUpper')
    have hrepr :
        ![1, σ - 1, 0] =
          a • ![1, (3 * n : ℝ) - 1, 0] + b • ![1, (3 * (n + 1) : ℝ) - 1, 0] := by
      ext i
      fin_cases i <;> dsimp [a, b] <;> ring
    simpa [hrepr] using hcomboUpper
  have hσLifted :
      ![0, σ - 1, 1] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
    -- The upper-right vertex is treated identically on the other non-axis family.
    have hcomboLifted :
        a • ![0, (3 * n : ℝ) - 1, 1] + b • ![0, (3 * (n + 1) : ℝ) - 1, 1] ∈
          convexHull ℝ exercise_6_2_projectedLattice := by
      exact
        hcombine
          (subset_convexHull ℝ exercise_6_2_projectedLattice hupperLiftedLower)
          (subset_convexHull ℝ exercise_6_2_projectedLattice hupperLiftedUpper')
    have hrepr :
        ![0, σ - 1, 1] =
          a • ![0, (3 * n : ℝ) - 1, 1] + b • ![0, (3 * (n + 1) : ℝ) - 1, 1] := by
      ext i
      fin_cases i <;> dsimp [a, b] <;> ring
    simpa [hrepr] using hcomboLifted
  have hσAxisLifted :
      ![0, 0, σ] ∈ convexHull ℝ exercise_6_2_projectedLattice := by
    -- The third-axis endpoints interpolate exactly as the first-axis ones did.
    have hcomboAxisLifted :
        a • ![0, 0, (3 * n : ℝ)] + b • ![0, 0, (3 * (n + 1) : ℝ)] ∈
          convexHull ℝ exercise_6_2_projectedLattice := by
      exact hcombine hliftedLower hliftedUpper'
    have hrepr :
        ![0, 0, σ] =
          a • ![0, 0, (3 * n : ℝ)] + b • ![0, 0, (3 * (n + 1) : ℝ)] := by
      ext i
      fin_cases i <;> dsimp [a, b] <;> ring
    simpa [hrepr] using hcomboAxisLifted
  exact ⟨hσAxis, hσUpper, hσLifted, hσAxisLifted⟩

/-- Helper for Exercise 6.2: every corner point lies in the convex hull of the four vertices of
its fixed-sum slice quadrilateral. -/
lemma exercise_6_2_mem_convexHull_sliceVertices
    {σ : ℝ} {y : Fin 3 → ℝ}
    (hy : y ∈ exercise_6_2_corner)
    (hσ : y 0 + y 1 + y 2 = σ) :
    y ∈ convexHull ℝ
      ({![σ, 0, 0], ![1, σ - 1, 0], ![0, σ - 1, 1], ![0, 0, σ]} : Set (Fin 3 → ℝ)) := by
  rw [mem_exercise_6_2_corner_iff] at hy
  rcases hy with ⟨hy0, hy1, hy2, hy02, hySum⟩
  have hσ_sub_one_pos : 0 < σ - 1 := by
    linarith
  have hy1_le : y 1 ≤ σ - 1 := by
    linarith [hy02, hσ]
  have hσ_sub_y1_pos : 0 < σ - y 1 := by
    linarith [hy02, hσ]
  have hy02sum : y 0 + y 2 = σ - y 1 := by
    linarith
  let lam : ℝ := y 1 / (σ - 1)
  let mu : ℝ := y 2 / (σ - y 1)
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    exact div_nonneg hy1 hσ_sub_one_pos.le
  have hmu_nonneg : 0 ≤ mu := by
    dsimp [mu]
    exact div_nonneg hy2 hσ_sub_y1_pos.le
  have hlam_eq : lam * (σ - 1) = y 1 := by
    dsimp [lam]
    field_simp [hσ_sub_one_pos.ne']
  have hmu_eq : mu * (σ - y 1) = y 2 := by
    dsimp [mu]
    field_simp [hσ_sub_y1_pos.ne']
  have hlam_le : lam ≤ 1 := by
    nlinarith [hlam_eq, hy1_le]
  have hmu_le : mu ≤ 1 := by
    have hy2_le : y 2 ≤ σ - y 1 := by
      linarith [hy0, hσ]
    nlinarith [hmu_eq, hy2_le]
  have hbalance : (1 - lam) * σ + lam = σ - y 1 := by
    linarith
  have hmu_comp : (1 - mu) * (σ - y 1) = y 0 := by
    nlinarith
  let w : Fin 4 → ℝ := fun i =>
    match i with
    | 0 => (1 - lam) * (1 - mu)
    | 1 => lam * (1 - mu)
    | 2 => lam * mu
    | 3 => (1 - lam) * mu
  let z : Fin 4 → Fin 3 → ℝ :=
    ![![σ, 0, 0], ![1, σ - 1, 0], ![0, σ - 1, 1], ![0, 0, σ]]
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · exact mul_nonneg (sub_nonneg.mpr hlam_le) (sub_nonneg.mpr hmu_le)
    · exact mul_nonneg hlam_nonneg (sub_nonneg.mpr hmu_le)
    · exact mul_nonneg hlam_nonneg hmu_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hlam_le) hmu_nonneg
  have hw_sum : ∑ i, w i = 1 := by
    rw [Fin.sum_univ_four]
    dsimp [w]
    ring
  have hz_mem :
      ∀ i, z i ∈ ({![σ, 0, 0], ![1, σ - 1, 0], ![0, σ - 1, 1], ![0, 0, σ]} :
        Set (Fin 3 → ℝ)) := by
    intro i
    fin_cases i <;> simp [z]
  have hrepr : ∑ i, w i • z i = y := by
    ext i
    fin_cases i
    · rw [Fin.sum_univ_four]
      dsimp [w, z]
      calc
        ((1 - lam) * (1 - mu)) * σ + (lam * (1 - mu)) * 1 + (lam * mu) * 0 +
              ((1 - lam) * mu) * 0
            = (1 - mu) * ((1 - lam) * σ + lam) := by ring
        _ = (1 - mu) * (σ - y 1) := by rw [hbalance]
        _ = y 0 := hmu_comp
    · rw [Fin.sum_univ_four]
      dsimp [w, z]
      calc
        ((1 - lam) * (1 - mu)) * 0 + (lam * (1 - mu)) * (σ - 1) + (lam * mu) * (σ - 1) +
              ((1 - lam) * mu) * 0
            = lam * (σ - 1) := by ring
        _ = y 1 := hlam_eq
    · rw [Fin.sum_univ_four]
      dsimp [w, z]
      calc
        ((1 - lam) * (1 - mu)) * 0 + (lam * (1 - mu)) * 0 + (lam * mu) * 1 +
              ((1 - lam) * mu) * σ
            = mu * ((1 - lam) * σ + lam) := by ring
        _ = mu * (σ - y 1) := by rw [hbalance]
        _ = y 2 := hmu_eq
  exact mem_convexHull_of_exists_fintype w z hw_nonneg hw_sum hz_mem hrepr

/-- Helper for Exercise 6.2: the displayed inequality system is convex, since every defining
inequality is preserved by convex combinations. -/
lemma exercise_6_2_corner_convex : Convex ℝ exercise_6_2_corner := by
  intro x hx y hy a b ha hb hab
  rw [mem_exercise_6_2_corner_iff] at hx hy ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Coordinatewise nonnegativity is preserved under convex combinations.
    exact add_nonneg (smul_nonneg ha hx.1) (smul_nonneg hb hy.1)
  · -- The same coordinatewise argument handles the second coordinate.
    exact add_nonneg (smul_nonneg ha hx.2.1) (smul_nonneg hb hy.2.1)
  · -- And likewise for the third coordinate.
    exact add_nonneg (smul_nonneg ha hx.2.2.1) (smul_nonneg hb hy.2.2.1)
  · -- The bridge inequality `1 ≤ x₄ + x₈` is linear in the point.
    have hpair :
        (a • x + b • y) 0 + (a • x + b • y) 2 =
          a * (x 0 + x 2) + b * (y 0 + y 2) := by
      simp
      ring
    rw [hpair]
    have hax : a ≤ a * (x 0 + x 2) := by
      have hmul := mul_le_mul_of_nonneg_left hx.2.2.2.1 ha
      simpa using hmul
    have hby : b ≤ b * (y 0 + y 2) := by
      have hmul := mul_le_mul_of_nonneg_left hy.2.2.2.1 hb
      simpa using hmul
    nlinarith [hax, hby, hab]
  · -- The total-sum inequality is also linear.
    have hsum :
        (a • x + b • y) 0 + (a • x + b • y) 1 + (a • x + b • y) 2 =
          a * (x 0 + x 1 + x 2) + b * (y 0 + y 1 + y 2) := by
      simp
      ring
    rw [hsum]
    have hax : 3 * a ≤ a * (x 0 + x 1 + x 2) := by
      have hmul := mul_le_mul_of_nonneg_left hx.2.2.2.2 ha
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hby : 3 * b ≤ b * (y 0 + y 1 + y 2) := by
      have hmul := mul_le_mul_of_nonneg_left hy.2.2.2.2 hb
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    nlinarith [hax, hby, hab]

/-- Helper for Exercise 6.2: every point of the displayed corner polyhedron lies in the convex
hull of the projected lattice. The proof passes through the four vertices of the point's fixed-sum
slice and then interpolates those vertices between adjacent `3n` levels. -/
lemma exercise_6_2_corner_subset_convexHull_projectedLattice :
    exercise_6_2_corner ⊆ convexHull ℝ exercise_6_2_projectedLattice := by
  intro y hy
  let σ : ℝ := y 0 + y 1 + y 2
  have hσ : y 0 + y 1 + y 2 = σ := rfl
  have hySlice :
      y ∈ convexHull ℝ
        ({![σ, 0, 0], ![1, σ - 1, 0], ![0, σ - 1, 1], ![0, 0, σ]} : Set (Fin 3 → ℝ)) := by
    -- First reduce the corner point to the convex hull of its four fixed-sum slice vertices.
    exact exercise_6_2_mem_convexHull_sliceVertices hy hσ
  rw [mem_exercise_6_2_corner_iff] at hy
  let n : ℕ := ⌊σ / 3⌋₊
  have hn : 0 < n := by
    -- The lower bound `3 ≤ σ` forces the floor index to be positive.
    have hσthird_one : 1 ≤ σ / 3 := by
      dsimp [σ]
      nlinarith [hy.2.2.2.2]
    simpa [n] using (Nat.floor_pos.mpr hσthird_one)
  have hleft : (3 * n : ℝ) ≤ σ := by
    -- The floor value gives the lower adjacent `3n` level.
    have hσthird_nonneg : 0 ≤ σ / 3 := by
      dsimp [σ]
      nlinarith [hy.2.2.2.2]
    have hfloor : (n : ℝ) ≤ σ / 3 := by
      simpa [n] using (Nat.floor_le hσthird_nonneg : ((⌊σ / 3⌋₊ : ℕ) : ℝ) ≤ σ / 3)
    nlinarith
  have hright : σ ≤ (3 * (n + 1) : ℝ) := by
    -- The strict upper floor bound gives the next adjacent `3(n+1)` level.
    have hfloor : σ / 3 < (n : ℝ) + 1 := by
      simpa [n] using (Nat.lt_floor_add_one (σ / 3))
    nlinarith
  rcases exercise_6_2_sliceVertices_mem_convexHull_of_adjacentThreeLevels hn hleft hright with
    ⟨hσAxis, hσUpper, hσLifted, hσAxisLifted⟩
  have hsliceSubset :
      ({![σ, 0, 0], ![1, σ - 1, 0], ![0, σ - 1, 1], ![0, 0, σ]} : Set (Fin 3 → ℝ)) ⊆
        convexHull ℝ exercise_6_2_projectedLattice := by
    intro x hx
    have hx' :
        x = ![σ, 0, 0] ∨
          x = ![1, σ - 1, 0] ∨ x = ![0, σ - 1, 1] ∨ x = ![0, 0, σ] := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    rcases hx' with rfl | rfl | rfl | rfl
    · exact hσAxis
    · exact hσUpper
    · exact hσLifted
    · exact hσAxisLifted
  -- Route correction: the closing step now uses the fixed-sum slice hull plus the adjacent-level
  -- vertex bridge, instead of transporting through `lineMap` or segment membership.
  exact (convexHull_min hsliceSubset (convex_convexHull ℝ exercise_6_2_projectedLattice)) hySlice

/-- Exercise 6.2. The source-facing inequality description is the nonbasic-coordinate view of
Example 6.3's tableau corner polyhedron. -/
theorem exercise_6_2_corner_eq_nonbasic_projection_image :
    exercise_6_2_corner =
      example_6_3_nonbasic_projection '' example_6_3_tableau_corner := by
  -- Route correction: the remaining work is to identify the displayed inequality polyhedron with
  -- the convex hull of the projected lattice, then transport across the projection theorem.
  rw [exercise_6_2_nonbasicProjection_image_tableauCorner_eq_convexHull_projectedLattice]
  refine Set.Subset.antisymm exercise_6_2_corner_subset_convexHull_projectedLattice ?_
  -- The reverse inclusion is the easy convexity direction: the corner contains the projected
  -- lattice and is itself convex.
  exact convexHull_min exercise_6_2_projectedLattice_subset_corner exercise_6_2_corner_convex

end Exercise62
