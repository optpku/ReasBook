/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_definition_6_1_extra_1

section Example63

/-- The integral feasible set of the pure integer program displayed in Example 6.3. -/
def example_6_3_original_feasible : Set (Fin 3 → ℤ) :=
  {x |
    x 0 + x 1 + x 2 ≤ 2 ∧
    x 2 ≤ 2 * x 0 ∧
    x 2 ≤ 2 * x 1 ∧
    2 * x 0 + x 2 ≤ 2 ∧
    -x 0 + x 1 + x 2 ≤ 1 ∧
    0 ≤ x 0 ∧
    0 ≤ x 1 ∧
    0 ≤ x 2}

/-- Helper for Example 6.3: every integral feasible point has third coordinate `0`. -/
lemma example_6_3_thirdCoordinate_eq_zero_of_feasible
    {x : Fin 3 → ℤ} (hx : x ∈ example_6_3_original_feasible) :
    x 2 = 0 := by
  -- Expand the feasible-set inequalities so `omega` can read the integer constraints directly.
  simp only [example_6_3_original_feasible, Set.mem_setOf_eq] at hx
  rcases hx with ⟨hsum, h20, h21, h02, htail, h0, h1, h2⟩
  -- The bounds `x₂ ≤ 2x₁`, `2x₁ + x₂ ≤ 2`, and nonnegativity force `x₃ = x 2` to vanish.
  omega

/-- Helper for Example 6.3: once a point is feasible, its first two coordinates are binary. -/
lemma example_6_3_binaryCoordinates_of_feasible
    {x : Fin 3 → ℤ} (hx : x ∈ example_6_3_original_feasible) :
    (x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1) := by
  -- First collapse the third coordinate to `0`, then bound the first two coordinates in `[0, 1]`.
  have hx2 : x 2 = 0 := example_6_3_thirdCoordinate_eq_zero_of_feasible hx
  simp only [example_6_3_original_feasible, Set.mem_setOf_eq] at hx
  rcases hx with ⟨hsum, h20, h21, h02, htail, h0, h1, h2⟩
  have hx0_bounds : 0 ≤ x 0 ∧ x 0 ≤ 1 := by
    -- The inequality `2 * x₁ + x₃ ≤ 2` becomes `2 * x₁ ≤ 2` after substituting `x₃ = 0`.
    omega
  have hx1_bounds : 0 ≤ x 1 ∧ x 1 ≤ 1 := by
    -- Combining the sum constraint with `-x₁ + x₂ + x₃ ≤ 1` leaves only `x₂ ∈ {0, 1}`.
    omega
  constructor
  · rcases hx0_bounds with ⟨hx0_nonneg, hx0_le⟩
    -- An integer in `[0, 1]` is either `0` or `1`.
    interval_cases hx0 : x 0 <;> simp
  · rcases hx1_bounds with ⟨hx1_nonneg, hx1_le⟩
    -- The same small-interval classification applies to the second coordinate.
    interval_cases hx1 : x 1 <;> simp

/-- Helper for Example 6.3: the coordinate cases enumerate the four listed feasible points. -/
lemma example_6_3_eq_listedPoint_of_coordinate_cases
    {x : Fin 3 → ℤ}
    (hx2 : x 2 = 0)
    (hx0 : x 0 = 0 ∨ x 0 = 1)
    (hx1 : x 1 = 0 ∨ x 1 = 1) :
    x = ![0, 0, 0] ∨
      x = ![1, 0, 0] ∨
      x = ![0, 1, 0] ∨
      x = ![1, 1, 0] := by
  -- Enumerate the binary first-coordinate and second-coordinate cases.
  rcases hx0 with hx0 | hx0 <;> rcases hx1 with hx1 | hx1
  · left
    -- Coordinatewise extensionality identifies the function with the listed vector.
    ext i
    fin_cases i <;> simp [hx0, hx1, hx2]
  · right
    right
    left
    -- This is the `(0,1,0)` listed point.
    ext i
    fin_cases i <;> simp [hx0, hx1, hx2]
  · right
    left
    -- This is the `(1,0,0)` listed point.
    ext i
    fin_cases i <;> simp [hx0, hx1, hx2]
  · right
    right
    right
    -- This is the `(1,1,0)` listed point.
    ext i
    fin_cases i <;> simp [hx0, hx1, hx2]

/-- Helper for Example 6.3: each listed point satisfies the original feasible-system
inequalities. -/
lemma example_6_3_listedPoint_mem_original_feasible
    {x : Fin 3 → ℤ}
    (hx :
      x = ![0, 0, 0] ∨
        x = ![1, 0, 0] ∨
        x = ![0, 1, 0] ∨
        x = ![1, 1, 0]) :
    x ∈ example_6_3_original_feasible := by
  -- Each listed vector satisfies the defining inequalities by direct computation.
  rcases hx with rfl | rfl | rfl | rfl <;> simp [example_6_3_original_feasible]

/-- Example 6.3. The feasible integral points of
`example_6_3_original_feasible` are exactly the four points listed in the text. -/
theorem mem_example_6_3_original_feasible_iff (x : Fin 3 → ℤ) :
    x ∈ example_6_3_original_feasible ↔
      x = ![0, 0, 0] ∨
      x = ![1, 0, 0] ∨
      x = ![0, 1, 0] ∨
      x = ![1, 1, 0] := by
  constructor
  · intro hx
    -- The feasible-set inequalities first force `x₃ = 0`, then force `x₁, x₂ ∈ {0,1}`.
    have hx2 : x 2 = 0 := example_6_3_thirdCoordinate_eq_zero_of_feasible hx
    have hbinary : (x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1) :=
      example_6_3_binaryCoordinates_of_feasible hx
    -- Once the coordinates are classified, only the four listed vectors remain.
    exact example_6_3_eq_listedPoint_of_coordinate_cases hx2 hbinary.1 hbinary.2
  · intro hx
    -- The reverse implication is a direct check on the four explicit feasible points.
    exact example_6_3_listedPoint_mem_original_feasible hx

/-- The tableau right-hand side for the basis realization `(6.6)` of Example 6.3, using the
coordinate order `(x₁, x₂, x₃, x₅, x₇, x₄, x₆, x₈)` so that the basic variables occupy the
first five coordinates and the nonbasic variables are `(x₄, x₆, x₈)`. -/
def example_6_3_barb : Fin 5 → ℚ :=
  fun i ↦
    match i.1 with
    | 0 => 1 / 2
    | 1 => 1 / 2
    | 2 => 1
    | _ => 0

/-- The tableau matrix for the basis realization `(6.6)` of Example 6.3, again ordered as
`(x₁, x₂, x₃, x₅, x₇, x₄, x₆, x₈)`. Only the nonbasic columns `(x₄, x₆, x₈)` are nonzero. -/
def example_6_3_barA : Matrix (Fin 5) (Fin 8) ℚ :=
  fun i j ↦
    match i.1, j.1 with
    | 0, 5 => 1 / 2
    | 0, 7 => -(1 / 2 : ℚ)
    | 1, 5 => 1 / 6
    | 1, 6 => -(1 / 3 : ℚ)
    | 1, 7 => 1 / 6
    | 2, 5 => 1 / 3
    | 2, 6 => 1 / 3
    | 2, 7 => 1 / 3
    | 3, 5 => 2 / 3
    | 3, 6 => -(1 / 3 : ℚ)
    | 3, 7 => -(4 / 3 : ℚ)
    | 4, 5 => -(4 / 3 : ℚ)
    | 4, 6 => -(1 / 3 : ℚ)
    | 4, 7 => 2 / 3
    | _, _ => 0

/-- The Chapter 6 corner polyhedron attached to the basis realization `(6.6)` of Example 6.3,
written in the ordered tableau coordinates `(x₁, x₂, x₃, x₅, x₇, x₄, x₆, x₈)`. -/
def example_6_3_tableau_corner : Set (Fin 8 → ℝ) :=
  corner_polyhedron (by decide : 5 ≤ 8) Finset.univ example_6_3_barA example_6_3_barb

/-- The projection from the ordered tableau coordinates
`(x₁, x₂, x₃, x₅, x₇, x₄, x₆, x₈)` to the original variables `(x₁, x₂, x₃)`. -/
def example_6_3_original_projection : (Fin 8 → ℝ) → Fin 3 → ℝ :=
  fun x ↦ ![x 0, x 1, x 2]

@[simp] theorem example_6_3_original_projection_apply (x : Fin 8 → ℝ) :
    example_6_3_original_projection x = ![x 0, x 1, x 2] := rfl

/-- The projection from the ordered tableau coordinates
`(x₁, x₂, x₃, x₅, x₇, x₄, x₆, x₈)` to the nonbasic variables `(x₄, x₆, x₈)`. -/
def example_6_3_nonbasic_projection : (Fin 8 → ℝ) → Fin 3 → ℝ :=
  fun x ↦ ![x 5, x 6, x 7]

@[simp] theorem example_6_3_nonbasic_projection_apply (x : Fin 8 → ℝ) :
    example_6_3_nonbasic_projection x = ![x 5, x 6, x 7] := rfl

/-- In the original variables `(x₁,x₂,x₃)`, the corner polyhedron `corner(B)` of Example 6.3 is
exactly the polyhedron cut out by the four displayed inequalities
`x₃ ≤ 0`, `x₂ - 1/2 x₃ ≥ 0`, `x₁ + 1/2 x₃ ≤ 1`, and `-x₁ + x₂ + x₃ ≤ 1`. -/
def example_6_3_corner : Set (Fin 3 → ℝ) :=
  {x | x 2 ≤ 0} ∩
    {x | x 2 ≤ 2 * x 1} ∩
      {x | 2 * x 0 + x 2 ≤ 2} ∩
        {x | -x 0 + x 1 + x 2 ≤ 1}

/-- Membership in the original-variable view of Example 6.3's corner polyhedron is equivalent to
the four displayed inequalities
`x₃ ≤ 0`, `x₂ - 1/2 x₃ ≥ 0`, `x₁ + 1/2 x₃ ≤ 1`, and `-x₁ + x₂ + x₃ ≤ 1`. -/
theorem mem_example_6_3_corner_iff (x : Fin 3 → ℝ) :
    x ∈ example_6_3_corner ↔
      x 2 ≤ 0 ∧
      x 2 ≤ 2 * x 1 ∧
      2 * x 0 + x 2 ≤ 2 ∧
      -x 0 + x 1 + x 2 ≤ 1 :=
  by
    simp [example_6_3_corner, and_assoc]

end Example63
