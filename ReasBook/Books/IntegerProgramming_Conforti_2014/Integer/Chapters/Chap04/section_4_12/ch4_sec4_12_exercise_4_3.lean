/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

-- This exercise reuses the Chapter 4 owner surface for mixed spaces and adds only the
-- exercise-specific supporting-hyperplane notions needed for the counterexample.

section Exercise43

/-- The rational hyperplane `c · x + d · y = δ` in `ℝ^n × ℝ^p`. -/
def mixed_rational_hyperplane
    {n p : ℕ}
    (c : Fin n → ℚ)
    (d : Fin p → ℚ)
    (δ : ℚ) : Set (MixedRealPoint n p) :=
  {xy | mixed_linear_objective (fun i ↦ (c i : ℝ)) (fun j ↦ (d j : ℝ)) xy = (δ : ℝ)}

/-- The rational inequality `c · x + d · y ≤ δ` is valid for `P` when it holds on all points of
`P`. -/
def is_valid_mixed_rational_inequality
    {n p : ℕ}
    (P : Set (MixedRealPoint n p))
    (c : Fin n → ℚ)
    (d : Fin p → ℚ)
    (δ : ℚ) : Prop :=
  ∀ ⦃xy : MixedRealPoint n p⦄,
    xy ∈ P →
      mixed_linear_objective (fun i ↦ (c i : ℝ)) (fun j ↦ (d j : ℝ)) xy ≤ (δ : ℝ)

/-- A rational supporting hyperplane of `P` is the equality hyperplane of a nonzero valid rational
inequality whose equality face on `P` is nonempty. -/
def is_rational_supporting_hyperplane
    {n p : ℕ}
    (P H : Set (MixedRealPoint n p)) : Prop :=
  ∃ c : Fin n → ℚ, ∃ d : Fin p → ℚ, ∃ δ : ℚ,
    (c ≠ 0 ∨ d ≠ 0) ∧
      is_valid_mixed_rational_inequality P c d δ ∧
      (P ∩ mixed_rational_hyperplane c d δ).Nonempty ∧
      H = mixed_rational_hyperplane c d δ

/-- Helper for Exercise 4.3: the `x`-coefficients of the explicit triangle system. -/
def counterexampleA : Matrix (Fin 3) (Fin 1) ℚ := fun i _ ↦ ![-2, 2, 0] i

/-- Helper for Exercise 4.3: the `y`-coefficients of the explicit triangle system. -/
def counterexampleG : Matrix (Fin 3) (Fin 1) ℚ := fun i _ ↦ ![1, 1, -1] i

/-- Helper for Exercise 4.3: the right-hand side of the explicit triangle system. -/
def counterexampleb : Fin 3 → ℚ := ![0, 2, 0]

/-- Helper for Exercise 4.3: the explicit mixed rational polyhedron used as the counterexample. -/
def counterexample_polyhedron : Set (MixedRealPoint 1 1) :=
  rational_mixed_polyhedron counterexampleA counterexampleG counterexampleb

/-- Helper for Exercise 4.3: scalar coordinates packaged as a point of `ℝ × ℝ`. -/
def point (x y : ℝ) : MixedRealPoint 1 1 :=
  (fun _ ↦ x, fun _ ↦ y)

/-- Helper for Exercise 4.3: the horizontal slice cut out by the equation `y = 0`. -/
def zero_height_slice : Set (MixedRealPoint 1 1) :=
  {xy | xy.2 0 = 0}

/-- Helper for Exercise 4.3: on `Fin 1`, the Chapter 4 mixed linear objective with rational
coefficients has one `x`-term and one `y`-term. -/
lemma mixed_linear_objective_rat_fin_one
    (c d : Fin 1 → ℚ) (xy : MixedRealPoint 1 1) :
    mixed_linear_objective (fun i ↦ (c i : ℝ)) (fun j ↦ (d j : ℝ)) xy =
      (c 0 : ℝ) * xy.1 0 + (d 0 : ℝ) * xy.2 0 := by
  -- Collapse both finite sums to their unique coordinate.
  simp [mixed_linear_objective, dotProduct]

/-- Helper for Exercise 4.3: membership in the explicit polyhedron is equivalent to the three
scalar inequalities defining the triangle. -/
lemma mem_counterexample_polyhedron_iff (xy : MixedRealPoint 1 1) :
    xy ∈ counterexample_polyhedron ↔
      0 ≤ xy.2 0 ∧ xy.2 0 ≤ 2 * xy.1 0 ∧ xy.2 0 ≤ 2 - 2 * xy.1 0 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    -- Read the third row as `0 ≤ y`.
    have hy_nonneg : 0 ≤ xy.2 0 := by
      have h2' : -(xy.2 0) ≤ 0 := by
        simpa [counterexample_polyhedron, rational_mixed_polyhedron, counterexampleA,
          counterexampleG, counterexampleb, Matrix.mulVec, dotProduct] using h2
      linarith
    -- Rearrange the first row into the inequality `y ≤ 2x`.
    have hy_le_left : xy.2 0 ≤ 2 * xy.1 0 := by
      norm_num [counterexample_polyhedron, rational_mixed_polyhedron, counterexampleA,
        counterexampleG, counterexampleb, Matrix.mulVec, dotProduct] at h0 ⊢
      linarith
    -- Rearrange the second row into the inequality `y ≤ 2 - 2x`.
    have hy_le_right : xy.2 0 ≤ 2 - 2 * xy.1 0 := by
      norm_num [counterexample_polyhedron, rational_mixed_polyhedron, counterexampleA,
        counterexampleG, counterexampleb, Matrix.mulVec, dotProduct] at h1 ⊢
      linarith
    exact ⟨hy_nonneg, hy_le_left, hy_le_right⟩
  · rintro ⟨hy_nonneg, hy_le_left, hy_le_right⟩ i
    -- Check the three rows of the matrix inequality one at a time.
    fin_cases i
    · norm_num [counterexample_polyhedron, rational_mixed_polyhedron, counterexampleA,
        counterexampleG, counterexampleb, Matrix.mulVec, dotProduct]
      linarith
    · norm_num [counterexample_polyhedron, rational_mixed_polyhedron, counterexampleA,
        counterexampleG, counterexampleb, Matrix.mulVec, dotProduct]
      linarith
    · norm_num [counterexample_polyhedron, rational_mixed_polyhedron, counterexampleA,
        counterexampleG, counterexampleb, Matrix.mulVec, dotProduct]
      linarith

/-- Helper for Exercise 4.3: every point of the explicit triangle has `x`-coordinate in
the interval `[0,1]`. -/
lemma counterexample_x_bounds {xy : MixedRealPoint 1 1}
    (hxy : xy ∈ counterexample_polyhedron) :
    0 ≤ xy.1 0 ∧ xy.1 0 ≤ 1 := by
  -- Combine the two upper bounds on `y` with the lower bound `0 ≤ y`.
  rcases (mem_counterexample_polyhedron_iff xy).1 hxy with ⟨hy_nonneg, hy_le_left, hy_le_right⟩
  constructor <;> linarith

/-- Helper for Exercise 4.3: the left base vertex belongs to the explicit triangle. -/
lemma point_zero_mem_counterexample_polyhedron :
    point 0 0 ∈ counterexample_polyhedron := by
  -- The origin satisfies each defining inequality.
  rw [mem_counterexample_polyhedron_iff]
  norm_num [point]

/-- Helper for Exercise 4.3: the right base vertex belongs to the explicit triangle. -/
lemma point_one_mem_counterexample_polyhedron :
    point 1 0 ∈ counterexample_polyhedron := by
  -- The point `(1,0)` lies on the bottom edge of the triangle.
  rw [mem_counterexample_polyhedron_iff]
  norm_num [point]

/-- Helper for Exercise 4.3: the top vertex `(1/2, 1)` belongs to the explicit triangle. -/
lemma point_top_mem_counterexample_polyhedron :
    point (1 / 2 : ℝ) 1 ∈ counterexample_polyhedron := by
  -- The top vertex satisfies the two slanted inequalities at equality.
  rw [mem_counterexample_polyhedron_iff]
  norm_num [point]

/-- Helper for Exercise 4.3: points with `x = 0` lie in the mixed-integer lattice. -/
lemma point_zero_mem_mixed_integer_lattice (y : ℝ) :
    point 0 y ∈ mixed_integer_lattice 1 1 := by
  -- Witness the integral first coordinate by the constant integer vector `0`.
  change (fun _ : Fin 1 ↦ (0 : ℝ)) ∈
    Set.range (fun z : Fin 1 → ℤ ↦ fun i : Fin 1 ↦ (z i : ℝ))
  refine ⟨fun _ ↦ (0 : ℤ), ?_⟩
  ext i
  fin_cases i
  norm_num [point]

/-- Helper for Exercise 4.3: points with `x = 1` lie in the mixed-integer lattice. -/
lemma point_one_mem_mixed_integer_lattice (y : ℝ) :
    point 1 y ∈ mixed_integer_lattice 1 1 := by
  -- Witness the integral first coordinate by the constant integer vector `1`.
  change (fun _ : Fin 1 ↦ (1 : ℝ)) ∈
    Set.range (fun z : Fin 1 → ℤ ↦ fun i : Fin 1 ↦ (z i : ℝ))
  refine ⟨fun _ ↦ (1 : ℤ), ?_⟩
  ext i
  fin_cases i
  norm_num [point]

/-- Helper for Exercise 4.3: if a supporting hyperplane is vertical, then it contains one of the
integer base vertices `(0,0)` or `(1,0)`. -/
lemma vertical_supporting_hyperplane_hits_integer_x
    {c d : Fin 1 → ℚ} {δ : ℚ}
    (hNonzero : c ≠ 0 ∨ d ≠ 0)
    (hValid : is_valid_mixed_rational_inequality counterexample_polyhedron c d δ)
    (hFace : (counterexample_polyhedron ∩ mixed_rational_hyperplane c d δ).Nonempty)
    (hd0 : d 0 = 0) :
    point 0 0 ∈ mixed_rational_hyperplane c d δ ∨
      point 1 0 ∈ mixed_rational_hyperplane c d δ := by
  have hd : d = 0 := by
    ext j
    fin_cases j
    exact hd0
  have hc : c ≠ 0 := by
    rcases hNonzero with hc | hd_ne
    · exact hc
    · exfalso
      exact hd_ne hd
  have hc0 : c 0 ≠ 0 := by
    intro hc0_eq
    apply hc
    ext i
    fin_cases i
    exact hc0_eq
  rcases hFace with ⟨xy, hxyFace⟩
  have hxy_mem : xy ∈ counterexample_polyhedron := hxyFace.1
  have hxy_hyperplane : xy ∈ mixed_rational_hyperplane c d δ := hxyFace.2
  have hxy_bounds := counterexample_x_bounds hxy_mem
  have hx_nonneg := hxy_bounds.1
  have hx_le_one := hxy_bounds.2
  -- Reduce the face equation to a scalar equality `c x = δ`.
  have hxy_eq : (c 0 : ℝ) * xy.1 0 = (δ : ℝ) := by
    rw [mixed_rational_hyperplane, Set.mem_setOf_eq,
      mixed_linear_objective_rat_fin_one] at hxy_hyperplane
    simpa [hd0] using hxy_hyperplane
  -- Evaluate the valid inequality on the two integer base vertices.
  have hPointZeroValid : 0 ≤ (δ : ℝ) := by
    have hPointZero := hValid point_zero_mem_counterexample_polyhedron
    rw [mixed_linear_objective_rat_fin_one] at hPointZero
    simpa [point, hd0] using hPointZero
  have hPointOneValid : (c 0 : ℝ) ≤ (δ : ℝ) := by
    have hPointOne := hValid point_one_mem_counterexample_polyhedron
    rw [mixed_linear_objective_rat_fin_one] at hPointOne
    simpa [point, hd0] using hPointOne
  have hc0R : (c 0 : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  have hc0_sign : (c 0 : ℝ) < 0 ∨ 0 < (c 0 : ℝ) := by
    exact lt_or_gt_of_ne hc0R
  rcases hc0_sign with hc0_neg | hc0_pos
  · left
    -- A negative `x`-coefficient forces the supporting line to be `x = 0`.
    have hδ_nonpos : (δ : ℝ) ≤ 0 := by
      nlinarith
    have hδ_zero : (0 : ℝ) = (δ : ℝ) := by
      linarith
    rw [mixed_rational_hyperplane, Set.mem_setOf_eq, mixed_linear_objective_rat_fin_one]
    simpa [point, hd0] using hδ_zero
  · right
    -- A positive `x`-coefficient forces the supporting line to be `x = 1`.
    have hδ_le : (δ : ℝ) ≤ (c 0 : ℝ) := by
      nlinarith
    have hδ_eq : (c 0 : ℝ) = (δ : ℝ) := by
      linarith
    rw [mixed_rational_hyperplane, Set.mem_setOf_eq, mixed_linear_objective_rat_fin_one]
    simpa [point, hd0] using hδ_eq

/-- Helper for Exercise 4.3: every mixed-integer point of the triangle lies on the base edge
`y = 0`. -/
lemma mixed_integer_points_subset_zero_height_slice :
    mixed_integer_points counterexample_polyhedron ⊆ zero_height_slice := by
  intro xy hxy
  rcases (mem_mixed_integer_points_iff).1 hxy with ⟨hxy_mem, hxy_lattice⟩
  rcases (mem_counterexample_polyhedron_iff xy).1 hxy_mem with ⟨hy_nonneg, hy_le_left, hy_le_right⟩
  rcases counterexample_x_bounds hxy_mem with ⟨hx_nonneg, hx_le_one⟩
  rcases hxy_lattice with ⟨z, hz⟩
  -- Convert the integral representation of the `x`-coordinate into scalar bounds on `z 0`.
  have hx_cast : xy.1 0 = (z 0 : ℝ) := by
    simpa using (congrFun hz 0).symm
  have hz_nonneg_real : (0 : ℝ) ≤ (z 0 : ℝ) := by
    simpa [hx_cast] using hx_nonneg
  have hz_le_one_real : (z 0 : ℝ) ≤ 1 := by
    simpa [hx_cast] using hx_le_one
  have hz_nonneg : (0 : ℤ) ≤ z 0 := by
    exact_mod_cast hz_nonneg_real
  have hz_le_one : z 0 ≤ 1 := by
    exact_mod_cast hz_le_one_real
  have hz_cases : z 0 = 0 ∨ z 0 = 1 := by
    omega
  change xy.2 0 = 0
  rcases hz_cases with hz_zero | hz_one
  · -- When `x = 0`, the inequality `y ≤ 2x` forces `y = 0`.
    have hx_zero : xy.1 0 = 0 := by
      simpa [hz_zero] using hx_cast
    linarith
  · -- When `x = 1`, the inequality `y ≤ 2 - 2x` forces `y = 0`.
    have hx_one : xy.1 0 = 1 := by
      simpa [hz_one] using hx_cast
    linarith

/-- Helper for Exercise 4.3: the slice `y = 0` is convex. -/
lemma zero_height_slice_convex : Convex ℝ zero_height_slice := by
  intro a ha b hb u v hu hv huv
  -- The second coordinate of a convex combination is the same convex combination of heights.
  have ha0 : a.2 0 = 0 := by
    simpa [zero_height_slice] using ha
  have hb0 : b.2 0 = 0 := by
    simpa [zero_height_slice] using hb
  change u * a.2 0 + v * b.2 0 = 0
  rw [ha0, hb0]
  ring

/-- Helper for Exercise 4.3: the convex hull of the mixed-integer points stays on the base
edge `y = 0`. -/
lemma convexHull_mixed_integer_points_subset_zero_height_slice :
    convexHull ℝ (mixed_integer_points counterexample_polyhedron) ⊆ zero_height_slice := by
  -- The zero-height slice is convex and already contains every mixed-integer point.
  apply convexHull_min
  · exact mixed_integer_points_subset_zero_height_slice
  · exact zero_height_slice_convex

/-- Exercise 4.3. There exists a rational polyhedron `P = {(x, y) ∈ ℝ^n × ℝ^p | A x + G y ≤ b}`
for which every rational supporting hyperplane of `P` contains a point of `ℤ^n × ℝ^p`, but
`P` is not the convex hull of its mixed-integer points. This gives a counterexample to the
displayed biconditional in the exercise statement. -/
theorem exists_counterexample_to_mixed_integer_supporting_hyperplane_characterization :
    ∃ m n p : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℚ,
      ∃ G : Matrix (Fin m) (Fin p) ℚ,
      ∃ b : Fin m → ℚ,
        let P := rational_mixed_polyhedron A G b
        let S := mixed_integer_points P
        (∀ H : Set (MixedRealPoint n p),
            is_rational_supporting_hyperplane P H →
              ∃ z : MixedRealPoint n p,
                z ∈ H ∧ z ∈ mixed_integer_lattice n p) ∧
          P ≠ convexHull ℝ S := by
  refine ⟨3, 1, 1, counterexampleA, counterexampleG, counterexampleb, ?_⟩
  change
    (∀ H : Set (MixedRealPoint 1 1),
        is_rational_supporting_hyperplane counterexample_polyhedron H →
          ∃ z : MixedRealPoint 1 1,
            z ∈ H ∧ z ∈ mixed_integer_lattice 1 1) ∧
      counterexample_polyhedron ≠ convexHull ℝ (mixed_integer_points counterexample_polyhedron)
  constructor
  · intro H hH
    rcases hH with ⟨c, d, δ, hNonzero, hValid, hFace, hH⟩
    by_cases hd0 : d 0 = 0
    · -- In the vertical case, the supporting line must be one of the integer side lines.
      have hVertical := vertical_supporting_hyperplane_hits_integer_x hNonzero hValid hFace hd0
      rw [← hH] at hVertical
      rcases hVertical with hZero | hOne
      · refine ⟨point 0 0, hZero, point_zero_mem_mixed_integer_lattice 0⟩
      · refine ⟨point 1 0, hOne, point_one_mem_mixed_integer_lattice 0⟩
    · -- In the nonvertical case, solve the hyperplane equation at the integer coordinate `x = 0`.
      refine ⟨point 0 ((δ : ℝ) / (d 0 : ℝ)), ?_, point_zero_mem_mixed_integer_lattice _⟩
      rw [hH, mixed_rational_hyperplane, Set.mem_setOf_eq, mixed_linear_objective_rat_fin_one]
      have hd0R : (d 0 : ℝ) ≠ 0 := by
        exact_mod_cast hd0
      simp [point]
      field_simp [hd0R]
  · intro hEq
    -- The top vertex belongs to `P`, so equality would force it into the mixed-integer hull.
    have hTopInHull :
        point (1 / 2 : ℝ) 1 ∈ convexHull ℝ (mixed_integer_points counterexample_polyhedron) := by
      rw [← hEq]
      exact point_top_mem_counterexample_polyhedron
    -- But every point of that hull lies on the base edge `y = 0`.
    have hTopOnBase : point (1 / 2 : ℝ) 1 ∈ zero_height_slice := by
      exact convexHull_mixed_integer_points_subset_zero_height_slice hTopInHull
    dsimp [zero_height_slice, point] at hTopOnBase
    norm_num at hTopOnBase

end Exercise43
