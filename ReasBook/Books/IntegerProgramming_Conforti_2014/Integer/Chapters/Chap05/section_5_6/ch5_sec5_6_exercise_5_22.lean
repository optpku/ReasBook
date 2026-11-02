import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped IntegerVectorNotation Matrix

variable {n : ℕ}

/-- The pure-integer points of a set `P ⊆ ℝ^n`.

This local owner keeps Exercise 5.22 independent of the heavier Chapter 5
Chvátal-rank import graph. -/
def pure_integer_points (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  P ∩ ℤ^n

/-- The pure-integer hull `P_I`, represented as the convex hull of the pure-integer points of
`P`.

This local owner is the only part of the broader Chapter 5 API used by
Exercise 5.22. -/
def pure_integer_hull (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  convexHull ℝ (pure_integer_points P)

-- Domain-style sampling for this refine pass:
-- * primary domain: split closures and integer hulls of polyhedra in `Fin n → ℝ`;
-- * core/canonical owners inspected upstream: `ℤ^n`, `pure_integer_points`,
--   `pure_integer_hull`, `split_hull`, `split_closure`, and the source-faithful local owner
--   `two_side_split_closure`;
-- * source-facing layer kept here: the concrete Exercise 5.22 polyhedron and its set
--   `S = P ∩ ℤ²`;
-- * bridge/view layer kept here: the source-faithful identification of `pure_integer_hull P`
--   with the textbook notation `conv(S)`, via the canonical owner `pure_integer_points`.

noncomputable section Exercise522

/-- A split `(π, π₀)` is two-sided for `P` if `π ≠ 0` and both split branches
`P ∩ {x | π x ≤ π₀}` and `P ∩ {x | π₀ + 1 ≤ π x}` are nonempty. -/
structure TwoSideSplit
    {n : ℕ}
    (P : Set (Fin n → ℝ)) where
  π : Fin n → ℤ
  π0 : ℤ
  nonzero : π ≠ 0
  lower_nonempty : Set.Nonempty (split_branch_lower P π π0)
  upper_nonempty : Set.Nonempty (split_branch_upper P π π0)

/-- The two-side-split closure of `P`: intersect `P` with the split hulls coming only from
two-sided splits, excluding one-side splits whose lower or upper branch is empty. -/
def two_side_split_closure
    {n : ℕ}
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  P ∩ ⋂ s : TwoSideSplit P, split_hull P s.π s.π0

/-- Membership in `two_side_split_closure P` means belonging to `P` and to every split hull
coming from a two-sided split of `P`. -/
@[simp] theorem mem_two_side_split_closure_iff
    {n : ℕ}
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ two_side_split_closure P ↔
      x ∈ P ∧ ∀ s : TwoSideSplit P, x ∈ split_hull P s.π s.π0 := by
  simp [two_side_split_closure]

/-- Helper for Exercise 5.22: negating the split vector flips the sign of `split_dot`. -/
lemma split_dot_neg
    {n : ℕ}
    (π : Fin n → ℤ)
    (x : Fin n → ℝ) :
    split_dot (-π) x = -split_dot π x := by
  -- Rewrite both dot products as finite sums and negate termwise.
  rw [split_dot_eq_sum, split_dot_eq_sum]
  simp

/-- Helper for Exercise 5.22: negating the split vector and replacing `π₀` by `-π₀ - 1`
only swaps the lower and upper split branches. -/
lemma split_hull_neg_eq
    {n : ℕ}
    (P : Set (Fin n → ℝ))
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    split_hull P (-π) (-π0 - 1) = split_hull P π π0 := by
  -- Transport lower/upper branch membership through the sign change of `split_dot`.
  have hbranches :
      split_branch_lower P (-π) (-π0 - 1) ∪
          split_branch_upper P (-π) (-π0 - 1) =
        split_branch_lower P π π0 ∪
          split_branch_upper P π π0 := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · right
        rcases (mem_split_branch_lower_iff).1 hx with ⟨hxP, hxle⟩
        have hxge : (π0 : ℝ) + 1 ≤ split_dot π x := by
          rw [split_dot_neg] at hxle
          have hxle' : -split_dot π x ≤ -((π0 : ℝ) + 1) := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxle
          linarith
        exact (mem_split_branch_upper_iff).2 ⟨hxP, hxge⟩
      · left
        rcases (mem_split_branch_upper_iff).1 hx with ⟨hxP, hxge⟩
        have hxle : split_dot π x ≤ (π0 : ℝ) := by
          rw [split_dot_neg] at hxge
          have hxge' : -(π0 : ℝ) ≤ -split_dot π x := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxge
          linarith
        exact (mem_split_branch_lower_iff).2 ⟨hxP, hxle⟩
    · intro hx
      rcases hx with hx | hx
      · right
        rcases (mem_split_branch_lower_iff).1 hx with ⟨hxP, hxle⟩
        have hxge : (((-π0 - 1 : ℤ) : ℝ) + 1) ≤ split_dot (-π) x := by
          rw [split_dot_neg]
          have hxge' : -(π0 : ℝ) ≤ -split_dot π x := by
            exact neg_le_neg hxle
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxge'
        exact (mem_split_branch_upper_iff).2 ⟨hxP, hxge⟩
      · left
        rcases (mem_split_branch_upper_iff).1 hx with ⟨hxP, hxge⟩
        have hxle : split_dot (-π) x ≤ (((-π0 - 1 : ℤ) : ℝ)) := by
          rw [split_dot_neg]
          have hxle' : -split_dot π x ≤ -((π0 : ℝ) + 1) := by
            linarith
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxle'
        exact (mem_split_branch_lower_iff).2 ⟨hxP, hxle⟩
  -- The split hull depends only on the union of the two branches.
  simp [split_hull, hbranches]

/-- Helper for Exercise 5.22: a point with an integral split value already lies in the split hull
because it belongs to one side of the split disjunction. -/
lemma integral_split_value_mem_split_hull
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {x : Fin n → ℝ}
    {π : Fin n → ℤ}
    {π0 m : ℤ}
    (hxP : x ∈ P)
    (hxm : split_dot π x = (m : ℝ)) :
    x ∈ split_hull P π π0 := by
  -- The integer split value is either at most `π₀` or at least `π₀ + 1`, so `x` lies in one
  -- branch and hence in the convex hull of the branch union.
  have hUnion :
      x ∈ split_branch_lower P π π0 ∪
        split_branch_upper P π π0 := by
    by_cases hm : m ≤ π0
    · left
      have hm' : split_dot π x ≤ (π0 : ℝ) := by
        simpa [hxm] using hm
      exact (mem_split_branch_lower_iff).2 ⟨hxP, hm'⟩
    · right
      have hm' : π0 + 1 ≤ m := by
        omega
      have hm'' : (π0 : ℝ) + 1 ≤ split_dot π x := by
        have hm''' : ((π0 + 1 : ℤ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hm'
        simpa [hxm] using hm'''
      exact (mem_split_branch_upper_iff).2 ⟨hxP, hm''⟩
  exact subset_convexHull ℝ _ hUnion

/-- Helper for Exercise 5.22: a point on a segment between two branch points lies in the split
hull. -/
lemma mem_split_hull_of_segment
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {π0 : ℤ}
    {x y z : Fin n → ℝ}
    (hx :
      x ∈ split_branch_lower P π π0 ∪
        split_branch_upper P π π0)
    (hy :
      y ∈ split_branch_lower P π π0 ∪
        split_branch_upper P π π0)
    (hz : z ∈ segment ℝ x y) :
    z ∈ split_hull P π π0 := by
  -- The split hull is the convex hull of the branch union, so every segment between branch
  -- points stays inside it.
  have hzHull :
      z ∈ convexHull ℝ
        (split_branch_lower P π π0 ∪
          split_branch_upper P π π0) :=
    (segment_subset_convexHull hx hy) hz
  simpa [split_hull] using hzHull

/-- Helper for Exercise 5.22: `split_dot` respects affine interpolation along an explicit convex
combination. -/
lemma split_dot_lineMap
    {n : ℕ}
    (π : Fin n → ℤ)
    (x y : Fin n → ℝ)
    (t : ℝ) :
    split_dot π ((1 - t) • x + t • y) =
      (1 - t) * split_dot π x + t * split_dot π y := by
  -- Expand the split functional coordinatewise and distribute across the affine combination.
  rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
  calc
    ∑ j : Fin n, (π j : ℝ) * (((1 - t) • x + t • y) j)
        = ∑ j : Fin n, ((1 - t) * ((π j : ℝ) * x j) + t * ((π j : ℝ) * y j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Pi.add_apply, Pi.smul_apply]
            ring
    _ = (1 - t) * ∑ j : Fin n, (π j : ℝ) * x j +
          t * ∑ j : Fin n, (π j : ℝ) * y j := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = (1 - t) * split_dot π x + t * split_dot π y := by
          rw [split_dot_eq_sum, split_dot_eq_sum]

/-- Helper for Exercise 5.22: the strict upper split halfspace
`{x | split_dot π x < π₀ + 1}` is convex. -/
lemma split_dot_strict_upper_halfspace_convex
    {n : ℕ}
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    Convex ℝ {x : Fin n → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
  intro x hx y hy a b ha hb hab
  -- Rewrite the split functional on the affine combination and keep one strict inequality.
  have hsplit :
      split_dot π (a • x + b • y) = a * split_dot π x + b * split_dot π y := by
    rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
    calc
      ∑ j : Fin n, (π j : ℝ) * (a * x j + b * y j)
          = ∑ j : Fin n, (a * ((π j : ℝ) * x j) + b * ((π j : ℝ) * y j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = a * ∑ j : Fin n, (π j : ℝ) * x j + b * ∑ j : Fin n, (π j : ℝ) * y j := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  by_cases ha_zero : a = 0
  · have hb_one : b = 1 := by linarith
    simpa [ha_zero, hb_one, hsplit] using hy
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
    have hx' : a * split_dot π x < a * ((π0 : ℝ) + 1) := by
      exact mul_lt_mul_of_pos_left hx ha_pos
    have hy' : b * split_dot π y ≤ b * ((π0 : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left hy.le hb
    calc
      split_dot π (a • x + b • y) = a * split_dot π x + b * split_dot π y := hsplit
      _ < a * ((π0 : ℝ) + 1) + b * ((π0 : ℝ) + 1) := by
            exact add_lt_add_of_lt_of_le hx' hy'
      _ = (π0 : ℝ) + 1 := by
            calc
              a * ((π0 : ℝ) + 1) + b * ((π0 : ℝ) + 1)
                  = (a + b) * ((π0 : ℝ) + 1) := by ring
              _ = (π0 : ℝ) + 1 := by rw [hab, one_mul]

/-- A matrix presentation of the polyhedron from Exercise 5.22. -/
def exercise_5_22_A : Matrix (Fin 4) (Fin 2) ℝ :=
  ![![-1, 0],
    ![0, -1],
    ![-(1 / 4 : ℝ), 1],
    ![1, -(1 / 4 : ℝ)]]

/-- The right-hand side vector for `exercise_5_22_A`. -/
def exercise_5_22_b : Fin 4 → ℝ :=
  ![0, 0, 1, 1]

/-- The polyhedron
`P = {(x₁, x₂) ∈ ℝ² | x₁ ≥ 0, x₂ ≥ 0, x₂ ≤ 1 + x₁ / 4, x₁ ≤ 1 + x₂ / 4}` from
Exercise 5.22. -/
def exercise_5_22_polyhedron : Set (Fin 2 → ℝ) :=
  polyhedron_le_set exercise_5_22_A exercise_5_22_b

/-- Membership in `exercise_5_22_polyhedron` is exactly the displayed system of four inequalities.
-/
theorem mem_exercise_5_22_polyhedron_iff
    {x : Fin 2 → ℝ} :
    x ∈ exercise_5_22_polyhedron ↔
      0 ≤ x 0 ∧
        0 ≤ x 1 ∧
          x 1 ≤ 1 + (1 / 4 : ℝ) * x 0 ∧
            x 0 ≤ 1 + (1 / 4 : ℝ) * x 1 := by
  rw [exercise_5_22_polyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hx
    have h0 : -x 0 ≤ 0 := by
      simpa [exercise_5_22_A, exercise_5_22_b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        using hx 0
    have h1 : -x 1 ≤ 0 := by
      simpa [exercise_5_22_A, exercise_5_22_b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        using hx 1
    have h2 : -((1 / 4 : ℝ) * x 0) + x 1 ≤ 1 := by
      simpa [exercise_5_22_A, exercise_5_22_b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        using hx 2
    have h3 : x 0 - (1 / 4 : ℝ) * x 1 ≤ 1 := by
      simpa [exercise_5_22_A, exercise_5_22_b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        using hx 3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨hx0, hx1, hx2, hx3⟩ i
    fin_cases i
    · simp [exercise_5_22_A, exercise_5_22_b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linarith
    · simp [exercise_5_22_A, exercise_5_22_b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linarith
    · simp [exercise_5_22_A, exercise_5_22_b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linarith
    · simp [exercise_5_22_A, exercise_5_22_b, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linarith

/-- The pure integer set `S = P ∩ ℤ²` from Exercise 5.22. -/
def exercise_5_22_integer_set : Set (Fin 2 → ℝ) :=
  exercise_5_22_polyhedron ∩ ℤ^2

/-- Membership in `exercise_5_22_integer_set` means feasibility in `P` together with membership in
the canonical Chapter 4 integer-vector owner `ℤ^2`. -/
theorem mem_exercise_5_22_integer_set_iff
    {x : Fin 2 → ℝ} :
    x ∈ exercise_5_22_integer_set ↔ x ∈ exercise_5_22_polyhedron ∧ x ∈ ℤ^2 :=
  Iff.rfl

/-- Membership in `exercise_5_22_integer_set` is equivalently feasibility in `P` together with
integrality of both coordinates. -/
theorem mem_exercise_5_22_integer_set_iff_forall
    {x : Fin 2 → ℝ} :
    x ∈ exercise_5_22_integer_set ↔
      x ∈ exercise_5_22_polyhedron ∧ ∀ i, ∃ z : ℤ, x i = (z : ℝ) := by
  rw [mem_exercise_5_22_integer_set_iff, mem_integerVectors_iff_forall]
  simp [Set.mem_range, eq_comm]

/-- The source-facing set `S = P ∩ ℤ²` is exactly the Chapter 5 owner
`pure_integer_points exercise_5_22_polyhedron`. -/
theorem exercise_5_22_integer_set_eq_pure_integer_points :
    exercise_5_22_integer_set = pure_integer_points exercise_5_22_polyhedron := by
  rfl

/-- The canonical pure-integer hull of the Exercise 5.22 polyhedron is the source-facing convex
hull `conv(S)` of `S = P ∩ ℤ²`, with `pure_integer_hull` taken from the earlier Chapter 5 owner.
-/
theorem exercise_5_22_pure_integer_hull_eq_conv_integer_set :
    pure_integer_hull exercise_5_22_polyhedron = convexHull ℝ exercise_5_22_integer_set := by
  simp [pure_integer_hull, exercise_5_22_integer_set_eq_pure_integer_points]

/-- Helper for Exercise 5.22: the apex `(4 / 3, 4 / 3)` of the source quadrilateral. -/
noncomputable def exercise_5_22_apex : Fin 2 → ℝ :=
  ![(4 / 3 : ℝ), (4 / 3 : ℝ)]

/-- Helper for Exercise 5.22: the explicit apex satisfies the four inequalities of the source
polyhedron. -/
lemma exercise_5_22_apex_mem_polyhedron :
    exercise_5_22_apex ∈ exercise_5_22_polyhedron := by
  -- Convert to the displayed inequality system and check the coordinates directly.
  refine mem_exercise_5_22_polyhedron_iff.2 ?_
  norm_num [exercise_5_22_apex]

/-- Helper for Exercise 5.22: every integer feasible point of `exercise_5_22_polyhedron` has first
coordinate at most `1`. -/
lemma exercise_5_22_integerPoint_first_le_one
    {x : Fin 2 → ℝ}
    (hxP : x ∈ exercise_5_22_polyhedron)
    (hxInt : x ∈ ℤ^2) :
    x 0 ≤ 1 := by
  -- First unpack the source inequalities and the integrality of the two coordinates.
  rw [mem_exercise_5_22_polyhedron_iff] at hxP
  rw [mem_integerVectors_iff_forall] at hxInt
  obtain ⟨z0, hz0⟩ := hxInt 0
  obtain ⟨z1, hz1⟩ := hxInt 1
  rcases hxP with ⟨hx0_nonneg, hx1_nonneg, hx1_upper, hx0_upper⟩
  -- The two slanted inequalities force the second coordinate below `2`.
  have hx1_lt_two : x 1 < 2 := by
    nlinarith
  have hz1_lt_two : z1 < 2 := by
    rw [← hz1] at hx1_lt_two
    exact_mod_cast hx1_lt_two
  have hz1_le_one : z1 ≤ 1 := by
    have hz1_nonneg : 0 ≤ z1 := by
      have hz1_nonneg_real : (0 : ℝ) ≤ z1 := by
        simpa [hz1] using hx1_nonneg
      exact_mod_cast hz1_nonneg_real
    omega
  have hx1_le_one : x 1 ≤ 1 := by
    rw [← hz1]
    exact_mod_cast hz1_le_one
  -- Then the fourth inequality forces the first coordinate below `2`.
  have hx0_lt_two : x 0 < 2 := by
    nlinarith
  have hz0_lt_two : z0 < 2 := by
    rw [← hz0] at hx0_lt_two
    exact_mod_cast hx0_lt_two
  have hz0_le_one : z0 ≤ 1 := by
    have hz0_nonneg : 0 ≤ z0 := by
      have hz0_nonneg_real : (0 : ℝ) ≤ z0 := by
        simpa [hz0] using hx0_nonneg
      exact_mod_cast hz0_nonneg_real
    omega
  rw [← hz0]
  exact_mod_cast hz0_le_one

/-- Helper for Exercise 5.22: the pure-integer hull of the source polyhedron lies in the
halfspace `x 0 ≤ 1`. -/
lemma exercise_5_22_pure_integer_hull_subset_x0_le_one :
    pure_integer_hull exercise_5_22_polyhedron ⊆ {x : Fin 2 → ℝ | x 0 ≤ 1} := by
  rw [exercise_5_22_pure_integer_hull_eq_conv_integer_set]
  refine convexHull_min ?_ ?_
  · -- Integer generators of the hull already satisfy the coordinate bound.
    intro x hx
    exact exercise_5_22_integerPoint_first_le_one hx.1 hx.2
  · -- The coordinate halfspace is convex, so it contains the whole convex hull.
    intro x hx y hy a b ha hb hab
    dsimp at hx hy ⊢
    nlinarith

/-- Helper for Exercise 5.22: the source apex lies outside the pure-integer hull. -/
lemma exercise_5_22_apex_not_mem_pure_integer_hull :
    exercise_5_22_apex ∉ pure_integer_hull exercise_5_22_polyhedron := by
  intro hapex_hull
  -- The previously established hull halfspace excludes the explicit apex.
  have hapex_le_one : exercise_5_22_apex 0 ≤ 1 :=
    exercise_5_22_pure_integer_hull_subset_x0_le_one hapex_hull
  norm_num [exercise_5_22_apex] at hapex_le_one

/-- Helper for Exercise 5.22: the symmetric quadrilateral layer with slanted facets
`x₂ ≤ 1 + x₁ / q` and `x₁ ≤ 1 + x₂ / q`. -/
def exercise_5_22_layer (q : ℕ) : Set (Fin 2 → ℝ) :=
  {x : Fin 2 → ℝ |
    0 ≤ x 0 ∧
      0 ≤ x 1 ∧
        x 1 ≤ 1 + x 0 / (q : ℝ) ∧
          x 0 ≤ 1 + x 1 / (q : ℝ)}

/-- Helper for Exercise 5.22: membership in `exercise_5_22_layer q` is exactly the displayed
system of inequalities. -/
theorem mem_exercise_5_22_layer_iff
    {q : ℕ}
    {x : Fin 2 → ℝ} :
    x ∈ exercise_5_22_layer q ↔
      0 ≤ x 0 ∧
        0 ≤ x 1 ∧
          x 1 ≤ 1 + x 0 / (q : ℝ) ∧
            x 0 ≤ 1 + x 1 / (q : ℝ) :=
  Iff.rfl

/-- Helper for Exercise 5.22: the layer with denominator `4` is the source polyhedron. -/
lemma exercise_5_22_polyhedron_eq_layer :
    exercise_5_22_polyhedron = exercise_5_22_layer 4 := by
  -- Rewrite both presentations to the same four inequalities.
  ext x
  rw [mem_exercise_5_22_polyhedron_iff, mem_exercise_5_22_layer_iff]
  constructor <;> intro hx <;> rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  · refine ⟨hx0, hx1, ?_, ?_⟩
    · simpa [show (1 : ℝ) + x 0 / (4 : ℝ) = 1 + (1 / 4 : ℝ) * x 0 by ring] using hx2
    · simpa [show (1 : ℝ) + x 1 / (4 : ℝ) = 1 + (1 / 4 : ℝ) * x 1 by ring] using hx3
  · refine ⟨hx0, hx1, ?_, ?_⟩
    · simpa [show (1 : ℝ) + x 0 / (4 : ℝ) = 1 + (1 / 4 : ℝ) * x 0 by ring] using hx2
    · simpa [show (1 : ℝ) + x 1 / (4 : ℝ) = 1 + (1 / 4 : ℝ) * x 1 by ring] using hx3

/-- Helper for Exercise 5.22: the top vertex of the layer `exercise_5_22_layer q`. -/
noncomputable def exercise_5_22_topVertex (q : ℕ) : Fin 2 → ℝ :=
  ![((q : ℝ) / ((q : ℝ) - 1)), ((q : ℝ) / ((q : ℝ) - 1))]

/-- Helper for Exercise 5.22: the top vertex already belongs to its layer when `q ≥ 2`. -/
lemma exercise_5_22_topVertex_mem_layer
    {q : ℕ}
    (hq : 2 ≤ q) :
    exercise_5_22_topVertex q ∈ exercise_5_22_layer q := by
  -- The top vertex lies on both slanted facets, so all four inequalities are immediate.
  have hqgt : 1 < q := by omega
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast (lt_trans (by norm_num) hq)
  have hq_ne : (q : ℝ) ≠ 0 := by linarith
  have hq_sub_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have hqgt' : (1 : ℝ) < q := by exact_mod_cast hqgt
    nlinarith
  have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by linarith
  refine (mem_exercise_5_22_layer_iff).2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hpos : 0 < (q : ℝ) / ((q : ℝ) - 1) := by positivity
    simpa [exercise_5_22_topVertex] using le_of_lt hpos
  · have hpos : 0 < (q : ℝ) / ((q : ℝ) - 1) := by positivity
    simpa [exercise_5_22_topVertex] using le_of_lt hpos
  · have hfacet :
        (q : ℝ) / ((q : ℝ) - 1) = 1 + ((q : ℝ) / ((q : ℝ) - 1)) / (q : ℝ) := by
      field_simp [hq_ne, hq_sub_ne]
      ring
    simpa [exercise_5_22_topVertex] using le_of_eq hfacet
  · have hfacet :
        (q : ℝ) / ((q : ℝ) - 1) = 1 + ((q : ℝ) / ((q : ℝ) - 1)) / (q : ℝ) := by
      field_simp [hq_ne, hq_sub_ne]
      ring
    simpa [exercise_5_22_topVertex] using le_of_eq hfacet

/-- Helper for Exercise 5.22: the first coordinate of the top vertex is strictly larger than `1`
for every admissible layer. -/
lemma exercise_5_22_one_lt_topVertex_first
    {q : ℕ}
    (hq : 2 ≤ q) :
    1 < exercise_5_22_topVertex q 0 := by
  -- The explicit coordinate is `q / (q - 1)`, which is greater than `1` when `q > 1`.
  have hqgt : 1 < q := by omega
  have hq_ne : (q : ℝ) ≠ 0 := by
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (lt_trans (by norm_num) hq)
    linarith
  have hq_sub_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have hqgt' : (1 : ℝ) < q := by exact_mod_cast hqgt
    nlinarith
  have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by linarith
  simp [exercise_5_22_topVertex]
  have hmain : 1 < (q : ℝ) / ((q : ℝ) - 1) := by
    field_simp [hq_ne, hq_sub_ne]
    linarith
  simpa using hmain

/-- Helper for Exercise 5.22: the origin of the layer quadrilateral. -/
def exercise_5_22_origin : Fin 2 → ℝ :=
  ![0, 0]

/-- Helper for Exercise 5.22: the axis vertex `(1,0)` of the layer quadrilateral. -/
def exercise_5_22_x0AxisVertex : Fin 2 → ℝ :=
  ![1, 0]

/-- Helper for Exercise 5.22: the axis vertex `(0,1)` of the layer quadrilateral. -/
def exercise_5_22_x1AxisVertex : Fin 2 → ℝ :=
  ![0, 1]

/-- Helper for Exercise 5.22: the fixed point on the edge from `(0,1)` to the current top vertex
used in the normalized split argument. -/
noncomputable def exercise_5_22_leftBoundaryPoint (q : ℕ) : Fin 2 → ℝ :=
  ![((q : ℝ) * ((q : ℝ) - 1)) / ((q : ℝ) ^ 2 - (q : ℝ) - 1),
    ((q : ℝ) ^ 2 - 2) / ((q : ℝ) ^ 2 - (q : ℝ) - 1)]

/-- Helper for Exercise 5.22: the symmetric point on the edge from `(1,0)` to the current top
vertex. -/
noncomputable def exercise_5_22_rightBoundaryPoint (q : ℕ) : Fin 2 → ℝ :=
  ![((q : ℝ) ^ 2 - 2) / ((q : ℝ) ^ 2 - (q : ℝ) - 1),
    ((q : ℝ) * ((q : ℝ) - 1)) / ((q : ℝ) ^ 2 - (q : ℝ) - 1)]

/-- Helper for Exercise 5.22: the split value of the origin is always `0`. -/
lemma exercise_5_22_split_dot_origin
    (π : Fin 2 → ℤ) :
    split_dot π exercise_5_22_origin = 0 := by
  -- Only zero coordinates contribute at the origin.
  rw [split_dot_eq_sum, Fin.sum_univ_two]
  simp [exercise_5_22_origin]

/-- Helper for Exercise 5.22: the split value at `(1,0)` is the first split coefficient. -/
lemma exercise_5_22_split_dot_x0AxisVertex
    (π : Fin 2 → ℤ) :
    split_dot π exercise_5_22_x0AxisVertex = (π 0 : ℝ) := by
  -- Only the first coordinate survives on the `x₀`-axis vertex.
  rw [split_dot_eq_sum, Fin.sum_univ_two]
  simp [exercise_5_22_x0AxisVertex]

/-- Helper for Exercise 5.22: the split value at `(0,1)` is the second split coefficient. -/
lemma exercise_5_22_split_dot_x1AxisVertex
    (π : Fin 2 → ℤ) :
    split_dot π exercise_5_22_x1AxisVertex = (π 1 : ℝ) := by
  -- Only the second coordinate survives on the `x₁`-axis vertex.
  rw [split_dot_eq_sum, Fin.sum_univ_two]
  simp [exercise_5_22_x1AxisVertex]

/-- Helper for Exercise 5.22: the split value at the top vertex depends only on the coefficient
sum `π₀ + π₁`. -/
lemma exercise_5_22_split_dot_topVertex
    (π : Fin 2 → ℤ)
    (q : ℕ) :
    split_dot π (exercise_5_22_topVertex q) =
      ((q : ℝ) * ((π 0 + π 1 : ℤ) : ℝ)) / ((q : ℝ) - 1) := by
  -- The two equal top coordinates collapse the dot product to the coefficient sum.
  rw [split_dot_eq_sum, Fin.sum_univ_two]
  simp [exercise_5_22_topVertex]
  ring

/-- Helper for Exercise 5.22: the corrected left boundary point has an explicit split-value
formula with denominator `q² - q - 1`. -/
lemma exercise_5_22_split_dot_leftBoundaryPoint
    (π : Fin 2 → ℤ)
    (q : ℕ) :
    split_dot π (exercise_5_22_leftBoundaryPoint q) =
      ((π 0 : ℝ) * (q : ℝ) * ((q : ℝ) - 1) +
          (π 1 : ℝ) * ((q : ℝ) ^ 2 - 2)) /
        ((q : ℝ) ^ 2 - (q : ℝ) - 1) := by
  -- Expand the dot product against the explicit bridge-point coordinates.
  rw [split_dot_eq_sum, Fin.sum_univ_two]
  simp [exercise_5_22_leftBoundaryPoint]
  ring

/-- Helper for Exercise 5.22: the corrected right boundary point has the symmetric split-value
formula with denominator `q² - q - 1`. -/
lemma exercise_5_22_split_dot_rightBoundaryPoint
    (π : Fin 2 → ℤ)
    (q : ℕ) :
    split_dot π (exercise_5_22_rightBoundaryPoint q) =
      ((π 0 : ℝ) * ((q : ℝ) ^ 2 - 2) +
          (π 1 : ℝ) * (q : ℝ) * ((q : ℝ) - 1)) /
        ((q : ℝ) ^ 2 - (q : ℝ) - 1) := by
  -- The symmetric bridge-point coordinates give the mirrored formula.
  rw [split_dot_eq_sum, Fin.sum_univ_two]
  simp [exercise_5_22_rightBoundaryPoint]
  ring

/-- Helper for Exercise 5.22: the layer family is convex because it is cut out by affine
halfspaces. -/
lemma exercise_5_22_layer_convex
    (q : ℕ) :
    Convex ℝ (exercise_5_22_layer q) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  rcases hy with ⟨hy0, hy1, hy2, hy3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Nonnegativity of the first coordinate is preserved by convex combinations.
    simp [Pi.add_apply, Pi.smul_apply]
    nlinarith
  · -- Nonnegativity of the second coordinate is preserved in the same way.
    simp [Pi.add_apply, Pi.smul_apply]
    nlinarith
  · -- The upper slanted facet inequality is affine in the coordinates.
    have hscaledx : a * x 1 ≤ a * (1 + x 0 / (q : ℝ)) := by
      gcongr
    have hscaledy : b * y 1 ≤ b * (1 + y 0 / (q : ℝ)) := by
      gcongr
    have hsum :
        a * x 1 + b * y 1 ≤
          a * (1 + x 0 / (q : ℝ)) + b * (1 + y 0 / (q : ℝ)) := by
      linarith
    have hrewrite :
        a * (1 + x 0 / (q : ℝ)) + b * (1 + y 0 / (q : ℝ)) =
          1 + (a * x 0 + b * y 0) / (q : ℝ) := by
      calc
        a * (1 + x 0 / (q : ℝ)) + b * (1 + y 0 / (q : ℝ))
            = a + b + (a * x 0 + b * y 0) / (q : ℝ) := by ring
        _ = 1 + (a * x 0 + b * y 0) / (q : ℝ) := by rw [hab]
    simpa only [Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ge_iff_le] using
      hsum.trans_eq hrewrite
  · -- The lower slanted facet inequality is the symmetric affine estimate.
    have hscaledx : a * x 0 ≤ a * (1 + x 1 / (q : ℝ)) := by
      gcongr
    have hscaledy : b * y 0 ≤ b * (1 + y 1 / (q : ℝ)) := by
      gcongr
    have hsum :
        a * x 0 + b * y 0 ≤
          a * (1 + x 1 / (q : ℝ)) + b * (1 + y 1 / (q : ℝ)) := by
      linarith
    have hrewrite :
        a * (1 + x 1 / (q : ℝ)) + b * (1 + y 1 / (q : ℝ)) =
          1 + (a * x 1 + b * y 1) / (q : ℝ) := by
      calc
        a * (1 + x 1 / (q : ℝ)) + b * (1 + y 1 / (q : ℝ))
            = a + b + (a * x 1 + b * y 1) / (q : ℝ) := by ring
        _ = 1 + (a * x 1 + b * y 1) / (q : ℝ) := by rw [hab]
    simpa only [Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ge_iff_le] using
      hsum.trans_eq hrewrite

/-- Helper for Exercise 5.22: the three integral vertices lie in every layer with denominator at
least `2`. -/
lemma exercise_5_22_axisVertices_mem_layer
    {q : ℕ}
    (hq : 2 ≤ q) :
    exercise_5_22_origin ∈ exercise_5_22_layer q ∧
      exercise_5_22_x0AxisVertex ∈ exercise_5_22_layer q ∧
        exercise_5_22_x1AxisVertex ∈ exercise_5_22_layer q := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_trans (by norm_num) hq)
  refine ⟨?_, ?_, ?_⟩
  · -- The origin satisfies all four defining inequalities trivially.
    refine (mem_exercise_5_22_layer_iff).2 ?_
    norm_num [exercise_5_22_origin]
  · -- The axis vertex `(1,0)` only uses positivity of `q` for the slanted upper bound.
    refine (mem_exercise_5_22_layer_iff).2 ?_
    refine ⟨by norm_num [exercise_5_22_x0AxisVertex],
      by norm_num [exercise_5_22_x0AxisVertex], ?_, ?_⟩
    · have hfacet : (0 : ℝ) ≤ 1 + 1 / (q : ℝ) := by
        positivity
      simpa [exercise_5_22_x0AxisVertex] using hfacet
    · norm_num [exercise_5_22_x0AxisVertex]
  · -- The symmetric axis vertex `(0,1)` is handled identically.
    refine (mem_exercise_5_22_layer_iff).2 ?_
    refine ⟨by norm_num [exercise_5_22_x1AxisVertex],
      by norm_num [exercise_5_22_x1AxisVertex], ?_, ?_⟩
    · norm_num [exercise_5_22_x1AxisVertex]
    · have hfacet : (0 : ℝ) ≤ 1 + 1 / (q : ℝ) := by
        positivity
      simpa [exercise_5_22_x1AxisVertex] using hfacet

/-- Helper for Exercise 5.22: the denominator used by the opposite-edge bridge points is
strictly positive once `q ≥ 2`. -/
lemma exercise_5_22_boundaryPoint_denom_pos
    {q : ℕ}
    (hq : 2 ≤ q) :
    0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 := by
  -- The corrected bridge-point denominator is `q² - q - 1`, which is already positive at `q = 2`.
  have hq_real : (2 : ℝ) ≤ q := by
    exact_mod_cast hq
  nlinarith

/-- Helper for Exercise 5.22: the corrected left bridge point is the explicit affine point on the
edge from `(0,1)` to the current top vertex. -/
lemma exercise_5_22_leftBoundaryPoint_eq_lineMap
    {q : ℕ}
    (hq : 2 ≤ q) :
    exercise_5_22_leftBoundaryPoint q =
      AffineMap.lineMap
        exercise_5_22_x1AxisVertex
        (exercise_5_22_topVertex q)
        (((q : ℝ) - 1) ^ 2 / ((q : ℝ) ^ 2 - (q : ℝ) - 1)) := by
  have hq_real : (2 : ℝ) ≤ q := by
    exact_mod_cast hq
  have hq_sub_pos : 0 < (q : ℝ) - 1 := by
    nlinarith
  have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by
    linarith
  have hden_pos : 0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 :=
    exercise_5_22_boundaryPoint_denom_pos hq
  have hden_ne : (q : ℝ) ^ 2 - (q : ℝ) - 1 ≠ 0 := by
    linarith
  ext i
  fin_cases i
  · -- The first coordinate is the top-vertex coordinate scaled by the line-map parameter.
    simp [AffineMap.lineMap_apply_module, exercise_5_22_leftBoundaryPoint,
      exercise_5_22_x1AxisVertex, exercise_5_22_topVertex]
    field_simp [hq_sub_ne, hden_ne]
  · -- The second coordinate also keeps the `1 - t` contribution coming from `(0,1)`.
    have hcoord :
        exercise_5_22_leftBoundaryPoint q 1 =
          (AffineMap.lineMap
            exercise_5_22_x1AxisVertex
            (exercise_5_22_topVertex q)
            (((q : ℝ) - 1) ^ 2 / ((q : ℝ) ^ 2 - (q : ℝ) - 1))) 1 := by
      have hden_alt_ne : (q : ℝ) * ((q : ℝ) - 1) - 1 ≠ 0 := by
        intro hzero
        apply hden_ne
        nlinarith
      -- Clearing the live denominator spelling reduces the coordinate equality to a polynomial.
      simp [AffineMap.lineMap_apply_module, exercise_5_22_leftBoundaryPoint,
        exercise_5_22_x1AxisVertex, exercise_5_22_topVertex]
      field_simp [hq_sub_ne, hden_alt_ne]
      ring
    simpa using hcoord

/-- Helper for Exercise 5.22: the corrected right bridge point is the symmetric affine point on
the edge from `(1,0)` to the current top vertex. -/
lemma exercise_5_22_rightBoundaryPoint_eq_lineMap
    {q : ℕ}
    (hq : 2 ≤ q) :
    exercise_5_22_rightBoundaryPoint q =
      AffineMap.lineMap
        exercise_5_22_x0AxisVertex
        (exercise_5_22_topVertex q)
        (((q : ℝ) - 1) ^ 2 / ((q : ℝ) ^ 2 - (q : ℝ) - 1)) := by
  have hq_real : (2 : ℝ) ≤ q := by
    exact_mod_cast hq
  have hq_sub_pos : 0 < (q : ℝ) - 1 := by
    nlinarith
  have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by
    linarith
  have hden_pos : 0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 :=
    exercise_5_22_boundaryPoint_denom_pos hq
  have hden_ne : (q : ℝ) ^ 2 - (q : ℝ) - 1 ≠ 0 := by
    linarith
  ext i
  fin_cases i
  · -- The first coordinate keeps the `1 - t` contribution from `(1,0)`.
    have hcoord :
        exercise_5_22_rightBoundaryPoint q 0 =
          (AffineMap.lineMap
            exercise_5_22_x0AxisVertex
            (exercise_5_22_topVertex q)
            (((q : ℝ) - 1) ^ 2 / ((q : ℝ) ^ 2 - (q : ℝ) - 1))) 0 := by
      have hden_alt_ne : (q : ℝ) * ((q : ℝ) - 1) - 1 ≠ 0 := by
        intro hzero
        apply hden_ne
        nlinarith
      -- The symmetric coordinate identity has the same denominator after swapping coordinates.
      simp [AffineMap.lineMap_apply_module, exercise_5_22_rightBoundaryPoint,
        exercise_5_22_x0AxisVertex, exercise_5_22_topVertex]
      field_simp [hq_sub_ne, hden_alt_ne]
      ring
    simpa using hcoord
  · -- The second coordinate is the scaled top-vertex coordinate by symmetry.
    simp [AffineMap.lineMap_apply_module, exercise_5_22_rightBoundaryPoint,
      exercise_5_22_x0AxisVertex, exercise_5_22_topVertex]
    field_simp [hq_sub_ne, hden_ne]

/-- Helper for Exercise 5.22: the corrected left bridge point lies on the opposite edge joining
`(0,1)` to the current top vertex. -/
lemma exercise_5_22_leftBoundaryPoint_mem_segment
    {q : ℕ}
    (hq : 2 ≤ q) :
    exercise_5_22_leftBoundaryPoint q ∈
      segment ℝ exercise_5_22_x1AxisVertex (exercise_5_22_topVertex q) := by
  -- Use the explicit `lineMap` parameter and verify that it lies in `[0, 1]`.
  rw [segment_eq_image_lineMap]
  refine ⟨((q : ℝ) - 1) ^ 2 / ((q : ℝ) ^ 2 - (q : ℝ) - 1), ?_, ?_⟩
  · have hden : 0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 :=
      exercise_5_22_boundaryPoint_denom_pos hq
    have hq_real : (2 : ℝ) ≤ q := by
      exact_mod_cast hq
    refine ⟨?_, ?_⟩
    · exact div_nonneg (sq_nonneg _) hden.le
    · rw [div_le_one hden]
      nlinarith
  · simpa using (exercise_5_22_leftBoundaryPoint_eq_lineMap hq).symm

/-- Helper for Exercise 5.22: the corrected right bridge point lies on the opposite edge joining
`(1,0)` to the current top vertex. -/
lemma exercise_5_22_rightBoundaryPoint_mem_segment
    {q : ℕ}
    (hq : 2 ≤ q) :
    exercise_5_22_rightBoundaryPoint q ∈
      segment ℝ exercise_5_22_x0AxisVertex (exercise_5_22_topVertex q) := by
  -- The symmetric bridge point uses the same parameter on the opposite edge.
  rw [segment_eq_image_lineMap]
  refine ⟨((q : ℝ) - 1) ^ 2 / ((q : ℝ) ^ 2 - (q : ℝ) - 1), ?_, ?_⟩
  · have hden : 0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 :=
      exercise_5_22_boundaryPoint_denom_pos hq
    have hq_real : (2 : ℝ) ≤ q := by
      exact_mod_cast hq
    refine ⟨?_, ?_⟩
    · exact div_nonneg (sq_nonneg _) hden.le
    · rw [div_le_one hden]
      nlinarith
  · simpa using (exercise_5_22_rightBoundaryPoint_eq_lineMap hq).symm

/-- Helper for Exercise 5.22: convexity of the layer keeps the corrected left bridge point inside
`exercise_5_22_layer q`. -/
lemma exercise_5_22_leftBoundaryPoint_mem_layer
    {q : ℕ}
    (hq : 2 ≤ q) :
    exercise_5_22_leftBoundaryPoint q ∈ exercise_5_22_layer q := by
  -- The corrected bridge point lies on an edge between two already feasible vertices.
  have haxes := exercise_5_22_axisVertices_mem_layer hq
  have hx1Layer : exercise_5_22_x1AxisVertex ∈ exercise_5_22_layer q := haxes.2.2
  have htopLayer : exercise_5_22_topVertex q ∈ exercise_5_22_layer q :=
    exercise_5_22_topVertex_mem_layer hq
  exact (exercise_5_22_layer_convex q).segment_subset
    hx1Layer
    htopLayer
    (exercise_5_22_leftBoundaryPoint_mem_segment hq)

/-- Helper for Exercise 5.22: convexity of the layer keeps the corrected right bridge point inside
`exercise_5_22_layer q`. -/
lemma exercise_5_22_rightBoundaryPoint_mem_layer
    {q : ℕ}
    (hq : 2 ≤ q) :
    exercise_5_22_rightBoundaryPoint q ∈ exercise_5_22_layer q := by
  -- The symmetric bridge point lies on the opposite feasible edge.
  have haxes := exercise_5_22_axisVertices_mem_layer hq
  have hx0Layer : exercise_5_22_x0AxisVertex ∈ exercise_5_22_layer q := haxes.2.1
  have htopLayer : exercise_5_22_topVertex q ∈ exercise_5_22_layer q :=
    exercise_5_22_topVertex_mem_layer hq
  exact (exercise_5_22_layer_convex q).segment_subset
    hx0Layer
    htopLayer
    (exercise_5_22_rightBoundaryPoint_mem_segment hq)

/-- Helper for Exercise 5.22: the next top vertex lies on the segment from the corrected left
bridge point to `(1,0)`. -/
lemma exercise_5_22_nextTopVertex_eq_leftBoundaryLineMap
    {q : ℕ}
    (hq : 4 ≤ q) :
    exercise_5_22_topVertex (q ^ 2 - 2) =
      AffineMap.lineMap
        (exercise_5_22_leftBoundaryPoint q)
        exercise_5_22_x0AxisVertex
        (((q : ℝ) - 2) / ((q : ℝ) ^ 2 - 3)) := by
  have hq2 : 2 ≤ q := by
    omega
  have hq_real : (4 : ℝ) ≤ q := by
    exact_mod_cast hq
  have hq_sub_pos : 0 < (q : ℝ) - 1 := by
    nlinarith
  have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by
    linarith
  have hboundary_den_pos : 0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 :=
    exercise_5_22_boundaryPoint_denom_pos hq2
  have hboundary_den_ne : (q : ℝ) ^ 2 - (q : ℝ) - 1 ≠ 0 := by
    linarith
  have hnext_den_pos : 0 < (q : ℝ) ^ 2 - 3 := by
    nlinarith
  have hnext_den_ne : (q : ℝ) ^ 2 - 3 ≠ 0 := by
    linarith
  have hsq_lower : 2 ≤ q ^ 2 := by
    have hq_one : 1 ≤ q := by
      omega
    have hq_le_sq : q ≤ q ^ 2 := by
      simpa [pow_two, Nat.mul_comm] using (Nat.mul_le_mul_left q hq_one)
    exact le_trans (by omega) hq_le_sq
  -- Route correction: normalize the next apex first as `((q² - 2) : ℝ) / ((q² - 2 : ℕ) - 1)`,
  -- then clear the two explicit denominators instead of reopening the split-hull arithmetic.
  ext i
  fin_cases i
  · -- The first coordinate mixes the boundary-point coordinate with the axis endpoint.
    have hcoord :
        exercise_5_22_topVertex (q ^ 2 - 2) 0 =
          (AffineMap.lineMap
            (exercise_5_22_leftBoundaryPoint q)
            exercise_5_22_x0AxisVertex
            (((q : ℝ) - 2) / ((q : ℝ) ^ 2 - 3))) 0 := by
      have htop_den :
          (q : ℝ) ^ 2 - 2 - 1 = (q : ℝ) ^ 2 - 3 := by
        ring
      have hboundary_den_alt_ne : (q : ℝ) * ((q : ℝ) - 1) - 1 ≠ 0 := by
        intro hzero
        apply hboundary_den_ne
        nlinarith
      -- Clear the `q * (q - 1) - 1` denominator spelling before the polynomial normalization.
      simp [AffineMap.lineMap_apply_module, exercise_5_22_topVertex,
        exercise_5_22_leftBoundaryPoint, exercise_5_22_x0AxisVertex, Nat.cast_sub hsq_lower,
        htop_den]
      field_simp [hq_sub_ne, hboundary_den_alt_ne, hnext_den_ne]
      ring
    simpa using hcoord
  · -- The second coordinate is the old boundary height scaled by `1 - t`.
    have hcoord :
        exercise_5_22_topVertex (q ^ 2 - 2) 1 =
          (AffineMap.lineMap
            (exercise_5_22_leftBoundaryPoint q)
            exercise_5_22_x0AxisVertex
            (((q : ℝ) - 2) / ((q : ℝ) ^ 2 - 3))) 1 := by
      have htop_den :
          (q : ℝ) ^ 2 - 2 - 1 = (q : ℝ) ^ 2 - 3 := by
        ring
      have hboundary_den_alt_ne : (q : ℝ) * ((q : ℝ) - 1) - 1 ≠ 0 := by
        intro hzero
        apply hboundary_den_ne
        nlinarith
      -- The second coordinate uses the same denominator shape with no contribution from `(1,0)`.
      simp [AffineMap.lineMap_apply_module, exercise_5_22_topVertex,
        exercise_5_22_leftBoundaryPoint, exercise_5_22_x0AxisVertex, Nat.cast_sub hsq_lower,
        htop_den]
      field_simp [hq_sub_ne, hboundary_den_alt_ne, hnext_den_ne]
      ring
    simpa using hcoord

/-- Helper for Exercise 5.22: the next top vertex lies on the symmetric segment from the
corrected right bridge point to `(0,1)`. -/
lemma exercise_5_22_nextTopVertex_eq_rightBoundaryLineMap
    {q : ℕ}
    (hq : 4 ≤ q) :
    exercise_5_22_topVertex (q ^ 2 - 2) =
      AffineMap.lineMap
        (exercise_5_22_rightBoundaryPoint q)
        exercise_5_22_x1AxisVertex
        (((q : ℝ) - 2) / ((q : ℝ) ^ 2 - 3)) := by
  have hq2 : 2 ≤ q := by
    omega
  have hq_real : (4 : ℝ) ≤ q := by
    exact_mod_cast hq
  have hq_sub_pos : 0 < (q : ℝ) - 1 := by
    nlinarith
  have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by
    linarith
  have hboundary_den_pos : 0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 :=
    exercise_5_22_boundaryPoint_denom_pos hq2
  have hboundary_den_ne : (q : ℝ) ^ 2 - (q : ℝ) - 1 ≠ 0 := by
    linarith
  have hnext_den_pos : 0 < (q : ℝ) ^ 2 - 3 := by
    nlinarith
  have hnext_den_ne : (q : ℝ) ^ 2 - 3 ≠ 0 := by
    linarith
  have hsq_lower : 2 ≤ q ^ 2 := by
    have hq_one : 1 ≤ q := by
      omega
    have hq_le_sq : q ≤ q ^ 2 := by
      simpa [pow_two, Nat.mul_comm] using (Nat.mul_le_mul_left q hq_one)
    exact le_trans (by omega) hq_le_sq
  -- The symmetric next-apex identity uses the same denominator normalization after swapping
  -- coordinates and the axis endpoint.
  ext i
  fin_cases i
  · -- The first coordinate is now the boundary-point coordinate scaled by `1 - t`.
    have hcoord :
        exercise_5_22_topVertex (q ^ 2 - 2) 0 =
          (AffineMap.lineMap
            (exercise_5_22_rightBoundaryPoint q)
            exercise_5_22_x1AxisVertex
            (((q : ℝ) - 2) / ((q : ℝ) ^ 2 - 3))) 0 := by
      have htop_den :
          (q : ℝ) ^ 2 - 2 - 1 = (q : ℝ) ^ 2 - 3 := by
        ring
      have hboundary_den_alt_ne : (q : ℝ) * ((q : ℝ) - 1) - 1 ≠ 0 := by
        intro hzero
        apply hboundary_den_ne
        nlinarith
      -- The symmetric first coordinate has the same live denominator spelling.
      simp [AffineMap.lineMap_apply_module, exercise_5_22_topVertex,
        exercise_5_22_rightBoundaryPoint, exercise_5_22_x1AxisVertex, Nat.cast_sub hsq_lower,
        htop_den]
      field_simp [hq_sub_ne, hboundary_den_alt_ne, hnext_den_ne]
      ring
    simpa using hcoord
  · -- The second coordinate mixes the boundary-point coordinate with the axis endpoint.
    have hcoord :
        exercise_5_22_topVertex (q ^ 2 - 2) 1 =
          (AffineMap.lineMap
            (exercise_5_22_rightBoundaryPoint q)
            exercise_5_22_x1AxisVertex
            (((q : ℝ) - 2) / ((q : ℝ) ^ 2 - 3))) 1 := by
      have htop_den :
          (q : ℝ) ^ 2 - 2 - 1 = (q : ℝ) ^ 2 - 3 := by
        ring
      have hboundary_den_alt_ne : (q : ℝ) * ((q : ℝ) - 1) - 1 ≠ 0 := by
        intro hzero
        apply hboundary_den_ne
        nlinarith
      -- The symmetric second coordinate again clears by matching the live denominator syntax.
      simp [AffineMap.lineMap_apply_module, exercise_5_22_topVertex,
        exercise_5_22_rightBoundaryPoint, exercise_5_22_x1AxisVertex, Nat.cast_sub hsq_lower,
        htop_den]
      field_simp [hq_sub_ne, hboundary_den_alt_ne, hnext_den_ne]
      ring
    simpa using hcoord

/-- Helper for Exercise 5.22: the next top vertex lies on the left bridge-point-to-axis segment.
-/
lemma exercise_5_22_nextTopVertex_mem_leftBoundarySegment
    {q : ℕ}
    (hq : 4 ≤ q) :
    exercise_5_22_topVertex (q ^ 2 - 2) ∈
      segment ℝ (exercise_5_22_leftBoundaryPoint q) exercise_5_22_x0AxisVertex := by
  -- The explicit interpolation parameter stays in `[0, 1]` once `q ≥ 4`.
  rw [segment_eq_image_lineMap]
  refine ⟨((q : ℝ) - 2) / ((q : ℝ) ^ 2 - 3), ?_, ?_⟩
  · have hq_real : (4 : ℝ) ≤ q := by
      exact_mod_cast hq
    have hden : 0 < (q : ℝ) ^ 2 - 3 := by
      nlinarith
    refine ⟨?_, ?_⟩
    · exact div_nonneg (by nlinarith) hden.le
    · rw [div_le_one hden]
      nlinarith
  · simpa using (exercise_5_22_nextTopVertex_eq_leftBoundaryLineMap hq).symm

/-- Helper for Exercise 5.22: the next top vertex lies on the right bridge-point-to-axis segment.
-/
lemma exercise_5_22_nextTopVertex_mem_rightBoundarySegment
    {q : ℕ}
    (hq : 4 ≤ q) :
    exercise_5_22_topVertex (q ^ 2 - 2) ∈
      segment ℝ (exercise_5_22_rightBoundaryPoint q) exercise_5_22_x1AxisVertex := by
  -- The same parameter gives the symmetric segment containment.
  rw [segment_eq_image_lineMap]
  refine ⟨((q : ℝ) - 2) / ((q : ℝ) ^ 2 - 3), ?_, ?_⟩
  · have hq_real : (4 : ℝ) ≤ q := by
      exact_mod_cast hq
    have hden : 0 < (q : ℝ) ^ 2 - 3 := by
      nlinarith
    refine ⟨?_, ?_⟩
    · exact div_nonneg (by nlinarith) hden.le
    · rw [div_le_one hden]
      nlinarith
  · simpa using (exercise_5_22_nextTopVertex_eq_rightBoundaryLineMap hq).symm

/-- Helper for Exercise 5.22: every layer point lies in one of the two triangles spanned by the
origin, one axis vertex, and the top vertex. -/
lemma exercise_5_22_layer_subset_triangleUnion
    {q : ℕ}
    (hq : 2 ≤ q)
    {x : Fin 2 → ℝ}
    (hx : x ∈ exercise_5_22_layer q) :
    x ∈ convexHull ℝ
          (Set.range fun i : Fin 3 ↦
            match i with
            | 0 => exercise_5_22_origin
            | 1 => exercise_5_22_x0AxisVertex
            | _ => exercise_5_22_topVertex q) ∨
      x ∈ convexHull ℝ
          (Set.range fun i : Fin 3 ↦
            match i with
            | 0 => exercise_5_22_origin
            | 1 => exercise_5_22_x1AxisVertex
            | _ => exercise_5_22_topVertex q) := by
  -- Route correction: this target-side triangle cover replaces the earlier dead-end attempt to
  -- prove a full convex-hull equality for the current layer.
  rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_trans (by norm_num) hq)
  have hq_ne : (q : ℝ) ≠ 0 := by linarith
  have hq_sub_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have hq_gt_one : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
    linarith
  have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by linarith
  by_cases hcase : x 1 ≤ x 0
  · left
    let w : Fin 3 → ℝ
      | 0 => 1 - x 0 + x 1 / (q : ℝ)
      | 1 => x 0 - x 1
      | _ => x 1 * (((q : ℝ) - 1) / (q : ℝ))
    have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
      intro i
      fin_cases i
      · simp [w]
        nlinarith
      · simp [w]
        linarith
      · have hratio_nonneg : 0 ≤ ((q : ℝ) - 1) / (q : ℝ) := by
          positivity
        simpa [w] using mul_nonneg hx1 hratio_nonneg
    have hw_sum : ∑ i, w i = 1 := by
      simp [w, Fin.sum_univ_three]
      field_simp [hq_ne]
      ring
    -- These barycentric coordinates reconstruct `x` inside the triangle
    -- `{origin, (1,0), topVertex q}`.
    refine mem_convexHull_of_exists_fintype w
      (fun i : Fin 3 ↦
        match i with
        | 0 => exercise_5_22_origin
        | 1 => exercise_5_22_x0AxisVertex
        | _ => exercise_5_22_topVertex q)
      hw_nonneg hw_sum (fun i ↦ Set.mem_range_self i) ?_
    ext j
    fin_cases j
    · simp [w, exercise_5_22_origin, exercise_5_22_x0AxisVertex,
        exercise_5_22_topVertex, Fin.sum_univ_three]
      field_simp [hq_ne, hq_sub_ne]
      ring
    · simp [w, exercise_5_22_origin, exercise_5_22_x0AxisVertex,
        exercise_5_22_topVertex, Fin.sum_univ_three]
      field_simp [hq_ne, hq_sub_ne]
  · right
    have hcase' : x 0 ≤ x 1 := by linarith
    let w : Fin 3 → ℝ
      | 0 => 1 - x 1 + x 0 / (q : ℝ)
      | 1 => x 1 - x 0
      | _ => x 0 * (((q : ℝ) - 1) / (q : ℝ))
    have hw_nonneg : ∀ i : Fin 3, 0 ≤ w i := by
      intro i
      fin_cases i
      · simp [w]
        nlinarith
      · simp [w]
        linarith
      · have hratio_nonneg : 0 ≤ ((q : ℝ) - 1) / (q : ℝ) := by
          positivity
        simpa [w] using mul_nonneg hx0 hratio_nonneg
    have hw_sum : ∑ i, w i = 1 := by
      simp [w, Fin.sum_univ_three]
      field_simp [hq_ne]
      ring
    -- The symmetric barycentric formula places `x` in the triangle
    -- `{origin, (0,1), topVertex q}`.
    refine mem_convexHull_of_exists_fintype w
      (fun i : Fin 3 ↦
        match i with
        | 0 => exercise_5_22_origin
        | 1 => exercise_5_22_x1AxisVertex
        | _ => exercise_5_22_topVertex q)
      hw_nonneg hw_sum (fun i ↦ Set.mem_range_self i) ?_
    ext j
    fin_cases j
    · simp [w, exercise_5_22_origin, exercise_5_22_x1AxisVertex,
        exercise_5_22_topVertex, Fin.sum_univ_three]
      field_simp [hq_ne, hq_sub_ne]
    · simp [w, exercise_5_22_origin, exercise_5_22_x1AxisVertex,
        exercise_5_22_topVertex, Fin.sum_univ_three]
      field_simp [hq_ne, hq_sub_ne]
      ring

/-- Helper for Exercise 5.22: once the origin is on the lower side and the top vertex stays in
the split strip, any upper-branch witness forces one axis vertex onto the upper side as well. -/
lemma exercise_5_22_upperWitness_forces_axisUpper
    {q : ℕ}
    (hq : 4 ≤ q)
    {π : Fin 2 → ℤ}
    {π0 : ℤ}
    (horigin :
      exercise_5_22_origin ∈ split_branch_lower (exercise_5_22_layer q) π π0)
    (htop_strip :
      exercise_5_22_topVertex q ∈ split_strip π π0)
    (hupper_nonempty :
      Set.Nonempty (split_branch_upper (exercise_5_22_layer q) π π0)) :
    exercise_5_22_x0AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) π π0 ∨
      exercise_5_22_x1AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) π π0 := by
  -- Route correction: use the triangle cover only to force an upper axis vertex from a single
  -- upper witness, instead of reopening the failed global convex-hull route.
  have hq2 : 2 ≤ q := by omega
  have haxes := exercise_5_22_axisVertices_mem_layer hq2
  have hx0Layer : exercise_5_22_x0AxisVertex ∈ exercise_5_22_layer q := haxes.2.1
  have hx1Layer : exercise_5_22_x1AxisVertex ∈ exercise_5_22_layer q := haxes.2.2
  rcases (mem_split_branch_lower_iff).1 horigin with ⟨_, horigin_lower⟩
  rcases (mem_split_strip_iff).1 htop_strip with ⟨_, htop_upper_strict⟩
  rcases hupper_nonempty with ⟨y, hyUpper⟩
  rcases (mem_split_branch_upper_iff).1 hyUpper with ⟨hyLayer, hyUpperIneq⟩
  rcases exercise_5_22_layer_subset_triangleUnion hq2 hyLayer with hyTri | hyTri
  · by_cases hx0Upper :
        exercise_5_22_x0AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) π π0
    · exact Or.inl hx0Upper
    · have horigin_strict :
          exercise_5_22_origin ∈ {x : Fin 2 → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
        -- The lower branch bound is strictly below the upper split threshold.
        change split_dot π exercise_5_22_origin < (π0 : ℝ) + 1
        linarith
      have hx0_strict :
          exercise_5_22_x0AxisVertex ∈ {x : Fin 2 → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
        -- If the axis vertex were not strictly below `π₀ + 1`, it would already be upper.
        have hx0_not_upper_ineq : ¬ (π0 : ℝ) + 1 ≤ split_dot π exercise_5_22_x0AxisVertex := by
          intro hx0_upper_ineq
          exact hx0Upper ((mem_split_branch_upper_iff).2 ⟨hx0Layer, hx0_upper_ineq⟩)
        exact lt_of_not_ge hx0_not_upper_ineq
      have htop_strict :
          exercise_5_22_topVertex q ∈ {x : Fin 2 → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
        exact htop_upper_strict
      have hy_strict :
          y ∈ {x : Fin 2 → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
        -- Convexity of the strict halfspace propagates the vertex inequalities to the witness.
        refine convexHull_min ?_ (split_dot_strict_upper_halfspace_convex π π0) hyTri
        rintro z ⟨i, rfl⟩
        fin_cases i
        · exact horigin_strict
        · exact hx0_strict
        · exact htop_strict
      have hy_upper_strict : split_dot π y < (π0 : ℝ) + 1 := hy_strict
      linarith
  · by_cases hx1Upper :
        exercise_5_22_x1AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) π π0
    · exact Or.inr hx1Upper
    · have horigin_strict :
          exercise_5_22_origin ∈ {x : Fin 2 → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
        -- The origin remains strictly below the upper split threshold.
        change split_dot π exercise_5_22_origin < (π0 : ℝ) + 1
        linarith
      have hx1_strict :
          exercise_5_22_x1AxisVertex ∈ {x : Fin 2 → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
        -- If the other axis vertex were not strict, it would already be an upper witness.
        have hx1_not_upper_ineq : ¬ (π0 : ℝ) + 1 ≤ split_dot π exercise_5_22_x1AxisVertex := by
          intro hx1_upper_ineq
          exact hx1Upper ((mem_split_branch_upper_iff).2 ⟨hx1Layer, hx1_upper_ineq⟩)
        exact lt_of_not_ge hx1_not_upper_ineq
      have htop_strict :
          exercise_5_22_topVertex q ∈ {x : Fin 2 → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
        exact htop_upper_strict
      have hy_strict :
          y ∈ {x : Fin 2 → ℝ | split_dot π x < (π0 : ℝ) + 1} := by
        -- The symmetric triangle argument forces the witness below `π₀ + 1`.
        refine convexHull_min ?_ (split_dot_strict_upper_halfspace_convex π π0) hyTri
        rintro z ⟨i, rfl⟩
        fin_cases i
        · exact horigin_strict
        · exact hx1_strict
        · exact htop_strict
      have hy_upper_strict : split_dot π y < (π0 : ℝ) + 1 := hy_strict
      linarith

/-- Helper for Exercise 5.22: the strip condition forces a quotient-remainder normal form for the
integer threshold `π₀`, and hence fixes the top split coefficient sum. -/
lemma exercise_5_22_stripThreshold_quotientRemainder
    {q : ℕ}
    (hq : 4 ≤ q)
    {π : Fin 2 → ℤ}
    {π0 : ℤ}
    (horigin :
      exercise_5_22_origin ∈ split_branch_lower (exercise_5_22_layer q) π π0)
    (htop_strip :
      exercise_5_22_topVertex q ∈ split_strip π π0) :
    0 ≤ π0 / (q : ℤ) ∧
      1 ≤ π0 % (q : ℤ) ∧
      π0 % (q : ℤ) ≤ (q : ℤ) - 2 ∧
      π 0 + π 1 = π0 - π0 / (q : ℤ) := by
  rcases (mem_split_branch_lower_iff).1 horigin with ⟨_, horigin_lower⟩
  rcases (mem_split_strip_iff).1 htop_strip with ⟨htop_lower, htop_upper⟩
  rw [exercise_5_22_split_dot_origin] at horigin_lower
  rw [exercise_5_22_split_dot_topVertex] at htop_lower htop_upper
  set a : ℤ := π0 / (q : ℤ)
  set r : ℤ := π0 % (q : ℤ)
  set m : ℤ := π 0 + π 1
  have hq_int_pos : 0 < (q : ℤ) := by
    exact_mod_cast (show 0 < q by omega)
  have hq_sub_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have hq_gt_one : (1 : ℝ) < q := by
      exact_mod_cast (show 1 < q by omega)
    linarith
  have hpi0_nonneg : 0 ≤ π0 := by
    exact_mod_cast horigin_lower
  have hm_lower_real :
      (π0 : ℝ) * ((q : ℝ) - 1) < (q : ℝ) * (m : ℝ) := by
    have htop_lower' :
        (π0 : ℝ) < (q : ℝ) * (m : ℝ) / ((q : ℝ) - 1) := by
      simpa [m] using htop_lower
    rw [lt_div_iff₀ hq_sub_pos] at htop_lower'
    simpa [mul_comm, mul_left_comm, mul_assoc] using htop_lower'
  have hm_upper_real :
      (q : ℝ) * (m : ℝ) < (((π0 + 1 : ℤ) : ℝ) * ((q : ℝ) - 1)) := by
    have htop_upper' :
        (q : ℝ) * (m : ℝ) / ((q : ℝ) - 1) < (π0 : ℝ) + 1 := by
      simpa [m] using htop_upper
    rw [div_lt_iff₀ hq_sub_pos] at htop_upper'
    simpa [mul_comm, mul_left_comm, mul_assoc] using htop_upper'
  have hm_lower :
      π0 * ((q : ℤ) - 1) + 1 ≤ (q : ℤ) * m := by
    have hm_lower_int : π0 * ((q : ℤ) - 1) < (q : ℤ) * m := by
      exact_mod_cast hm_lower_real
    omega
  have hm_upper :
      (q : ℤ) * m ≤ π0 * ((q : ℤ) - 1) + ((q : ℤ) - 2) := by
    have hm_upper_int : (q : ℤ) * m < (π0 + 1) * ((q : ℤ) - 1) := by
      exact_mod_cast hm_upper_real
    have hm_upper_step : (q : ℤ) * m + 1 ≤ (π0 + 1) * ((q : ℤ) - 1) := by
      omega
    nlinarith
  have hdivmod : (q : ℤ) * a + r = π0 := by
    simpa [a, r] using (Int.mul_ediv_add_emod π0 (q : ℤ))
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg _ (by omega)
  have hr_lt : r < (q : ℤ) := by
    dsimp [r]
    exact Int.emod_lt_of_pos _ hq_int_pos
  have hcandidate :
      (q : ℤ) * (π0 - a) = π0 * ((q : ℤ) - 1) + r := by
    nlinarith [hdivmod]
  let k : ℤ := m - (π0 - a)
  have hk_lower : -((q : ℤ) - 1) ≤ (q : ℤ) * k := by
    have hstep : 1 - r ≤ (q : ℤ) * k := by
      nlinarith [hm_lower, hcandidate]
    nlinarith
  have hk_upper : (q : ℤ) * k ≤ (q : ℤ) - 2 := by
    have hstep : (q : ℤ) * k ≤ (q : ℤ) - 2 - r := by
      nlinarith [hm_upper, hcandidate]
    nlinarith
  have hk_zero : k = 0 := by
    by_cases hk_pos : 0 < k
    · have hq_le : (q : ℤ) ≤ (q : ℤ) * k := by
        nlinarith
      linarith
    · by_cases hk_neg : k < 0
      · have hk_le_neg_q : (q : ℤ) * k ≤ -(q : ℤ) := by
          nlinarith
        linarith
      · omega
  have hm_eq : m = π0 - a := by
    have hk_zero' : m - (π0 - a) = 0 := by
      simpa [k] using hk_zero
    omega
  have hqm :
      (q : ℤ) * m = π0 * ((q : ℤ) - 1) + r := by
    nlinarith [hm_eq, hcandidate]
  have hr_lower : 1 ≤ r := by
    nlinarith [hm_lower, hqm]
  have hr_upper : r ≤ (q : ℤ) - 2 := by
    nlinarith [hm_upper, hqm]
  have ha_nonneg : 0 ≤ a := by
    by_contra ha_neg
    have ha_le : a ≤ -1 := by omega
    have hpi0_neg : π0 < 0 := by
      nlinarith [hdivmod, hr_lt, ha_le]
    exact (not_lt_of_ge hpi0_nonneg) hpi0_neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [a] using ha_nonneg
  · simpa [r] using hr_lower
  · simpa [r] using hr_upper
  · simpa [a, m] using hm_eq

/-- Helper for Exercise 5.22: in normalized split position, if `(1,0)` is on the upper branch,
then the corrected left boundary point is forced onto the lower branch. -/
lemma exercise_5_22_leftBoundaryPoint_mem_lower_of_normalized
    {q : ℕ}
    (hq : 4 ≤ q)
    {π : Fin 2 → ℤ}
    {π0 : ℤ}
    (horigin :
      exercise_5_22_origin ∈ split_branch_lower (exercise_5_22_layer q) π π0)
    (htop_strip :
      exercise_5_22_topVertex q ∈ split_strip π π0)
    (hx0_upper :
      exercise_5_22_x0AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) π π0) :
    exercise_5_22_leftBoundaryPoint q ∈ split_branch_lower (exercise_5_22_layer q) π π0 := by
  have hq2 : 2 ≤ q := by omega
  have hleft_mem : exercise_5_22_leftBoundaryPoint q ∈ exercise_5_22_layer q :=
    exercise_5_22_leftBoundaryPoint_mem_layer hq2
  rcases (mem_split_branch_upper_iff).1 hx0_upper with ⟨_, hx0_upper_ineq⟩
  rcases exercise_5_22_stripThreshold_quotientRemainder hq horigin htop_strip with
    ⟨ha_nonneg, hr_lower, hr_upper, hm_eq⟩
  have hx0_upper_int : π0 + 1 ≤ π 0 := by
    rw [exercise_5_22_split_dot_x0AxisVertex] at hx0_upper_ineq
    exact_mod_cast hx0_upper_ineq
  set a : ℤ := π0 / (q : ℤ)
  set r : ℤ := π0 % (q : ℤ)
  have hpi0_decomp : π0 = (q : ℤ) * a + r := by
    simpa [a, r] using (Int.mul_ediv_add_emod π0 (q : ℤ)).symm
  have hm_eq' : π 0 + π 1 = π0 - a := by
    simpa [a] using hm_eq
  have hp1_upper : π 1 ≤ -a - 1 := by
    omega
  refine (mem_split_branch_lower_iff).2 ⟨hleft_mem, ?_⟩
  -- Rewrite the bridge-point split value and bound its numerator using the forced negative
  -- second coefficient.
  rw [exercise_5_22_split_dot_leftBoundaryPoint]
  have hden_pos : 0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 :=
    exercise_5_22_boundaryPoint_denom_pos hq2
  refine (div_le_iff₀ hden_pos).2 ?_
  have hnum_int :
      π 0 * (q : ℤ) * ((q : ℤ) - 1) + π 1 * ((q : ℤ) ^ 2 - 2) ≤
        π0 * ((q : ℤ) ^ 2 - (q : ℤ) - 1) := by
    have hq_sub_two_nonneg : 0 ≤ (q : ℤ) - 2 := by
      omega
    have hrewrite :
        π 0 * (q : ℤ) * ((q : ℤ) - 1) + π 1 * ((q : ℤ) ^ 2 - 2) =
          (π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + π 1 * ((q : ℤ) - 2) := by
      nlinarith [hm_eq']
    rw [hrewrite]
    have hbound1 :
        (π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + π 1 * ((q : ℤ) - 2) ≤
          (π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + (-a - 1) * ((q : ℤ) - 2) := by
      nlinarith [hp1_upper, hq_sub_two_nonneg]
    have hbound2 :
        (π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + (-a - 1) * ((q : ℤ) - 2) ≤
          π0 * ((q : ℤ) ^ 2 - (q : ℤ) - 1) := by
      have hq_add_one_nonneg : 0 ≤ (q : ℤ) + 1 := by
        omega
      have hrem_nonneg : 0 ≤ (q : ℤ) - 2 - r := by
        omega
      have hdiff :
          π0 * ((q : ℤ) ^ 2 - (q : ℤ) - 1) -
              ((π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + (-a - 1) * ((q : ℤ) - 2)) =
            a * ((q : ℤ) - 2) * ((q : ℤ) + 1) + ((q : ℤ) - 2 - r) := by
        nlinarith [hpi0_decomp]
      have hprod_nonneg : 0 ≤ a * ((q : ℤ) - 2) * ((q : ℤ) + 1) := by
        have hmul_nonneg : 0 ≤ a * ((q : ℤ) - 2) := by
          exact mul_nonneg ha_nonneg hq_sub_two_nonneg
        exact mul_nonneg hmul_nonneg hq_add_one_nonneg
      have hdiff_nonneg :
          0 ≤ π0 * ((q : ℤ) ^ 2 - (q : ℤ) - 1) -
              ((π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + (-a - 1) * ((q : ℤ) - 2)) := by
        rw [hdiff]
        nlinarith
      linarith
    exact hbound1.trans hbound2
  exact_mod_cast hnum_int

/-- Helper for Exercise 5.22: in normalized split position, if `(0,1)` is on the upper branch,
then the corrected right boundary point is forced onto the lower branch. -/
lemma exercise_5_22_rightBoundaryPoint_mem_lower_of_normalized
    {q : ℕ}
    (hq : 4 ≤ q)
    {π : Fin 2 → ℤ}
    {π0 : ℤ}
    (horigin :
      exercise_5_22_origin ∈ split_branch_lower (exercise_5_22_layer q) π π0)
    (htop_strip :
      exercise_5_22_topVertex q ∈ split_strip π π0)
    (hx1_upper :
      exercise_5_22_x1AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) π π0) :
    exercise_5_22_rightBoundaryPoint q ∈ split_branch_lower (exercise_5_22_layer q) π π0 := by
  have hq2 : 2 ≤ q := by omega
  have hright_mem : exercise_5_22_rightBoundaryPoint q ∈ exercise_5_22_layer q :=
    exercise_5_22_rightBoundaryPoint_mem_layer hq2
  rcases (mem_split_branch_upper_iff).1 hx1_upper with ⟨_, hx1_upper_ineq⟩
  rcases exercise_5_22_stripThreshold_quotientRemainder hq horigin htop_strip with
    ⟨ha_nonneg, hr_lower, hr_upper, hm_eq⟩
  have hx1_upper_int : π0 + 1 ≤ π 1 := by
    rw [exercise_5_22_split_dot_x1AxisVertex] at hx1_upper_ineq
    exact_mod_cast hx1_upper_ineq
  set a : ℤ := π0 / (q : ℤ)
  set r : ℤ := π0 % (q : ℤ)
  have hpi0_decomp : π0 = (q : ℤ) * a + r := by
    simpa [a, r] using (Int.mul_ediv_add_emod π0 (q : ℤ)).symm
  have hm_eq' : π 0 + π 1 = π0 - a := by
    simpa [a] using hm_eq
  have hp0_upper : π 0 ≤ -a - 1 := by
    omega
  refine (mem_split_branch_lower_iff).2 ⟨hright_mem, ?_⟩
  -- Use the symmetric bridge-point formula and the forced negative first coefficient.
  rw [exercise_5_22_split_dot_rightBoundaryPoint]
  have hden_pos : 0 < (q : ℝ) ^ 2 - (q : ℝ) - 1 :=
    exercise_5_22_boundaryPoint_denom_pos hq2
  refine (div_le_iff₀ hden_pos).2 ?_
  have hnum_int :
      π 0 * ((q : ℤ) ^ 2 - 2) + π 1 * (q : ℤ) * ((q : ℤ) - 1) ≤
        π0 * ((q : ℤ) ^ 2 - (q : ℤ) - 1) := by
    have hq_sub_two_nonneg : 0 ≤ (q : ℤ) - 2 := by
      omega
    have hrewrite :
        π 0 * ((q : ℤ) ^ 2 - 2) + π 1 * (q : ℤ) * ((q : ℤ) - 1) =
          (π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + π 0 * ((q : ℤ) - 2) := by
      nlinarith [hm_eq']
    rw [hrewrite]
    have hbound1 :
        (π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + π 0 * ((q : ℤ) - 2) ≤
          (π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + (-a - 1) * ((q : ℤ) - 2) := by
      nlinarith [hp0_upper, hq_sub_two_nonneg]
    have hbound2 :
        (π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + (-a - 1) * ((q : ℤ) - 2) ≤
          π0 * ((q : ℤ) ^ 2 - (q : ℤ) - 1) := by
      have hq_add_one_nonneg : 0 ≤ (q : ℤ) + 1 := by
        omega
      have hrem_nonneg : 0 ≤ (q : ℤ) - 2 - r := by
        omega
      have hdiff :
          π0 * ((q : ℤ) ^ 2 - (q : ℤ) - 1) -
              ((π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + (-a - 1) * ((q : ℤ) - 2)) =
            a * ((q : ℤ) - 2) * ((q : ℤ) + 1) + ((q : ℤ) - 2 - r) := by
        nlinarith [hpi0_decomp]
      have hprod_nonneg : 0 ≤ a * ((q : ℤ) - 2) * ((q : ℤ) + 1) := by
        have hmul_nonneg : 0 ≤ a * ((q : ℤ) - 2) := by
          exact mul_nonneg ha_nonneg hq_sub_two_nonneg
        exact mul_nonneg hmul_nonneg hq_add_one_nonneg
      have hdiff_nonneg :
          0 ≤ π0 * ((q : ℤ) ^ 2 - (q : ℤ) - 1) -
              ((π0 - a) * (q : ℤ) * ((q : ℤ) - 1) + (-a - 1) * ((q : ℤ) - 2)) := by
        rw [hdiff]
        nlinarith
      linarith
    exact hbound1.trans hbound2
  exact_mod_cast hnum_int

/-- Helper for Exercise 5.22: once the split is normalized and one axis vertex is forced onto the
upper branch, the next top vertex lies in the corresponding split hull. -/
lemma exercise_5_22_nextTopVertex_mem_normalizedSplitHull
    {q : ℕ}
    (hq : 4 ≤ q)
    {π : Fin 2 → ℤ}
    {π0 : ℤ}
    (horigin :
      exercise_5_22_origin ∈ split_branch_lower (exercise_5_22_layer q) π π0)
    (htop_strip :
      exercise_5_22_topVertex q ∈ split_strip π π0)
    (haxis_upper :
      exercise_5_22_x0AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) π π0 ∨
        exercise_5_22_x1AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) π π0) :
    exercise_5_22_topVertex (q ^ 2 - 2) ∈ split_hull (exercise_5_22_layer q) π π0 := by
  rcases haxis_upper with hx0_upper | hx1_upper
  · -- Use the left bridge point and the upper `(1,0)` vertex to span the next apex.
    have hleft_lower :
        exercise_5_22_leftBoundaryPoint q ∈ split_branch_lower (exercise_5_22_layer q) π π0 :=
      exercise_5_22_leftBoundaryPoint_mem_lower_of_normalized hq horigin htop_strip hx0_upper
    exact mem_split_hull_of_segment
      (Or.inl hleft_lower)
      (Or.inr hx0_upper)
      (exercise_5_22_nextTopVertex_mem_leftBoundarySegment hq)
  · -- The symmetric branch uses the right bridge point and the upper `(0,1)` vertex.
    have hright_lower :
        exercise_5_22_rightBoundaryPoint q ∈ split_branch_lower (exercise_5_22_layer q) π π0 :=
      exercise_5_22_rightBoundaryPoint_mem_lower_of_normalized hq horigin htop_strip hx1_upper
    exact mem_split_hull_of_segment
      (Or.inl hright_lower)
      (Or.inr hx1_upper)
      (exercise_5_22_nextTopVertex_mem_rightBoundarySegment hq)

/-- Helper for Exercise 5.22: the next top vertex lies on the diagonal segment from the origin to
the current top vertex. -/
lemma exercise_5_22_nextTopVertex_mem_originTopSegment
    {q : ℕ}
    (hq : 4 ≤ q) :
    exercise_5_22_topVertex (q ^ 2 - 2) ∈
      segment ℝ exercise_5_22_origin (exercise_5_22_topVertex q) := by
  -- Use the explicit diagonal interpolation parameter and check that it lies in `[0, 1]`.
  rw [segment_eq_image_lineMap]
  refine ⟨((q : ℝ) - 1) * ((q : ℝ) ^ 2 - 2) / ((q : ℝ) * ((q : ℝ) ^ 2 - 3)), ?_, ?_⟩
  · have hq_real : (4 : ℝ) ≤ q := by
      exact_mod_cast hq
    have hq_pos : (0 : ℝ) < q := by
      nlinarith
    have hden_pos : 0 < (q : ℝ) * ((q : ℝ) ^ 2 - 3) := by
      have hquad_pos : 0 < (q : ℝ) ^ 2 - 3 := by
        nlinarith
      positivity
    refine ⟨?_, ?_⟩
    · exact div_nonneg (by nlinarith) hden_pos.le
    · rw [div_le_one hden_pos]
      nlinarith
  · -- Both coordinates collapse to the same scalar identity after clearing denominators.
    ext i
    fin_cases i
    · have hq_real : (4 : ℝ) ≤ q := by
        exact_mod_cast hq
      have hq_ne : (q : ℝ) ≠ 0 := by
        nlinarith
      have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by
        nlinarith
      have hnext_den_ne : ((q : ℝ) ^ 2 - 3) ≠ 0 := by
        nlinarith
      have hsq_lower : 2 ≤ q ^ 2 := by
        have hq_one : 1 ≤ q := by
          omega
        have hq_le_sq : q ≤ q ^ 2 := by
          simpa [pow_two, Nat.mul_comm] using (Nat.mul_le_mul_left q hq_one)
        exact le_trans (by omega) hq_le_sq
      have hcoord :
          exercise_5_22_topVertex (q ^ 2 - 2) 0 =
            (AffineMap.lineMap
              exercise_5_22_origin
              (exercise_5_22_topVertex q)
              (((q : ℝ) - 1) * ((q : ℝ) ^ 2 - 2) / ((q : ℝ) * ((q : ℝ) ^ 2 - 3)))) 0 := by
        have hscalar :
            ((q : ℝ) ^ 2 - 2) / ((q : ℝ) ^ 2 - 3) =
              (((q : ℝ) - 1) * ((q : ℝ) ^ 2 - 2) / ((q : ℝ) * ((q : ℝ) ^ 2 - 3))) *
                ((q : ℝ) / ((q : ℝ) - 1)) := by
          field_simp [hq_ne, hq_sub_ne, hnext_den_ne]
        have htop_den :
            (q : ℝ) ^ 2 - 2 - 1 = (q : ℝ) ^ 2 - 3 := by
          ring
        simpa [AffineMap.lineMap_apply_module, exercise_5_22_topVertex, exercise_5_22_origin,
          Nat.cast_sub hsq_lower, htop_den] using hscalar
      simpa using hcoord.symm
    · have hq_real : (4 : ℝ) ≤ q := by
        exact_mod_cast hq
      have hq_ne : (q : ℝ) ≠ 0 := by
        nlinarith
      have hq_sub_ne : (q : ℝ) - 1 ≠ 0 := by
        nlinarith
      have hnext_den_ne : ((q : ℝ) ^ 2 - 3) ≠ 0 := by
        nlinarith
      have hsq_lower : 2 ≤ q ^ 2 := by
        have hq_one : 1 ≤ q := by
          omega
        have hq_le_sq : q ≤ q ^ 2 := by
          simpa [pow_two, Nat.mul_comm] using (Nat.mul_le_mul_left q hq_one)
        exact le_trans (by omega) hq_le_sq
      have hcoord :
          exercise_5_22_topVertex (q ^ 2 - 2) 1 =
            (AffineMap.lineMap
              exercise_5_22_origin
              (exercise_5_22_topVertex q)
              (((q : ℝ) - 1) * ((q : ℝ) ^ 2 - 2) / ((q : ℝ) * ((q : ℝ) ^ 2 - 3)))) 1 := by
        have hscalar :
            ((q : ℝ) ^ 2 - 2) / ((q : ℝ) ^ 2 - 3) =
              (((q : ℝ) - 1) * ((q : ℝ) ^ 2 - 2) / ((q : ℝ) * ((q : ℝ) ^ 2 - 3))) *
                ((q : ℝ) / ((q : ℝ) - 1)) := by
          field_simp [hq_ne, hq_sub_ne, hnext_den_ne]
        have htop_den :
            (q : ℝ) ^ 2 - 2 - 1 = (q : ℝ) ^ 2 - 3 := by
          ring
        simpa [AffineMap.lineMap_apply_module, exercise_5_22_topVertex, exercise_5_22_origin,
          Nat.cast_sub hsq_lower, htop_den] using hscalar
      simpa using hcoord.symm

/-- Helper for Exercise 5.22: in the genuine strip case, one sign normalization suffices to place
the next top vertex into the arbitrary split hull. -/
lemma exercise_5_22_nextTopVertex_mem_twoSideSplitHullOfStripCase
    {q : ℕ}
    (hq : 4 ≤ q)
    (s : TwoSideSplit (exercise_5_22_layer q))
    (htop_strip :
      exercise_5_22_topVertex q ∈ split_strip s.π s.π0) :
    exercise_5_22_topVertex (q ^ 2 - 2) ∈
      split_hull (exercise_5_22_layer q) s.π s.π0 := by
  have hq2 : 2 ≤ q := by
    omega
  have haxes := exercise_5_22_axisVertices_mem_layer hq2
  by_cases hπ0_nonneg : 0 ≤ s.π0
  · have horigin_lower :
        exercise_5_22_origin ∈ split_branch_lower (exercise_5_22_layer q) s.π s.π0 := by
      -- When `π₀ ≥ 0`, the origin lies on the lower side because its split value is `0`.
      refine (mem_split_branch_lower_iff).2 ⟨haxes.1, ?_⟩
      rw [exercise_5_22_split_dot_origin]
      exact_mod_cast hπ0_nonneg
    have haxis_upper :
        exercise_5_22_x0AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) s.π s.π0 ∨
          exercise_5_22_x1AxisVertex ∈ split_branch_upper (exercise_5_22_layer q) s.π s.π0 :=
      exercise_5_22_upperWitness_forces_axisUpper hq horigin_lower htop_strip s.upper_nonempty
    exact exercise_5_22_nextTopVertex_mem_normalizedSplitHull
      hq horigin_lower htop_strip haxis_upper
  · have horigin_lower_neg :
        exercise_5_22_origin ∈
          split_branch_lower (exercise_5_22_layer q) (-s.π) (-s.π0 - 1) := by
      -- Route correction: if the origin is upper for `(π, π₀)`, flip the split once so the
      -- origin becomes lower for `(-π, -π₀ - 1)`.
      refine (mem_split_branch_lower_iff).2 ⟨haxes.1, ?_⟩
      rw [exercise_5_22_split_dot_origin]
      have hπ0_le_neg_one : s.π0 + 1 ≤ 0 := by
        omega
      have hbound_int : (0 : ℤ) ≤ -s.π0 - 1 := by
        omega
      have hbound : (0 : ℝ) ≤ (((-s.π0 - 1 : ℤ) : ℝ)) := by
        exact_mod_cast hbound_int
      simpa using hbound
    have htop_strip_neg :
        exercise_5_22_topVertex q ∈ split_strip (-s.π) (-s.π0 - 1) := by
      -- Negating the split data preserves strip membership after rewriting both strict bounds.
      rcases (mem_split_strip_iff).1 htop_strip with ⟨htop_lower, htop_upper⟩
      refine (mem_split_strip_iff).2 ?_
      rw [split_dot_neg]
      constructor
      · have hcast : (((-s.π0 - 1 : ℤ) : ℝ)) = -((s.π0 : ℝ) + 1) := by
          norm_num
          ring
        have hlower : -((s.π0 : ℝ) + 1) < -split_dot s.π (exercise_5_22_topVertex q) := by
          linarith
        simpa [hcast] using hlower
      · have hcast : (((-s.π0 - 1 : ℤ) : ℝ) + 1) = -(s.π0 : ℝ) := by
          norm_num
        have hupper : -split_dot s.π (exercise_5_22_topVertex q) < -(s.π0 : ℝ) := by
          linarith
        simpa [hcast] using hupper
    have hupper_nonempty_neg :
        Set.Nonempty (split_branch_upper (exercise_5_22_layer q) (-s.π) (-s.π0 - 1)) := by
      -- The original lower witness becomes an upper witness after the sign flip.
      rcases s.lower_nonempty with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rcases (mem_split_branch_lower_iff).1 hy with ⟨hyLayer, hyLower⟩
      refine (mem_split_branch_upper_iff).2 ⟨hyLayer, ?_⟩
      rw [split_dot_neg]
      have hcast : (((-s.π0 - 1 : ℤ) : ℝ) + 1) = -(s.π0 : ℝ) := by
        norm_num
      have hyUpper : -(s.π0 : ℝ) ≤ -split_dot s.π y := by
        linarith
      simpa [hcast] using hyUpper
    have haxis_upper_neg :
        exercise_5_22_x0AxisVertex ∈
            split_branch_upper (exercise_5_22_layer q) (-s.π) (-s.π0 - 1) ∨
          exercise_5_22_x1AxisVertex ∈
            split_branch_upper (exercise_5_22_layer q) (-s.π) (-s.π0 - 1) :=
      exercise_5_22_upperWitness_forces_axisUpper
        hq horigin_lower_neg htop_strip_neg hupper_nonempty_neg
    have hnext_neg :
        exercise_5_22_topVertex (q ^ 2 - 2) ∈
          split_hull (exercise_5_22_layer q) (-s.π) (-s.π0 - 1) :=
      exercise_5_22_nextTopVertex_mem_normalizedSplitHull
        hq horigin_lower_neg htop_strip_neg haxis_upper_neg
    simpa [split_hull_neg_eq] using hnext_neg

/-- Helper for Exercise 5.22: the next top vertex belongs to the split hull of every two-sided
split of the current layer. -/
lemma exercise_5_22_nextTopVertex_mem_twoSideSplitHull
    {q : ℕ}
    (hq : 4 ≤ q)
    (s : TwoSideSplit (exercise_5_22_layer q)) :
    exercise_5_22_topVertex (q ^ 2 - 2) ∈
      split_hull (exercise_5_22_layer q) s.π s.π0 := by
  have hq2 : 2 ≤ q := by
    omega
  have haxes := exercise_5_22_axisVertices_mem_layer hq2
  have htopLayer : exercise_5_22_topVertex q ∈ exercise_5_22_layer q :=
    exercise_5_22_topVertex_mem_layer hq2
  have hsplit_convex :
      Convex ℝ (split_hull (exercise_5_22_layer q) s.π s.π0) := by
    simpa [split_hull] using
      (convex_convexHull ℝ
        (split_branch_lower (exercise_5_22_layer q) s.π s.π0 ∪
          split_branch_upper (exercise_5_22_layer q) s.π s.π0))
  have horigin_hull :
      exercise_5_22_origin ∈ split_hull (exercise_5_22_layer q) s.π s.π0 :=
    integral_split_value_mem_split_hull haxes.1
      (m := 0)
      (by simpa using exercise_5_22_split_dot_origin s.π)
  by_cases htop_lower :
      exercise_5_22_topVertex q ∈ split_branch_lower (exercise_5_22_layer q) s.π s.π0
  · have htop_hull :
        exercise_5_22_topVertex q ∈ split_hull (exercise_5_22_layer q) s.π s.π0 := by
      simpa [split_hull] using
        (subset_convexHull ℝ
          (split_branch_lower (exercise_5_22_layer q) s.π s.π0 ∪
            split_branch_upper (exercise_5_22_layer q) s.π s.π0)
          (Or.inl htop_lower))
    -- The easy lower-branch case uses convexity along the origin-to-top diagonal segment.
    exact hsplit_convex.segment_subset
      horigin_hull
      htop_hull
      (exercise_5_22_nextTopVertex_mem_originTopSegment hq)
  · by_cases htop_upper :
        exercise_5_22_topVertex q ∈ split_branch_upper (exercise_5_22_layer q) s.π s.π0
    · have htop_hull :
          exercise_5_22_topVertex q ∈ split_hull (exercise_5_22_layer q) s.π s.π0 := by
        simpa [split_hull] using
          (subset_convexHull ℝ
            (split_branch_lower (exercise_5_22_layer q) s.π s.π0 ∪
              split_branch_upper (exercise_5_22_layer q) s.π s.π0)
            (Or.inr htop_upper))
      -- The upper-branch case is symmetric: the same diagonal segment stays in the split hull.
      exact hsplit_convex.segment_subset
        horigin_hull
        htop_hull
        (exercise_5_22_nextTopVertex_mem_originTopSegment hq)
    · have htop_strip :
          exercise_5_22_topVertex q ∈ split_strip s.π s.π0 := by
        -- Outside the lower and upper branches, the current top vertex must lie in the strip.
        refine (mem_split_strip_iff).2 ?_
        have hnot_lower_ineq : ¬ split_dot s.π (exercise_5_22_topVertex q) ≤ (s.π0 : ℝ) := by
          intro hle
          exact htop_lower ((mem_split_branch_lower_iff).2 ⟨htopLayer, hle⟩)
        have hnot_upper_ineq : ¬ (s.π0 : ℝ) + 1 ≤ split_dot s.π (exercise_5_22_topVertex q) := by
          intro hge
          exact htop_upper ((mem_split_branch_upper_iff).2 ⟨htopLayer, hge⟩)
        exact ⟨lt_of_not_ge hnot_lower_ineq, lt_of_not_ge hnot_upper_ineq⟩
      -- The strip case is the only place where the normalized split-hull machinery is needed.
      exact exercise_5_22_nextTopVertex_mem_twoSideSplitHullOfStripCase hq s htop_strip

/-- Helper for Exercise 5.22: the denominator sequence driving the successive layer apexes. -/
def exercise_5_22_denominator : ℕ → ℕ
  | 0 => 4
  | n + 1 => exercise_5_22_denominator n ^ 2 - 2

/-- Helper for Exercise 5.22: every denominator in the recursive layer family stays at least `4`.
-/
lemma exercise_5_22_denominator_ge_four
    (n : ℕ) :
    4 ≤ exercise_5_22_denominator n := by
  induction n with
  | zero =>
      simp [exercise_5_22_denominator]
  | succ n ihn =>
      have hsquare :
          16 ≤ exercise_5_22_denominator n ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul ihn ihn
      have hnext : 4 ≤ exercise_5_22_denominator n ^ 2 - 2 := by
        omega
      simpa [exercise_5_22_denominator] using hnext

/-- Helper for Exercise 5.22: the split hull cut out by the left separating split already
satisfies the sharper future left-facet inequality. -/
lemma exercise_5_22_mem_leftFutureFacet_of_leftSplitHull
    {q : ℕ}
    (hq : 4 ≤ q)
    {x : Fin 2 → ℝ}
    (hx :
    x ∈ split_hull
        (exercise_5_22_layer q)
        (![((q : ℤ) - 1), -1] : Fin 2 → ℤ)
        ((q : ℤ) - 2)) :
    x 0 ≤ 1 + x 1 / (q ^ 2 - 2 : ℝ) := by
  have hq_real : (4 : ℝ) ≤ q := by
    exact_mod_cast hq
  have hd_pos : (0 : ℝ) < (q ^ 2 - 2 : ℝ) := by
    nlinarith
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    nlinarith
  have hq_ne : (q : ℝ) ≠ 0 := by
    linarith
  have hconv :
      Convex ℝ {y : Fin 2 → ℝ | y 0 ≤ 1 + y 1 / (q ^ 2 - 2 : ℝ)} := by
    -- The future left-facet halfspace is convex because the defining inequality is affine.
    intro y hy z hz a b ha hb hab
    have hy' : y 0 ≤ 1 + y 1 / (q ^ 2 - 2 : ℝ) := by
      simpa using hy
    have hz' : z 0 ≤ 1 + z 1 / (q ^ 2 - 2 : ℝ) := by
      simpa using hz
    have hscaledy : a * y 0 ≤ a * (1 + y 1 / (q ^ 2 - 2 : ℝ)) := by
      gcongr
    have hscaledz : b * z 0 ≤ b * (1 + z 1 / (q ^ 2 - 2 : ℝ)) := by
      gcongr
    have hsum :
        a * y 0 + b * z 0 ≤
          a * (1 + y 1 / (q ^ 2 - 2 : ℝ)) + b * (1 + z 1 / (q ^ 2 - 2 : ℝ)) := by
      linarith
    have hrewrite :
        a * (1 + y 1 / (q ^ 2 - 2 : ℝ)) + b * (1 + z 1 / (q ^ 2 - 2 : ℝ)) =
          1 + (a * y 1 + b * z 1) / (q ^ 2 - 2 : ℝ) := by
      calc
        a * (1 + y 1 / (q ^ 2 - 2 : ℝ)) + b * (1 + z 1 / (q ^ 2 - 2 : ℝ))
            = a + b + (a * y 1 + b * z 1) / (q ^ 2 - 2 : ℝ) := by ring
        _ = 1 + (a * y 1 + b * z 1) / (q ^ 2 - 2 : ℝ) := by rw [hab]
    simpa only [Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ge_iff_le] using
      hsum.trans_eq hrewrite
  rw [split_hull] at hx
  refine (convexHull_min ?_ hconv) hx
  intro y hy
  rcases hy with hyLower | hyUpper
  · rcases (mem_split_branch_lower_iff).1 hyLower with ⟨hyLayer, hyLowerIneq⟩
    rcases (mem_exercise_5_22_layer_iff).1 hyLayer with
      ⟨hy0, hy1, hyUpperFacet, hyRightFacet⟩
    have hyLowerExplicit : ((q : ℝ) - 1) * y 0 - y 1 ≤ (q : ℝ) - 2 := by
      -- Expand the left split functional so the branch inequality becomes a scalar inequality.
      simpa [split_dot_eq_sum, Fin.sum_univ_two, Int.cast_sub, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
        using hyLowerIneq
    have hscaled : (q ^ 2 - 2 : ℝ) * y 0 ≤ (q ^ 2 - 2 : ℝ) + y 1 := by
      -- Combine the lower-branch inequality with the current upper slanted facet.
      have hyUpperScaled : (q : ℝ) * y 1 - y 0 ≤ (q : ℝ) := by
        have hyMul :
            (q : ℝ) * y 1 ≤ (q : ℝ) * (1 + y 0 / (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hyUpperFacet hq_pos.le
        have hyMul' : (q : ℝ) * y 1 ≤ (q : ℝ) + y 0 := by
          calc
            (q : ℝ) * y 1 ≤ (q : ℝ) * (1 + y 0 / (q : ℝ)) := hyMul
            _ = (q : ℝ) + y 0 := by
              field_simp [hq_ne]
        linarith
      nlinarith [hyLowerExplicit, hyUpperScaled]
    have hratio :
        y 0 ≤ ((q ^ 2 - 2 : ℝ) + y 1) / (q ^ 2 - 2 : ℝ) := by
      exact (le_div_iff₀ hd_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    have hrewrite :
        ((q ^ 2 - 2 : ℝ) + y 1) / (q ^ 2 - 2 : ℝ) =
          1 + y 1 / (q ^ 2 - 2 : ℝ) := by
      field_simp [show (q ^ 2 - 2 : ℝ) ≠ 0 by linarith]
    simpa [hrewrite] using hratio
  · rcases (mem_split_branch_upper_iff).1 hyUpper with ⟨hyLayer, hyUpperIneq⟩
    rcases (mem_exercise_5_22_layer_iff).1 hyLayer with
      ⟨hy0, hy1, hyUpperFacet, hyRightFacet⟩
    have hyUpperExplicit : (q : ℝ) - 1 ≤ ((q : ℝ) - 1) * y 0 - y 1 := by
      -- The upper branch of the left separating split has the complementary scalar form.
      have hyUpperExpanded : (q : ℝ) + (1 + (-2 + y 1)) ≤ ((q : ℝ) + -1) * y 0 := by
        simpa [split_dot_eq_sum, Fin.sum_univ_two, Int.cast_sub, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm]
          using hyUpperIneq
      nlinarith
    have hscaled : (q ^ 2 - 2 : ℝ) * y 0 ≤ (q ^ 2 - 2 : ℝ) + y 1 := by
      -- Combine the upper-branch inequality with the current right slanted facet.
      have hyRightScaled : (q : ℝ) * y 0 - y 1 ≤ (q : ℝ) := by
        have hyMul :
            (q : ℝ) * y 0 ≤ (q : ℝ) * (1 + y 1 / (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hyRightFacet hq_pos.le
        have hyMul' : (q : ℝ) * y 0 ≤ (q : ℝ) + y 1 := by
          calc
            (q : ℝ) * y 0 ≤ (q : ℝ) * (1 + y 1 / (q : ℝ)) := hyMul
            _ = (q : ℝ) + y 1 := by
              field_simp [hq_ne]
        linarith
      nlinarith [hyUpperExplicit, hyRightScaled, hq_real]
    have hratio :
        y 0 ≤ ((q ^ 2 - 2 : ℝ) + y 1) / (q ^ 2 - 2 : ℝ) := by
      exact (le_div_iff₀ hd_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    have hrewrite :
        ((q ^ 2 - 2 : ℝ) + y 1) / (q ^ 2 - 2 : ℝ) =
          1 + y 1 / (q ^ 2 - 2 : ℝ) := by
      field_simp [show (q ^ 2 - 2 : ℝ) ≠ 0 by linarith]
    simpa [hrewrite] using hratio

/-- Helper for Exercise 5.22: the split hull cut out by the right separating split already
satisfies the sharper future upper-facet inequality. -/
lemma exercise_5_22_mem_rightFutureFacet_of_rightSplitHull
    {q : ℕ}
    (hq : 4 ≤ q)
    {x : Fin 2 → ℝ}
    (hx :
    x ∈ split_hull
        (exercise_5_22_layer q)
        (![-1, ((q : ℤ) - 1)] : Fin 2 → ℤ)
        ((q : ℤ) - 2)) :
    x 1 ≤ 1 + x 0 / (q ^ 2 - 2 : ℝ) := by
  have hq_real : (4 : ℝ) ≤ q := by
    exact_mod_cast hq
  have hd_pos : (0 : ℝ) < (q ^ 2 - 2 : ℝ) := by
    nlinarith
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    nlinarith
  have hq_ne : (q : ℝ) ≠ 0 := by
    linarith
  have hconv :
      Convex ℝ {y : Fin 2 → ℝ | y 1 ≤ 1 + y 0 / (q ^ 2 - 2 : ℝ)} := by
    -- The future upper-facet halfspace is convex for the same affine reason.
    intro y hy z hz a b ha hb hab
    have hy' : y 1 ≤ 1 + y 0 / (q ^ 2 - 2 : ℝ) := by
      simpa using hy
    have hz' : z 1 ≤ 1 + z 0 / (q ^ 2 - 2 : ℝ) := by
      simpa using hz
    have hscaledy : a * y 1 ≤ a * (1 + y 0 / (q ^ 2 - 2 : ℝ)) := by
      gcongr
    have hscaledz : b * z 1 ≤ b * (1 + z 0 / (q ^ 2 - 2 : ℝ)) := by
      gcongr
    have hsum :
        a * y 1 + b * z 1 ≤
          a * (1 + y 0 / (q ^ 2 - 2 : ℝ)) + b * (1 + z 0 / (q ^ 2 - 2 : ℝ)) := by
      linarith
    have hrewrite :
        a * (1 + y 0 / (q ^ 2 - 2 : ℝ)) + b * (1 + z 0 / (q ^ 2 - 2 : ℝ)) =
          1 + (a * y 0 + b * z 0) / (q ^ 2 - 2 : ℝ) := by
      calc
        a * (1 + y 0 / (q ^ 2 - 2 : ℝ)) + b * (1 + z 0 / (q ^ 2 - 2 : ℝ))
            = a + b + (a * y 0 + b * z 0) / (q ^ 2 - 2 : ℝ) := by ring
        _ = 1 + (a * y 0 + b * z 0) / (q ^ 2 - 2 : ℝ) := by rw [hab]
    simpa only [Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ge_iff_le] using
      hsum.trans_eq hrewrite
  rw [split_hull] at hx
  refine (convexHull_min ?_ hconv) hx
  intro y hy
  rcases hy with hyLower | hyUpper
  · rcases (mem_split_branch_lower_iff).1 hyLower with ⟨hyLayer, hyLowerIneq⟩
    rcases (mem_exercise_5_22_layer_iff).1 hyLayer with
      ⟨hy0, hy1, hyUpperFacet, hyRightFacet⟩
    have hyLowerExplicit : -y 0 + ((q : ℝ) - 1) * y 1 ≤ (q : ℝ) - 2 := by
      -- Expand the right split functional on the lower branch.
      simpa [split_dot_eq_sum, Fin.sum_univ_two, Int.cast_sub, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
        using hyLowerIneq
    have hscaled : (q ^ 2 - 2 : ℝ) * y 1 ≤ (q ^ 2 - 2 : ℝ) + y 0 := by
      -- Combine the lower branch with the current right slanted facet.
      have hyRightScaled : (q : ℝ) * y 0 - y 1 ≤ (q : ℝ) := by
        have hyMul :
            (q : ℝ) * y 0 ≤ (q : ℝ) * (1 + y 1 / (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hyRightFacet hq_pos.le
        have hyMul' : (q : ℝ) * y 0 ≤ (q : ℝ) + y 1 := by
          calc
            (q : ℝ) * y 0 ≤ (q : ℝ) * (1 + y 1 / (q : ℝ)) := hyMul
            _ = (q : ℝ) + y 1 := by
              field_simp [hq_ne]
        linarith
      nlinarith [hyLowerExplicit, hyRightScaled]
    have hratio :
        y 1 ≤ ((q ^ 2 - 2 : ℝ) + y 0) / (q ^ 2 - 2 : ℝ) := by
      exact (le_div_iff₀ hd_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    have hrewrite :
        ((q ^ 2 - 2 : ℝ) + y 0) / (q ^ 2 - 2 : ℝ) =
          1 + y 0 / (q ^ 2 - 2 : ℝ) := by
      field_simp [show (q ^ 2 - 2 : ℝ) ≠ 0 by linarith]
    simpa [hrewrite] using hratio
  · rcases (mem_split_branch_upper_iff).1 hyUpper with ⟨hyLayer, hyUpperIneq⟩
    rcases (mem_exercise_5_22_layer_iff).1 hyLayer with
      ⟨hy0, hy1, hyUpperFacet, hyRightFacet⟩
    have hyUpperExplicit : (q : ℝ) - 1 ≤ -y 0 + ((q : ℝ) - 1) * y 1 := by
      -- The upper branch again becomes an explicit scalar inequality after expansion.
      have hyUpperExpanded : (q : ℝ) + (1 + (-2 + y 0)) ≤ ((q : ℝ) + -1) * y 1 := by
        simpa [split_dot_eq_sum, Fin.sum_univ_two, Int.cast_sub, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm]
          using hyUpperIneq
      nlinarith
    have hscaled : (q ^ 2 - 2 : ℝ) * y 1 ≤ (q ^ 2 - 2 : ℝ) + y 0 := by
      -- Combine the upper branch with the current upper slanted facet.
      have hyUpperScaled : (q : ℝ) * y 1 - y 0 ≤ (q : ℝ) := by
        have hyMul :
            (q : ℝ) * y 1 ≤ (q : ℝ) * (1 + y 0 / (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hyUpperFacet hq_pos.le
        have hyMul' : (q : ℝ) * y 1 ≤ (q : ℝ) + y 0 := by
          calc
            (q : ℝ) * y 1 ≤ (q : ℝ) * (1 + y 0 / (q : ℝ)) := hyMul
            _ = (q : ℝ) + y 0 := by
              field_simp [hq_ne]
        linarith
      nlinarith [hyUpperExplicit, hyUpperScaled, hq_real]
    have hratio :
        y 1 ≤ ((q ^ 2 - 2 : ℝ) + y 0) / (q ^ 2 - 2 : ℝ) := by
      exact (le_div_iff₀ hd_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    have hrewrite :
        ((q ^ 2 - 2 : ℝ) + y 0) / (q ^ 2 - 2 : ℝ) =
          1 + y 0 / (q ^ 2 - 2 : ℝ) := by
      field_simp [show (q ^ 2 - 2 : ℝ) ≠ 0 by linarith]
    simpa [hrewrite] using hratio

/-- Helper for Exercise 5.22: the two explicit facet-separating two-sided splits force every
point of the closure into the next layer. -/
lemma exercise_5_22_twoSideSplitClosure_subset_nextLayer
    {q : ℕ}
    (hq : 4 ≤ q) :
    two_side_split_closure (exercise_5_22_layer q) ⊆
      exercise_5_22_layer (q ^ 2 - 2) := by
  intro x hx
  rcases (mem_two_side_split_closure_iff _ x).1 hx with ⟨hxLayer, hxSplitHull⟩
  have hq2 : 2 ≤ q := by
    omega
  have haxes := exercise_5_22_axisVertices_mem_layer hq2
  rcases (mem_exercise_5_22_layer_iff).1 hxLayer with ⟨hx0, hx1, hxUpperFacet, hxRightFacet⟩
  let leftSplit : TwoSideSplit (exercise_5_22_layer q) :=
    { π := ![((q : ℤ) - 1), -1]
      π0 := (q : ℤ) - 2
      nonzero := by
        -- The second coefficient is `-1`, so this separating split is genuinely nonzero.
        intro hzero
        have hzeroAtOne := congrFun hzero 1
        norm_num at hzeroAtOne
      lower_nonempty := by
        -- The origin witnesses that the lower branch is nonempty.
        refine ⟨exercise_5_22_origin, ?_⟩
        refine (mem_split_branch_lower_iff).2 ⟨haxes.1, ?_⟩
        rw [exercise_5_22_split_dot_origin]
        have hbound : (0 : ℝ) ≤ (q : ℝ) - 2 := by
          have hq_real : (4 : ℝ) ≤ q := by
            exact_mod_cast hq
          linarith
        simpa using hbound
      upper_nonempty := by
        -- The axis vertex `(1,0)` witnesses that the upper branch is nonempty.
        refine ⟨exercise_5_22_x0AxisVertex, ?_⟩
        refine (mem_split_branch_upper_iff).2 ⟨haxes.2.1, ?_⟩
        rw [exercise_5_22_split_dot_x0AxisVertex]
        have hcast :
            (q : ℝ) - 2 + 1 = (q : ℝ) - 1 := by
          ring
        simpa using (le_of_eq hcast) }
  let rightSplit : TwoSideSplit (exercise_5_22_layer q) :=
    { π := ![-1, ((q : ℤ) - 1)]
      π0 := (q : ℤ) - 2
      nonzero := by
        -- The first coefficient is `-1`, so the symmetric separating split is nonzero.
        intro hzero
        have hzeroAtZero := congrFun hzero 0
        norm_num at hzeroAtZero
      lower_nonempty := by
        -- The origin also lies on the lower side of the symmetric split.
        refine ⟨exercise_5_22_origin, ?_⟩
        refine (mem_split_branch_lower_iff).2 ⟨haxes.1, ?_⟩
        rw [exercise_5_22_split_dot_origin]
        have hbound : (0 : ℝ) ≤ (q : ℝ) - 2 := by
          have hq_real : (4 : ℝ) ≤ q := by
            exact_mod_cast hq
          linarith
        simpa using hbound
      upper_nonempty := by
        -- The axis vertex `(0,1)` provides the upper witness on the symmetric side.
        refine ⟨exercise_5_22_x1AxisVertex, ?_⟩
        refine (mem_split_branch_upper_iff).2 ⟨haxes.2.2, ?_⟩
        rw [exercise_5_22_split_dot_x1AxisVertex]
        have hcast :
            (q : ℝ) - 2 + 1 = (q : ℝ) - 1 := by
          ring
        simpa using (le_of_eq hcast) }
  refine (mem_exercise_5_22_layer_iff).2 ⟨hx0, hx1, ?_, ?_⟩
  · -- Apply the right separating split to recover the sharper upper slanted facet.
    have hxRightHull :
        x ∈ split_hull
          (exercise_5_22_layer q)
          (![-1, ((q : ℤ) - 1)] : Fin 2 → ℤ)
          ((q : ℤ) - 2) := by
      simpa [rightSplit] using hxSplitHull rightSplit
    have hsq_lower : 2 ≤ q ^ 2 := by
      have hq_one : 1 ≤ q := by
        omega
      have hq_le_sq : q ≤ q ^ 2 := by
        simpa [pow_two, Nat.mul_comm] using (Nat.mul_le_mul_left q hq_one)
      exact le_trans (by omega) hq_le_sq
    simpa [Nat.cast_sub hsq_lower] using
      exercise_5_22_mem_rightFutureFacet_of_rightSplitHull hq hxRightHull
  · -- Apply the left separating split to recover the sharper left slanted facet.
    have hxLeftHull :
        x ∈ split_hull
          (exercise_5_22_layer q)
          (![((q : ℤ) - 1), -1] : Fin 2 → ℤ)
          ((q : ℤ) - 2) := by
      simpa [leftSplit] using hxSplitHull leftSplit
    have hsq_lower : 2 ≤ q ^ 2 := by
      have hq_one : 1 ≤ q := by
        omega
      have hq_le_sq : q ≤ q ^ 2 := by
        simpa [pow_two, Nat.mul_comm] using (Nat.mul_le_mul_left q hq_one)
      exact le_trans (by omega) hq_le_sq
    simpa [Nat.cast_sub hsq_lower] using
      exercise_5_22_mem_leftFutureFacet_of_leftSplitHull hq hxLeftHull

/-- Exercise 5.22. Every point of the next layer belongs to the two-side-split closure of the
current layer. -/
lemma exercise_5_22_nextLayer_subset_twoSideSplitClosure
    {q : ℕ}
    (hq : 4 ≤ q) :
    exercise_5_22_layer (q ^ 2 - 2) ⊆
      two_side_split_closure (exercise_5_22_layer q) := by
  have hq2 : 2 ≤ q := by
    omega
  have hq_le_next : q ≤ q ^ 2 - 2 := by
    have hq_int : (4 : ℤ) ≤ q := by
      exact_mod_cast hq
    have hq_plus_two_le_sq_int : (q : ℤ) + 2 ≤ q ^ 2 := by
      nlinarith
    have hq_plus_two_le_sq : q + 2 ≤ q ^ 2 := by
      exact_mod_cast hq_plus_two_le_sq_int
    omega
  have hnext2 : 2 ≤ q ^ 2 - 2 := by
    omega
  have haxes := exercise_5_22_axisVertices_mem_layer hq2
  intro x hx
  rw [mem_two_side_split_closure_iff]
  have hxLayer :
      x ∈ exercise_5_22_layer q := by
    -- The next layer sits inside the current layer because the slanted facets only get weaker.
    rcases (mem_exercise_5_22_layer_iff).1 hx with ⟨hx0, hx1, hxUpper, hxRight⟩
    have hq_ne : (q : ℝ) ≠ 0 := by
      have hq_pos : (0 : ℝ) < q := by
        exact_mod_cast (show 0 < q by omega)
      linarith
    have hnext_ne : (((q ^ 2 - 2 : ℕ) : ℝ)) ≠ 0 := by
      have hnext_pos : (0 : ℝ) < ((q ^ 2 - 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < q ^ 2 - 2 by omega)
      linarith
    have hq_le_next_real : (q : ℝ) ≤ ((q ^ 2 - 2 : ℕ) : ℝ) := by
      exact_mod_cast hq_le_next
    refine (mem_exercise_5_22_layer_iff).2 ⟨hx0, hx1, ?_, ?_⟩
    · have hfrac :
          x 0 / ((q ^ 2 - 2 : ℕ) : ℝ) ≤ x 0 / (q : ℝ) := by
        field_simp [hq_ne, hnext_ne]
        nlinarith [hx0, hq_le_next_real]
      linarith
    · have hfrac :
          x 1 / ((q ^ 2 - 2 : ℕ) : ℝ) ≤ x 1 / (q : ℝ) := by
        field_simp [hq_ne, hnext_ne]
        nlinarith [hx1, hq_le_next_real]
      linarith
  refine ⟨hxLayer, ?_⟩
  intro s
  have hsplit_convex :
      Convex ℝ (split_hull (exercise_5_22_layer q) s.π s.π0) := by
    simpa [split_hull] using
      (convex_convexHull ℝ
        (split_branch_lower (exercise_5_22_layer q) s.π s.π0 ∪
          split_branch_upper (exercise_5_22_layer q) s.π s.π0))
  have horigin_hull :
      exercise_5_22_origin ∈ split_hull (exercise_5_22_layer q) s.π s.π0 :=
    integral_split_value_mem_split_hull haxes.1
      (m := 0)
      (by simpa using exercise_5_22_split_dot_origin s.π)
  have hx0_hull :
      exercise_5_22_x0AxisVertex ∈ split_hull (exercise_5_22_layer q) s.π s.π0 :=
    integral_split_value_mem_split_hull haxes.2.1
      (m := s.π 0)
      (by rw [exercise_5_22_split_dot_x0AxisVertex])
  have hx1_hull :
      exercise_5_22_x1AxisVertex ∈ split_hull (exercise_5_22_layer q) s.π s.π0 :=
    integral_split_value_mem_split_hull haxes.2.2
      (m := s.π 1)
      (by rw [exercise_5_22_split_dot_x1AxisVertex])
  have hnext_hull :
      exercise_5_22_topVertex (q ^ 2 - 2) ∈ split_hull (exercise_5_22_layer q) s.π s.π0 :=
    exercise_5_22_nextTopVertex_mem_twoSideSplitHull hq s
  rcases exercise_5_22_layer_subset_triangleUnion hnext2 hx with hxTri | hxTri
  · -- Push the left triangle generators into the ambient split hull, then use convexity.
    refine convexHull_min ?_ hsplit_convex hxTri
    rintro y ⟨i, rfl⟩
    fin_cases i
    · exact horigin_hull
    · exact hx0_hull
    · exact hnext_hull
  · -- The symmetric triangle uses the other axis vertex instead.
    refine convexHull_min ?_ hsplit_convex hxTri
    rintro y ⟨i, rfl⟩
    fin_cases i
    · exact horigin_hull
    · exact hx1_hull
    · exact hnext_hull

/-- Helper for Exercise 5.22: one two-side-split closure step sends the layer with denominator
`q` to the next layer with denominator `q^2 - 2`. -/
lemma exercise_5_22_two_side_split_closure_layer_eq
    {q : ℕ}
    (hq : 4 ≤ q) :
    two_side_split_closure (exercise_5_22_layer q) =
      exercise_5_22_layer (q ^ 2 - 2) := by
  -- Route correction: the reverse inclusion is now isolated in the explicit facet-separation
  -- lemmas, so only the forward arbitrary-split normalization remains as the open frontier.
  exact Set.Subset.antisymm
    (exercise_5_22_twoSideSplitClosure_subset_nextLayer hq)
    (exercise_5_22_nextLayer_subset_twoSideSplitClosure hq)

/-- Helper for Exercise 5.22: after `k` two-side-split iterations, the source polyhedron is the
layer with denominator `exercise_5_22_denominator k`. -/
lemma exercise_5_22_iterate_eq_layer
    (k : ℕ) :
    (two_side_split_closure^[k]) exercise_5_22_polyhedron =
      exercise_5_22_layer (exercise_5_22_denominator k) := by
  induction k with
  | zero =>
      -- The base layer is the original source polyhedron.
      simp [exercise_5_22_denominator, exercise_5_22_polyhedron_eq_layer]
  | succ k ih =>
      -- Each additional iterate applies the exact one-step layer recursion.
      rw [Function.iterate_succ_apply', ih]
      rw [exercise_5_22_two_side_split_closure_layer_eq (exercise_5_22_denominator_ge_four k)]
      simp [exercise_5_22_denominator]

/-- Final consequence for Exercise 5.22. For the polyhedron
`P = {(x₁, x₂) ∈ ℝ² | x₁ ≥ 0, x₂ ≥ 0, x₂ ≤ 1 + x₁ / 4, x₁ ≤ 1 + x₂ / 4}` and the pure integer set
`S = P ∩ ℤ²`, no positive finite iterated two-side-split closure equals the canonical
pure-integer hull `P_I`. -/
theorem exercise_5_22_no_finite_split_rank
    (k : ℕ)
    (hk : 1 ≤ k) :
    (two_side_split_closure^[k]) exercise_5_22_polyhedron ≠
      pure_integer_hull exercise_5_22_polyhedron := by
  -- Route correction: instead of working directly with the source apex at every iterate, pass to
  -- the layer family and use its recursive top vertex as the surviving witness.
  have _hk_pos : 0 < k := by omega
  intro hEq
  have hk' : 2 ≤ exercise_5_22_denominator k := by
    have hfour : 4 ≤ exercise_5_22_denominator k :=
      exercise_5_22_denominator_ge_four k
    omega
  have htop_mem :
      exercise_5_22_topVertex (exercise_5_22_denominator k) ∈
        (two_side_split_closure^[k]) exercise_5_22_polyhedron := by
    -- The iterate formula reduces membership to the explicit layer inequalities.
    rw [exercise_5_22_iterate_eq_layer]
    exact exercise_5_22_topVertex_mem_layer hk'
  have htop_hull :
      exercise_5_22_topVertex (exercise_5_22_denominator k) ∈
        pure_integer_hull exercise_5_22_polyhedron := by
    simpa [hEq] using htop_mem
  have htop_le_one :
      exercise_5_22_topVertex (exercise_5_22_denominator k) 0 ≤ 1 :=
    exercise_5_22_pure_integer_hull_subset_x0_le_one htop_hull
  have htop_gt_one :
      1 < exercise_5_22_topVertex (exercise_5_22_denominator k) 0 :=
    exercise_5_22_one_lt_topVertex_first hk'
  linarith

/-- Source-notation restatement of `exercise_5_22_no_finite_split_rank` using `conv(S)` for
`S = P ∩ ℤ²`. -/
theorem exercise_5_22_no_finite_split_rank_conv_integer_set
    (k : ℕ)
    (hk : 1 ≤ k) :
    (two_side_split_closure^[k]) exercise_5_22_polyhedron ≠
      convexHull ℝ exercise_5_22_integer_set := by
  -- Rewrite the source notation `conv(S)` back to the canonical pure-integer hull owner.
  simpa [exercise_5_22_pure_integer_hull_eq_conv_integer_set] using
    exercise_5_22_no_finite_split_rank k hk

end Exercise522
