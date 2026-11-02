import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_5.ch5_sec5_1_5_theorem_5_12

open scoped BigOperators Matrix

noncomputable section Exercise54

/-- The integer-variable index set `{x₁, x₂}` used in Exercise 5.4. -/
def exercise_5_4_integer_indices : Set (Fin 3) :=
  ({0, 1} : Finset (Fin 3))

/-- The polyhedron
`P = {(x₁, x₂, y) ∈ ℝ³ | x₁ ≥ y, x₂ ≥ y, x₁ + x₂ + 2 y ≤ 2, y ≥ 0}`
from Exercise 5.4, written in `Fin 3 → ℝ` coordinates with `0,1,2` standing for `x₁,x₂,y`. -/
def exercise_5_4_polyhedron : Set (Fin 3 → ℝ) :=
  {v : Fin 3 → ℝ |
    v 0 ≥ v 2 ∧
      v 1 ≥ v 2 ∧
        v 0 + v 1 + 2 * v 2 ≤ 2 ∧
          v 2 ≥ 0}

/-- The mixed-integer set
`S = P ∩ (ℤ² × ℝ)` from Exercise 5.4, again encoded in `Fin 3 → ℝ` coordinates. -/
def exercise_5_4_mixed_integer_set : Set (Fin 3 → ℝ) :=
  {v : Fin 3 → ℝ |
    v ∈ exercise_5_4_polyhedron ∧
      ∀ j ∈ exercise_5_4_integer_indices, ∃ z : ℤ, v j = (z : ℝ)}

/-- The explicit polyhedron claimed in Exercise 5.4 to equal the mixed split closure of `P`. -/
def exercise_5_4_split_closure_polyhedron : Set (Fin 3 → ℝ) :=
  {v : Fin 3 → ℝ |
    v 0 ≥ 3 * v 2 ∧
      v 1 ≥ 3 * v 2 ∧
        v 0 + v 1 + 2 * v 2 ≤ 2 ∧
          v 2 ≥ 0}

/-- Helper for Exercise 5.4: the origin vertex of the claimed split closure. -/
def exercise_5_4_origin : Fin 3 → ℝ :=
  ![0, 0, 0]

/-- Helper for Exercise 5.4: the `x₁`-axis base vertex `(2, 0, 0)`. -/
def exercise_5_4_x0_axis_vertex : Fin 3 → ℝ :=
  ![2, 0, 0]

/-- Helper for Exercise 5.4: the `x₂`-axis base vertex `(0, 2, 0)`. -/
def exercise_5_4_x1_axis_vertex : Fin 3 → ℝ :=
  ![0, 2, 0]

/-- Helper for Exercise 5.4: the apex `(3/4, 3/4, 1/4)` of the claimed split closure. -/
def exercise_5_4_apex : Fin 3 → ℝ :=
  ![(3 / 4 : ℝ), (3 / 4 : ℝ), (1 / 4 : ℝ)]

/-- Helper for Exercise 5.4: the original apex `(1/2, 1/2, 1/2)` of `P`. -/
def exercise_5_4_polyhedron_apex : Fin 3 → ℝ :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- Helper for Exercise 5.4: the base point `(1, 1, 0)` used in the vertical midpoint
decomposition of the split-closure apex. -/
def exercise_5_4_base_midpoint : Fin 3 → ℝ :=
  ![(1 : ℝ), (1 : ℝ), 0]

/-- Helper for Exercise 5.4: the point `(1, 1/3, 1/3)` used when the supported split
coefficients sum to `1`. -/
def exercise_5_4_left_upper_point : Fin 3 → ℝ :=
  ![(1 : ℝ), (1 / 3 : ℝ), (1 / 3 : ℝ)]

/-- Helper for Exercise 5.4: the point `(1/3, 1, 1/3)` used by the symmetric
sum-`1` decomposition. -/
def exercise_5_4_right_upper_point : Fin 3 → ℝ :=
  ![(1 / 3 : ℝ), (1 : ℝ), (1 / 3 : ℝ)]

/-- Helper for Exercise 5.4: the four vertices of the claimed split-closure tetrahedron. -/
def exercise_5_4_split_vertices : Fin 4 → Fin 3 → ℝ
  | 0 => exercise_5_4_origin
  | 1 => exercise_5_4_x0_axis_vertex
  | 2 => exercise_5_4_x1_axis_vertex
  | 3 => exercise_5_4_apex

/-- Helper for Exercise 5.4: the original tetrahedron `P` is convex. -/
lemma exercise_5_4_polyhedron_convex : Convex ℝ exercise_5_4_polyhedron := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  rcases hy with ⟨hy0, hy1, hy2, hy3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The first coordinate inequality is preserved by taking a convex combination.
    have hax : a * x 2 ≤ a * x 0 := by
      gcongr
    have hby : b * y 2 ≤ b * y 0 := by
      gcongr
    have hineq : a * x 2 + b * y 2 ≤ a * x 0 + b * y 0 := by
      linarith
    simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
      using hineq
  · -- The same argument works for the second coordinate inequality.
    have hax : a * x 2 ≤ a * x 1 := by
      gcongr
    have hby : b * y 2 ≤ b * y 1 := by
      gcongr
    have hineq : a * x 2 + b * y 2 ≤ a * x 1 + b * y 1 := by
      linarith
    simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
      using hineq
  · -- The aggregate inequality is also stable under convex combinations.
    have hax : a * (x 0 + x 1 + 2 * x 2) ≤ a * 2 := by
      gcongr
    have hby : b * (y 0 + y 1 + 2 * y 2) ≤ b * 2 := by
      gcongr
    have hineq :
        a * (x 0 + x 1 + 2 * x 2) + b * (y 0 + y 1 + 2 * y 2) ≤ 2 := by
      nlinarith
    simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
      two_mul, left_distrib, right_distrib] using hineq
  · -- Finally, nonnegativity of `y` is preserved as well.
    have hax : 0 ≤ a * x 2 := by
      positivity
    have hby : 0 ≤ b * y 2 := by
      positivity
    have hineq : 0 ≤ a * x 2 + b * y 2 := by
      linarith
    simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
      using hineq

/-- Helper for Exercise 5.4: the claimed split-closure tetrahedron is convex. -/
lemma exercise_5_4_split_closure_polyhedron_convex :
    Convex ℝ exercise_5_4_split_closure_polyhedron := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  rcases hy with ⟨hy0, hy1, hy2, hy3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The strengthened `x₁ ≥ 3 y` inequality is convex.
    have hax : a * (3 * x 2) ≤ a * x 0 := by
      gcongr
    have hby : b * (3 * y 2) ≤ b * y 0 := by
      gcongr
    have hineq : 3 * (a * x 2 + b * y 2) ≤ a * x 0 + b * y 0 := by
      linarith
    simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
      using hineq
  · -- The symmetric inequality `x₂ ≥ 3 y` is handled identically.
    have hax : a * (3 * x 2) ≤ a * x 1 := by
      gcongr
    have hby : b * (3 * y 2) ≤ b * y 1 := by
      gcongr
    have hineq : 3 * (a * x 2 + b * y 2) ≤ a * x 1 + b * y 1 := by
      linarith
    simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
      using hineq
  · -- The remaining defining inequalities are the same ones from the original tetrahedron.
    have hax : a * (x 0 + x 1 + 2 * x 2) ≤ a * 2 := by
      gcongr
    have hby : b * (y 0 + y 1 + 2 * y 2) ≤ b * 2 := by
      gcongr
    have hineq :
        a * (x 0 + x 1 + 2 * x 2) + b * (y 0 + y 1 + 2 * y 2) ≤ 2 := by
      nlinarith
    simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
      two_mul, left_distrib, right_distrib] using hineq
  · -- The nonnegativity constraint is convex for the same reason as above.
    have hax : 0 ≤ a * x 2 := by
      positivity
    have hby : 0 ≤ b * y 2 := by
      positivity
    have hineq : 0 ≤ a * x 2 + b * y 2 := by
      linarith
    simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
      using hineq

/-- Helper for Exercise 5.4: the halfspace `x₁ ≥ 3y` is convex. -/
lemma exercise_5_4_x0_ge_three_y_convex :
    Convex ℝ {v : Fin 3 → ℝ | v 0 ≥ 3 * v 2} := by
  intro x hx y hy a b ha hb hab
  -- This halfspace is stable under convex combinations by linearity.
  have hx' : 3 * x 2 ≤ x 0 := by
    simpa using hx
  have hy' : 3 * y 2 ≤ y 0 := by
    simpa using hy
  have hax : a * (3 * x 2) ≤ a * x 0 := by
    gcongr
  have hby : b * (3 * y 2) ≤ b * y 0 := by
    gcongr
  have hineq : 3 * (a * x 2 + b * y 2) ≤ a * x 0 + b * y 0 := by
    linarith
  simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
    using hineq

/-- Helper for Exercise 5.4: the symmetric halfspace `x₂ ≥ 3y` is convex. -/
lemma exercise_5_4_x1_ge_three_y_convex :
    Convex ℝ {v : Fin 3 → ℝ | v 1 ≥ 3 * v 2} := by
  intro x hx y hy a b ha hb hab
  -- The symmetric halfspace is handled in the same way.
  have hx' : 3 * x 2 ≤ x 1 := by
    simpa using hx
  have hy' : 3 * y 2 ≤ y 1 := by
    simpa using hy
  have hax : a * (3 * x 2) ≤ a * x 1 := by
    gcongr
  have hby : b * (3 * y 2) ≤ b * y 1 := by
    gcongr
  have hineq : 3 * (a * x 2 + b * y 2) ≤ a * x 1 + b * y 1 := by
    linarith
  simpa [Pi.add_apply, Pi.smul_apply, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
    using hineq

/-- Helper for Exercise 5.4: every split hull of `P` stays inside `P` because both split
branches are contained in `P` and `P` is convex. -/
lemma exercise_5_4_split_hull_subset_polyhedron
    (π : Fin 3 → ℤ)
    (π0 : ℤ) :
    split_hull exercise_5_4_polyhedron π π0 ⊆ exercise_5_4_polyhedron := by
  simpa [split_hull] using
    (convexHull_min
      (s := split_branch_lower exercise_5_4_polyhedron π π0 ∪
        split_branch_upper exercise_5_4_polyhedron π π0)
      (t := exercise_5_4_polyhedron)
      (fun x hx ↦ by
        rcases hx with hx | hx
        · exact hx.1
        · exact hx.1)
      exercise_5_4_polyhedron_convex)

/-- Helper for Exercise 5.4: negating the split vector and replacing `π₀` by `-π₀ - 1`
only swaps the lower and upper split branches. -/
lemma exercise_5_4_split_hull_neg_eq
    (π : Fin 3 → ℤ)
    (π0 : ℤ) :
    split_hull exercise_5_4_polyhedron (-π) (-π0 - 1) =
      split_hull exercise_5_4_polyhedron π π0 := by
  have hbranches :
      split_branch_lower exercise_5_4_polyhedron (-π) (-π0 - 1) ∪
          split_branch_upper exercise_5_4_polyhedron (-π) (-π0 - 1) =
        split_branch_lower exercise_5_4_polyhedron π π0 ∪
          split_branch_upper exercise_5_4_polyhedron π π0 := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · right
        rcases (mem_split_branch_lower_iff).1 hx with ⟨hxP, hxle⟩
        have hxge : (π0 : ℝ) + 1 ≤ split_dot π x := by
          have hxle' : -(∑ j, (π j : ℝ) * x j) ≤ -(π0 : ℝ) - 1 := by
            simpa [split_dot_eq_sum, Fin.sum_univ_three]
              using hxle
          have hxge' : (π0 : ℝ) + 1 ≤ ∑ j, (π j : ℝ) * x j := by
            linarith
          simpa [split_dot_eq_sum] using hxge'
        exact (mem_split_branch_upper_iff).2 ⟨hxP, hxge⟩
      · left
        rcases (mem_split_branch_upper_iff).1 hx with ⟨hxP, hxge⟩
        have hxle : split_dot π x ≤ (π0 : ℝ) := by
          have hxge' : -(π0 : ℝ) ≤ -(∑ j, (π j : ℝ) * x j) := by
            simpa [split_dot_eq_sum, Fin.sum_univ_three]
              using hxge
          have hxle' : ∑ j, (π j : ℝ) * x j ≤ (π0 : ℝ) := by
            linarith
          simpa [split_dot_eq_sum] using hxle'
        exact (mem_split_branch_lower_iff).2 ⟨hxP, hxle⟩
    · intro hx
      rcases hx with hx | hx
      · right
        rcases (mem_split_branch_lower_iff).1 hx with ⟨hxP, hxle⟩
        have hxge : ((-π0 - 1 : ℤ) : ℝ) + 1 ≤ split_dot (-π) x := by
          have hxle' : ∑ j, (π j : ℝ) * x j ≤ (π0 : ℝ) := by
            simpa [split_dot_eq_sum, Fin.sum_univ_three] using hxle
          have hxge' : -(π0 : ℝ) ≤ -(∑ j, (π j : ℝ) * x j) := by
            exact neg_le_neg hxle'
          simpa [split_dot_eq_sum, Fin.sum_univ_three] using hxge'
        exact (mem_split_branch_upper_iff).2 ⟨hxP, hxge⟩
      · left
        rcases (mem_split_branch_upper_iff).1 hx with ⟨hxP, hxge⟩
        have hxle : split_dot (-π) x ≤ ((-π0 - 1 : ℤ) : ℝ) := by
          -- Negating the split vector turns the upper-branch inequality into the lower one.
          have hnegDot : split_dot (-π) x = -split_dot π x := by
            rw [split_dot_eq_sum, split_dot_eq_sum]
            simp [Fin.sum_univ_three]
          rw [hnegDot]
          have hxle' : -split_dot π x ≤ -((π0 : ℝ) + 1) := by
            linarith
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxle'
        exact (mem_split_branch_lower_iff).2 ⟨hxP, hxle⟩
  simp [split_hull, hbranches]

/-- Helper for Exercise 5.4: a supported split vector has zero `y`-coefficient because the
continuous index is `2`. -/
lemma exercise_5_4_supported_third_zero
    {π : Fin 3 → ℤ}
    (hπsupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → π j = 0) :
    π 2 = 0 := by
  have h2 : (2 : Fin 3) ∉ exercise_5_4_integer_indices := by
    simp [exercise_5_4_integer_indices]
  exact hπsupport 2 h2

/-- Helper for Exercise 5.4: on supported split vectors, `split_dot` depends only on the
integral coordinates `x₁` and `x₂`. -/
lemma exercise_5_4_supported_split_dot
    {π : Fin 3 → ℤ}
    {v : Fin 3 → ℝ}
    (hπsupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → π j = 0) :
    split_dot π v = (π 0 : ℝ) * v 0 + (π 1 : ℝ) * v 1 := by
  have h2 : π 2 = 0 := exercise_5_4_supported_third_zero hπsupport
  rw [split_dot_eq_sum, Fin.sum_univ_three]
  simp [h2]

/-- Helper for Exercise 5.4: if a point of `P` has an integral split value, then it lies in the
split hull because it belongs to one side of the split disjunction. -/
lemma exercise_5_4_integral_split_value_mem_split_hull
    {x : Fin 3 → ℝ}
    {π : Fin 3 → ℤ}
    {π0 m : ℤ}
    (hxP : x ∈ exercise_5_4_polyhedron)
    (hxm : split_dot π x = (m : ℝ)) :
    x ∈ split_hull exercise_5_4_polyhedron π π0 := by
  have hUnion :
      x ∈ split_branch_lower exercise_5_4_polyhedron π π0 ∪
        split_branch_upper exercise_5_4_polyhedron π π0 := by
    by_cases hm : m ≤ π0
    · left
      have hm' : split_dot π x ≤ (π0 : ℝ) := by
        simpa [hxm] using hm
      exact (mem_split_branch_lower_iff).2 ⟨hxP, hm'⟩
    · right
      have hm' : π0 + 1 ≤ m := by
        omega
      have hm'' : (π0 : ℝ) + 1 ≤ split_dot π x := by
        have hm'' : ((π0 + 1 : ℤ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hm'
        simpa [hxm] using hm''
      exact (mem_split_branch_upper_iff).2 ⟨hxP, hm''⟩
  exact subset_convexHull ℝ _ hUnion

/-- Helper for Exercise 5.4: if two split-branch points span a segment containing `z`, then
`z` lies in the corresponding split hull. -/
lemma exercise_5_4_mem_split_hull_of_segment
    {π : Fin 3 → ℤ}
    {π0 : ℤ}
    {x y z : Fin 3 → ℝ}
    (hx :
      x ∈ split_branch_lower exercise_5_4_polyhedron π π0 ∪
        split_branch_upper exercise_5_4_polyhedron π π0)
    (hy :
      y ∈ split_branch_lower exercise_5_4_polyhedron π π0 ∪
        split_branch_upper exercise_5_4_polyhedron π π0)
    (hz : z ∈ segment ℝ x y) :
    z ∈ split_hull exercise_5_4_polyhedron π π0 := by
  have hzHull :
      z ∈ convexHull ℝ
        (split_branch_lower exercise_5_4_polyhedron π π0 ∪
          split_branch_upper exercise_5_4_polyhedron π π0) :=
    (segment_subset_convexHull hx hy) hz
  simpa [split_hull] using hzHull

/-- Helper for Exercise 5.4: the split vector selecting the `x₁`-coordinate is supported on the
integer indices. -/
lemma exercise_5_4_x0_split_supported :
    ![(1 : ℤ), 0, 0] ≠ 0 ∧
      ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → (![ (1 : ℤ), 0, 0 ] : Fin 3 → ℤ) j = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Fin 3 → ℤ ↦ f 0) h
    simp at h0
  · intro j hj
    fin_cases j <;> simp [exercise_5_4_integer_indices] at hj ⊢

/-- Helper for Exercise 5.4: the split vector selecting the `x₂`-coordinate is supported on the
integer indices. -/
lemma exercise_5_4_x1_split_supported :
    ![0, (1 : ℤ), 0] ≠ 0 ∧
      ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → (![ 0, (1 : ℤ), 0 ] : Fin 3 → ℤ) j = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun f : Fin 3 → ℤ ↦ f 1) h
    simp at h1
  · intro j hj
    fin_cases j <;> simp [exercise_5_4_integer_indices] at hj ⊢

/-- Helper for Exercise 5.4: both branches of the `x₁`-coordinate split satisfy the inequality
`x₁ ≥ 3y`. -/
lemma exercise_5_4_x0_split_branches_subset_three_y :
    split_branch_lower exercise_5_4_polyhedron ![(1 : ℤ), 0, 0] 0 ∪
        split_branch_upper exercise_5_4_polyhedron ![(1 : ℤ), 0, 0] 0 ⊆
      {v : Fin 3 → ℝ | v 0 ≥ 3 * v 2} := by
  intro v hv
  rcases hv with hv | hv
  · rcases (mem_split_branch_lower_iff).1 hv with ⟨hvP, hvSplit⟩
    rcases hvP with ⟨hv0, hv1, hv2, hv3⟩
    have hv0le : v 0 ≤ 0 := by
      simpa [split_dot_eq_sum, Fin.sum_univ_three] using hvSplit
    have hv2eq : v 2 = 0 := by
      linarith
    have hgoal : 3 * v 2 ≤ v 0 := by
      nlinarith [hv0, hv2eq]
    simpa using hgoal
  · rcases (mem_split_branch_upper_iff).1 hv with ⟨hvP, hvSplit⟩
    rcases hvP with ⟨hv0, hv1, hv2, hv3⟩
    have hv0ge : 1 ≤ v 0 := by
      simpa [split_dot_eq_sum, Fin.sum_univ_three] using hvSplit
    have hthree : 3 * v 2 ≤ 1 := by
      linarith
    have hgoal : 3 * v 2 ≤ v 0 := by
      nlinarith
    simpa using hgoal

/-- Helper for Exercise 5.4: the split hull for the `x₁`-coordinate split is contained in the
halfspace `x₁ ≥ 3y`. -/
lemma exercise_5_4_x0_coordinate_split_hull_subset_three_y :
    split_hull exercise_5_4_polyhedron ![(1 : ℤ), 0, 0] 0 ⊆
      {v : Fin 3 → ℝ | v 0 ≥ 3 * v 2} := by
  simpa [split_hull] using
    (convexHull_min
      (s := split_branch_lower exercise_5_4_polyhedron ![(1 : ℤ), 0, 0] 0 ∪
        split_branch_upper exercise_5_4_polyhedron ![(1 : ℤ), 0, 0] 0)
      (t := {v : Fin 3 → ℝ | v 0 ≥ 3 * v 2})
      exercise_5_4_x0_split_branches_subset_three_y
      exercise_5_4_x0_ge_three_y_convex)

/-- Helper for Exercise 5.4: both branches of the `x₂`-coordinate split satisfy the inequality
`x₂ ≥ 3y`. -/
lemma exercise_5_4_x1_split_branches_subset_three_y :
    split_branch_lower exercise_5_4_polyhedron ![0, (1 : ℤ), 0] 0 ∪
        split_branch_upper exercise_5_4_polyhedron ![0, (1 : ℤ), 0] 0 ⊆
      {v : Fin 3 → ℝ | v 1 ≥ 3 * v 2} := by
  intro v hv
  rcases hv with hv | hv
  · rcases (mem_split_branch_lower_iff).1 hv with ⟨hvP, hvSplit⟩
    rcases hvP with ⟨hv0, hv1, hv2, hv3⟩
    have hv1le : v 1 ≤ 0 := by
      simpa [split_dot_eq_sum, Fin.sum_univ_three] using hvSplit
    have hv2eq : v 2 = 0 := by
      linarith
    have hgoal : 3 * v 2 ≤ v 1 := by
      nlinarith [hv1, hv2eq]
    simpa using hgoal
  · rcases (mem_split_branch_upper_iff).1 hv with ⟨hvP, hvSplit⟩
    rcases hvP with ⟨hv0, hv1, hv2, hv3⟩
    have hv1ge : 1 ≤ v 1 := by
      simpa [split_dot_eq_sum, Fin.sum_univ_three] using hvSplit
    have hthree : 3 * v 2 ≤ 1 := by
      linarith
    have hgoal : 3 * v 2 ≤ v 1 := by
      nlinarith
    simpa using hgoal

/-- Helper for Exercise 5.4: the split hull for the `x₂`-coordinate split is contained in the
halfspace `x₂ ≥ 3y`. -/
lemma exercise_5_4_x1_coordinate_split_hull_subset_three_y :
    split_hull exercise_5_4_polyhedron ![0, (1 : ℤ), 0] 0 ⊆
      {v : Fin 3 → ℝ | v 1 ≥ 3 * v 2} := by
  simpa [split_hull] using
    (convexHull_min
      (s := split_branch_lower exercise_5_4_polyhedron ![0, (1 : ℤ), 0] 0 ∪
        split_branch_upper exercise_5_4_polyhedron ![0, (1 : ℤ), 0] 0)
      (t := {v : Fin 3 → ℝ | v 1 ≥ 3 * v 2})
      exercise_5_4_x1_split_branches_subset_three_y
      exercise_5_4_x1_ge_three_y_convex)

/-- Helper for Exercise 5.4: the origin belongs to `P`. -/
lemma exercise_5_4_origin_mem_polyhedron :
    exercise_5_4_origin ∈ exercise_5_4_polyhedron := by
  -- This is a direct coordinate check at `(0,0,0)`.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [exercise_5_4_origin]

/-- Helper for Exercise 5.4: `(2, 0, 0)` belongs to `P`. -/
lemma exercise_5_4_x0_axis_vertex_mem_polyhedron :
    exercise_5_4_x0_axis_vertex ∈ exercise_5_4_polyhedron := by
  -- This is a direct coordinate check at `(2,0,0)`.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [exercise_5_4_x0_axis_vertex]

/-- Helper for Exercise 5.4: `(0, 2, 0)` belongs to `P`. -/
lemma exercise_5_4_x1_axis_vertex_mem_polyhedron :
    exercise_5_4_x1_axis_vertex ∈ exercise_5_4_polyhedron := by
  -- This is a direct coordinate check at `(0,2,0)`.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [exercise_5_4_x1_axis_vertex]

/-- Helper for Exercise 5.4: `(3/4, 3/4, 1/4)` belongs to the claimed split-closure polyhedron. -/
lemma exercise_5_4_apex_mem_split_closure_polyhedron :
    exercise_5_4_apex ∈ exercise_5_4_split_closure_polyhedron := by
  -- The apex is obtained by a direct coordinate check in the claimed tetrahedron.
  simp [exercise_5_4_apex, exercise_5_4_split_closure_polyhedron]
  norm_num

/-- Helper for Exercise 5.4: `(1/2, 1/2, 1/2)` belongs to `P`. -/
lemma exercise_5_4_polyhedron_apex_mem_polyhedron :
    exercise_5_4_polyhedron_apex ∈ exercise_5_4_polyhedron := by
  -- This is the original top vertex of `P`, so the defining inequalities are numeric.
  simp [exercise_5_4_polyhedron_apex, exercise_5_4_polyhedron]
  norm_num

/-- Helper for Exercise 5.4: `(1, 1, 0)` belongs to `P`. -/
lemma exercise_5_4_base_midpoint_mem_polyhedron :
    exercise_5_4_base_midpoint ∈ exercise_5_4_polyhedron := by
  -- The midpoint lies on the base face, so each inequality reduces immediately.
  simp [exercise_5_4_base_midpoint, exercise_5_4_polyhedron]
  norm_num

/-- Helper for Exercise 5.4: `(1, 1/3, 1/3)` belongs to `P`. -/
lemma exercise_5_4_left_upper_point_mem_polyhedron :
    exercise_5_4_left_upper_point ∈ exercise_5_4_polyhedron := by
  -- This auxiliary point also satisfies `P` by direct arithmetic on its coordinates.
  simp [exercise_5_4_left_upper_point, exercise_5_4_polyhedron]
  norm_num

/-- Helper for Exercise 5.4: `(1/3, 1, 1/3)` belongs to `P`. -/
lemma exercise_5_4_right_upper_point_mem_polyhedron :
    exercise_5_4_right_upper_point ∈ exercise_5_4_polyhedron := by
  -- This symmetric companion point is verified in the same direct way.
  simp [exercise_5_4_right_upper_point, exercise_5_4_polyhedron]
  norm_num

/-- Helper for Exercise 5.4: the split value of the origin is `0`. -/
lemma exercise_5_4_split_dot_origin
    (π : Fin 3 → ℤ) :
    split_dot π exercise_5_4_origin = 0 := by
  rw [split_dot_eq_sum, Fin.sum_univ_three]
  simp [exercise_5_4_origin]

/-- Helper for Exercise 5.4: the split value of `(2, 0, 0)` is `2 π₁`. -/
lemma exercise_5_4_split_dot_x0_axis_vertex
    (π : Fin 3 → ℤ) :
    split_dot π exercise_5_4_x0_axis_vertex = (2 * π 0 : ℤ) := by
  -- Only the first coordinate contributes on `(2,0,0)`.
  rw [split_dot_eq_sum, Fin.sum_univ_three]
  simp [exercise_5_4_x0_axis_vertex]
  ring

/-- Helper for Exercise 5.4: the split value of `(0, 2, 0)` is `2 π₂`. -/
lemma exercise_5_4_split_dot_x1_axis_vertex
    (π : Fin 3 → ℤ) :
    split_dot π exercise_5_4_x1_axis_vertex = (2 * π 1 : ℤ) := by
  -- Only the second coordinate contributes on `(0,2,0)`.
  rw [split_dot_eq_sum, Fin.sum_univ_three]
  simp [exercise_5_4_x1_axis_vertex]
  ring

/-- Helper for Exercise 5.4: the split value of `(1, 1, 0)` is `π₁ + π₂`. -/
lemma exercise_5_4_split_dot_base_midpoint
    (π : Fin 3 → ℤ) :
    split_dot π exercise_5_4_base_midpoint = ((π 0 + π 1 : ℤ) : ℝ) := by
  -- The base midpoint has zero `y`-coordinate.
  rw [split_dot_eq_sum, Fin.sum_univ_three]
  simp [exercise_5_4_base_midpoint]

/-- Helper for Exercise 5.4: the original apex evaluates to half of the supported coefficient
sum. -/
lemma exercise_5_4_split_dot_polyhedron_apex
    (π : Fin 3 → ℤ)
    (hπsupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → π j = 0) :
    split_dot π exercise_5_4_polyhedron_apex =
      ((π 0 + π 1 : ℤ) : ℝ) / 2 := by
  have hdot := exercise_5_4_supported_split_dot (v := exercise_5_4_polyhedron_apex) hπsupport
  rw [hdot]
  norm_num [exercise_5_4_polyhedron_apex]
  ring

/-- Helper for Exercise 5.4: the split-closure apex evaluates to three quarters of the supported
coefficient sum. -/
lemma exercise_5_4_split_dot_apex
    (π : Fin 3 → ℤ)
    (hπsupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → π j = 0) :
    split_dot π exercise_5_4_apex =
      3 * ((π 0 + π 1 : ℤ) : ℝ) / 4 := by
  have hdot := exercise_5_4_supported_split_dot (v := exercise_5_4_apex) hπsupport
  rw [hdot]
  norm_num [exercise_5_4_apex]
  ring

/-- Helper for Exercise 5.4: `(1, 1/3, 1/3)` evaluates to `π₁ + π₂/3` under supported split
vectors. -/
lemma exercise_5_4_split_dot_left_upper_point
    (π : Fin 3 → ℤ)
    (hπsupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → π j = 0) :
    split_dot π exercise_5_4_left_upper_point =
      (π 0 : ℝ) + (π 1 : ℝ) / 3 := by
  have hdot := exercise_5_4_supported_split_dot (v := exercise_5_4_left_upper_point) hπsupport
  rw [hdot]
  norm_num [exercise_5_4_left_upper_point]
  ring

/-- Helper for Exercise 5.4: `(1/3, 1, 1/3)` evaluates to `π₁/3 + π₂` under supported split
vectors. -/
lemma exercise_5_4_split_dot_right_upper_point
    (π : Fin 3 → ℤ)
    (hπsupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → π j = 0) :
    split_dot π exercise_5_4_right_upper_point =
      (π 0 : ℝ) / 3 + (π 1 : ℝ) := by
  have hdot := exercise_5_4_supported_split_dot (v := exercise_5_4_right_upper_point) hπsupport
  rw [hdot]
  norm_num [exercise_5_4_right_upper_point]
  ring

/-- Helper for Exercise 5.4: the claimed split-closure apex is the midpoint of `(1, 1, 0)` and
the original apex `(1/2, 1/2, 1/2)`. -/
lemma exercise_5_4_apex_mem_vertical_segment :
    exercise_5_4_apex ∈
      segment ℝ exercise_5_4_base_midpoint exercise_5_4_polyhedron_apex := by
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  fin_cases i <;> norm_num [exercise_5_4_apex, exercise_5_4_base_midpoint,
    exercise_5_4_polyhedron_apex]

/-- Helper for Exercise 5.4: the apex is also on the segment joining `(0, 2, 0)` and
`(1, 1/3, 1/3)`. -/
lemma exercise_5_4_apex_mem_left_segment :
    exercise_5_4_apex ∈
      segment ℝ exercise_5_4_x1_axis_vertex exercise_5_4_left_upper_point := by
  refine ⟨(1 / 4 : ℝ), (3 / 4 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  fin_cases i <;> norm_num [exercise_5_4_apex, exercise_5_4_x1_axis_vertex,
    exercise_5_4_left_upper_point]

/-- Helper for Exercise 5.4: by symmetry, the apex lies on the segment joining `(2, 0, 0)` and
`(1/3, 1, 1/3)`. -/
lemma exercise_5_4_apex_mem_right_segment :
    exercise_5_4_apex ∈
      segment ℝ exercise_5_4_x0_axis_vertex exercise_5_4_right_upper_point := by
  refine ⟨(1 / 4 : ℝ), (3 / 4 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  fin_cases i <;> norm_num [exercise_5_4_apex, exercise_5_4_x0_axis_vertex,
    exercise_5_4_right_upper_point]

/-- Helper for Exercise 5.4: if a supported split sees positive total coefficient sum on
`x₁ + x₂`, then the apex can be placed between one lower-branch point and one upper-branch point. -/
lemma exercise_5_4_apex_mem_supported_split_hull_of_positive_sum
    (π : Fin 3 → ℤ)
    (π0 : ℤ)
    (hπsupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → π j = 0)
    (hs_pos : 0 < π 0 + π 1)
    (hstripLower : (π0 : ℝ) < split_dot π exercise_5_4_apex)
    (hstripUpper : split_dot π exercise_5_4_apex < (π0 : ℝ) + 1) :
    exercise_5_4_apex ∈ split_hull exercise_5_4_polyhedron π π0 := by
  let s : ℤ := π 0 + π 1
  have hs_eq : s = π 0 + π 1 := rfl
  have hs_pos' : 0 < s := by
    simpa [s] using hs_pos
  have hapex_dot : split_dot π exercise_5_4_apex = 3 * (s : ℝ) / 4 := by
    simpa [s] using exercise_5_4_split_dot_apex π hπsupport
  have hlow_int : 4 * π0 < 3 * s := by
    have hreal : (4 : ℝ) * (π0 : ℝ) < (3 : ℝ) * (s : ℝ) := by
      rw [hapex_dot] at hstripLower
      nlinarith
    exact_mod_cast hreal
  have hupp_int : 3 * s < 4 * π0 + 4 := by
    have hreal : (3 : ℝ) * (s : ℝ) < (4 : ℝ) * (π0 : ℝ) + 4 := by
      rw [hapex_dot] at hstripUpper
      nlinarith
    exact_mod_cast hreal
  by_cases hs_two : 2 ≤ s
  · -- The large-sum case uses the vertical midpoint decomposition between `(1,1,0)` and the
    -- original apex `(1/2,1/2,1/2)`.
    have hs_le_twopi0 : s ≤ 2 * π0 := by
      omega
    have hpi0p1_le_s : π0 + 1 ≤ s := by
      omega
    have hLower :
        exercise_5_4_polyhedron_apex ∈
          split_branch_lower exercise_5_4_polyhedron π π0 := by
      have hbranch : split_dot π exercise_5_4_polyhedron_apex ≤ (π0 : ℝ) := by
        rw [exercise_5_4_split_dot_polyhedron_apex π hπsupport]
        have hreal : (s : ℝ) ≤ 2 * (π0 : ℝ) := by
          exact_mod_cast hs_le_twopi0
        nlinarith
      exact (mem_split_branch_lower_iff).2
        ⟨exercise_5_4_polyhedron_apex_mem_polyhedron, hbranch⟩
    have hUpper :
        exercise_5_4_base_midpoint ∈
          split_branch_upper exercise_5_4_polyhedron π π0 := by
      have hbranch : (π0 : ℝ) + 1 ≤ split_dot π exercise_5_4_base_midpoint := by
        rw [exercise_5_4_split_dot_base_midpoint π]
        exact_mod_cast hpi0p1_le_s
      exact (mem_split_branch_upper_iff).2
        ⟨exercise_5_4_base_midpoint_mem_polyhedron, hbranch⟩
    have hUnionLower :
        exercise_5_4_polyhedron_apex ∈
          split_branch_lower exercise_5_4_polyhedron π π0 ∪
            split_branch_upper exercise_5_4_polyhedron π π0 := by
      exact Or.inl hLower
    have hUnionUpper :
        exercise_5_4_base_midpoint ∈
          split_branch_lower exercise_5_4_polyhedron π π0 ∪
            split_branch_upper exercise_5_4_polyhedron π π0 := by
      exact Or.inr hUpper
    exact exercise_5_4_mem_split_hull_of_segment hUnionUpper hUnionLower
      exercise_5_4_apex_mem_vertical_segment
  · -- When the supported coefficient sum is `1`, one endpoint decomposition hits an integral
    -- branch point at `0` and the other endpoint hits the opposite branch at `1`.
    have hs_one : s = 1 := by
      omega
    have hpi0_zero : π0 = 0 := by
      omega
    have hcoeff : π 1 ≤ 0 ∨ π 0 ≤ 0 := by
      omega
    rcases hcoeff with hcoeff | hcoeff
    · have hLower :
          exercise_5_4_x1_axis_vertex ∈
            split_branch_lower exercise_5_4_polyhedron π π0 := by
        have hbranch : split_dot π exercise_5_4_x1_axis_vertex ≤ (π0 : ℝ) := by
          rw [exercise_5_4_split_dot_x1_axis_vertex π, hpi0_zero]
          have hint : (2 * π 1 : ℤ) ≤ 0 := by
            omega
          exact_mod_cast hint
        exact (mem_split_branch_lower_iff).2
          ⟨exercise_5_4_x1_axis_vertex_mem_polyhedron, hbranch⟩
      have hUpper :
          exercise_5_4_left_upper_point ∈
            split_branch_upper exercise_5_4_polyhedron π π0 := by
        have hbranch : (π0 : ℝ) + 1 ≤ split_dot π exercise_5_4_left_upper_point := by
          rw [exercise_5_4_split_dot_left_upper_point π hπsupport, hpi0_zero]
          have hs_one_real : (π 0 : ℝ) + (π 1 : ℝ) = 1 := by
            exact_mod_cast hs_one
          have hcoeff_real : (π 1 : ℝ) ≤ 0 := by
            exact_mod_cast hcoeff
          nlinarith
        exact (mem_split_branch_upper_iff).2
          ⟨exercise_5_4_left_upper_point_mem_polyhedron, hbranch⟩
      have hUnionLower :
          exercise_5_4_x1_axis_vertex ∈
            split_branch_lower exercise_5_4_polyhedron π π0 ∪
              split_branch_upper exercise_5_4_polyhedron π π0 := by
        exact Or.inl hLower
      have hUnionUpper :
          exercise_5_4_left_upper_point ∈
            split_branch_lower exercise_5_4_polyhedron π π0 ∪
              split_branch_upper exercise_5_4_polyhedron π π0 := by
        exact Or.inr hUpper
      exact exercise_5_4_mem_split_hull_of_segment hUnionLower hUnionUpper
        exercise_5_4_apex_mem_left_segment
    · have hLower :
          exercise_5_4_x0_axis_vertex ∈
            split_branch_lower exercise_5_4_polyhedron π π0 := by
        have hbranch : split_dot π exercise_5_4_x0_axis_vertex ≤ (π0 : ℝ) := by
          rw [exercise_5_4_split_dot_x0_axis_vertex π, hpi0_zero]
          have hint : (2 * π 0 : ℤ) ≤ 0 := by
            omega
          exact_mod_cast hint
        exact (mem_split_branch_lower_iff).2
          ⟨exercise_5_4_x0_axis_vertex_mem_polyhedron, hbranch⟩
      have hUpper :
          exercise_5_4_right_upper_point ∈
            split_branch_upper exercise_5_4_polyhedron π π0 := by
        have hbranch : (π0 : ℝ) + 1 ≤ split_dot π exercise_5_4_right_upper_point := by
          rw [exercise_5_4_split_dot_right_upper_point π hπsupport, hpi0_zero]
          have hs_one_real : (π 0 : ℝ) + (π 1 : ℝ) = 1 := by
            exact_mod_cast hs_one
          have hcoeff_real : (π 0 : ℝ) ≤ 0 := by
            exact_mod_cast hcoeff
          nlinarith
        exact (mem_split_branch_upper_iff).2
          ⟨exercise_5_4_right_upper_point_mem_polyhedron, hbranch⟩
      have hUnionLower :
          exercise_5_4_x0_axis_vertex ∈
            split_branch_lower exercise_5_4_polyhedron π π0 ∪
              split_branch_upper exercise_5_4_polyhedron π π0 := by
        exact Or.inl hLower
      have hUnionUpper :
          exercise_5_4_right_upper_point ∈
            split_branch_lower exercise_5_4_polyhedron π π0 ∪
              split_branch_upper exercise_5_4_polyhedron π π0 := by
        exact Or.inr hUpper
      exact exercise_5_4_mem_split_hull_of_segment hUnionLower hUnionUpper
        exercise_5_4_apex_mem_right_segment

/-- Helper for Exercise 5.4: the apex belongs to every supported split hull. The proof first
handles the easy outside-the-strip cases directly, then flips negative splits and finally uses
explicit segment decompositions in the positive strip case. -/
lemma exercise_5_4_apex_mem_supported_split_hull
    (π : Fin 3 → ℤ)
    (π0 : ℤ)
    (_hπnz : π ≠ 0)
    (hπsupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → π j = 0) :
    exercise_5_4_apex ∈ split_hull exercise_5_4_polyhedron π π0 := by
  by_cases hlower : split_dot π exercise_5_4_apex ≤ (π0 : ℝ)
  · have hLower :
        exercise_5_4_apex ∈ split_branch_lower exercise_5_4_polyhedron π π0 := by
      -- If the apex already lies on the lower side of the disjunction, we are done immediately.
      exact (mem_split_branch_lower_iff).2 ⟨by
        have hP : exercise_5_4_apex ∈ exercise_5_4_split_closure_polyhedron :=
          exercise_5_4_apex_mem_split_closure_polyhedron
        rcases hP with ⟨h0, h1, h2, h3⟩
        refine ⟨?_, ?_, h2, h3⟩ <;> linarith, hlower⟩
    exact subset_convexHull ℝ _ (Or.inl hLower)
  · by_cases hupper : (π0 : ℝ) + 1 ≤ split_dot π exercise_5_4_apex
    · have hUpper :
          exercise_5_4_apex ∈ split_branch_upper exercise_5_4_polyhedron π π0 := by
        -- The upper-branch case is symmetric.
        exact (mem_split_branch_upper_iff).2 ⟨by
          have hP : exercise_5_4_apex ∈ exercise_5_4_split_closure_polyhedron :=
            exercise_5_4_apex_mem_split_closure_polyhedron
          rcases hP with ⟨h0, h1, h2, h3⟩
          refine ⟨?_, ?_, h2, h3⟩ <;> linarith, hupper⟩
      exact subset_convexHull ℝ _ (Or.inr hUpper)
    · have hstripLower : (π0 : ℝ) < split_dot π exercise_5_4_apex := by
        linarith
      have hstripUpper : split_dot π exercise_5_4_apex < (π0 : ℝ) + 1 := by
        linarith
      let s : ℤ := π 0 + π 1
      have hapex_dot : split_dot π exercise_5_4_apex = 3 * (s : ℝ) / 4 := by
        simpa [s] using exercise_5_4_split_dot_apex π hπsupport
      have hs_ne_zero : s ≠ 0 := by
        intro hs_zero
        have hzero_dot : split_dot π exercise_5_4_apex = 0 := by
          rw [hapex_dot, hs_zero]
          norm_num
        rw [hzero_dot] at hstripLower hstripUpper
        have hπ0neg : π0 < 0 := by
          exact_mod_cast hstripLower
        have hπ0pos : 0 < π0 + 1 := by
          exact_mod_cast hstripUpper
        omega
      by_cases hs_pos : 0 < s
      · exact exercise_5_4_apex_mem_supported_split_hull_of_positive_sum π π0 hπsupport hs_pos
          hstripLower hstripUpper
      · have hs_neg : 0 < -s := by
          have hs_le : s ≤ 0 := le_of_not_gt hs_pos
          omega
        have hnegSupport : ∀ j : Fin 3, j ∉ exercise_5_4_integer_indices → (-π) j = 0 := by
          intro j hj
          have hzero : π j = 0 := hπsupport j hj
          simp [hzero]
        have hnegDot : split_dot (-π) exercise_5_4_apex = - split_dot π exercise_5_4_apex := by
          rw [split_dot_eq_sum, split_dot_eq_sum]
          simp [exercise_5_4_apex, Fin.sum_univ_three]
        have hnegStripLower : (((-π0 - 1 : ℤ) : ℝ) < split_dot (-π) exercise_5_4_apex) := by
          rw [hnegDot]
          have hlower' : -((π0 : ℝ) + 1) < -split_dot π exercise_5_4_apex := by
            linarith [hstripUpper]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlower'
        have hnegStripUpper :
            split_dot (-π) exercise_5_4_apex < (((-π0 - 1 : ℤ) : ℝ) + 1) := by
          rw [hnegDot]
          have hupper' : -split_dot π exercise_5_4_apex < -(π0 : ℝ) := by
            linarith [hstripLower]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hupper'
        have hs_neg' : 0 < (-π) 0 + (-π) 1 := by
          dsimp [s] at hs_neg ⊢
          omega
        have hneg :
            exercise_5_4_apex ∈ split_hull exercise_5_4_polyhedron (-π) (-π0 - 1) :=
          exercise_5_4_apex_mem_supported_split_hull_of_positive_sum (-π) (-π0 - 1)
            hnegSupport hs_neg' hnegStripLower hnegStripUpper
        simpa [exercise_5_4_split_hull_neg_eq π π0] using hneg

/-- Helper for Exercise 5.4: each vertex of the claimed split-closure tetrahedron already lies in
that tetrahedron. -/
lemma exercise_5_4_split_vertices_subset_split_closure_polyhedron :
    Set.range exercise_5_4_split_vertices ⊆ exercise_5_4_split_closure_polyhedron := by
  intro x hx
  rcases hx with ⟨i, rfl⟩
  fin_cases i
  · -- The three base vertices satisfy the target inequalities by inspection.
    simp [exercise_5_4_split_vertices, exercise_5_4_origin,
      exercise_5_4_split_closure_polyhedron]
  · simp [exercise_5_4_split_vertices, exercise_5_4_x0_axis_vertex,
      exercise_5_4_split_closure_polyhedron]
  · simp [exercise_5_4_split_vertices, exercise_5_4_x1_axis_vertex,
      exercise_5_4_split_closure_polyhedron]
  · exact exercise_5_4_apex_mem_split_closure_polyhedron

/-- Helper for Exercise 5.4: every point of the claimed split-closure polyhedron is a convex
combination of the four explicit vertices `(0,0,0)`, `(2,0,0)`, `(0,2,0)`, and
`(3/4, 3/4, 1/4)`. -/
lemma exercise_5_4_split_closure_polyhedron_subset_convexHull_vertices :
    exercise_5_4_split_closure_polyhedron ⊆
      convexHull ℝ (Set.range exercise_5_4_split_vertices) := by
  intro v hv
  rcases hv with ⟨hv0, hv1, hv2, hv3⟩
  let w : Fin 4 → ℝ
    | 0 => 1 - v 0 / 2 - v 1 / 2 - v 2
    | 1 => (v 0 - 3 * v 2) / 2
    | 2 => (v 1 - 3 * v 2) / 2
    | 3 => 4 * v 2
  have hw_nonneg : ∀ i : Fin 4, 0 ≤ w i := by
    intro i
    fin_cases i
    · simp [w]
      linarith
    · simp [w]
      linarith
    · simp [w]
      linarith
    · simp [w]
      linarith
  have hw_sum : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_four]
    ring
  -- The barycentric coordinates are chosen so that the vertex combination reproduces each
  -- coordinate of `v` exactly.
  refine mem_convexHull_of_exists_fintype w exercise_5_4_split_vertices hw_nonneg hw_sum
    (fun i ↦ Set.mem_range_self i) ?_
  ext j
  fin_cases j
  · simp [w, exercise_5_4_split_vertices, exercise_5_4_origin, exercise_5_4_x0_axis_vertex,
      exercise_5_4_x1_axis_vertex, exercise_5_4_apex, Fin.sum_univ_four]
    ring_nf
  · simp [w, exercise_5_4_split_vertices, exercise_5_4_origin, exercise_5_4_x0_axis_vertex,
      exercise_5_4_x1_axis_vertex, exercise_5_4_apex, Fin.sum_univ_four]
    ring_nf
  · simp [w, exercise_5_4_split_vertices, exercise_5_4_origin, exercise_5_4_x0_axis_vertex,
      exercise_5_4_x1_axis_vertex, exercise_5_4_apex, Fin.sum_univ_four]
    ring_nf

/-- Helper for Exercise 5.4: the claimed split-closure polyhedron is exactly the convex hull of
the four explicit vertices. -/
lemma exercise_5_4_split_closure_polyhedron_eq_convexHull_vertices :
    exercise_5_4_split_closure_polyhedron =
      convexHull ℝ (Set.range exercise_5_4_split_vertices) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact exercise_5_4_split_closure_polyhedron_subset_convexHull_vertices
  · exact convexHull_min
      exercise_5_4_split_vertices_subset_split_closure_polyhedron
      exercise_5_4_split_closure_polyhedron_convex

/-- Exercise 5.4. Let
`P = {(x₁, x₂, y) ∈ ℝ³ | x₁ ≥ y, x₂ ≥ y, x₁ + x₂ + 2 y ≤ 2, y ≥ 0}` and
`S = P ∩ (ℤ² × ℝ)`. Then the mixed split closure of `P` with respect to the integral coordinates
`x₁` and `x₂` is exactly
`{(x₁, x₂, y) ∈ ℝ³ | x₁ ≥ 3 y, x₂ ≥ 3 y, x₁ + x₂ + 2 y ≤ 2, y ≥ 0}`. -/
theorem exercise_5_4_mixed_split_closure_eq :
    mixed_split_closure exercise_5_4_integer_indices exercise_5_4_polyhedron =
      exercise_5_4_split_closure_polyhedron := by
  ext v
  constructor
  · intro hv
    rw [mem_mixed_split_closure_iff] at hv
    rcases hv with ⟨hvP, hvSplits⟩
    let sx0 : Split exercise_5_4_integer_indices.toFinite.toFinset := {
      π := ![(1 : ℤ), 0, 0]
      π0 := 0
      nonzero := exercise_5_4_x0_split_supported.1
      zero_on_continuous := by
        intro j hj
        exact exercise_5_4_x0_split_supported.2 j (by simpa using hj)
    }
    let sx1 : Split exercise_5_4_integer_indices.toFinite.toFinset := {
      π := ![0, (1 : ℤ), 0]
      π0 := 0
      nonzero := exercise_5_4_x1_split_supported.1
      zero_on_continuous := by
        intro j hj
        exact exercise_5_4_x1_split_supported.2 j (by simpa using hj)
    }
    have hx0Hull : v ∈ split_hull exercise_5_4_polyhedron ![(1 : ℤ), 0, 0] 0 := by
      simpa [sx0] using hvSplits sx0
    have hx1Hull : v ∈ split_hull exercise_5_4_polyhedron ![0, (1 : ℤ), 0] 0 := by
      simpa [sx1] using hvSplits sx1
    -- The two coordinate splits produce the new inequalities `x₁ ≥ 3y` and `x₂ ≥ 3y`, while
    -- membership in the mixed split closure already keeps the original inequalities of `P`.
    have hv0 : v 0 ≥ 3 * v 2 := exercise_5_4_x0_coordinate_split_hull_subset_three_y hx0Hull
    have hv1 : v 1 ≥ 3 * v 2 := exercise_5_4_x1_coordinate_split_hull_subset_three_y hx1Hull
    rcases hvP with ⟨-, -, hv2, hv3⟩
    exact ⟨hv0, hv1, hv2, hv3⟩
  · intro hv
    rw [mem_mixed_split_closure_iff]
    refine ⟨?_, ?_⟩
    · -- The claimed split-closure polyhedron strengthens the two `x_i ≥ y` inequalities of `P`.
      rcases hv with ⟨hv0, hv1, hv2, hv3⟩
      refine ⟨?_, ?_, hv2, hv3⟩ <;> linarith
    · intro s
    rw [exercise_5_4_split_closure_polyhedron_eq_convexHull_vertices] at hv
    -- For the reverse inclusion, each explicit vertex lies in every supported split hull, so
    -- convexity of the split hull pulls the whole tetrahedron into that hull.
    have hsubset :
        Set.range exercise_5_4_split_vertices ⊆
          convexHull ℝ
            (split_branch_lower exercise_5_4_polyhedron s s.π0 ∪
              split_branch_upper exercise_5_4_polyhedron s s.π0) := by
      intro x hx
      rcases hx with ⟨i, rfl⟩
      fin_cases i
      · simpa [split_hull, exercise_5_4_split_vertices] using
          (exercise_5_4_integral_split_value_mem_split_hull
            (m := 0)
            exercise_5_4_origin_mem_polyhedron
            (by
              have horigin : split_dot s exercise_5_4_origin = ((0 : ℤ) : ℝ) := by
                simpa using exercise_5_4_split_dot_origin s
              exact horigin))
      · simpa [split_hull, exercise_5_4_split_vertices] using
          (exercise_5_4_integral_split_value_mem_split_hull
            (m := 2 * s 0)
            exercise_5_4_x0_axis_vertex_mem_polyhedron
            (exercise_5_4_split_dot_x0_axis_vertex s))
      · simpa [split_hull, exercise_5_4_split_vertices] using
          (exercise_5_4_integral_split_value_mem_split_hull
            (m := 2 * s 1)
            exercise_5_4_x1_axis_vertex_mem_polyhedron
            (exercise_5_4_split_dot_x1_axis_vertex s))
      · simpa [split_hull, exercise_5_4_split_vertices] using
          (exercise_5_4_apex_mem_supported_split_hull s s.π0 s.nonzero
            (by
              intro j hj
              exact s.zero_on_continuous j (by simpa using hj)))
    -- The explicit convex-hull model of the target tetrahedron now transfers directly into the
    -- split hull generated by the two split branches.
    simpa [split_hull] using (convexHull_min hsubset (convex_convexHull ℝ _)) hv

end Exercise54
