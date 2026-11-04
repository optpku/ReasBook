/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1

open scoped Matrix

section Exercise521

variable {n p : ℕ}

/-- The ternary coordinate hull obtained by fixing the `j`th coordinate to `0`, `1`, or `2` and
taking the convex hull of the three resulting slices. -/
def ternary_coordinate_lift_project_hull
    (P : Set (Fin n → ℝ))
    (j : Fin n) : Set (Fin n → ℝ) :=
  convexHull ℝ
    (((P ∩ {x : Fin n → ℝ | x j = 0}) ∪
      (P ∩ {x : Fin n → ℝ | x j = 1})) ∪
      (P ∩ {x : Fin n → ℝ | x j = 2}))

/-- `ternary_coordinate_lift_project_hull P j` is definitionally the convex hull of the `x_j = 0`,
`x_j = 1`, and `x_j = 2` slices of `P`. -/
theorem ternary_coordinate_lift_project_hull_def
    (P : Set (Fin n → ℝ))
    (j : Fin n) :
    ternary_coordinate_lift_project_hull P j =
      convexHull ℝ
        (((P ∩ {x : Fin n → ℝ | x j = 0}) ∪
          (P ∩ {x : Fin n → ℝ | x j = 1})) ∪
          (P ∩ {x : Fin n → ℝ | x j = 2})) := rfl

/-- The `t`th ternary convexification of `P` along the coordinate schedule `σ`, obtained by
successively convexifying the coordinates `σ 0, …, σ (t - 1)`. -/
def ordered_ternary_convexification_iter
    (P : Set (Fin n → ℝ))
    (σ : Fin p → Fin n) :
    ∀ {t : ℕ}, t ≤ p → Set (Fin n → ℝ)
  | 0, _ => P
  | t + 1, ht =>
      ternary_coordinate_lift_project_hull
        (ordered_ternary_convexification_iter P σ (Nat.le_of_succ_le ht))
        (σ ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩)

/-- The zeroth ordered ternary convexification is `P` itself. -/
theorem ordered_ternary_convexification_iter_zero
    (P : Set (Fin n → ℝ))
    (σ : Fin p → Fin n) :
    ordered_ternary_convexification_iter P σ (Nat.zero_le p) = P :=
  rfl

/-- The successor ordered ternary convexification is obtained by applying the ternary coordinate
hull along the next scheduled coordinate. -/
theorem ordered_ternary_convexification_iter_succ
    (P : Set (Fin n → ℝ))
    (σ : Fin p → Fin n)
    {t : ℕ}
    (ht : t + 1 ≤ p) :
    ordered_ternary_convexification_iter P σ ht =
      ternary_coordinate_lift_project_hull
        (ordered_ternary_convexification_iter P σ (Nat.le_of_succ_le ht))
        (σ ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩) :=
  rfl

/-- The `t`th ternary sequential convexification of `P`, obtained by successively convexifying
along the first `t` coordinates. -/
def ternary_sequential_convexification_iter
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    ∀ {t : ℕ}, t ≤ p → Set (Fin n → ℝ) :=
  ordered_ternary_convexification_iter P (Fin.castLE hpn)

/-- The zeroth ternary sequential convexification is `P` itself. -/
theorem ternary_sequential_convexification_iter_zero
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    ternary_sequential_convexification_iter hpn P (Nat.zero_le p) = P :=
  rfl

/-- The successor ternary sequential convexification is obtained by convexifying the previous
iterate along the next coordinate. -/
theorem ternary_sequential_convexification_iter_succ
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    {t : ℕ}
    (ht : t + 1 ≤ p) :
    ternary_sequential_convexification_iter hpn P ht =
      ternary_coordinate_lift_project_hull
        (ternary_sequential_convexification_iter hpn P (Nat.le_of_succ_le ht))
        (Fin.castLE hpn ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩) :=
  rfl

/-- The points of `P` whose first `t` coordinates lie in `{0, 1, 2}`. -/
def prefix_ternary_points
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    {t : ℕ}
    (ht : t ≤ p) : Set (Fin n → ℝ) :=
  {x |
    x ∈ P ∧
      ∀ j : Fin t,
        x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 0 ∨
          x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 1 ∨
            x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 2}

/-- Membership in `prefix_ternary_points hpn P ht` means belonging to `P` and having first `t`
coordinates in `{0, 1, 2}`. -/
theorem mem_prefix_ternary_points_iff
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    {t : ℕ}
    (ht : t ≤ p)
    (x : Fin n → ℝ) :
    x ∈ prefix_ternary_points hpn P ht ↔
      x ∈ P ∧
        ∀ j : Fin t,
          x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 0 ∨
            x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 1 ∨
              x (Fin.castLE hpn ⟨j.1, lt_of_lt_of_le j.2 ht⟩) = 2 :=
  Iff.rfl

/-- The set `S = {x ∈ P : x_j ∈ {0, 1, 2} for j = 1, …, p}` attached to the first `p`
coordinates. -/
def zero_one_two_points
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  prefix_ternary_points hpn P (Nat.le_refl p)

/-- The full-prefix ternary-point owner agrees with the specialized source-facing owner
`zero_one_two_points`. -/
theorem prefix_ternary_points_full_eq_zero_one_two_points
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    prefix_ternary_points hpn P (Nat.le_refl p) = zero_one_two_points hpn P :=
  rfl

/-- If there are no distinguished ternary coordinates, then `zero_one_two_points hpn P` is
just `P`. -/
theorem zero_one_two_points_eq_self_of_eq_zero
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hp0 : p = 0) :
    zero_one_two_points hpn P = P := by
  subst p
  ext x
  simp [zero_one_two_points, prefix_ternary_points]

/-- Membership in `zero_one_two_points hpn P` means belonging to `P` and having first `p`
coordinates in `{0, 1, 2}`. -/
theorem mem_zero_one_two_points_iff
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ zero_one_two_points hpn P ↔
      x ∈ P ∧
        ∀ j : Fin p,
          x (Fin.castLE hpn j) = 0 ∨
            x (Fin.castLE hpn j) = 1 ∨
              x (Fin.castLE hpn j) = 2 :=
  Iff.rfl

/-- The matrix `A` for the explicit `Ax ≥ b` counterexample used in Exercise 5.21. -/
def exercise_5_21_example_matrix : Matrix (Fin 3) (Fin 2) ℝ :=
  !![(1 : ℝ), 0;
    -3, 2;
    2, -2]

/-- The right-hand side vector `b` for the explicit `Ax ≥ b` counterexample used in
Exercise 5.21. -/
def exercise_5_21_example_rhs : Fin 3 → ℝ :=
  ![(0 : ℝ), 0, -1]

/-- The explicit polyhedron `P = {x ∈ ℝ_+^2 : Ax ≥ b}` used for the Exercise 5.21
counterexamples, stated on the canonical Chapter 3 owner `polyhedron_le_set`. -/
def exercise_5_21_example_polyhedron : Set (Fin 2 → ℝ) :=
  polyhedron_le_set (-exercise_5_21_example_matrix) (-exercise_5_21_example_rhs)

/-- Membership in the canonical matrix-inequality presentation of the Exercise 5.21 example
polyhedron is exactly the conjunction `0 ≤ x₀`, `3 x₀ ≤ 2 x₁`, and `2 x₁ ≤ 2 x₀ + 1`. -/
theorem mem_exercise_5_21_example_polyhedron_iff
    (x : Fin 2 → ℝ) :
    x ∈ exercise_5_21_example_polyhedron ↔
      0 ≤ x 0 ∧ 3 * x 0 ≤ 2 * x 1 ∧ 2 * x 1 ≤ 2 * x 0 + 1 := by
  rw [exercise_5_21_example_polyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hx
    have h0 : -x 0 ≤ 0 := by
      simpa [exercise_5_21_example_matrix, exercise_5_21_example_rhs, dotProduct,
        Fin.sum_univ_two] using hx 0
    have h1 : 3 * x 0 - 2 * x 1 ≤ 0 := by
      simpa [exercise_5_21_example_matrix, exercise_5_21_example_rhs, dotProduct,
        Fin.sum_univ_two] using hx 1
    have h2 : -2 * x 0 + 2 * x 1 ≤ 1 := by
      simpa [exercise_5_21_example_matrix, exercise_5_21_example_rhs, dotProduct,
        Fin.sum_univ_two] using hx 2
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  · rintro ⟨hx0, hineq1, hineq2⟩ i
    fin_cases i
    · have h0 : -x 0 ≤ 0 := by
        linarith
      simpa [exercise_5_21_example_matrix, exercise_5_21_example_rhs, dotProduct,
        Fin.sum_univ_two] using h0
    · have h1 : 3 * x 0 - 2 * x 1 ≤ 0 := by
        linarith
      simpa [exercise_5_21_example_matrix, exercise_5_21_example_rhs, dotProduct,
        Fin.sum_univ_two] using h1
    · have h2 : -2 * x 0 + 2 * x 1 ≤ 1 := by
        linarith
      simpa [exercise_5_21_example_matrix, exercise_5_21_example_rhs, dotProduct,
        Fin.sum_univ_two] using h2

/-- The reverse coordinate order `(1, 0)` used in Exercise 5.21 (2). -/
def exercise_5_21_reverse_coordinate_order : Fin 2 → Fin 2 :=
  ![(1 : Fin 2), 0]

/-- Helper for Exercise 5.21: the separating witness `((1 / 2), 1)` used in both counterexamples. -/
noncomputable def separatingWitness : Fin 2 → ℝ :=
  ![((1 : ℝ) / 2), 1]

/-- Helper for Exercise 5.21: the point `(0, 1 / 2)` in the `x₀ = 0` slice of the example
polyhedron. -/
noncomputable def zeroSlicePoint : Fin 2 → ℝ :=
  ![(0 : ℝ), (1 : ℝ) / 2]

/-- Helper for Exercise 5.21: the point `(1, 3 / 2)` in the `x₀ = 1` slice of the example
polyhedron. -/
noncomputable def oneSlicePoint : Fin 2 → ℝ :=
  ![(1 : ℝ), (3 : ℝ) / 2]

/-- Helper for Exercise 5.21: the origin point in `Fin 2 → ℝ`. -/
def originPoint : Fin 2 → ℝ :=
  ![(0 : ℝ), 0]

/-- Helper for Exercise 5.21: the reverse first-step invariant
`x 0 ≤ 2 / 3 ∧ 0 ≤ x 1 ∧ x 1 ≤ 2 * x 0`. -/
def reverseCoordinateBoundSet : Set (Fin 2 → ℝ) :=
  {x : Fin 2 → ℝ | x 0 ≤ (2 : ℝ) / 3 ∧ 0 ≤ x 1 ∧ x 1 ≤ 2 * x 0}

/-- Helper for Exercise 5.21: the point `zeroSlicePoint` satisfies the example polyhedron
inequalities. -/
lemma zeroSlicePoint_mem_example_polyhedron :
    zeroSlicePoint ∈ exercise_5_21_example_polyhedron := by
  -- Convert membership to the explicit scalar inequalities of the example.
  refine (mem_exercise_5_21_example_polyhedron_iff zeroSlicePoint).2 ?_
  norm_num [zeroSlicePoint]

/-- Helper for Exercise 5.21: the point `oneSlicePoint` satisfies the example polyhedron
inequalities. -/
lemma oneSlicePoint_mem_example_polyhedron :
    oneSlicePoint ∈ exercise_5_21_example_polyhedron := by
  -- Convert membership to the explicit scalar inequalities of the example.
  refine (mem_exercise_5_21_example_polyhedron_iff oneSlicePoint).2 ?_
  norm_num [oneSlicePoint]

/-- Helper for Exercise 5.21: the separating witness is the midpoint of the two explicit
first-step slice points. -/
lemma separatingWitness_eq_midpoint :
    separatingWitness = midpoint ℝ zeroSlicePoint oneSlicePoint := by
  -- Compare both coordinates of the explicit vectors.
  rw [midpoint_eq_smul_add]
  ext i
  fin_cases i <;> norm_num [separatingWitness, zeroSlicePoint, oneSlicePoint]

/-- Helper for Exercise 5.21: the separating witness already lies in the first forward ternary
convexification step. -/
lemma separatingWitnessMemFirstSequentialStep :
    separatingWitness ∈
      ternary_sequential_convexification_iter (Nat.le_refl 2)
        exercise_5_21_example_polyhedron (by decide : 1 ≤ 2) := by
  -- Unfold the first recursive step to the ternary hull in coordinate `0`.
  rw [ternary_sequential_convexification_iter_succ
    (hpn := Nat.le_refl 2) (P := exercise_5_21_example_polyhedron) (t := 0)
    (by decide : 0 + 1 ≤ 2)]
  rw [ternary_coordinate_lift_project_hull_def]
  simp only [Fin.castLE, Fin.mk_zero, Fin.isValue]
  -- Place the witness on the segment joining two explicit generator points.
  have hZeroCoord : zeroSlicePoint 0 = 0 := by
    norm_num [zeroSlicePoint]
  have hZeroMem :
      zeroSlicePoint ∈
        (((exercise_5_21_example_polyhedron ∩ {x : Fin 2 → ℝ | x 0 = 0}) ∪
          (exercise_5_21_example_polyhedron ∩ {x : Fin 2 → ℝ | x 0 = 1})) ∪
          (exercise_5_21_example_polyhedron ∩ {x : Fin 2 → ℝ | x 0 = 2})) := by
    exact Or.inl (Or.inl ⟨zeroSlicePoint_mem_example_polyhedron, hZeroCoord⟩)
  have hOneCoord : oneSlicePoint 0 = 1 := by
    norm_num [oneSlicePoint]
  have hOneMem :
      oneSlicePoint ∈
        (((exercise_5_21_example_polyhedron ∩ {x : Fin 2 → ℝ | x 0 = 0}) ∪
          (exercise_5_21_example_polyhedron ∩ {x : Fin 2 → ℝ | x 0 = 1})) ∪
          (exercise_5_21_example_polyhedron ∩ {x : Fin 2 → ℝ | x 0 = 2})) := by
    exact Or.inl (Or.inr ⟨oneSlicePoint_mem_example_polyhedron, hOneCoord⟩)
  have hSegment :
      separatingWitness ∈ segment ℝ zeroSlicePoint oneSlicePoint := by
    rw [separatingWitness_eq_midpoint]
    exact midpoint_mem_segment (𝕜 := ℝ) zeroSlicePoint oneSlicePoint
  exact (segment_subset_convexHull hZeroMem hOneMem) hSegment

/-- Helper for Exercise 5.21: the separating witness lies in the two-step forward ternary
sequential convexification. -/
lemma forwardWitnessMemSequentialTernaryConvexification :
    separatingWitness ∈
      ternary_sequential_convexification_iter (Nat.le_refl 2)
        exercise_5_21_example_polyhedron (Nat.le_refl 2) := by
  -- Unfold the second recursive step to the ternary hull in coordinate `1`.
  rw [ternary_sequential_convexification_iter_succ
    (hpn := Nat.le_refl 2) (P := exercise_5_21_example_polyhedron) (t := 1)
    (by decide : 1 + 1 ≤ 2)]
  rw [ternary_coordinate_lift_project_hull_def]
  simp only [Fin.castLE, Fin.mk_one, Fin.isValue]
  -- The witness itself lies in the `x₁ = 1` generator slice of the second hull.
  have hFirst :
      separatingWitness ∈
        ternary_sequential_convexification_iter (Nat.le_refl 2)
          exercise_5_21_example_polyhedron (by decide : 1 ≤ 2) :=
    separatingWitnessMemFirstSequentialStep
  have hWitnessCoord : separatingWitness 1 = 1 := by
    norm_num [separatingWitness]
  have hSlice :
      separatingWitness ∈
        (((ternary_sequential_convexification_iter (Nat.le_refl 2)
            exercise_5_21_example_polyhedron (by decide : 1 ≤ 2)) ∩
            {x : Fin 2 → ℝ | x 1 = 0}) ∪
          ((ternary_sequential_convexification_iter (Nat.le_refl 2)
            exercise_5_21_example_polyhedron (by decide : 1 ≤ 2)) ∩
            {x : Fin 2 → ℝ | x 1 = 1})) ∪
          ((ternary_sequential_convexification_iter (Nat.le_refl 2)
            exercise_5_21_example_polyhedron (by decide : 1 ≤ 2)) ∩
            {x : Fin 2 → ℝ | x 1 = 2}) := by
    exact Or.inl (Or.inr ⟨hFirst, hWitnessCoord⟩)
  exact subset_convexHull ℝ _ hSlice

/-- Helper for Exercise 5.21: every feasible point of
`zero_one_two_points (Nat.le_refl 2) exercise_5_21_example_polyhedron` is the origin. -/
lemma ternaryFeasiblePointsSubsetOrigin :
    zero_one_two_points (Nat.le_refl 2) exercise_5_21_example_polyhedron ⊆
      ({originPoint} : Set (Fin 2 → ℝ)) := by
  intro x hx
  -- Reduce feasible ternary points to the explicit inequalities and ternary coordinate cases.
  rcases (mem_zero_one_two_points_iff (Nat.le_refl 2) exercise_5_21_example_polyhedron x).1 hx with
    ⟨hxP, hxT⟩
  rcases (mem_exercise_5_21_example_polyhedron_iff x).1 hxP with ⟨_, hineq1, hineq2⟩
  have hx0Cases : x 0 = 0 ∨ x 0 = 1 ∨ x 0 = 2 := by
    simpa using hxT 0
  have hx1Cases : x 1 = 0 ∨ x 1 = 1 ∨ x 1 = 2 := by
    simpa using hxT 1
  have hx0 : x 0 = 0 := by
    rcases hx0Cases with hx0 | hx0 | hx0
    · exact hx0
    · exfalso
      rcases hx1Cases with hx1 | hx1 | hx1 <;> linarith
    · exfalso
      rcases hx1Cases with hx1 | hx1 | hx1 <;> linarith
  have hx1 : x 1 = 0 := by
    have hx1_upper : 2 * x 1 ≤ 1 := by
      linarith
    rcases hx1Cases with hx1 | hx1 | hx1
    · exact hx1
    · exfalso
      linarith
    · exfalso
      linarith
  -- Reassemble the point from its two coordinates.
  have hxEq : x = originPoint := by
    ext i
    fin_cases i <;> simp [originPoint, hx0, hx1]
  simpa [hxEq]

/-- Helper for Exercise 5.21: the reverse first-step invariant region is convex. -/
lemma reverseCoordinateBoundSet_convex :
    Convex ℝ reverseCoordinateBoundSet := by
  let π₀ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let π₁ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  let L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := π₁ - (2 : ℝ) • π₀
  -- Express each inequality as a convex halfspace and then intersect them.
  have h0 : Convex ℝ {x : Fin 2 → ℝ | x 0 ≤ (2 : ℝ) / 3} := by
    simpa [π₀] using convex_halfSpace_le π₀.isLinear ((2 : ℝ) / 3)
  have h1 : Convex ℝ {x : Fin 2 → ℝ | 0 ≤ x 1} := by
    simpa [π₁] using convex_halfSpace_ge π₁.isLinear (0 : ℝ)
  have h2 : Convex ℝ {x : Fin 2 → ℝ | x 1 - 2 * x 0 ≤ 0} := by
    simpa [L, π₀, π₁, sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using convex_halfSpace_le L.isLinear (0 : ℝ)
  have hEq :
      reverseCoordinateBoundSet =
        ({x : Fin 2 → ℝ | x 0 ≤ (2 : ℝ) / 3} ∩
          ({x : Fin 2 → ℝ | 0 ≤ x 1} ∩
            {x : Fin 2 → ℝ | x 1 - 2 * x 0 ≤ 0})) := by
    ext x
    constructor
    · intro hx
      rw [reverseCoordinateBoundSet] at hx
      rcases hx with ⟨hx0, hx1_nonneg, hx1_le⟩
      refine ⟨hx0, ⟨hx1_nonneg, ?_⟩⟩
      simpa using sub_nonpos.mpr hx1_le
    · intro hx
      rcases hx with ⟨hx0, hxrest⟩
      rcases hxrest with ⟨hx1_nonneg, hxdiff⟩
      have hx0' : x 0 ≤ (2 : ℝ) / 3 := by
        simpa using hx0
      have hx1_nonneg' : 0 ≤ x 1 := by
        simpa using hx1_nonneg
      have hxdiff' : x 1 - 2 * x 0 ≤ 0 := by
        simpa using hxdiff
      rw [reverseCoordinateBoundSet]
      exact ⟨hx0', hx1_nonneg', sub_nonpos.mp hxdiff'⟩
  rw [hEq]
  exact h0.inter (h1.inter h2)

/-- Helper for Exercise 5.21: after convexifying first in coordinate `1`, every point satisfies
`x 0 ≤ 2 / 3 ∧ 0 ≤ x 1 ∧ x 1 ≤ 2 * x 0`. -/
lemma reverseFirstStepSubsetCoordinateBounds :
    ordered_ternary_convexification_iter
        exercise_5_21_example_polyhedron
        exercise_5_21_reverse_coordinate_order
        (by decide : 1 ≤ 2) ⊆ reverseCoordinateBoundSet := by
  -- Unfold the first reverse step to the ternary hull in coordinate `1`.
  rw [ordered_ternary_convexification_iter_succ
    (P := exercise_5_21_example_polyhedron)
    (σ := exercise_5_21_reverse_coordinate_order) (t := 0)
    (by decide : 0 + 1 ≤ 2)]
  rw [ternary_coordinate_lift_project_hull_def]
  simp only [exercise_5_21_reverse_coordinate_order]
  -- Check the invariant on the three generator slices and lift it through convexity.
  refine convexHull_min ?_ reverseCoordinateBoundSet_convex
  intro x hx
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with ⟨hxP, hx1eq⟩
      have hx1eq' : x 1 = 0 := by
        simpa [exercise_5_21_reverse_coordinate_order] using hx1eq
      rcases (mem_exercise_5_21_example_polyhedron_iff x).1 hxP with
        ⟨hx0_nonneg, hineq1, _⟩
      have hx0 : x 0 = 0 := by
        linarith
      refine ⟨?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
    · rcases hx with ⟨hxP, hx1eq⟩
      have hx1eq' : x 1 = 1 := by
        simpa [exercise_5_21_reverse_coordinate_order] using hx1eq
      rcases (mem_exercise_5_21_example_polyhedron_iff x).1 hxP with
        ⟨_, hineq1, hineq2⟩
      refine ⟨?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
  · rcases hx with ⟨hxP, hx1eq⟩
    have hx1eq' : x 1 = 2 := by
      simpa [exercise_5_21_reverse_coordinate_order] using hx1eq
    rcases (mem_exercise_5_21_example_polyhedron_iff x).1 hxP with
      ⟨_, hineq1, hineq2⟩
    exfalso
    linarith

/-- Helper for Exercise 5.21: the reverse two-step ternary convexification is contained in the
singleton `{originPoint}`. -/
lemma reverseTernaryConvexificationSubsetOrigin :
    ordered_ternary_convexification_iter
        exercise_5_21_example_polyhedron
        exercise_5_21_reverse_coordinate_order
        (Nat.le_refl 2) ⊆ ({originPoint} : Set (Fin 2 → ℝ)) := by
  -- Unfold the second reverse step to the ternary hull in coordinate `0`.
  rw [ordered_ternary_convexification_iter_succ
    (P := exercise_5_21_example_polyhedron)
    (σ := exercise_5_21_reverse_coordinate_order) (t := 1)
    (by decide : 1 + 1 ≤ 2)]
  rw [ternary_coordinate_lift_project_hull_def]
  simp only [exercise_5_21_reverse_coordinate_order]
  -- The first-step bounds kill the `x₀ = 1` and `x₀ = 2` slices and collapse `x₀ = 0` to the origin.
  refine convexHull_min ?_ (convex_singleton originPoint)
  intro x hx
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with ⟨hxFirst, hx0eq⟩
      have hx0eq' : x 0 = 0 := by
        simpa [exercise_5_21_reverse_coordinate_order] using hx0eq
      have hxBounds : x ∈ reverseCoordinateBoundSet := reverseFirstStepSubsetCoordinateBounds hxFirst
      rw [reverseCoordinateBoundSet] at hxBounds
      rcases hxBounds with ⟨_, hx1_nonneg, hx1_le⟩
      have hx1eq : x 1 = 0 := by
        linarith
      have hxEq : x = originPoint := by
        ext i
        fin_cases i <;> simp [originPoint, hx0eq', hx1eq]
      simp [hxEq]
    · rcases hx with ⟨hxFirst, hx0eq⟩
      have hx0eq' : x 0 = 1 := by
        simpa [exercise_5_21_reverse_coordinate_order] using hx0eq
      have hxBounds : x ∈ reverseCoordinateBoundSet := reverseFirstStepSubsetCoordinateBounds hxFirst
      rw [reverseCoordinateBoundSet] at hxBounds
      rcases hxBounds with ⟨hx0_le, _, _⟩
      exfalso
      linarith
  · rcases hx with ⟨hxFirst, hx0eq⟩
    have hx0eq' : x 0 = 2 := by
      simpa [exercise_5_21_reverse_coordinate_order] using hx0eq
    have hxBounds : x ∈ reverseCoordinateBoundSet := reverseFirstStepSubsetCoordinateBounds hxFirst
    rw [reverseCoordinateBoundSet] at hxBounds
    rcases hxBounds with ⟨hx0_le, _, _⟩
    exfalso
    linarith

/-- Exercise 5.21 (1). For the explicit polyhedron `P = {x ∈ ℝ_+^2 : Ax ≥ b}` determined by
`exercise_5_21_example_matrix` and `exercise_5_21_example_rhs`, the two-step ternary
convexification along coordinates `0` and `1` is strictly larger than the convex hull of the
`{0,1,2}^2` feasible points of `P`, encoded as `zero_one_two_points (Nat.le_refl 2) P`. Hence the
sequential convexification theorem does not extend to `{0,1,2}`-variables. -/
theorem exercise_5_21_counterexample_to_ternary_sequential_convexification :
    ternary_sequential_convexification_iter (Nat.le_refl 2)
      exercise_5_21_example_polyhedron (Nat.le_refl 2) ≠
        convexHull ℝ (zero_one_two_points (Nat.le_refl 2) exercise_5_21_example_polyhedron) := by
  intro hEq
  -- The explicit witness belongs to the forward ternary iterate.
  have hForward :
      separatingWitness ∈
        ternary_sequential_convexification_iter (Nat.le_refl 2)
          exercise_5_21_example_polyhedron (Nat.le_refl 2) :=
    forwardWitnessMemSequentialTernaryConvexification
  have hHull :
      separatingWitness ∈
        convexHull ℝ (zero_one_two_points (Nat.le_refl 2) exercise_5_21_example_polyhedron) := by
    simpa [hEq] using hForward
  -- Every ternary feasible point, and hence its convex hull, collapses to the origin.
  have hHullSubset :
      convexHull ℝ (zero_one_two_points (Nat.le_refl 2) exercise_5_21_example_polyhedron) ⊆
        ({originPoint} : Set (Fin 2 → ℝ)) := by
    refine convexHull_min ternaryFeasiblePointsSubsetOrigin (convex_singleton originPoint)
  have hOrigin : separatingWitness ∈ ({originPoint} : Set (Fin 2 → ℝ)) :=
    hHullSubset hHull
  simpa [separatingWitness, originPoint] using hOrigin

/-- Exercise 5.21 (2). The same explicit example shows that ternary coordinate convexification
need not commute: convexifying first in coordinate `0` and then in coordinate `1` does not agree
with the reverse order `exercise_5_21_reverse_coordinate_order`. -/
theorem exercise_5_21_ternary_convexification_order_matters :
    ternary_sequential_convexification_iter (Nat.le_refl 2)
      exercise_5_21_example_polyhedron (Nat.le_refl 2) ≠
        ordered_ternary_convexification_iter
          exercise_5_21_example_polyhedron
          exercise_5_21_reverse_coordinate_order
          (Nat.le_refl 2) := by
  intro hEq
  -- Reuse the same separating witness from the forward-order counterexample.
  have hForward :
      separatingWitness ∈
        ternary_sequential_convexification_iter (Nat.le_refl 2)
          exercise_5_21_example_polyhedron (Nat.le_refl 2) :=
    forwardWitnessMemSequentialTernaryConvexification
  have hReverse :
      separatingWitness ∈
        ordered_ternary_convexification_iter
          exercise_5_21_example_polyhedron
          exercise_5_21_reverse_coordinate_order
          (Nat.le_refl 2) := by
    simpa [hEq] using hForward
  -- The reverse-order iterate is contained in the singleton `{originPoint}`.
  have hOrigin : separatingWitness ∈ ({originPoint} : Set (Fin 2 → ℝ)) :=
    reverseTernaryConvexificationSubsetOrigin hReverse
  simpa [separatingWitness, originPoint] using hOrigin

end Exercise521
