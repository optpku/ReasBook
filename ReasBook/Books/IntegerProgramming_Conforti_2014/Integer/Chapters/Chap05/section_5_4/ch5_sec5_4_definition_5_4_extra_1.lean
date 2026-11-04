/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_lemma_4_45
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped Matrix

-- This file reuses the Chapter 3 polyhedron owner and the Chapter 5 split owner API, and adds
-- the source-facing lift-and-project constructions attached to coordinate splits.

section Definition54Extra1

variable {m n : ℕ}

/-- In Definition 5.4-extra-1 (1), for a coordinate `j`, the set `P_j` is the convex hull of the
two coordinate sections of `P` cut out by `x_j = 0` and `x_j = 1`. -/
def coordinate_lift_project_hull
    (P : Set (Fin n → ℝ))
    (j : Fin n) : Set (Fin n → ℝ) :=
  convexHull ℝ ((P ∩ {x : Fin n → ℝ | x j = 0}) ∪ (P ∩ {x : Fin n → ℝ | x j = 1}))

namespace CoordinateLiftProjectNotation

/-- Lean surface for the textbook family `P_j`, written as `P_{j}`. -/
scoped macro:max P:term noWs "_{" j:term "}" : term =>
  `(coordinate_lift_project_hull $P $j)

end CoordinateLiftProjectNotation

open scoped CoordinateLiftProjectNotation

/-- The coordinate lift-and-project hull is definitionally the convex hull of the two coordinate
faces `x_j = 0` and `x_j = 1`. -/
theorem coordinate_lift_project_hull_def
    (P : Set (Fin n → ℝ))
    (j : Fin n) :
    (P)_{j} =
      convexHull ℝ ((P ∩ {x : Fin n → ℝ | x j = 0}) ∪ (P ∩ {x : Fin n → ℝ | x j = 1})) := rfl

/-- The coordinate split over `I` at `j ∈ I`, namely `(e^j, 0)`. -/
def coordinate_split
    (I : Finset (Fin n))
    (j : Fin n)
    (hj : j ∈ I) : Split I where
  π := fun k ↦ if k = j then 1 else 0
  π0 := 0
  nonzero := by
    intro h
    have hj' : (1 : ℤ) = 0 := by
      simpa using congrArg (fun π : Fin n → ℤ ↦ π j) h
    exact one_ne_zero hj'
  zero_on_continuous := by
    intro k hk
    have hkj : k ≠ j := fun h ↦ Finset.mem_compl.mp hk (h ▸ hj)
    change (if k = j then (1 : ℤ) else 0) = 0
    simp [hkj]

/-- The coordinate split has right-hand side `0`. -/
@[simp] theorem coordinate_split_pi0
    (I : Finset (Fin n))
    (j : Fin n)
    (hj : j ∈ I) :
    (coordinate_split I j hj).π0 = 0 :=
  rfl

/-- The coordinate split coefficient vector is `1` at its distinguished coordinate. -/
@[simp] theorem coordinate_split_apply_self
    (I : Finset (Fin n))
    (j : Fin n)
    (hj : j ∈ I) :
    coordinate_split I j hj j = 1 := by
  simp [coordinate_split]

/-- The coordinate split coefficient vector vanishes away from its distinguished coordinate. -/
theorem coordinate_split_apply_of_ne
    (I : Finset (Fin n))
    {j k : Fin n}
    (hj : j ∈ I)
    (hkj : k ≠ j) :
    coordinate_split I j hj k = 0 := by
  change (if k = j then (1 : ℤ) else 0) = 0
  simp [hkj]

/-- The split scalar product for the coordinate split `(e^j, 0)` is the `j`th coordinate. -/
theorem coordinate_split_dot_eq
    (I : Finset (Fin n))
    (j : Fin n)
    (hj : j ∈ I)
    (x : Fin n → ℝ) :
    split_dot (coordinate_split I j hj) x = x j := by
  rw [split_dot_eq_sum]
  classical
  simp [coordinate_split]

/-- If `0 ≤ x j ≤ 1` holds on `P`, then the textbook coordinate hull `P_j` agrees with the split
polyhedron for the coordinate split `(e^j, 0)`. -/
theorem coordinate_lift_project_hull_eq_split_polyhedron_of_bounds
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (j : Fin n)
    (hj : j ∈ I)
    (hbox :
      ∀ x : Fin n → ℝ, x ∈ polyhedron_le_set A b → 0 ≤ x j ∧ x j ≤ 1) :
    (polyhedron_le_set A b)_{j} =
      split_polyhedron A b (coordinate_split I j hj) := by
  have hlower :
      split_branch_lower
          (polyhedron_le_set A b) (coordinate_split I j hj) (coordinate_split I j hj).π0 =
        polyhedron_le_set A b ∩ {x : Fin n → ℝ | x j = 0} := by
    ext x
    constructor
    · intro hx
      rw [mem_split_branch_lower_iff] at hx
      rcases hx with ⟨hxP, hxle⟩
      have hxj_bounds := hbox x hxP
      have hxj_le_zero : x j ≤ 0 := by
        simpa [coordinate_split_dot_eq] using hxle
      exact ⟨hxP, le_antisymm hxj_le_zero hxj_bounds.1⟩
    · rintro ⟨hxP, hxj⟩
      simp at hxj
      rw [mem_split_branch_lower_iff]
      refine ⟨hxP, ?_⟩
      simpa [coordinate_split_dot_eq] using hxj.le
  have hupper :
      split_branch_upper
          (polyhedron_le_set A b) (coordinate_split I j hj) (coordinate_split I j hj).π0 =
        polyhedron_le_set A b ∩ {x : Fin n → ℝ | x j = 1} := by
    ext x
    constructor
    · intro hx
      rw [mem_split_branch_upper_iff] at hx
      rcases hx with ⟨hxP, hxle⟩
      have hxj_bounds := hbox x hxP
      have hxj_ge_one : 1 ≤ x j := by
        simpa [coordinate_split_dot_eq] using hxle
      exact ⟨hxP, le_antisymm hxj_bounds.2 hxj_ge_one⟩
    · rintro ⟨hxP, hxj⟩
      simp at hxj
      rw [mem_split_branch_upper_iff]
      refine ⟨hxP, ?_⟩
      simpa [coordinate_split_dot_eq] using hxj.symm.le
  unfold coordinate_lift_project_hull split_polyhedron split_hull
  rw [hlower, hupper]

/-- In Definition 5.4-extra-1 (2), an inequality `α x ≤ β` is a lift-and-project inequality for
`P` relative to `I` if it is valid for `P_j` for some `j ∈ I`. -/
def IsLiftProjectInequality
    (P : Set (Fin n → ℝ))
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ) : Prop :=
  ∃ j ∈ I, is_valid_inequality ((P)_{j}) α β

/-- A lift-and-project inequality is exactly an inequality valid on one coordinate
lift-and-project hull `P_j` with `j ∈ I`. -/
theorem isLiftProjectInequality_iff_exists_valid_on_coordinate_lift_project_hull
    (P : Set (Fin n → ℝ))
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ) :
    IsLiftProjectInequality P I α β ↔
      ∃ j ∈ I, is_valid_inequality ((P)_{j}) α β := by
  rfl

/-- Unfolding characterization of `IsLiftProjectInequality`. -/
theorem isLiftProjectInequality_iff
    (P : Set (Fin n → ℝ))
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ) :
    IsLiftProjectInequality P I α β ↔
      ∃ j ∈ I, ∀ ⦃x : Fin n → ℝ⦄, x ∈ (P)_{j} → α ⬝ᵥ x ≤ β := by
  simp [IsLiftProjectInequality, is_valid_inequality_iff]

/-- In Definition 5.4-extra-1 (3), the lift-and-project closure of `P` relative to `I` is the
intersection of the coordinate hulls `P_j` over all `j ∈ I`. -/
def lift_project_closure
    (P : Set (Fin n → ℝ))
    (I : Finset (Fin n)) : Set (Fin n → ℝ) :=
  ⋂ j : {j // j ∈ I}, (P)_{j.1}

/-- Membership in the lift-and-project closure means membership in every coordinate hull `P_j`
with `j ∈ I`. -/
@[simp] theorem mem_lift_project_closure_iff
    (P : Set (Fin n → ℝ))
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ lift_project_closure P I ↔
      ∀ j ∈ I, x ∈ (P)_{j} := by
  simp [lift_project_closure]

/-- For `I = Finset.univ`, the lift-and-project closure is the intersection of all coordinate
lift-and-project hulls. -/
theorem lift_project_closure_univ_eq_iInter_coordinate_lift_project_hull
    (P : Set (Fin n → ℝ)) :
    lift_project_closure P (Finset.univ : Finset (Fin n)) =
      ⋂ j : Fin n, (P)_{j} := by
  ext x
  simp [lift_project_closure]

/-- Helper for Definition 5.4-extra-1: the coordinate row selecting the `j`th coordinate. -/
private def coordinateRow
    (j : Fin n) : Fin n → ℝ :=
  fun k ↦ if k = j then 1 else 0

/-- Helper for Definition 5.4-extra-1: the two auxiliary rows encoding `0 ≤ x j` and `x j ≤ 1`.
-/
private def coordinateBoundRows
    (j : Fin n) : Matrix (Fin 2) (Fin n) ℝ :=
  fun i ↦ if i = 0 then -coordinateRow j else coordinateRow j

/-- Helper for Definition 5.4-extra-1: the right-hand side `0, 1` for the auxiliary coordinate
bounds. -/
private def coordinateBoundTailRhs : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then 0 else 1

/-- Helper for Definition 5.4-extra-1: append the two coordinate-bound rows to the ambient matrix
presentation. -/
private def coordinateBoundMatrix
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) : Matrix (Fin (m + 2)) (Fin n) ℝ :=
  Fin.append A (coordinateBoundRows j)

/-- Helper for Definition 5.4-extra-1: append the right-hand side `0, 1` for the coordinate
bounds. -/
private def coordinateBoundRhs
    (b : Fin m → ℝ) : Fin (m + 2) → ℝ :=
  Fin.append b coordinateBoundTailRhs

/-- Helper for Definition 5.4-extra-1: the coordinate row evaluates to the `j`th coordinate. -/
private theorem coordinateRow_dot_eq
    (j : Fin n)
    (x : Fin n → ℝ) :
    coordinateRow j ⬝ᵥ x = x j := by
  -- The indicator row kills every coordinate except the distinguished one.
  simp [coordinateRow, dotProduct]

/-- Helper for Definition 5.4-extra-1: the negated coordinate row evaluates to `-x j`. -/
private theorem neg_coordinateRow_dot_eq
    (j : Fin n)
    (x : Fin n → ℝ) :
    (-coordinateRow j) ⬝ᵥ x = -x j := by
  -- Negating the coordinate row negates its scalar product with `x`.
  simp [coordinateRow, dotProduct]

/-- Helper for Definition 5.4-extra-1: the first appended auxiliary row is `-coordinateRow j`. -/
private theorem coordinateBoundMatrix_natAdd_zero
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    coordinateBoundMatrix A j (Fin.natAdd m 0) = -coordinateRow j := by
  ext k
  simp [coordinateBoundMatrix, coordinateBoundRows]

/-- Helper for Definition 5.4-extra-1: the second appended auxiliary row is `coordinateRow j`. -/
private theorem coordinateBoundMatrix_natAdd_one
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    coordinateBoundMatrix A j (Fin.natAdd m 1) = coordinateRow j := by
  ext k
  simp [coordinateBoundMatrix, coordinateBoundRows]

/-- Helper for Definition 5.4-extra-1: the first appended right-hand side entry is `0`. -/
private theorem coordinateBoundRhs_natAdd_zero
    (b : Fin m → ℝ) :
    coordinateBoundRhs b (Fin.natAdd m 0) = 0 := by
  simp [coordinateBoundRhs, coordinateBoundTailRhs]

/-- Helper for Definition 5.4-extra-1: the second appended right-hand side entry is `1`. -/
private theorem coordinateBoundRhs_natAdd_one
    (b : Fin m → ℝ) :
    coordinateBoundRhs b (Fin.natAdd m 1) = 1 := by
  simp [coordinateBoundRhs, coordinateBoundTailRhs]

/-- Helper for Definition 5.4-extra-1: evaluating the first appended auxiliary row in
`coordinateBoundMatrix A j *ᵥ x` gives the dot product with `-coordinateRow j`. -/
private theorem coordinateBoundLowerEntry_eq_negCoordinateRowDot
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n)
    (x : Fin n → ℝ) :
    (coordinateBoundMatrix A j *ᵥ x) (Fin.natAdd m 0) = (-coordinateRow j) ⬝ᵥ x := by
  -- Evaluate the matrix-vector product at the first auxiliary row, then rewrite that row.
  rw [Matrix.mulVec, coordinateBoundMatrix_natAdd_zero]

/-- Helper for Definition 5.4-extra-1: the first appended auxiliary row evaluates to `-x j`. -/
private theorem coordinateBoundLowerEntry_eq_negCoord
    (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n)
    (x : Fin n → ℝ) :
    (coordinateBoundMatrix A j *ᵥ x) (Fin.natAdd m 0) = -x j := by
  -- Route correction: rewrite the exact `mulVec` entry first, then use the scalar row formula.
  rw [coordinateBoundLowerEntry_eq_negCoordinateRowDot A j x, neg_coordinateRow_dot_eq]

/-- Helper for Definition 5.4-extra-1: the first appended auxiliary inequality is equivalent to
the lower coordinate bound `0 ≤ x j`. -/
private theorem coordinateBoundLowerRow_nonneg_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin n)
    (x : Fin n → ℝ) :
    ((coordinateBoundMatrix A j *ᵥ x) (Fin.natAdd m 0) ≤ coordinateBoundRhs b (Fin.natAdd m 0)) ↔
      0 ≤ x j := by
  -- Normalize the appended auxiliary inequality to the scalar form `-x j ≤ 0`.
  rw [coordinateBoundLowerEntry_eq_negCoord A j x, coordinateBoundRhs_natAdd_zero]
  exact (neg_nonpos : -x j ≤ 0 ↔ 0 ≤ x j)

/-- Helper for Definition 5.4-extra-1: the augmented matrix presentation is exactly the original
polyhedron together with the coordinate bounds `0 ≤ x j` and `x j ≤ 1`. -/
private theorem mem_coordinateBoundPolyhedron_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin n)
    (x : Fin n → ℝ) :
    x ∈ polyhedron_le_set (coordinateBoundMatrix A j) (coordinateBoundRhs b) ↔
      x ∈ polyhedron_le_set A b ∧ 0 ≤ x j ∧ x j ≤ 1 := by
  rw [mem_polyhedron_le_set_iff, mem_polyhedron_le_set_iff]
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · -- The leading block is the original system `A *ᵥ x ≤ b`.
      intro i
      simpa [coordinateBoundMatrix, coordinateBoundRhs, Matrix.mulVec] using hx (Fin.castAdd 2 i)
    · -- The first auxiliary row is `-x j ≤ 0`, which is equivalent to `0 ≤ x j`.
      have hLower := hx (Fin.natAdd m 0)
      exact (coordinateBoundLowerRow_nonneg_iff A b j x).1 hLower
    · -- The second auxiliary row is exactly `x j ≤ 1`.
      have hUpper := hx (Fin.natAdd m 1)
      simpa [Matrix.mulVec, coordinateBoundMatrix_natAdd_one, coordinateBoundRhs_natAdd_one,
        coordinateRow_dot_eq] using hUpper
  · rintro ⟨hxA, hxLower, hxUpper⟩
    -- Reassemble the original inequalities and the two bound rows into one stacked system.
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [coordinateBoundMatrix, coordinateBoundRhs, Matrix.mulVec] using hxA i
    · intro i
      have hi : i = 0 ∨ i = 1 := by
        fin_cases i <;> simp
      rcases hi with rfl | rfl
      · -- Reuse the normalized lower-row equivalence instead of redoing the scalar arithmetic.
        exact (coordinateBoundLowerRow_nonneg_iff A b j x).2 hxLower
      · simpa [Matrix.mulVec, coordinateBoundMatrix_natAdd_one, coordinateBoundRhs_natAdd_one,
          coordinateRow_dot_eq] using hxUpper

/-- Helper for Definition 5.4-extra-1: after adjoining the bounds `0 ≤ x j ≤ 1`, the left Balas
split is exactly the coordinate section `x j = 0`. -/
private theorem coordinateSectionZero_eq_splitPolyhedronLeft
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin n) :
    polyhedron_le_set A b ∩ {x : Fin n → ℝ | x j = 0} =
      split_polyhedron_left
        (coordinateBoundMatrix A j) (coordinateBoundRhs b) (coordinateRow j) 0 := by
  ext x
  constructor
  · rintro ⟨hxP, hxj⟩
    have hxj_eq : x j = 0 := by
      simpa using hxj
    rw [mem_split_polyhedron_left_iff, ← mem_polyhedron_le_set_iff,
      mem_coordinateBoundPolyhedron_iff, coordinateRow_dot_eq]
    refine ⟨⟨hxP, ?_, ?_⟩, ?_⟩
    · simp [hxj_eq]
    · simp [hxj_eq]
    · simp [hxj_eq]
  · intro hx
    rw [mem_split_polyhedron_left_iff, ← mem_polyhedron_le_set_iff,
      mem_coordinateBoundPolyhedron_iff, coordinateRow_dot_eq] at hx
    rcases hx with ⟨⟨hxP, hxLower, _hxUpper⟩, hxZero⟩
    -- The auxiliary lower bound and the split inequality force `x j = 0`.
    exact ⟨hxP, le_antisymm hxZero hxLower⟩

/-- Helper for Definition 5.4-extra-1: after adjoining the bounds `0 ≤ x j ≤ 1`, the right
Balas split is exactly the coordinate section `x j = 1`. -/
private theorem coordinateSectionOne_eq_splitPolyhedronRight
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin n) :
    polyhedron_le_set A b ∩ {x : Fin n → ℝ | x j = 1} =
      split_polyhedron_right
        (coordinateBoundMatrix A j) (coordinateBoundRhs b) (coordinateRow j) 1 := by
  ext x
  constructor
  · rintro ⟨hxP, hxj⟩
    have hxj_eq : x j = 1 := by
      simpa using hxj
    rw [mem_split_polyhedron_right_iff, ← mem_polyhedron_le_set_iff,
      mem_coordinateBoundPolyhedron_iff, coordinateRow_dot_eq]
    refine ⟨⟨hxP, ?_, ?_⟩, ?_⟩
    · simp [hxj_eq]
    · simp [hxj_eq]
    · simp [hxj_eq]
  · intro hx
    rw [mem_split_polyhedron_right_iff, ← mem_polyhedron_le_set_iff,
      mem_coordinateBoundPolyhedron_iff, coordinateRow_dot_eq] at hx
    rcases hx with ⟨⟨hxP, _hxLower, hxUpper⟩, hxOne⟩
    -- The ambient upper bound and the split inequality force `x j = 1`.
    exact ⟨hxP, le_antisymm hxUpper hxOne⟩

/-- Helper for Definition 5.4-extra-1: stacking two matrix systems with `Fin.append` presents the
intersection of the corresponding polyhedra. -/
private theorem polyhedronLeSet_inter_eq_append
    {p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ) :
    polyhedron_le_set A b ∩ polyhedron_le_set C d =
      polyhedron_le_set (Fin.append A C) (Fin.append b d) := by
  ext x
  constructor
  · rintro ⟨hxA, hxC⟩
    rw [mem_polyhedron_le_set_iff] at hxA hxC ⊢
    -- Each block of the appended system is discharged by the matching input polyhedron.
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [Matrix.mulVec] using hxA i
    · intro i
      simpa [Matrix.mulVec] using hxC i
  · intro hx
    rw [mem_polyhedron_le_set_iff] at hx
    refine ⟨?_, ?_⟩
    · -- Restrict the stacked system to the first block of rows.
      rw [mem_polyhedron_le_set_iff]
      intro i
      simpa [Matrix.mulVec] using hx (Fin.castAdd p i)
    · -- Restrict the stacked system to the second block of rows.
      rw [mem_polyhedron_le_set_iff]
      intro i
      simpa [Matrix.mulVec] using hx (Fin.natAdd m i)

/-- Helper for Definition 5.4-extra-1: the class of polyhedra is closed under binary
intersection. -/
private theorem isPolyhedron_inter
    {P Q : Set (Fin n → ℝ)}
    (hP : is_polyhedron P)
    (hQ : is_polyhedron Q) :
    is_polyhedron (P ∩ Q) := by
  rcases is_polyhedron_iff.mp hP with ⟨m, A, b, rfl⟩
  rcases is_polyhedron_iff.mp hQ with ⟨p, C, d, rfl⟩
  -- Present both polyhedra by matrices and then stack the rows.
  refine (is_polyhedron_iff).2 ⟨m + p, Fin.append A C, Fin.append b d, ?_⟩
  exact polyhedronLeSet_inter_eq_append A b C d

/-- Helper for Definition 5.4-extra-1: inserting one index splits the lift-and-project closure
into the new coordinate hull intersected with the smaller closure. -/
private theorem lift_project_closure_insert
    (P : Set (Fin n → ℝ))
    (I : Finset (Fin n))
    (j : Fin n)
    (hj : j ∉ I) :
    lift_project_closure P (insert j I) = (P)_{j} ∩ lift_project_closure P I := by
  ext x
  rw [mem_lift_project_closure_iff, Set.mem_inter_iff, mem_lift_project_closure_iff]
  constructor
  · intro hx
    refine ⟨hx j (Finset.mem_insert_self j I), ?_⟩
    intro k hk
    exact hx k (Finset.mem_insert_of_mem hk)
  · rintro ⟨hxj, hxI⟩ k hk
    rcases Finset.mem_insert.mp hk with rfl | hkI
    · exact hxj
    · exact hxI k hkI

/-- The coordinate lift-and-project hull of a matrix polyhedron is again a polyhedron. -/
theorem coordinate_lift_project_hull_is_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin n) :
    is_polyhedron ((polyhedron_le_set A b)_{j}) := by
  -- Route correction: instead of using an unavailable external box hypothesis, adjoin the
  -- coordinate bounds to the ambient matrix system so the two sections become Balas split pieces.
  simpa [coordinate_lift_project_hull, coordinateSectionZero_eq_splitPolyhedronLeft,
    coordinateSectionOne_eq_splitPolyhedronRight] using
    convexHull_split_polyhedra_is_polyhedron
      (coordinateBoundMatrix A j) (coordinateBoundRhs b) (coordinateRow j) 0 1

/-- Definition 5.4-extra-1 (4). If `P = {x : ℝ^n | A x ≤ b}`, then its lift-and-project closure
relative to `I` is a polyhedron. -/
theorem lift_project_closure_is_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) :
    is_polyhedron (lift_project_closure (polyhedron_le_set A b) I) := by
  induction I using Finset.induction_on with
  | empty =>
      -- The empty lift-and-project closure is the whole ambient space.
      refine (is_polyhedron_iff).2 ?_
      refine ⟨0, 0, 0, ?_⟩
      ext x
      simp [lift_project_closure, polyhedron_le_set]
  | @insert j I hj ih =>
      -- Split off the new coordinate hull and use closure of polyhedra under intersection.
      rw [lift_project_closure_insert (polyhedron_le_set A b) I j hj]
      exact isPolyhedron_inter (coordinate_lift_project_hull_is_polyhedron A b j) ih

/-- In Definition 5.4-extra-1 (5), under the source assumption that `0 ≤ x_j ≤ 1` is valid for
`P = {x : ℝ^n | A x ≤ b}` on every `j ∈ I`, the split closure of `P` is contained in its
lift-and-project closure. -/
theorem splitClosure_subset_lift_project_closure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (hbox :
      ∀ x : Fin n → ℝ, x ∈ polyhedron_le_set A b → ∀ j ∈ I, 0 ≤ x j ∧ x j ≤ 1) :
    splitClosure A b I ⊆ lift_project_closure (polyhedron_le_set A b) I := by
  intro x hx
  rw [mem_lift_project_closure_iff]
  intro j hj
  have hxsplit : x ∈ split_polyhedron A b (coordinate_split I j hj) := by
    rw [mem_splitClosure_iff] at hx
    exact hx.2 (coordinate_split I j hj)
  simpa [coordinate_lift_project_hull_eq_split_polyhedron_of_bounds A b I j hj
    (fun x hxP ↦ hbox x hxP j hj)] using hxsplit

end Definition54Extra1
