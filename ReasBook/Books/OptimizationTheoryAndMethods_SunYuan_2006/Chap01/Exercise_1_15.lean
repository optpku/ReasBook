/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

section Chapter01Exercise115

-- Semantic recall hits verified for this item: `Finset.mem_convexHull`,
-- `Finset.convexHull_eq`, and `convexHull_basis_eq_stdSimplex`.

local notation "Point" => EuclideanSpace ℝ (Fin 2)
local notation "e0" => (EuclideanSpace.single 0 (1 : ℝ) : Point)
local notation "e1" => (EuclideanSpace.single 1 (1 : ℝ) : Point)

/-- Helper for Chapter01 Exercise 1.15: the range of the two coordinate basis vectors is the
explicit two-point set `{e0, e1}`. -/
lemma range_single_eq_pair :
    Set.range (fun i : Fin 2 ↦ EuclideanSpace.single i (1 : ℝ)) = ({e0, e1} : Set Point) := by
  -- Normalize the indexed range to the two concrete triangle vertices.
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hy
    rcases hy with rfl | rfl <;> exact ⟨_, rfl⟩

/-- Helper for Chapter01 Exercise 1.15: the origin is different from the first basis vertex. -/
lemma zero_ne_e0 : (0 : Point) ≠ e0 := by
  -- Compare the first coordinates of the two vertices.
  intro h
  have h0 : (0 : ℝ) = 1 := by
    simpa [PiLp.single_apply] using congrArg (fun v : Point => v 0) h
  norm_num at h0

/-- Helper for Chapter01 Exercise 1.15: the origin is different from the second basis vertex. -/
lemma zero_ne_e1 : (0 : Point) ≠ e1 := by
  -- Compare the second coordinates of the two vertices.
  intro h
  have h1 : (0 : ℝ) = 1 := by
    simpa [PiLp.single_apply] using congrArg (fun v : Point => v 1) h
  norm_num at h1

/-- Helper for Chapter01 Exercise 1.15: the two basis vertices are distinct. -/
lemma e0_ne_e1 : e0 ≠ e1 := by
  -- Compare the first coordinates of the two basis vertices.
  intro h
  have h0 : (1 : ℝ) = 0 := by
    simpa [PiLp.single_apply] using congrArg (fun v : Point => v 0) h
  norm_num at h0

/-- Helper for Chapter01 Exercise 1.15: inserting the origin into the unit-basis range produces
the three vertices of the standard coordinate triangle. -/
lemma insert_origin_range_eq_triangle :
    Set.insert (0 : Point) (Set.range (fun i : Fin 2 ↦ EuclideanSpace.single i (1 : ℝ))) =
      ({0, e0, e1} : Set Point) := by
  -- Rewrite the source set as the explicit triangle-vertex set.
  rw [range_single_eq_pair]
  ext y
  constructor <;> intro hy
  · change y = 0 ∨ y ∈ ({e0, e1} : Set Point) at hy
    change y = 0 ∨ y ∈ ({e0, e1} : Set Point)
    exact hy
  · change y = 0 ∨ y ∈ ({e0, e1} : Set Point) at hy
    change y = 0 ∨ y ∈ ({e0, e1} : Set Point)
    exact hy

/-- Helper for Chapter01 Exercise 1.15: membership in the convex hull of the three triangle
vertices is equivalent to the coordinate inequalities defining the triangle. -/
lemma mem_triangleHull_iff (x : Point) :
    x ∈ convexHull ℝ ({0, e0, e1} : Set Point) ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
  constructor
  · intro hx
    have hx' : x ∈ convexHull ℝ ((({(0 : Point), e0, e1} : Finset Point) : Set Point)) := by
      simpa [Finset.coe_insert, Finset.coe_singleton] using hx
    rcases (Finset.mem_convexHull'.mp hx') with ⟨w, hw_nonneg, hw_sum, hw_eq⟩
    have hw0 : 0 ≤ w 0 := hw_nonneg 0 (by simp)
    have hwe0 : 0 ≤ w e0 := hw_nonneg e0 (by simp)
    have hwe1 : 0 ≤ w e1 := hw_nonneg e1 (by simp)
    -- Read off the two coordinates from the barycentric combination equality.
    have hw_sum' : w 0 + w e0 + w e1 = 1 := by
      have h := hw_sum
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton] at h
      · simpa [add_comm, add_left_comm, add_assoc] using h
      · simp [e0_ne_e1]
      · simp [zero_ne_e0, zero_ne_e1]
    have hx0 : w e0 = x 0 := by
      have h0 := congrArg (fun v : Point => v 0) hw_eq
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton] at h0
      · simpa [PiLp.single_apply] using h0
      · simp [e0_ne_e1]
      · simp [zero_ne_e0, zero_ne_e1]
    have hx1 : w e1 = x 1 := by
      have h1 := congrArg (fun v : Point => v 1) hw_eq
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton] at h1
      · simpa [PiLp.single_apply] using h1
      · simp [e0_ne_e1]
      · simp [zero_ne_e0, zero_ne_e1]
    refine ⟨?_, ?_, ?_⟩
    · simpa [hx0] using hwe0
    · simpa [hx1] using hwe1
    · linarith [hw_sum']
  · rintro ⟨hx0, hx1, hsum⟩
    let w : Fin 3 → ℝ := fun i ↦
      match i with
      | 0 => 1 - x 0 - x 1
      | 1 => x 0
      | 2 => x 1
    let z : Fin 3 → Point := fun i ↦
      match i with
      | 0 => 0
      | 1 => e0
      | 2 => e1
    -- Use the explicit barycentric coordinates of the triangle.
    have hw_nonneg : ∀ i, 0 ≤ w i := by
      intro i
      fin_cases i
      · dsimp [w]
        linarith
      · simpa [w] using hx0
      · simpa [w] using hx1
    have hw_sum : ∑ i, w i = 1 := by
      rw [Fin.sum_univ_three]
      dsimp [w]
      ring
    have hz_mem : ∀ i, z i ∈ ({0, e0, e1} : Set Point) := by
      intro i
      fin_cases i <;> simp [z]
    have hw_eq : ∑ i, w i • z i = x := by
      -- Check the barycentric combination coordinatewise.
      ext i
      fin_cases i
      · rw [Fin.sum_univ_three]
        simp [w, z]
      · rw [Fin.sum_univ_three]
        simp [w, z]
    exact mem_convexHull_of_exists_fintype w z hw_nonneg hw_sum hz_mem hw_eq

/-- Chapter01 Exercise 1.15: the convex hull of
`Set.insert 0 (Set.range (fun i : Fin 2 ↦ EuclideanSpace.single i 1)) = {(0, 0), (1, 0), (0, 1)}`
is the triangle `{x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}`. -/
theorem convexHull_originAndUnitBasisSet_eq :
    convexHull ℝ
        (Set.insert (0 : EuclideanSpace ℝ (Fin 2))
          (Set.range (fun i : Fin 2 ↦ EuclideanSpace.single i (1 : ℝ)))) =
      {x : EuclideanSpace ℝ (Fin 2) | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} := by
  -- Rewrite the source set to the three explicit vertices of the triangle.
  rw [insert_origin_range_eq_triangle]
  -- Then use the barycentric-coordinate description of that triangle hull.
  ext x
  exact mem_triangleHull_iff x

end Chapter01Exercise115
