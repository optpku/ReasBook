/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4.ch5_sec5_4_definition_5_4_extra_1

open scoped IntegerVectorNotation

/-
Source/core/bridge triage for Exercise 10.12:
* `source-facing`: the exercise says every vertex of the full-coordinate lift-project closure of
  `[0,1]^n` is half-integral.
* `core/canonical`: Chapter 3 already owns the canonical `zero_one_cube` and its extreme-point API.
* `bridge/view`: this file computes that the Chapter 5 full-coordinate lift-project closure of
  `Set.Icc 0 1` is the cube itself, so its extreme points are exactly `zero_one_cube n`. The
  source statement is then a short corollary in the Chapter 4 lattice owner `ℤ^n`.
-/

section Exercise1012

variable {n : ℕ}

private lemma coordinate_lift_project_hull_unit_hypercube_eq
    (j : Fin n) :
    coordinate_lift_project_hull (Set.Icc (0 : Fin n → ℝ) 1) j =
      Set.Icc (0 : Fin n → ℝ) 1 := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_Icc (0 : Fin n → ℝ) 1)
    intro x hx
    rcases hx with (⟨hx, -⟩ | ⟨hx, -⟩)
    · exact hx
    · exact hx
  · intro x hx
    let xZero : Fin n → ℝ := Function.update x j 0
    let xOne : Fin n → ℝ := Function.update x j 1
    have hx_nonneg : 0 ≤ x := hx.1
    have hx_le_one : x ≤ 1 := hx.2
    have hxj : x j ∈ Set.Icc (0 : ℝ) 1 := ⟨hx_nonneg j, hx_le_one j⟩
    have hxZero_mem :
        xZero ∈ Set.Icc (0 : Fin n → ℝ) 1 ∩ {y : Fin n → ℝ | y j = 0} := by
      refine ⟨?_, by simp [xZero]⟩
      refine ⟨?_, ?_⟩
      · intro k
        by_cases hkj : k = j
        · subst hkj
          simp [xZero]
        · simpa [xZero, Function.update, hkj] using hx_nonneg k
      · intro k
        by_cases hkj : k = j
        · subst hkj
          simp [xZero]
        · simpa [xZero, Function.update, hkj] using hx_le_one k
    have hxOne_mem :
        xOne ∈ Set.Icc (0 : Fin n → ℝ) 1 ∩ {y : Fin n → ℝ | y j = 1} := by
      refine ⟨?_, by simp [xOne]⟩
      refine ⟨?_, ?_⟩
      · intro k
        by_cases hkj : k = j
        · subst hkj
          simp [xOne]
        · simpa [xOne, Function.update, hkj] using hx_nonneg k
      · intro k
        by_cases hkj : k = j
        · subst hkj
          simp [xOne]
        · simpa [xOne, Function.update, hkj] using hx_le_one k
    have hx_lineMap : AffineMap.lineMap xZero xOne (x j) = x := by
      funext k
      by_cases hkj : k = j
      · subst hkj
        simp [AffineMap.lineMap_apply, xZero, xOne]
      · simp [AffineMap.lineMap_apply, xZero, xOne, Function.update, hkj]
    have hx_segment : x ∈ segment ℝ xZero xOne := by
      rw [← hx_lineMap]
      exact lineMap_mem_segment ℝ xZero xOne hxj
    let S : Set (Fin n → ℝ) :=
      (Set.Icc (0 : Fin n → ℝ) 1 ∩ {y : Fin n → ℝ | y j = 0}) ∪
        (Set.Icc (0 : Fin n → ℝ) 1 ∩ {y : Fin n → ℝ | y j = 1})
    have hxZero_mem' : xZero ∈ S := Or.inl hxZero_mem
    have hxOne_mem' : xOne ∈ S := Or.inr hxOne_mem
    exact
      (segment_subset_convexHull hxZero_mem' hxOne_mem') hx_segment

/-- The full-coordinate Chapter 5 lift-project closure of the unit hypercube `[0,1]^n` is the
cube itself. -/
theorem lift_project_closure_unit_hypercube_eq
    (n : ℕ) :
    lift_project_closure (Set.Icc (0 : Fin n → ℝ) 1) Finset.univ =
      Set.Icc (0 : Fin n → ℝ) 1 := by
  cases n with
  | zero =>
      ext x
      simp [lift_project_closure]
  | succ n =>
      ext x
      rw [mem_lift_project_closure_iff]
      constructor
      · intro hx
        simpa [coordinate_lift_project_hull_unit_hypercube_eq] using
          hx 0 (by simp)
      · intro hx j hj
        simpa [coordinate_lift_project_hull_unit_hypercube_eq] using hx

/-- The vertices of the full-coordinate lift-project closure of `[0,1]^n` are exactly the `0/1`
vectors of `zero_one_cube n`. -/
theorem extremePoints_lift_project_closure_unit_hypercube_eq_zero_one_cube
    (n : ℕ) :
    (lift_project_closure (Set.Icc (0 : Fin n → ℝ) 1) Finset.univ).extremePoints ℝ =
      zero_one_cube n := by
  rw [lift_project_closure_unit_hypercube_eq]
  simpa [Set.mem_Icc, Set.mem_univ_pi] using extremePoints_unit_box_eq_zero_one_cube n

/-- Exercise 10.12. For the Chapter 5 lift-and-project closure over all coordinates of the unit
cube `[0,1]^n`, written canonically as `Set.Icc 0 1`, every vertex is half-integral; equivalently,
doubling it gives an integer vector. -/
theorem vertices_of_lovasz_schrijver_N_unit_hypercube_are_half_integral
    {x : Fin n → ℝ}
    (hx : x ∈ (lift_project_closure (Set.Icc (0 : Fin n → ℝ) 1) Finset.univ).extremePoints ℝ) :
    (2 : ℝ) • x ∈ ℤ^n := by
  have hx_zero_one : x ∈ zero_one_cube n := by
    rwa [← extremePoints_lift_project_closure_unit_hypercube_eq_zero_one_cube n]
  rw [mem_integerVectors_iff_forall]
  intro i
  rcases (mem_zero_one_cube_iff.mp hx_zero_one) i with hxi | hxi
  · refine ⟨0, ?_⟩
    simp [hxi]
  · refine ⟨2, ?_⟩
    simp [hxi]

end Exercise1012
