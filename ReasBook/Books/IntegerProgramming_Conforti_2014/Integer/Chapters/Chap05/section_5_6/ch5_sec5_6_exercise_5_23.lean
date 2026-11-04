/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22

open scoped Matrix
open scoped CoordinateLiftProjectNotation

-- Primary domain: Chapter 5 lift-and-project closures on prefix-binary relaxations in `ℝ^n`.
-- Core/canonical owners sampled upstream: `lift_project_closure`, `zero_one_points`,
-- `prefix_unit_box`, and `sequential_convexification_iter_eq_convexHull_zero_one_points`.
-- This file stays source-facing: it records the strict-containment consequence for the prefix
-- lift-and-project closure, rather than introducing a parallel local closure owner.

section Exercise523

variable {n : ℕ}

/-- Exercise 5.23. Let `P` be a polyhedron contained in the unit box on the first `p`
coordinates, and let `S` be the set of points of `P` whose first `p` coordinates are in
`{0, 1}`; here `S` is formalized as `zero_one_points hp P`. If `P ≠ conv(S)`, then the
lift-and-project closure of `P` over those coordinates, namely the Chapter 5 owner
`lift_project_closure P (Finset.univ.image (Fin.castLEEmb hp))`, is strictly contained in `P`. -/
theorem lift_project_closure_prefix_ssubset_of_ne_convexHull_zero_one_points
    (P : Set (Fin n → ℝ))
    (p : ℕ)
    (hp : p ≤ n)
    (hP_polyhedron : is_polyhedron P)
    (hP_subset : P ⊆ prefix_unit_box hp)
    (hP_ne : P ≠ convexHull ℝ (zero_one_points hp P)) :
    lift_project_closure P (Finset.univ.image (Fin.castLEEmb hp)) ⊂ P := by
  by_cases hp0 : p = 0
  · have hP_eq :
        P = convexHull ℝ (zero_one_points hp P) := by
      rw [zero_one_points_eq_self_of_eq_zero hp P hp0]
      exact (convexHull_eq_self.2 (convex_of_is_polyhedron hP_polyhedron)).symm
    exact False.elim (hP_ne hP_eq)
  · let I : Finset (Fin n) := Finset.univ.image (Fin.castLEEmb hp)
    have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
    have hcoord_subset : ∀ j ∈ I, (P)_{j} ⊆ P := by
      intro j hj
      refine convexHull_min ?_ hP_convex
      intro x hx
      rcases hx with hx | hx <;> exact hx.1
    have hp_pos : 0 < p := Nat.pos_of_ne_zero hp0
    let j0 : Fin n := Fin.castLE hp ⟨0, hp_pos⟩
    have hj0_mem : j0 ∈ I := by
      refine Finset.mem_image.mpr ?_
      exact ⟨⟨0, hp_pos⟩, Finset.mem_univ _, rfl⟩
    have hclosure_subset : lift_project_closure P I ⊆ P := by
      intro x hx
      rw [mem_lift_project_closure_iff] at hx
      exact hcoord_subset j0 hj0_mem (hx j0 hj0_mem)
    have hclosure_ne : lift_project_closure P I ≠ P := by
      intro hclosure_eq
      have hcoord_eq :
          ∀ j : Fin p, (P)_{Fin.castLE hp j} = P := by
        intro j
        refine Set.Subset.antisymm ?_ ?_
        · exact hcoord_subset (Fin.castLE hp j) <|
            Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · intro x hx
          have hx' : x ∈ lift_project_closure P I := by
            simpa [hclosure_eq] using hx
          rw [mem_lift_project_closure_iff] at hx'
          exact hx' (Fin.castLE hp j) <|
            Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hseq_eq :
          ∀ {t : ℕ} (ht : t ≤ p), sequential_convexification_iter hp P ht = P := by
        intro t ht
        induction t with
        | zero =>
            simpa using sequential_convexification_iter_zero hp P
        | succ t ih =>
            rw [sequential_convexification_iter_succ hp P ht]
            rw [ih (Nat.le_of_succ_le ht)]
            exact hcoord_eq ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩
      have hP_eq :
          P = convexHull ℝ (zero_one_points hp P) := by
        calc
          P = sequential_convexification_iter hp P (Nat.le_refl p) :=
            (hseq_eq (Nat.le_refl p)).symm
          _ = convexHull ℝ (zero_one_points hp P) :=
            sequential_convexification_iter_eq_convexHull_zero_one_points
              hp P hP_polyhedron hP_subset
      exact hP_ne hP_eq
    exact Set.ssubset_iff_subset_ne.mpr ⟨hclosure_subset, hclosure_ne⟩

end Exercise523
