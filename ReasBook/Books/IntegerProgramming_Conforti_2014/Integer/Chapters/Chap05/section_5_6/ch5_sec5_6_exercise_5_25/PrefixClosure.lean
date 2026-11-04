/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22

open scoped CoordinateLiftProjectNotation

-- Reusable prefix-coordinate closure and binary-point API for Exercise 5.25.

section Exercise525

variable {n p : ℕ}

/-- The one-step lift-and-project closure of `P` along the first `p` coordinates. -/
def prefix_lift_project_closure
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  lift_project_closure P (Finset.univ.image (Fin.castLEEmb hp))

/-- Membership in `prefix_lift_project_closure hp P` means membership in every coordinate
lift-and-project hull attached to the first `p` coordinates. -/
theorem mem_prefix_lift_project_closure_iff
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ prefix_lift_project_closure hp P ↔
      ∀ j : Fin p, x ∈ (P)_{Fin.castLE hp j} := by
  simp [prefix_lift_project_closure, mem_lift_project_closure_iff]

/-- The points of `P` whose coordinates indexed by `J` are binary. -/
def binary_prefix_points_on_subset
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (J : Finset (Fin p)) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | x ∈ P ∧ ∀ j ∈ J, x (Fin.castLE hp j) = 0 ∨ x (Fin.castLE hp j) = 1}

/-- Membership in `binary_prefix_points_on_subset hp P J` means belonging to `P` and having
binary coordinates on the prefix index set `J`. -/
theorem mem_binary_prefix_points_on_subset_iff
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (J : Finset (Fin p))
    (x : Fin n → ℝ) :
    x ∈ binary_prefix_points_on_subset hp P J ↔
      x ∈ P ∧ ∀ j ∈ J, x (Fin.castLE hp j) = 0 ∨ x (Fin.castLE hp j) = 1 :=
  Iff.rfl

/-- For the full prefix index set `Fin p`, the subset-based binary-point owner agrees with the
Chapter 5 full-prefix owner `zero_one_points`. -/
theorem binary_prefix_points_on_subset_univ_eq_zero_one_points
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    binary_prefix_points_on_subset hp P (Finset.univ : Finset (Fin p)) = zero_one_points hp P := by
  ext x
  simp [binary_prefix_points_on_subset, zero_one_points, prefix_binary_points]

/-- For the full prefix index set `Fin p`, the subset-based binary-point owner agrees with the
underlying `prefix_binary_points` owner from Theorem 5.22. -/
theorem binary_prefix_points_on_subset_univ_eq_prefix_binary_points
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    binary_prefix_points_on_subset hp P (Finset.univ : Finset (Fin p)) =
      prefix_binary_points hp P (Nat.le_refl p) := by
  simpa [zero_one_points] using binary_prefix_points_on_subset_univ_eq_zero_one_points hp P

/-- The `k`th lift-and-project closure is obtained by iterating the one-step closure operator
along the first `p` coordinates. -/
def kth_lift_project_closure
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (k : ℕ) : Set (Fin n → ℝ) :=
  Nat.iterate (prefix_lift_project_closure hp) k P

/-- The zeroth lift-and-project closure is the original set `P`. -/
theorem kth_lift_project_closure_zero
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    kth_lift_project_closure hp P 0 = P :=
  rfl

/-- The successor lift-and-project closure is the one-step closure of the previous iterate. -/
theorem kth_lift_project_closure_succ
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (k : ℕ) :
    kth_lift_project_closure hp P (k + 1) =
      prefix_lift_project_closure hp (kth_lift_project_closure hp P k) := by
  simpa [kth_lift_project_closure] using
    Function.iterate_succ_apply' (prefix_lift_project_closure hp) k P

end Exercise525
