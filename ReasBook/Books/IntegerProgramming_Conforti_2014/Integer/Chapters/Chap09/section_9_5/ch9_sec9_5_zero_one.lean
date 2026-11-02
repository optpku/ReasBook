import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

universe u v

open scoped BigOperators

/-- A family is `0/1`-valued when each coordinate is equal to `0` or `1`. -/
def is_zero_one_family {ι : Type u} {α : Type v} [Zero α] [One α] (x : ι → α) : Prop :=
  ∀ i, x i = 0 ∨ x i = 1

/-- Membership in `is_zero_one_family x` is exactly the coordinatewise `0/1` condition. -/
theorem is_zero_one_family_iff {ι : Type u} {α : Type v} [Zero α] [One α] {x : ι → α} :
    is_zero_one_family x ↔ ∀ i, x i = 0 ∨ x i = 1 :=
  Iff.rfl

/-- A real vector is `0/1`-valued when each coordinate is equal to `0` or `1`. -/
abbrev is_zero_one_vector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  is_zero_one_family x

/-- Membership in `is_zero_one_vector x` is exactly the coordinatewise `0/1` condition. -/
theorem is_zero_one_vector_iff {n : ℕ} {x : Fin n → ℝ} :
    is_zero_one_vector x ↔ ∀ i, x i = 0 ∨ x i = 1 :=
  Iff.rfl

namespace is_zero_one_family

/-- A `0/1`-valued family takes only the values `0` and `1`. -/
theorem apply {ι : Type u} {α : Type v} [Zero α] [One α] {x : ι → α}
    (hx : is_zero_one_family x) (i : ι) :
    x i = 0 ∨ x i = 1 :=
  hx i

end is_zero_one_family

namespace is_zero_one_vector

/-- A `0/1` real vector takes only the values `0` and `1`. -/
theorem apply {n : ℕ} {x : Fin n → ℝ} (hx : is_zero_one_vector x) (i : Fin n) :
    x i = 0 ∨ x i = 1 :=
  is_zero_one_family.apply hx i

/-- Each coordinate of a `0/1` real vector is nonnegative. -/
theorem nonneg {n : ℕ} {x : Fin n → ℝ} (hx : is_zero_one_vector x) (i : Fin n) :
    0 ≤ x i := by
  rcases apply hx i with hxi | hxi
  · simp [hxi]
  · simp [hxi]

/-- Each coordinate of a `0/1` real vector is bounded above by the total coordinate sum. -/
theorem le_sum_univ {n : ℕ} {x : Fin n → ℝ} (hx : is_zero_one_vector x) (i : Fin n) :
    x i ≤ ∑ j : Fin n, x j := by
  have htail_nonneg : 0 ≤ (Finset.univ.erase i).sum x := by
    exact Finset.sum_nonneg fun j _ ↦ nonneg hx j
  calc
    x i ≤ (Finset.univ.erase i).sum x + x i := by
      exact le_add_of_nonneg_left htail_nonneg
    _ = ∑ j : Fin n, x j := by
      exact Finset.sum_erase_add (s := Finset.univ) (f := x) (Finset.mem_univ i)

end is_zero_one_vector
