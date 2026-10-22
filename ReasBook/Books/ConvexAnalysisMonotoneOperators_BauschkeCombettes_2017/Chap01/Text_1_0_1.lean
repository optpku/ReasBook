/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

section Additive

variable {X : Type u} [AddCommGroup X]

/-- Pointwise addition of two subsets of an additive commutative group is the set of all
pairwise sums. -/
theorem pointwise_add_eq_setOf_add (C D : Set X) :
    C + D = {x | ∃ c ∈ C, ∃ d ∈ D, c + d = x} := by
  ext x
  simp [Set.mem_add]

/-- Pointwise subtraction of two subsets of an additive commutative group is the set of all
pairwise differences. -/
theorem pointwise_sub_eq_setOf_sub (C D : Set X) :
    C - D = {x | ∃ c ∈ C, ∃ d ∈ D, c - d = x} := by
  ext x
  simp [Set.mem_sub]

end Additive

section Module

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Scalar multiplication of a singleton subset by a set of scalars is the set of all scalar
multiples of the chosen vector. -/
theorem set_smul_singleton_eq_setOf_smul (Λ : Set ℝ) (z : X) :
    Λ • ({z} : Set X) = {x | ∃ r ∈ Λ, r • z = x} := by
  ext x
  simp

end Module
