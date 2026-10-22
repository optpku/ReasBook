/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Extr

section Chapter01Definition142

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/- Chapter01 Definition 1.4.2 (1): the canonical owner for an unconstrained global minimizer of
`f : Point → ℝ` at `xStar` is `IsMinOn f Set.univ xStar`. The exact pointwise characterization is
already the mathlib theorem `isMinOn_univ_iff`, so this item is a direct canonical recall rather
than a new local wrapper.

Core/canonical owner:
- `IsMinOn f Set.univ xStar`

Derived API already available in mathlib:
- `isMinOn_univ_iff`
-/
#check (IsMinOn : (Point → ℝ) → Set Point → Point → Prop)
#check isMinOn_univ_iff

/-
Chapter01 Definition 1.4.2 (2) is best organized around the source-facing owner “strict
minimization on a set”, with the unconstrained strict global notion obtained by specializing to
`Set.univ`.

Source-facing owner:
- `IsStrictMinOn f s a`

Chapter 1 global specialization:
- `IsStrictMinOn f Set.univ xStar`
- `isStrictMinOn_univ_iff`
-/
section StrictMinOn

variable {α : Type*} {β : Type*} [Preorder β]

/-- A strict minimizer of `f` on `s` is a point of `s` whose value is strictly smaller than that
of every distinct point of `s`. -/
class IsStrictMinOn (f : α → β) (s : Set α) (a : α) : Prop where
  mem : a ∈ s
  objective_lt (x : α) (_ : x ∈ s) (_ : x ≠ a) : f a < f x

/-- Unfolding formula for `IsStrictMinOn`. -/
theorem isStrictMinOn_iff
    (f : α → β) (s : Set α) (a : α) :
    IsStrictMinOn f s a ↔ a ∈ s ∧ ∀ x : α, x ∈ s → x ≠ a → f a < f x := by
  constructor
  · intro h
    exact ⟨h.mem, h.objective_lt⟩
  · rintro ⟨ha, hlt⟩
    exact ⟨ha, hlt⟩

/-- A strict minimizer on `s` is, in particular, a minimizer on `s`. -/
theorem IsStrictMinOn.isMinOn
    {f : α → β} {s : Set α} {a : α} (h : IsStrictMinOn f s a) :
    IsMinOn f s a := by
  rw [isMinOn_iff]
  intro x hx
  by_cases hxa : x = a
  · simp [hxa]
  · exact le_of_lt (h.objective_lt x hx hxa)

/-- Specializing `IsStrictMinOn` to `Set.univ` removes the membership field and leaves the usual
strict pointwise global-minimum inequality. -/
theorem isStrictMinOn_univ_iff
    (f : α → β) (a : α) :
    IsStrictMinOn f Set.univ a ↔ ∀ x : α, x ≠ a → f a < f x := by
  rw [isStrictMinOn_iff]
  simp

end StrictMinOn

end Chapter01Definition142
