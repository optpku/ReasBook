/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {G : Type u} [Group G]

/-- The elementary Nielsen move `(T1)` inverts one entry of a finite list of group elements. -/
def invert_elementary_nielsen_move (U V : List G) : Prop :=
  ∃ i : ℕ, ∃ hi : i < U.length, V = U.set i (U.get ⟨i, hi⟩)⁻¹

/-- The elementary Nielsen move `(T2)` replaces one entry by its product with a distinct entry. -/
def multiply_elementary_nielsen_move (U V : List G) : Prop :=
  ∃ i j : ℕ, ∃ hi : i < U.length, ∃ hj : j < U.length,
    i ≠ j ∧ V = U.set i (U.get ⟨i, hi⟩ * U.get ⟨j, hj⟩)

/-- The elementary Nielsen move `(T3)` deletes an entry equal to `1`. -/
def delete_elementary_nielsen_move (U V : List G) : Prop :=
  ∃ i : ℕ, ∃ hi : i < U.length, U.get ⟨i, hi⟩ = 1 ∧ V = U.eraseIdx i

/-- Definition 1-2-1: an elementary Nielsen move on a finite vector of group elements is one of
the three operations `(T1)`, `(T2)`, or `(T3)`: invert one entry, replace one entry by its
product with a distinct entry, or delete an entry equal to `1`. -/
def elementary_nielsen_move (U V : List G) : Prop :=
  invert_elementary_nielsen_move U V ∨
    multiply_elementary_nielsen_move U V ∨
    delete_elementary_nielsen_move U V

/-- A regular elementary Nielsen move is an elementary Nielsen move of type `(T1)` or `(T2)`,
so it does not delete a trivial entry. -/
def regular_elementary_nielsen_move (U V : List G) : Prop :=
  invert_elementary_nielsen_move U V ∨ multiply_elementary_nielsen_move U V

/-- A Nielsen transformation is a finite composition of elementary Nielsen moves. -/
abbrev nielsen_transforms_to : List G → List G → Prop :=
  Relation.ReflTransGen elementary_nielsen_move

/-- A regular Nielsen transformation is a finite composition of regular elementary Nielsen moves,
equivalently a Nielsen transformation with no factor of type `(T3)`. -/
abbrev regular_nielsen_transforms_to : List G → List G → Prop :=
  Relation.ReflTransGen regular_elementary_nielsen_move

/-- A singular Nielsen transformation is a Nielsen transformation that admits a factorization with
at least one elementary move of type `(T3)`. -/
def singular_nielsen_transforms_to (U V : List G) : Prop :=
  ∃ W₁ W₂ : List G,
    regular_nielsen_transforms_to U W₁ ∧
      delete_elementary_nielsen_move W₁ W₂ ∧
      nielsen_transforms_to W₂ V
