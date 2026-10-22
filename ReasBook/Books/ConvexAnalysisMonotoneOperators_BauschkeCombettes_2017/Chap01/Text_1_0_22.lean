/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Reflexive relations are formalized by the canonical predicate `Std.Refl`. -/
recall Std.Refl

/- Transitive relations are formalized by the canonical predicate `IsTrans`. -/
recall IsTrans

/- Preorder relations are formalized by the canonical predicate `IsPreorder α r`. -/
recall IsPreorder

/- Antisymmetric relations are formalized by the canonical predicate `Std.Antisymm`. -/
recall Std.Antisymm

/- Total relations are formalized by the canonical predicate `Std.Total`. -/
recall Std.Total

/- A partially ordered set in the textbook sense is formalized by `IsPartialOrder α r`. -/
recall IsPartialOrder

/- A totally ordered set in the textbook sense is formalized by `IsLinearOrder α r`. -/
recall IsLinearOrder

/- A chain in a relation is formalized by the canonical predicate `IsChain`. -/
recall IsChain

/- Directed relations are formalized by the canonical predicate `IsDirected α r`. -/
recall IsDirected

/- The textbook converse relation is the canonical `Function.swap`. -/
recall Function.swap

/- Relation-theoretic upper bounds are formalized by the canonical upper polar `upperPolar r s`. -/
recall upperPolar {α β : Type*} (r : α → β → Prop) (s : Set α) : Set β

/- Companion recall: membership in `upperPolar r s` means that every element of `s` is `r`-below
the given point. -/
recall mem_upperPolar_iff {α β : Type*} {r : α → β → Prop} {s : Set α} {b : β} :
    b ∈ upperPolar r s ↔ ∀ ⦃a⦄, a ∈ s → r a b

/- For `≤`, the upper polar is exactly the canonical set of upper bounds `upperBounds s`. -/
recall upperPolar_le {α : Type*} {s : Set α} [LE α] :
    upperPolar (· ≤ ·) s = upperBounds s

/- Relation-theoretic lower bounds are formalized by the canonical lower polar `lowerPolar r t`. -/
recall lowerPolar {α β : Type*} (r : α → β → Prop) (t : Set β) : Set α

/- Companion recall: membership in `lowerPolar r t` means that the given point is `r`-below every
element of `t`. -/
recall mem_lowerPolar_iff {α β : Type*} {r : α → β → Prop} {t : Set β} {a : α} :
    a ∈ lowerPolar r t ↔ ∀ ⦃b⦄, b ∈ t → r a b

/- For `≤`, the lower polar is exactly the canonical set of lower bounds `lowerBounds s`. -/
recall lowerPolar_le {α : Type*} {s : Set α} [LE α] :
    lowerPolar (· ≤ ·) s = lowerBounds s

/- A least element of a set in an ordered type is formalized by the canonical predicate
`IsLeast s a`. -/
recall IsLeast {α : Type*} [LE α] (s : Set α) (a : α) : Prop

/- A maximal element of an ordered type is formalized by the canonical predicate `IsMax a`. -/
recall IsMax {α : Type*} [LE α] (a : α) : Prop

/-- Text 1.0.22: the textbook notion of a directed set is exactly a nonempty type equipped with a
reflexive, transitive, and directed relation, equivalently a nonempty type with a directed
preorder relation. -/
theorem isDirectedSet_iff {α : Type u} {r : α → α → Prop} :
    (Nonempty α ∧ Std.Refl r ∧ IsTrans α r ∧ IsDirected α r) ↔
      Nonempty α ∧ IsPreorder α r ∧ IsDirected α r := by
  constructor
  · rintro ⟨hα, hrefl, htrans, hdir⟩
    exact ⟨hα, @IsPreorder.mk α r hrefl htrans, hdir⟩
  · rintro ⟨hα, hpre, hdir⟩
    exact ⟨hα, hpre.toRefl, hpre.toIsTrans, hdir⟩

/-- The textbook converse relation satisfies `Function.swap r a b` exactly when `r b a` holds. -/
theorem converseRelation_iff {α : Type u} {r : α → α → Prop} {a b : α} :
    Function.swap r a b ↔ r b a :=
  Iff.rfl

/-- Text 1.0.22: in a partial order, the textbook strict-order relation `a ≤ b ∧ a ≠ b` is the
canonical relation `<`. -/
theorem strictOrder {α : Type u} [PartialOrder α] :
    (fun a b : α ↦ a ≤ b ∧ a ≠ b) = (· < ·) := by
  funext a b
  exact propext lt_iff_le_and_ne.symm

/-- Companion bridge: the textbook strict-order condition is equivalent to the canonical relation
`a < b`. -/
theorem strictOrder_iff {α : Type u} [PartialOrder α] {a b : α} :
    (a ≤ b ∧ a ≠ b) ↔ a < b :=
  lt_iff_le_and_ne.symm
