module

public import Mathlib.Topology.GDelta.Basic
import all Mathlib.Topology.GDelta.Basic
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for finite unions of nowhere dense subsets:
- primary domain: general topology of nowhere dense subsets
- sampled owner-level declarations:
  `isNowhereDense_empty`,
  `IsNowhereDense`,
  `IsNowhereDense.closure`,
  `isClosed_isNowhereDense_iff_compl`
- best owner abstraction: `IsNowhereDense`, with finite-union API living in its namespace
- primitive data: a finite family of subsets together with pointwise `IsNowhereDense` hypotheses
- derived API: the finite `sUnion` theorem below; the closed/dense-complement reformulation is a
  proof tool, not primitive public data

Layer triage:
- `source-facing`: finite unions of nowhere dense subsets
- `core/canonical`: `IsNowhereDense`
- `bridge/view`: the dense-open-complement reformulation used in the proof
-/

namespace IsNowhereDense

/-- The union of two nowhere dense subsets is nowhere dense. -/
theorem union {s t : Set X} (hs : IsNowhereDense s) (ht : IsNowhereDense t) :
    IsNowhereDense (s ∪ t) := by
  -- Reinterpret the closures of `s` and `t` via dense open complements.
  have hs' := (isClosed_isNowhereDense_iff_compl).mp ⟨isClosed_closure, hs.closure⟩
  have ht' := (isClosed_isNowhereDense_iff_compl).mp ⟨isClosed_closure, ht.closure⟩
  -- It is enough to prove nowhere denseness for the union of the closures.
  refine (((isClosed_isNowhereDense_iff_compl).mpr ?_).2).mono
    (union_subset_union subset_closure subset_closure)
  -- The complement of the union is the intersection of the two dense open complements.
  rw [compl_union]
  exact ⟨hs'.1.inter ht'.1, hs'.2.inter_of_isOpen_right ht'.2 ht'.1⟩

/-- Lemma 5.21.2: the union of finitely many nowhere dense subsets of a topological space is
nowhere dense. -/
-- Proof sketch: induct on the finite family of subsets; the empty union is nowhere dense, and the
-- inductive step reduces to the binary union theorem.
theorem sUnion {S : Set (Set X)} (hS : S.Finite)
    (h : ∀ s ∈ S, IsNowhereDense s) :
    IsNowhereDense (⋃₀ S) := by
  -- Induct on the finite family and reduce the insert step to the binary union theorem.
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      simp
  | insert _ _ ih =>
      simp only [forall_mem_insert, sUnion_insert] at h ⊢
      exact h.1.union (ih h.2)

end IsNowhereDense
