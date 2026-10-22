/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

variable {Omega : Type u}

/-- A family of sets contains `univ` and is closed under complements and binary intersections. -/
class HasUnivComplInter (A : Set (Set Omega)) : Prop where
  univ_mem : univ ∈ A
  compl_mem : ∀ ⦃s : Set Omega⦄, s ∈ A → sᶜ ∈ A
  inter_mem : ∀ ⦃s t : Set Omega⦄, s ∈ A → t ∈ A → s ∩ t ∈ A

/-- Helper for Theorem 1.7: an algebra of sets satisfies the `univ`/complement/intersection
closure formulation. -/
lemma hasUnivComplInter_of_isSetAlgebra {A : Set (Set Omega)} (hA : IsSetAlgebra A) :
    HasUnivComplInter A where
  univ_mem := by
    -- Repackage the existing algebra axiom that `univ` belongs to the family.
    exact hA.univ_mem
  compl_mem := by
    -- Complement closure is already one of the algebra axioms.
    intro s hs
    exact hA.compl_mem hs
  inter_mem := by
    -- Intersection closure is a standard derived fact for algebras of sets.
    intro s t hs ht
    exact hA.inter_mem hs ht

/-- Helper for Theorem 1.7: closure under complements and membership of `univ` force
membership of `∅`. -/
lemma empty_mem_of_hasUnivComplInter {A : Set (Set Omega)} (hA : HasUnivComplInter A) :
    (∅ : Set Omega) ∈ A := by
  -- Take the complement of `univ` and rewrite it as `∅`.
  simpa using hA.compl_mem hA.univ_mem

/-- Helper for Theorem 1.7: closure under complements and intersections implies closure under
binary unions. -/
lemma union_mem_of_hasUnivComplInter {A : Set (Set Omega)} (hA : HasUnivComplInter A)
    {s t : Set Omega} (hs : s ∈ A) (ht : t ∈ A) : s ∪ t ∈ A := by
  -- Apply De Morgan: a union is the complement of an intersection of complements.
  have h_inter_compl : sᶜ ∩ tᶜ ∈ A := hA.inter_mem (hA.compl_mem hs) (hA.compl_mem ht)
  have h_union_compl : (sᶜ ∩ tᶜ)ᶜ ∈ A := hA.compl_mem h_inter_compl
  simpa [Set.union_eq_compl_compl_inter_compl] using h_union_compl

/-- Helper for Theorem 1.7: the textbook `univ`/complement/intersection axioms reconstruct
mathlib's algebra-of-sets structure. -/
lemma isSetAlgebra_of_hasUnivComplInter {A : Set (Set Omega)} (hA : HasUnivComplInter A) :
    IsSetAlgebra A where
  empty_mem := by
    -- Recover the missing empty-set axiom from `univ` by complementing once.
    exact empty_mem_of_hasUnivComplInter hA
  compl_mem := by
    -- Complement closure is part of the assumed textbook structure.
    intro s hs
    exact hA.compl_mem hs
  union_mem := by
    -- Recover unions from intersections via De Morgan's law.
    intro s t hs ht
    exact union_mem_of_hasUnivComplInter hA hs ht

-- Proof sketch: For the forward direction, use `IsSetAlgebra.univ_mem`, `IsSetAlgebra.compl_mem`,
-- and `IsSetAlgebra.inter_mem`. For the reverse direction, obtain `∅ ∈ A` from `univ ∈ A` and
-- complement closure, then recover closure under binary unions from complements and intersections
-- by De Morgan's law.
/-- Theorem 1.7: A class of subsets of `Omega` is an algebra of sets if and only if it contains
`univ`, is closed under complements, and is closed under binary intersections. -/
theorem isSetAlgebra_iff_univ_compl_inter {Omega : Type u} {A : Set (Set Omega)} :
    IsSetAlgebra A ↔ HasUnivComplInter A := by
  constructor
  · -- Forward direction: repackage the standard algebra axioms into the textbook formulation.
    intro hA
    exact hasUnivComplInter_of_isSetAlgebra hA
  · -- Reverse direction: rebuild the missing empty-set and union axioms from the textbook ones.
    intro hA
    exact isSetAlgebra_of_hasUnivComplInter hA
