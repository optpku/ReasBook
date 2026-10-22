/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FreeGroup
open MulAction

noncomputable section

private def tupleLetters {ι : Type*} [DecidableEq ι] {F : Type*} [Group F] {n : ℕ}
    (basis : FreeGroupBasis ι F)
    (u v : Fin n → F) : List ι :=
  List.flatMap (fun i ↦
    ((basis.repr (u i)).toWord.map Prod.fst) ++ ((basis.repr (v i)).toWord.map Prod.fst)
  ) (List.finRange n)

private def signedLetters {ι : Type*} (letters : List ι) : List (ι × Bool) :=
  List.flatMap (fun a ↦ [(a, false), (a, true)]) letters

private def wordsOfLength {ι : Type*} (letters : List ι) : ℕ → List (List (ι × Bool))
  | 0 => [[]]
  | n + 1 =>
      List.flatMap (fun w ↦ (signedLetters letters).map fun a ↦ a :: w) (wordsOfLength letters n)

private def searchBound {ι : Type*} [DecidableEq ι] {F : Type*} [Group F] {n : ℕ}
    (basis : FreeGroupBasis ι F)
    (u v : Fin n → F) : ℕ :=
  ∑ i : Fin n, (FreeGroup.norm (basis.repr (u i)) + FreeGroup.norm (basis.repr (v i)))

private def candidateWords {ι : Type*} [DecidableEq ι] {F : Type*} [Group F] {n : ℕ}
    (basis : FreeGroupBasis ι F) (u v : Fin n → F) : List (List (ι × Bool)) :=
  List.flatMap (wordsOfLength (tupleLetters basis u v)) (List.range (searchBound basis u v + 1))

private def commonConjugatorSearch {ι : Type*} [DecidableEq ι] {F : Type*} [Group F] {n : ℕ}
    (basis : FreeGroupBasis ι F) (u v : Fin n → F) : Bool := by
  let _ : DecidableEq F := Classical.decEq F
  exact
    (candidateWords basis u v).any fun word ↦
      let w := basis.repr.symm (FreeGroup.mk word)
      decide (∀ i, w⁻¹ * u i * w = v i)

section Search

variable {ι : Type*} [DecidableEq ι] {F : Type u} [Group F] [IsFreeGroup F] {n : ℕ}

/-- Internal bounded-search specification: relative to a chosen free basis, the simultaneous
conjugacy predicate on tuples is detected by searching candidate conjugators up to the standard
length bound built from the tuple entries. -/
private theorem exists_common_conjugator_iff_search_true (basis : FreeGroupBasis ι F)
    (u v : Fin n → F) :
    (∃ w : F, ∀ i, w⁻¹ * u i * w = v i) ↔
      commonConjugatorSearch basis u v = true := by
  sorry

end Search

section

variable {F : Type u} [Group F] {n : ℕ}

/-- The diagonal conjugation action on `Fin n → F` recovers the textbook common-conjugator
predicate. -/
-- Layer: `bridge/view`.
-- `core/canonical`: `orbitRel (ConjAct F) (Fin n → F)`.
theorem exists_common_conjugator_iff_orbitRel (u v : Fin n → F) :
    orbitRel (ConjAct F) (Fin n → F) v u ↔
      ∃ w : F, ∀ i, w⁻¹ * u i * w = v i := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨ConjAct.ofConjAct g⁻¹, ?_⟩
    intro i
    simp [Pi.smul_apply, ConjAct.smul_def, mul_assoc]
  · rintro ⟨w, hw⟩
    refine ⟨ConjAct.toConjAct w⁻¹, ?_⟩
    ext i
    simpa [Pi.smul_apply, ConjAct.smul_def, mul_assoc] using hw i

private theorem orbitRel_iff_search_true {ι : Type*} [DecidableEq ι] [IsFreeGroup F]
    (basis : FreeGroupBasis ι F) (u v : Fin n → F) :
    orbitRel (ConjAct F) (Fin n → F) v u ↔ commonConjugatorSearch basis u v = true :=
  (exists_common_conjugator_iff_orbitRel u v).trans
    (exists_common_conjugator_iff_search_true basis u v)

/-- The canonical diagonal conjugation-action orbit relation on `Fin n → F` is decidable in a free
group.

This is the owner-side bounded-search decision procedure behind Proposition `1-2-26`. The
companion bridge theorem `exists_common_conjugator_iff_orbitRel` recovers the textbook
common-conjugator predicate from this canonical `orbitRel` formulation. -/
-- Layer: `core/canonical`.
noncomputable instance decidableRel_commonConjugatorOrbitRel [IsFreeGroup F] :
    DecidableRel (orbitRel (ConjAct F) (Fin n → F)) := by
  let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  intro v u
  exact
    decidable_of_iff
      (commonConjugatorSearch basis u v = true)
      (orbitRel_iff_search_true basis u v).symm

/-- Proposition 1-2-26: it is decidable whether two `n`-tuples admit a common conjugator.

The public statement keeps the source-facing free-group decision problem. Its canonical owner is
still the diagonal conjugation-action orbit relation on `Fin n → F`, exposed by the companion
bridge theorem `exists_common_conjugator_iff_orbitRel`. The bounded-search construction is exposed
owner-side through `decidableRel_commonConjugatorOrbitRel`, and this source-facing declaration is
the corresponding bridge back to the textbook existential predicate. -/
-- Layer: `source-facing`.
-- `core/canonical`: `orbitRel (ConjAct F) (Fin n → F)`.
noncomputable def exists_common_conjugator_decidable [IsFreeGroup F] (u v : Fin n → F) :
    Decidable (∃ w : F, ∀ i, w⁻¹ * u i * w = v i) :=
  decidable_of_iff
    (orbitRel (ConjAct F) (Fin n → F) v u)
    (exists_common_conjugator_iff_orbitRel u v)

end
