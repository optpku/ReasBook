/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Monoid

namespace Monoid.PushoutI

/- Layer triage:
- `source-facing`: the Section `11` syllable length on an amalgamated-product element and the
  associated subset `U` of conjugates of elements of syllable length at most `1`.
- `core/canonical`: `Monoid.PushoutI.NormalWord` together with its syllable list and product map,
  and mathlib's conjugacy relation `IsConj`.
- `bridge/view`: a chosen `NormalWord.Transversal φ`, which turns an element of the pushout into a
  concrete normal word via `NormalWord.equiv`.

Domain sampling:
1. `Monoid.PushoutI` is mathlib's owner abstraction for an indexed amalgamated product.
2. `Monoid.PushoutI.NormalWord.Transversal` is the canonical data used to realize normal forms.
3. `Monoid.PushoutI.NormalWord.equiv` gives the normal form attached to a chosen transversal.
4. `Monoid.PushoutI.base` is the canonical embedding of the amalgamated subgroup, so the
   source clause "`u ∈ A`" is represented by membership in `(base φ).range`.
5. `IsConj` is mathlib's canonical owner relation for conjugacy, so the source subset `U` should
   be phrased directly using it instead of a local witness wrapper.

Primitive vs. derived:
the primitive source data are the pushout diagram `φ`, a chosen transversal `d`, and the canonical
normal word `NormalWord d`; the book's length is the derived list length on that owner, while the
length of an element `u : PushoutI φ` is obtained by transporting `u` through `NormalWord.equiv`.
The subset `U` is then derived canonically from that length together with `IsConj`.
-/

section

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

/-- The owner syllable length of a chosen normal word: the number of non-base syllables in its
syllable list. -/
abbrev NormalWord.syllableLength {d : NormalWord.Transversal φ} (w : NormalWord d) : ℕ :=
  w.toList.length

namespace NormalWord

theorem prod_mem_base_range_of_syllableLength_eq_zero {d : Transversal φ} {w : NormalWord d}
    (hw : syllableLength w = 0) :
    w.prod ∈ (base φ).range := by
  cases hlist : w.toList with
  | nil =>
      refine ⟨w.head, ?_⟩
      simp [prod, CoprodI.Word.prod, hlist]
  | cons g l =>
      simp [syllableLength, hlist] at hw

/-- A chosen normal word has syllable length zero exactly when it is represented only by its
base-group head. -/
theorem syllableLength_eq_zero_iff_prod_mem_base_range {d : Transversal φ} (w : NormalWord d) :
    syllableLength w = 0 ↔ w.prod ∈ (base φ).range := by
  constructor
  · exact prod_mem_base_range_of_syllableLength_eq_zero
  · rintro ⟨h, hh⟩
    have hw : w = h • (empty : NormalWord d) := by
      apply prod_injective
      simp [hh]
    rw [hw]
    simp [syllableLength, base_smul_def', empty]

end NormalWord

/-- Definition 1-11-2: for a chosen transversal in an amalgamated product, the length of an
element is the number of non-base syllables in its normal form; equivalently, elements of the
amalgamated subgroup have length `0`. -/
noncomputable abbrev syllableLength (d : NormalWord.Transversal φ) (u : PushoutI φ) : ℕ :=
  let _ : DecidableEq ι := Classical.decEq ι
  let _ : ∀ i, DecidableEq (G i) := fun i ↦ Classical.decEq (G i)
  let w : NormalWord d := NormalWord.equiv u
  w.syllableLength

/-- The syllable length is zero exactly on the amalgamated subgroup. -/
-- Proof sketch: the forward direction says that an empty normal-form list leaves only the head
-- term from the base group, so the element lies in `(base φ).range`. Conversely, any element of
-- the base subgroup is represented by the normal word with empty syllable list.
theorem syllableLength_eq_zero_iff_mem_base_range
    (d : NormalWord.Transversal φ) (u : PushoutI φ) :
    syllableLength d u = 0 ↔ u ∈ (base φ).range := by
  let _ : DecidableEq ι := Classical.decEq ι
  let _ : ∀ i, DecidableEq (G i) := fun i ↦ Classical.decEq (G i)
  let w : NormalWord d := NormalWord.equiv u
  have hwprod : w.prod = u := by
    change NormalWord.equiv.symm (NormalWord.equiv u) = u
    exact Equiv.symm_apply_apply NormalWord.equiv u
  simpa [syllableLength, w, hwprod] using
    NormalWord.syllableLength_eq_zero_iff_prod_mem_base_range w

/-- The source-facing subset `U` from Section `11`: the conjugates of elements whose syllable
length in the amalgamated product is at most `1`. -/
def shortSyllableConjugates (d : NormalWord.Transversal φ) : Set (PushoutI φ) :=
  {u | ∃ h : PushoutI φ, syllableLength d h ≤ 1 ∧ IsConj u h}

/-- A source-side conjugacy witness with syllable length at most `1` is exactly the primitive data
needed to place an element in the owner subset `shortSyllableConjugates d`. -/
theorem mem_shortSyllableConjugates_of_eq_conjugate_of_syllableLength_le_one
    (d : NormalWord.Transversal φ) {u h p : PushoutI φ} (hu : u = p⁻¹ * h * p)
    (hh : syllableLength d h ≤ 1) :
    u ∈ shortSyllableConjugates d := by
  refine ⟨h, hh, ?_⟩
  rw [isConj_iff]
  refine ⟨p, ?_⟩
  simp [hu, mul_assoc]

end

end Monoid.PushoutI
