/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_11_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Monoid.PushoutI

section

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

open NormalWord

/- Layer triage:
- `source-facing`: the textbook witness `u = p⁻¹ * h * p` with `syllableLength d h = 1`, together
  with the shortening hypothesis for conjugation by a base element.
- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form
  data `NormalWord.Transversal φ`, the derived owner length `syllableLength d`, the amalgamated
  subgroup `(base φ).range`, and the owner subset `shortSyllableConjugates d`.
- `bridge/view`: the source statement names a specific length-one conjugacy witness, while the
  chapter's owner abstraction packages such elements as membership in `shortSyllableConjugates d`.

Domain sampling:
1. `Monoid.PushoutI` is the owner abstraction for the amalgamated product.
2. `Monoid.PushoutI.NormalWord.Transversal` is the canonical chosen normal-form data.
3. `Monoid.PushoutI.shortSyllableConjugates` from Lemma `1-11-14` is the owner subset for
   conjugates of elements of syllable length at most `1`.
4. `Monoid.PushoutI.syllableLength_eq_zero_iff_mem_base_range` from Definition `1-11-2` is the
   canonical translation between syllable length `0` and membership in the amalgamated subgroup.

Primitive vs. derived:
the primitive source data are still the explicit conjugacy witness `u = p⁻¹ * h * p` and the
length-one hypothesis on `h`. Membership in `shortSyllableConjugates d` for `u` and for its base
conjugate is derived owner-side API, so this file reuses that owner abstraction through thin
bridge lemmas instead of introducing a parallel wrapper.
-/

/-- Conjugating a length-one source witness by a base element stays inside the owner subset
`shortSyllableConjugates d`. -/
theorem baseConjugate_mem_shortSyllableConjugates_of_eq_conjugate_of_syllableLength_eq_one
    (d : Transversal φ) {u h p : PushoutI φ} (a : H)
    (hu : u = p⁻¹ * h * p) (hh : syllableLength d h = 1) :
    (base φ a)⁻¹ * u * base φ a ∈ shortSyllableConjugates d := by
  refine ⟨h, Nat.le_of_eq hh, toUnits (p * base φ a), ?_⟩
  dsimp [SemiconjBy]
  rw [hu]
  group

-- Proof sketch: the shorter base conjugate is still in `shortSyllableConjugates d` by the
-- preceding owner bridge. If the conjugating word `p` had positive syllable length, the textbook
-- normal-form calculation would keep `(base φ a)⁻¹ * u * base φ a` reduced with the same
-- syllable length as `u`. Hence strict shortening forces `p` to lie in the base subgroup, so `u`
-- itself already has syllable length `1`; the shorter base conjugate then has syllable length
-- `0`, and `syllableLength_eq_zero_iff_mem_base_range` turns that into membership in
-- `(base φ).range`.
/-- Lemma 1-11-10: if an amalgamated-product element `u` is a conjugate `p⁻¹ * h * p` of a
syllable-length-one element `h`, and conjugating `u` by a base element `a` strictly shortens its
syllable length, then `u` itself has syllable length `1` and that base conjugate lies in the
amalgamated subgroup. -/
theorem syllableLength_eq_one_and_mem_base_of_conj_eq_of_lengthOne_of_baseConjugate_shorter
    (d : Transversal φ) {u h p : PushoutI φ} (hu : u = p⁻¹ * h * p)
    (hh : syllableLength d h = 1) (a : H)
    (hshort : syllableLength d ((base φ a)⁻¹ * u * base φ a) < syllableLength d u) :
    syllableLength d u = 1 ∧ (base φ a)⁻¹ * u * base φ a ∈ (base φ).range := sorry

end

end Monoid.PushoutI
