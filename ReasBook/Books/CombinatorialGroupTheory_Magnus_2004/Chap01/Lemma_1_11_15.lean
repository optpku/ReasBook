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

-- Layer triage:
-- `source-facing`: the Section `11` subset `U`, realized here by `shortSyllableConjugates d`,
-- and the syllable-length inequalities on `u`, `v`, `u * v`, and the conjugate `v⁻¹ * u * v`.
-- `core/canonical`: the amalgamated product owner `Monoid.PushoutI φ`, its group structure, and
-- the canonical normal-form owner `NormalWord`.
-- `bridge/view`: the chosen transversal `d`, which supplies the actual normal-form representative
-- and hence the derived chapter length `syllableLength d`.
--
-- Domain sampling:
-- 1. `Monoid.PushoutI` is the mathlib/project owner abstraction for the amalgamated product.
-- 2. `Monoid.PushoutI.NormalWord.Transversal` is the canonical chapter owner for the chosen
--    normal-form data.
-- 3. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the owner length API attached
--    to that transversal.
-- 4. `Monoid.PushoutI.shortSyllableConjugates` from Lemma `1-11-14` is the upstream source-facing
--    subset `U`, so this file should reuse it directly rather than restating the subset locally.
--
-- Primitive vs. derived:
-- the primitive data remain the pushout diagram `φ` and the chosen transversal `d`; the subset
-- `shortSyllableConjugates d` and the length comparisons are derived API on that owner
-- abstraction, so this lemma stays theorem-level and does not introduce any new wrapper data.

-- Proof sketch: write `u = p⁻¹ * h * p` with `syllableLength h ≤ 1`, so `u` is a source-side
-- element of `U`. The hypothesis `syllableLength v < syllableLength u` forces the terminal
-- overlap of the normal form of `v` to lie strictly inside the conjugating word `p`. The further
-- inequality `syllableLength (u * v) < syllableLength u` implies that one additional syllable
-- cancels in `p * v`, producing a shorter conjugating word `p'` with
-- `v⁻¹ * u * v = p'⁻¹ * h * p'`. Hence the conjugate has strictly smaller syllable length.
/-- Lemma 1-11-15: if `u` belongs to the section-11 subset `U` and both `v` and `u * v` are
strictly shorter than `u`, then the conjugate `v⁻¹ * u * v` is strictly shorter than `u`. -/
theorem syllableLength_conj_lt_of_mem_shortSyllableConjugates_of_lt_of_mul_lt
    (d : Transversal φ) {u v : PushoutI φ}
    (hu : u ∈ shortSyllableConjugates d)
    (hv : syllableLength d v < syllableLength d u)
    (huv : syllableLength d (u * v) < syllableLength d u) :
    syllableLength d (v⁻¹ * u * v) < syllableLength d u := sorry

end

end Monoid.PushoutI
