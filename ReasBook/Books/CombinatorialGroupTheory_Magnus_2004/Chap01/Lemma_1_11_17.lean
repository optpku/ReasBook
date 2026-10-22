/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_11_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Monoid.PushoutI

section

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

open NormalWord

-- Layer triage:
-- `source-facing`: the Section `11` element `g`, the distinguished subset `W`, the textbook
-- middle product `v * g * v`, and the cyclic shift `g * v = v⁻¹ * (v * g) * v`.
-- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form
-- data `NormalWord.Transversal φ`, the owner length `syllableLength d`, and the auxiliary subset
-- `shortSyllableConjugatesStar d` from Lemma `1-11-16`.
-- `bridge/view`: this item is the one-step case split used by Lemma `1-11-16`, before imposing
-- the disjointness hypothesis that rules out the `U*` alternative.
--
-- Domain sampling:
-- 1. `Monoid.PushoutI` is the chapter owner abstraction for the amalgamated product.
-- 2. `Monoid.PushoutI.NormalWord.Transversal` is the canonical chosen normal-form data.
-- 3. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the Section `11` length.
-- 4. `Monoid.PushoutI.shortSyllableConjugatesStar` and
--    `Monoid.PushoutI.conj_mem_shortSyllableConjugatesStar_of_mem_shortSyllableConjugates_of_lt_of_mul_le`
--    from Lemma `1-11-16` are the upstream owner declarations for the source auxiliary subset
--    `U*` and the criterion placing a cyclic shift in it.
--
-- Primitive vs. derived:
-- the primitive public data are the pushout diagram `φ`, the chosen transversal `d`, the fixed
-- element `g`, and the distinguished subset `W`. The hypotheses that `v * g ∈ U` and
-- `syllableLength d v < syllableLength d (v * g)` for `v ∈ W` are the substantive Section `11`
-- assumptions for this bridge theorem. The auxiliary subset `U*` is already owned by
-- `shortSyllableConjugatesStar d`, so it should not remain a second abstract set parameter here.

/-- Lemma 1-11-17: in the Section `11` setup, if every `v ∈ W` satisfies `v * g ∈ U` and
`syllableLength d v < syllableLength d (v * g)`, then for each `v ∈ W` either
`syllableLength d v < syllableLength d (v * g * v)` or the cyclic shift
`g * v = v⁻¹ * (v * g) * v` belongs to the auxiliary subset `U*`. -/
-- Proof sketch: if `syllableLength d v < syllableLength d (v * g * v)` already holds, we are in
-- the first case. Otherwise
-- `syllableLength d (v * g * v) ≤ syllableLength d v`, so with `u := v * g` the hypotheses
-- `u ∈ U` and `syllableLength d v < syllableLength d u` allow Lemma `1-11-16`'s owner-side
-- criterion to place the cyclic shift `v⁻¹ * u * v = g * v` in `shortSyllableConjugatesStar d`.
theorem syllableLength_lt_middle_product_or_mul_mem_shortSyllableConjugatesStar_of_mem_W
    (d : Transversal φ) (g : PushoutI φ) (W : Set (PushoutI φ))
    (hmemU :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → v * g ∈ shortSyllableConjugates d)
    (hshort :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → syllableLength d v < syllableLength d (v * g))
    {v : PushoutI φ} (hv : v ∈ W) :
    syllableLength d v < syllableLength d (v * g * v) ∨
      g * v ∈ shortSyllableConjugatesStar d := by
  by_cases hlt : syllableLength d v < syllableLength d (v * g * v)
  · exact Or.inl hlt
  · right
    simpa [mul_assoc] using
      conj_mem_shortSyllableConjugatesStar_of_mem_shortSyllableConjugates_of_lt_of_mul_le
        d (hmemU hv) (hshort hv) (Nat.le_of_not_gt hlt)

end

end Monoid.PushoutI
