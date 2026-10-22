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

-- Layer triage:
-- `source-facing`: the Section `11` element `g`, the distinguished subset `W`, the upstream
-- subset `U = shortSyllableConjugates d`, the auxiliary subset `U*`, and the length comparison
-- for `v`, `v * g`, and `v * g * v`.
-- `core/canonical`: the amalgamated-product owner `Monoid.PushoutI φ`, the chosen normal-form
-- data `NormalWord.Transversal φ`, the derived owner length `syllableLength d`, and the canonical
-- set operators `Set.preimage` and `Disjoint`.
-- `bridge/view`: `U*` is the source-facing auxiliary subset derived from the canonical owner
-- subset `shortSyllableConjugates d` by recording the concrete Section `11` situation in which a
-- cyclic shift `v⁻¹ * u * v` is produced from some `u ∈ U` with a shorter right factor `v`.
--
-- Domain sampling:
-- 1. `Monoid.PushoutI` is the chapter/mathlib owner abstraction for the amalgamated product.
-- 2. `Monoid.PushoutI.NormalWord.Transversal` is the canonical chosen normal-form data.
-- 3. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner declaration
--    for the Section `11` length.
-- 4. `Monoid.PushoutI.shortSyllableConjugates` from Lemma `1-11-14` is the upstream owner for
--    the source subset `U`, so the auxiliary subset `U*` should be derived from it rather than
--    introduced as an abstract set parameter.
--
-- Primitive vs. derived:
-- the primitive public data are the pushout diagram `φ`, the chosen transversal `d`, the Section
-- `11` subset `W`, the middle element `g`, and the source hypotheses that for `v ∈ W` the word
-- `v * g` lies in `U` and is longer than `v`. The auxiliary subset `U*` is derived API from the
-- canonical owner subset `shortSyllableConjugates d`, so it should not remain primitive data in
-- the main theorem statement.

/-- The source-facing auxiliary subset `U*` from Section `11`: the cyclic shifts `v⁻¹ * u * v`
of elements `u ∈ U = shortSyllableConjugates d` by a strictly shorter right factor `v` whose
product `u * v` is still strictly shorter than `u`. -/
noncomputable def shortSyllableConjugatesStar (d : NormalWord.Transversal φ) :
    Set (PushoutI φ) :=
  {w | ∃ u v : PushoutI φ,
      u ∈ shortSyllableConjugates d ∧
        syllableLength d v < syllableLength d u ∧
        syllableLength d (u * v) < syllableLength d u ∧
        w = v⁻¹ * u * v}

/-- If `u ∈ U`, if `v` is strictly shorter than `u`, and if `u * v` is no longer than `v`, then
the cyclic shift `v⁻¹ * u * v` belongs to the auxiliary subset `U*`. -/
theorem conj_mem_shortSyllableConjugatesStar_of_mem_shortSyllableConjugates_of_lt_of_mul_le
    (d : NormalWord.Transversal φ) {u v : PushoutI φ}
    (hu : u ∈ shortSyllableConjugates d)
    (hv : syllableLength d v < syllableLength d u)
    (huv : syllableLength d (u * v) ≤ syllableLength d v) :
    v⁻¹ * u * v ∈ shortSyllableConjugatesStar d := by
  exact ⟨u, v, hu, hv, lt_of_le_of_lt huv hv, rfl⟩

/-- Lemma 1-11-16: in the Section `11` setup, if every `v ∈ W` satisfies `v * g ∈ U` and
`syllableLength d v < syllableLength d (v * g)`, and if `W` is disjoint from the left-translate
preimage of the auxiliary subset `U*`, then every `v ∈ W` satisfies
`syllableLength d v < syllableLength d (v * g * v)`. -/
-- Proof sketch: argue by contradiction from
-- `syllableLength d (v * g * v) ≤ syllableLength d v`. For `u := v * g`, the hypotheses
-- `u ∈ U` and `syllableLength d v < syllableLength d u` place the cyclic shift
-- `v⁻¹ * u * v = g * v` in `U*`. Thus `v` lies in the preimage of `U*` under left multiplication
-- by `g`, contradicting the disjointness of `W` from that preimage.
theorem length_lt_middle_product_of_mem_W
    (d : NormalWord.Transversal φ) (g : PushoutI φ) (W : Set (PushoutI φ))
    (hmemU :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → v * g ∈ shortSyllableConjugates d)
    (hshort :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → syllableLength d v < syllableLength d (v * g))
    (hW :
      Disjoint W ((fun v : PushoutI φ ↦ g * v) ⁻¹' shortSyllableConjugatesStar d))
    {v : PushoutI φ} (hv : v ∈ W) :
    syllableLength d v < syllableLength d (v * g * v) := by
  by_contra hlt
  have hgvUStar : g * v ∈ shortSyllableConjugatesStar d := by
    simpa [mul_assoc] using
      conj_mem_shortSyllableConjugatesStar_of_mem_shortSyllableConjugates_of_lt_of_mul_le
        d (hmemU hv) (hshort hv) (Nat.le_of_not_gt hlt)
  exact (Set.disjoint_left.mp hW hv) (by simpa using hgvUStar)

end

end Monoid.PushoutI
