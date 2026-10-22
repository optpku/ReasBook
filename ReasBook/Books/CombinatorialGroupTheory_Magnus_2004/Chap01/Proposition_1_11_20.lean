/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Lemma_1_11_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Proposition 1-11-20 lies in Section `11`, where a distinguished subset `W` has the property
that every nonempty noncancelling word in letters from `W` has nontrivial product.

Layer triage:
- `source-facing`: the Section `11` distinguished subset `W` inside an amalgamated product
  `PushoutI φ`, together with the theorem that every nonempty noncancelling word in letters from
  `W` has nontrivial product.
- `core/canonical`: `Monoid.PushoutI` for the ambient amalgamated product, the owner length
  `syllableLength d`, the upstream Section `11` subsets `shortSyllableConjugates d` and
  `shortSyllableConjugatesStar d`, and the reusable subset property
  `Set.HasNontrivialNoncancellingProducts`.
- `bridge/view`: the `Set`-level owner property remains as the reusable packaging consumed
  downstream by Corollary `1-11-21`, while the main theorem below restores the missing
  Section-`11` theorem over the actual amalgamated-product setup.

Domain sampling:
1. `Monoid.PushoutI.syllableLength` from Definition `1-11-2` is the chapter owner for the
   Section `11` length.
2. `Monoid.PushoutI.shortSyllableConjugates` from Definition `1-11-2` is the upstream owner for
   the subset `U`.
3. `Monoid.PushoutI.shortSyllableConjugatesStar` from Lemma `1-11-16` is the upstream owner for
   the auxiliary subset `U*`.
4. `Set.HasNontrivialNoncancellingProducts`, kept below as a companion owner predicate, is the
   right reusable downstream abstraction once the source-facing Section `11` theorem is present.
5. `List.IsChain` and `List.prod` are mathlib's canonical APIs for the noncancelling word and its
   total product.

Primitive vs. derived:
the primitive public data for the source-facing theorem are the amalgamated-product diagram `φ`,
the chosen transversal `d`, the distinguished subset `W`, and the concrete Section `11`
hypotheses on `W`. The quantified list statement is the main proposition-level conclusion, while
the `Set`-level owner predicate is its derived reusable packaging for downstream files.
-/

section

variable {G : Type u} [Group G]

namespace Set

/-- Proposition 1-11-20, owner form: a distinguished subset `W` has nontrivial noncancelling
products when every nonempty finite word in letters from `W` with no adjacent cancellation has
nonidentity total product. -/
class HasNontrivialNoncancellingProducts (W : Set G) : Prop where
  prod_ne_one {us : List G} (hus : us ≠ []) (hW : ∀ u ∈ us, u ∈ W)
      (hchain : us.IsChain (fun u v ↦ u * v ≠ 1)) :
      us.prod ≠ (1 : G)

end Set

end

namespace Monoid.PushoutI

section

variable {ι : Type u} {H : Type v} {G : ι → Type w}
variable [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i}

/-- Proposition 1-11-20: in the Section `11` amalgamated-product setup, every nonempty
noncancelling word in letters from the distinguished subset `W` has nontrivial product. -/
-- Proof sketch: argue by induction on the length of the word. The one-letter case uses the
-- source hypothesis that elements of `W` are nontrivial. For longer words, the preceding
-- Section `11` length estimates force the syllable length of the total product to dominate the
-- relevant endpoint syllables, so the total product cannot lie in the amalgamated subgroup and in
-- particular cannot be `1`.
theorem prod_ne_one_of_ne_nil_of_forall_mem_of_IsChain
    (d : NormalWord.Transversal φ) (g : PushoutI φ) (W : Set (PushoutI φ))
    (hmemU :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → v * g ∈ shortSyllableConjugates d)
    (hshort :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → syllableLength d v < syllableLength d (v * g))
    (hdisjoint :
      Disjoint W ((fun v : PushoutI φ ↦ g * v) ⁻¹' shortSyllableConjugatesStar d))
    (hne :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → v ≠ 1)
    {us : List (PushoutI φ)} (hus : us ≠ [])
    (hW : ∀ u ∈ us, u ∈ W)
    (hchain : us.IsChain (fun u v ↦ u * v ≠ 1)) :
    us.prod ≠ (1 : PushoutI φ) := by
  sorry

/-- Companion owner-form packaging of Proposition `1-11-20` for downstream reuse. -/
theorem hasNontrivialNoncancellingProducts
    (d : NormalWord.Transversal φ) (g : PushoutI φ) (W : Set (PushoutI φ))
    (hmemU :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → v * g ∈ shortSyllableConjugates d)
    (hshort :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → syllableLength d v < syllableLength d (v * g))
    (hdisjoint :
      Disjoint W ((fun v : PushoutI φ ↦ g * v) ⁻¹' shortSyllableConjugatesStar d))
    (hne :
      ∀ ⦃v : PushoutI φ⦄, v ∈ W → v ≠ 1) :
    Set.HasNontrivialNoncancellingProducts W := by
  refine ⟨?_⟩
  intro us hus hWus hchain
  exact prod_ne_one_of_ne_nil_of_forall_mem_of_IsChain
    d g W hmemU hshort hdisjoint hne hus hWus hchain

end

end Monoid.PushoutI
