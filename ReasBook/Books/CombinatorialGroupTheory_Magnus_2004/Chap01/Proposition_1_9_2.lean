/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_9_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

set_option autoImplicit false

open scoped AbstractLengthFunction

namespace Monoid.CoprodI

section

variable {ι : Type u} {factors : ι → Type v} [∀ i, Group (factors i)]

/-- The syllable length of an element of an indexed free product, computed from its canonical
reduced word. -/
noncomputable abbrev syllableLength (g : CoprodI factors) : ℕ :=
  let _ : DecidableEq ι := Classical.decEq ι
  let _ : ∀ i, DecidableEq (factors i) := fun i ↦ Classical.decEq (factors i)
  (Word.equiv g).toList.length

end

end Monoid.CoprodI

section

variable {G : Type u} [Group G]

/-- A natural-number-valued length on `G` satisfying the textbook axioms `A1` through `A5` from
Section `9`. This is the free-product specialization of the shared `A1`-through-`A4` owner
predicate from Proposition `1-9-1`, obtained by adjoining the free-product rigidity axiom
`A5`. -/
class IsFreeProductLengthFunction (length : G → ℕ) : Prop
    extends IsCoreAbstractLengthFunction length where
  /-- Axiom `A5`: if the forward and backward overlap terms sum to more than the common length,
  then the two elements coincide. -/
  overlap_rigidity :
    ∀ g h : G,
      c[length](g, h) + c[length](g⁻¹, h⁻¹) > length g →
        length g = length h →
          g = h

/-- Proposition 1-9-2: a group carrying a Section `9` length function satisfying axioms `A1`
through `A5` admits an injective homomorphism into a free product whose canonical syllable-length
restricts to the given length function. -/
-- Layer triage:
-- `source-facing`: a group `G` equipped with a natural-number-valued length function `length`
-- satisfying the Section 9 owner predicate `IsFreeProductLengthFunction length`.
-- `core/canonical`: `Monoid.CoprodI` and the reduced-word normal form `Word.equiv`.
-- `bridge/view`: an injective homomorphism from `G` into a chosen indexed free product whose
-- pullback of the owner syllable-length `Monoid.CoprodI.syllableLength` equals `length`.
-- Domain sampling:
-- 1. `Monoid.CoprodI` is mathlib's owner abstraction for indexed free products of groups.
-- 2. `Word.equiv` gives the canonical reduced-word representative of each element.
-- 3. `IsCoreAbstractLengthFunction length` from Proposition `1-9-1` is the chapter owner
--    predicate for the shared axioms `A1` through `A4`, so this file specializes that owner by
--    adding only the new source-facing axiom `A5` instead of duplicating the common data.
-- 4. `Monoid.CoprodI.syllableLength` is the owner derived API for the reduced word's list length,
--    so the theorem should expose that canonical declaration rather than repeating
--    `(Word.equiv g).toList.length` at the theorem surface.
-- 5. An embedding of groups is stated canonically as an injective `MonoidHom`.
-- Proof sketch: build the Lyndon-Chiswell tree associated to `length`, identify the induced
-- action of `G` with the Bass-Serre action of a suitable indexed free product of vertex
-- stabilizers, and use the normal form theorem for free products to obtain an injective
-- homomorphism whose reduced-word syllable-length pulls back to `length`.
theorem exists_freeProduct_embedding_preserving_length
    (length : G → ℕ) [IsFreeProductLengthFunction length] :
    ∃ (ι : Type v) (factors : ι → Type w),
      ∃ _ : ∀ i, Group (factors i),
        ∃ φ : G →* Monoid.CoprodI factors,
          Function.Injective φ ∧
            ∀ g : G, length g = Monoid.CoprodI.syllableLength (φ g) := sorry

end
