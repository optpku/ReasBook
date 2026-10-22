/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_24
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MulAction

noncomputable section

section

variable {X : Type u}

local instance proposition_2_5_11_decidableEq : DecidableEq X := Classical.decEq X

-- Layer triage:
-- `source-facing`: two relators in a free group that are automorphism-equivalent and each have
-- minimal reduced-word length under the `Aut(F(X))`-action.
-- `core/canonical`: `FreeGroup X`, the reduced-word normal form `FreeGroup.toWord`, the support
-- view `reducedWordSupport`, the automorphism group `MulAut (FreeGroup X)`, and
-- `orbitRel (MulAut (FreeGroup X)) (FreeGroup X)`.
-- `bridge/view`: Proposition `1-5-6` gives the one-sided support monotonicity result for a
-- minimal-length word and one automorphic image; this item upgrades it to equality for two
-- minimal representatives in the same orbit.
--
-- Domain sampling:
-- 1. `FreeGroup.toWord` is the owner reduced-word API for `FreeGroup X`.
-- 2. `reducedWordSupport` from Proposition `1-5-6` is the chapter owner notion of the generators
--    that actually occur in a free-group element.
-- 3. `MulAut (FreeGroup X)` and `orbitRel` are the canonical automorphism-action owners.
-- 4. `automorphism_orbitRel_iff_exists_automorphism_eq` is the chapter bridge from `orbitRel` to
--    an explicit automorphism witness.
-- Primitive vs. derived:
-- the primitive inputs are the two relators and their orbit/minimality hypotheses; the number of
-- generators occurring in each relator is derived canonically as the cardinality of
-- `reducedWordSupport`.

/-- Proposition 2-5-11: if `r₁` and `r₂` lie in the same automorphism orbit of the free group and
each has minimal reduced-word length under `Aut(F(X))`, then the same number of generators occur
in their canonical reduced words. -/
-- Proof sketch: extract an automorphism sending `r₁` to `r₂` from `hequiv`. Apply
-- `reducedWord_support_card_le_automorphic_image_support_card_of_minimal_length` to `r₁` and that
-- automorphism to get one inequality, then apply the same theorem to `r₂` and the inverse
-- automorphism to get the reverse inequality.
theorem reducedWord_support_card_eq_of_orbitRel_of_minimal_length
    (r₁ r₂ : FreeGroup X)
    (hmin₁ : ∀ α : MulAut (FreeGroup X), r₁.toWord.length ≤ (α r₁).toWord.length)
    (hmin₂ : ∀ α : MulAut (FreeGroup X), r₂.toWord.length ≤ (α r₂).toWord.length)
    (hequiv : orbitRel (MulAut (FreeGroup X)) (FreeGroup X) r₂ r₁) :
    (reducedWordSupport r₁).card = (reducedWordSupport r₂).card := by
  obtain ⟨α, hα⟩ :=
    (automorphism_orbitRel_iff_exists_automorphism_eq r₁ r₂).1 hequiv
  have hα_inv : α⁻¹ r₂ = r₁ := by
    rw [← hα]
    simp
  refine le_antisymm ?_ ?_
  · simpa [hα] using
      reducedWord_support_card_le_automorphic_image_support_card_of_minimal_length r₁ hmin₁ α
  · simpa [hα_inv] using
      reducedWord_support_card_le_automorphic_image_support_card_of_minimal_length r₂ hmin₂ α⁻¹

end
