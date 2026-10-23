module

public import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Definition 7.3.5:
- primary domain: images of morphisms of set-valued presheaves
- sampled owner declarations:
  `CategoryTheory.Subfunctor.range`,
  `CategoryTheory.Subfunctor.toRange`,
  `CategoryTheory.Subfunctor.toRange_ι`,
  `CategoryTheory.Subfunctor.range_eq_top`
- best owner abstraction: the image subpresheaf is owned canonically by
  `CategoryTheory.Subfunctor.range`
- primitive data: the morphism `φ : ℱ ⟶ 𝒢`
- derived API: the factorization `Subfunctor.toRange φ`, the inclusion `(Subfunctor.range φ).ι`,
  and their companion lemmas already come from the owner abstraction and should not be repackaged
  locally

Source/core/bridge triage:
- `source-facing`: the image subpresheaf of a morphism of presheaves of sets
- `core/canonical`: `CategoryTheory.Subfunctor.range`
- `bridge/view`: none; the factorization through the image is already derived API of the canonical
  owner

This numbered item is only a recall of the canonical owner, so the refined file should keep the
direct recall and no parallel local alias or wrapper.
-/
/- Definition 7.3.5: notation as in Lemma 7.3.4, the image of a morphism `φ` of presheaves of
sets is the canonical subpresheaf `Subfunctor.range φ`. -/
recall CategoryTheory.Subfunctor.range
