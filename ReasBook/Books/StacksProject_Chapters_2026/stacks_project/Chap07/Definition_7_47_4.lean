module

public import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Definition 7.47.4:
- primary domain: pullbacks of sieves along morphisms in a category;
- sampled owner API:
  `CategoryTheory.Sieve`,
  `CategoryTheory.Sieve.pullback`,
  `CategoryTheory.Sieve.pullback_apply`,
  `CategoryTheory.Sieve.pullback_comp`;
- source/core/bridge triage:
  `source-facing`: the inverse-image sieve on `V` induced by a sieve on `U` and a morphism
  `f : V ⟶ U`;
  `core/canonical`: the owner construction `Sieve.pullback`;
  `bridge/view`: the membership characterization `Sieve.pullback_apply`.

Primitive data are only the sieve `S` and the morphism `f`. The pulled-back sieve and its
pointwise membership criterion are already owned upstream by the canonical mathlib API, so this
file should recall that owner directly and introduce no parallel local definition.
-/

/- Definition 7.47.4: the pullback of a sieve `S` on `U` along a morphism `f : V ⟶ U` is the
canonical sieve `Sieve.pullback`; equivalently, it is the sieve on `V` whose arrows
`α : T ⟶ V` are exactly those for which the composite `α ≫ f : T ⟶ U` lies in `S`. -/
recall Sieve.pullback

/- Companion recall: membership in the pullback sieve is characterized by composition with the
pullback morphism, i.e. `(S.pullback f) α ↔ S (α ≫ f)`. -/
recall Sieve.pullback_apply
