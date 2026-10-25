module

public import Mathlib.Topology.Sheaves.Functors

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory TopCat
open TopCat.Sheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒢 : Y.Sheaf (Type v)) (ℱ : X.Sheaf (Type v))

/- Domain-style sampling for Definition 6.21.7:
- primary domain: pushforward of sheaves of sets along a continuous map, together with the
  pullback-pushforward adjunction on `TopCat.Sheaf`;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforward_sheaf_of_sheaf`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Presheaf.pushforward`;
- owner abstraction: the canonical owner for the direct-image sheaf is `TopCat.Sheaf.pushforward`,
  and the Stacks notion of an `f`-map is the resulting hom type into `f_* ℱ`;
- primitive data: only the continuous map `f` and the two sheaves `𝒢` and `ℱ`;
- derived API: the adjunction bijection and the explicit two-open-set description treated in the
  following lemma.

Source/core/bridge triage:
- `source-facing`: the textbook notion of an `f`-map from `𝒢` to `ℱ`;
- `core/canonical`: the owner functor `TopCat.Sheaf.pushforward`;
- `bridge/view`: the Hom-set adjunction
  `TopCat.Sheaf.pullbackPushforwardAdjunction`, and the compatible-family description in
  `Lemma_6_21_8`.

Since the source item is only naming the canonical morphism type into the direct image, this file
should remain a direct `#check` of that type expression rather than introducing a duplicate local
alias or wrapper. -/

/- Definition 6.21.7: for a continuous map `f : X ⟶ Y`, an `f`-map from a sheaf of sets `𝒢` on
`Y` to a sheaf of sets `ℱ` on `X` is exactly a morphism `𝒢 ⟶ f_* ℱ` of sheaves on `Y`. The
canonical mathlib expression for this notion is the following hom type. -/
#check (𝒢 ⟶ (pushforward (Type v) f).obj ℱ)
