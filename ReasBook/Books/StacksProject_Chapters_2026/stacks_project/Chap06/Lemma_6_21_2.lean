module

public import Mathlib.Topology.Sheaves.Functors

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory TopCat

/- Domain-style sampling for Lemma 6.21.2:
- primary domain: pushforward of presheaves and sheaves of sets along continuous maps;
- inspected owner declarations:
  `TopCat.Presheaf.pushforward`,
  `TopCat.Presheaf.Pushforward.comp_eq`,
  `TopCat.Presheaf.Pushforward.comp`,
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforward_forget`;
- owner abstraction: for both presheaves and sheaves, the owner is the pushforward functor itself,
  `TopCat.Presheaf.pushforward` and `TopCat.Sheaf.pushforward`; the objectwise presheaf theorems
  `TopCat.Presheaf.Pushforward.comp_eq` and `TopCat.Presheaf.Pushforward.comp` are derived API;
- primitive data: continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the objectwise presheaf comparison isomorphism/equality; the functor-level
  comparison below is just the raw canonical equality expression and needs no local theorem wrapper.

Source/core/bridge triage:
- `source-facing`: Lemma 6.21.2 records how direct image behaves under composition;
- `core/canonical`: `TopCat.Presheaf.pushforward` and `TopCat.Sheaf.pushforward`;
- `bridge/view`: the objectwise presheaf API `TopCat.Presheaf.Pushforward.comp_eq` /
  `TopCat.Presheaf.Pushforward.comp`, which remains available as companion data beneath the
  source-facing functor equalities below.

Since both parts are definitional equalities of pushforward functors, the source-facing public
surface should state those equalities directly. The presheaf objectwise theorem
`TopCat.Presheaf.Pushforward.comp_eq` remains only companion API, and this file records the
functor-level statements by direct canonical checks instead of parallel theorem names. -/

namespace TopCat.Presheaf

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 6.21.2 (1): for continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`, the direct image of a
presheaf of sets along `g ∘ f` is definitionally the iterated direct image functor `g_* ∘ f_*`.
Objectwise this specializes to `TopCat.Presheaf.Pushforward.comp_eq`. -/
#check (rfl :
  TopCat.Presheaf.pushforward (Type u) (f ≫ g) =
    TopCat.Presheaf.pushforward (Type u) f ⋙ TopCat.Presheaf.pushforward (Type u) g)

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 6.21.2 (2): for continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`, the pushforward on sheaves
of sets along `g ∘ f` is definitionally the composite `g_* ∘ f_*`. -/
#check (rfl :
  TopCat.Sheaf.pushforward (Type u) (f ≫ g) =
    TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g)

end TopCat.Sheaf
