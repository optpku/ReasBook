module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w

namespace CategoryTheory

open GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.32.5:
- primary domain: points of Grothendieck sites, their fiber functors, and the associated
  skyscraper sheaf construction;
- sampled owner API:
  `GrothendieckTopology.Point.skyscraperPresheaf`,
  `GrothendieckTopology.Point.isSheaf_skyscraperPresheaf`,
  `GrothendieckTopology.Point.skyscraperSheafAdjunction`,
  `GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`;
- primitive data: only the point `Φ : Point.{w} J`;
- derived API: the sheaf condition for `Φ.skyscraperPresheaf E`, the adjunction
  `Φ.sheafFiber ⊣ Φ.skyscraperSheafFunctor`, and the sheafification/fiber comparison isomorphism.

Source/core/bridge triage:
- `source-facing`: the three clauses of Stacks Lemma 7.32.5;
- `core/canonical`: the owner namespace `GrothendieckTopology.Point`;
- `bridge/view`: the set-valued specialization `A := Type w`.

The source statements already coincide with canonical owner-level declarations in mathlib, so this
file should remain a direct recall of those declarations rather than introducing any parallel local
wrapper API.
-/

variable (Φ : Point.{w} J) (E : Type w)

/- Lemma 7.32.5 (1): for a point `p` of the site `(C, J)` and a set `E`, the canonical
skyscraper presheaf `p^p E`, given by `X ↦ (p.fiber.obj X → E)`, is a sheaf. In mathlib this is
the canonical point API `Φ.isSheaf_skyscraperPresheaf E`. -/
#check
  (Φ.isSheaf_skyscraperPresheaf E :
    Presheaf.IsSheaf J (Φ.skyscraperPresheaf E))

/- Lemma 7.32.5 (2): the stalk functor on sheaves attached to a point is left adjoint to the
canonical skyscraper-sheaf functor; this is `Φ.skyscraperSheafAdjunction`. -/
#check
  (Φ.skyscraperSheafAdjunction :
    (Φ.sheafFiber : Sheaf J (Type w) ⥤ Type w) ⊣ Φ.skyscraperSheafFunctor)

variable [HasWeakSheafify J (Type w)]

/- Lemma 7.32.5 (3): the point fiber functor on presheaves identifies canonically with the point
fiber functor on associated sheaves; this is `Φ.presheafToSheafCompSheafFiberIso`. -/
#check
  (Φ.presheafToSheafCompSheafFiberIso (Type w) :
    presheafToSheaf J (Type w) ⋙ (Φ.sheafFiber : Sheaf J (Type w) ⥤ Type w) ≅
      Φ.presheafFiber)

end CategoryTheory
