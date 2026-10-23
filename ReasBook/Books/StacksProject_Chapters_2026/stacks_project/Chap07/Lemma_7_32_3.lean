module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

variable (Φ : GrothendieckTopology.Point.{v} J)

/- Source/core/bridge triage for Lemma 7.32.3:
- primary domain: point fibers of representable presheaves on a site;
- sampled owner API:
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.fiber`,
  `GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberIso`,
  `shrinkYonedaIsoYoneda`;
- source-facing statement: `yoneda ⋙ Φ.presheafFiber ≅ Φ.fiber`
- core/canonical owner: `Φ.shrinkYonedaCompPresheafFiberIso`
- bridge/view: transport along `shrinkYonedaIsoYoneda`
- primitive data: the point `Φ`, its functor `Φ.fiber`, and the derived functor
  `Φ.presheafFiber`;
- derived API kept here: only the change-of-owner comparison from `shrinkYoneda` to `yoneda`.
-/
/- Lemma 7.32.3: the point fiber of the representable presheaf `h_U` is functorially
isomorphic to the fiber value `Φ(U)`. This is the canonical point comparison
`Φ.shrinkYonedaCompPresheafFiberIso`, rewritten from `shrinkYoneda` to `yoneda` via
`shrinkYonedaIsoYoneda`. -/
#check
  ((Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm Φ.presheafFiber) ≪≫
    Φ.shrinkYonedaCompPresheafFiberIso :
      CategoryTheory.yoneda ⋙ Φ.presheafFiber ≅ Φ.fiber)

end GrothendieckTopology.Point

end CategoryTheory
