module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

namespace AlgebraicGeometry

/- Domain-style sampling for Definition 6.25.1:
- primary domain: ringed spaces and morphisms of ringed spaces;
- sampled owner declarations:
  `RingedSpace`,
  `SheafedSpace`,
  `SheafedSpace.sheaf`,
  `TopCat.Sheaf.pushforward`;
- owner abstraction: the source-facing owner is `RingedSpace`; the underlying
  `SheafedSpace CommRingCat` infrastructure is core/canonical support and should not replace the
  ringed-space surface;
- primitive data: a ringed space `X` and a morphism `f : X ⟶ Y`;
- derived API: the underlying continuous map `f.hom.base` and the structure-sheaf morphism
  `⟨f.hom.c⟩ : 𝒪_Y ⟶ f_* 𝒪_X`.

Source/core/bridge triage:
- `source-facing`: ringed spaces and morphisms of ringed spaces;
- `core/canonical`: `SheafedSpace CommRingCat`;
- `bridge/view`: the component maps `f.hom.base` and `⟨f.hom.c⟩`.
-/

variable {X Y : RingedSpace.{u}}

/- Definition 6.25.1, owner recall: a ringed space is the canonical mathlib owner
`AlgebraicGeometry.RingedSpace`. -/
recall RingedSpace

/- A morphism of ringed spaces is an arrow in the category `AlgebraicGeometry.RingedSpace`. -/
#check (X ⟶ Y)

/- The first component of a morphism of ringed spaces is the underlying continuous map. -/
#check fun (f : X ⟶ Y) ↦ f.hom.base

/- The second component is the structure-sheaf morphism
`f^\sharp : \mathcal{O}_Y ⟶ f_* \mathcal{O}_X`. -/
#check fun (f : X ⟶ Y) ↦
  (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf from
    ⟨f.hom.c⟩)

end AlgebraicGeometry
