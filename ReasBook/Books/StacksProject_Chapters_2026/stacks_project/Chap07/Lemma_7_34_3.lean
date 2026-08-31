module

public import stacks_project.Chap07.Definition_7_32_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : MorphismOfTopoiIn J K)
variable (q : MorphismOfTopoiIn K typesGrothendieckTopology.{w})
variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Lemma 7.34.3:
- primary domain: points of topoi and their inverse-image/stalk functors;
- sampled owner API:
  `MorphismOfTopoiIn.typeInverseImage`,
  `MorphismOfTopoiIn.comp`,
  `typeEquiv`;
- owner abstraction: `MorphismOfTopoiIn.comp`;
- layer: bridge/view, since the stalk statement is the objectwise computation of the inverse-image
  functor of the composite point, viewed in `Type` through `typeEquiv` via `typeInverseImage`.

Primitive data are just the morphism of topoi `f`, the point `q`, and the sheaf `ℱ`. The stalk
comparison is derived API from the owner `MorphismOfTopoiIn.comp`, so this item should be a direct
recall of that canonical computation rather than a parallel theorem wrapper.
-/

/- Lemma 7.34.3: for a morphism of topoi `f : Sh(𝒟) ⟶ Sh(𝒞)`, a point `q` of `Sh(𝒟)`, and a
sheaf `ℱ` on `𝒞`, the stalk `(f⁻¹ ℱ)_q` is canonically identified with the stalk of `ℱ` at the
composite point `f.comp q`. -/
#check
  (rfl :
    q.typeInverseImage.obj ((f⁻¹).obj ℱ) =
      (f.comp q).typeInverseImage.obj ℱ)

end CategoryTheory
