module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import stacks_project.Chap06.Definition_6_30_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

universe u v w u1

variable {X : Type u} [TopologicalSpace X]

variable {C : Type v} [Category.{w} C]
variable {B : Set (Opens X)}

/- Domain-style sampling for Definition 6.30.8:
- primary domain: `C`-valued presheaves and sheaves on the basis site attached to a topological
  basis of `X`;
- sampled owner abstractions:
  `Presheaf`,
  `basisGrothendieckTopology`,
  `BasisSiteSheaf`,
  `Presheaf.isSheaf_iff_isSheaf_comp`;
- source-facing layer: `C`-valued presheaves on the full subcategory of basis opens, their
  morphisms, and the source description of the sheaf condition via the underlying set-valued basis
  presheaf `ℱ ⋙ F`;
- core/canonical owner: for the sheaf notion this is the chapter owner `BasisSiteSheaf C B`;
  for raw `C`-valued presheaves there is no separate upstream generic owner beyond the functor
  category `((BasisOpen B)ᵒᵖ ⥤ C)`, so this file should not introduce a parallel local wrapper;
- bridge/view layer: the canonical comparison theorem
  `Presheaf.isSheaf_iff_isSheaf_comp (basisGrothendieckTopology B) ℱ F`, which identifies the
  basis-site sheaf condition on `ℱ` with the sheaf condition on the underlying set-valued basis
  presheaf `ℱ ⋙ F`;
- primitive data versus derived API: the primitive data are only the functor
  `((BasisOpen B)ᵒᵖ ⥤ C)` and its natural transformations. Once `hB` is fixed, the sheaf notion
  is already owned by `BasisSiteSheaf C B`; the underlying `Type`-valued basis presheaf and the
  comparison theorem are derived companion views rather than parallel owners.

Source/core/bridge triage:
- `source-facing`: a `C`-valued basis presheaf, its morphisms, and the source criterion using the
  underlying set-valued basis presheaf;
- `core/canonical`: the chapter owner `BasisSiteSheaf C B` for sheaves on the basis site;
- `bridge/view`: `Presheaf.isSheaf_iff_isSheaf_comp (basisGrothendieckTopology B) ℱ F`.
-/

/- Definition 6.30.8 (1): a presheaf with values in a category `C` on a basis `B` of `X` is a
`C`-valued contravariant functor on the full subcategory of basis opens. -/
#check ((BasisOpen B)ᵒᵖ ⥤ C)

variable (ℱ 𝒢 : (BasisOpen B)ᵒᵖ ⥤ C)

/- Definition 6.30.8 (2): a morphism of presheaves with values in `C` on `B` is a natural
transformation, i.e. a family of morphisms compatible with restriction. -/
#check (ℱ ⟶ 𝒢)

variable (hB : Opens.IsBasis B)
variable (F : C ⥤ Type u1)

/- Definition 6.30.8 (3): for a type of algebraic structure `(C, F)`, the source's underlying
presheaf of sets attached to a `C`-valued basis presheaf `ℱ` is the composite `ℱ ⋙ F`, i.e.
`U ↦ F.obj (ℱ.obj U)`. -/
#check (ℱ ⋙ F)

/- Definition 6.30.8 (4): the canonical owner for `C`-valued sheaves on the basis `B` is the
basis-site sheaf category `BasisSiteSheaf C B`. -/
#check (BasisSiteSheaf C B hB)

section

variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F] [F.ReflectsIsomorphisms]

/- Companion bridge: under the standard algebraic-category hypotheses on the underlying-set
functor `F`, the source sheaf condition on the underlying set-valued basis presheaf `ℱ ⋙ F`
is equivalent to the canonical basis-site sheaf condition on `ℱ`. -/
#check
  (Presheaf.isSheaf_iff_isSheaf_comp (basisGrothendieckTopology B hB) ℱ F :
    Presheaf.IsSheaf (basisGrothendieckTopology B hB) ℱ ↔
      Presheaf.IsSheaf (basisGrothendieckTopology B hB) (ℱ ⋙ F))

end
