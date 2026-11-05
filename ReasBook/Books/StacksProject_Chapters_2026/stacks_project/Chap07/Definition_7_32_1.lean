module

public import Mathlib.CategoryTheory.Sites.Types
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_15_1_Topoi

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Source/core/bridge triage for Definition 7.32.1:
- source-facing notion: a point of the topos `Sh(C)`, i.e.
  `MorphismOfTopoiIn J typesGrothendieckTopology`
- core/canonical owner: the source-facing owner
  `MorphismOfTopoiIn J typesGrothendieckTopology`, viewed internally as the specialization
  `LeftExactAdjunction (Sheaf typesGrothendieckTopology (Type w)) (Sheaf J (Type w))`, of which
  `MorphismOfTopoiIn J typesGrothendieckTopology` is the site-presented specialization already
  chosen upstream in Chapter 7
- bridge/view: the canonical equivalence `typeEquiv` identifies sheaves on the terminal site of
  sets with `Type`, so the inverse and direct image functors of a topos point may be viewed as
  the `Type`-valued functors `p.typeInverseImage` and `p.typePushforward`
- primitive data: the inverse-image functor `p⁻¹`, the direct-image functor `p _*`, and their
  adjunction, already packaged by `MorphismOfTopoiIn`
- derived API: the bridge functors `p.typeInverseImage`, `p.typePushforward`, the `Type`-valued
  adjunction `p.typeAdjunction`, and the right-adjoint instance on `p.typePushforward`
-/
/- Definition 7.32.1: a point of the topos `Sh(C)` is a morphism from the terminal topos,
identified canonically with `Sh(typesGrothendieckTopology)`, to `Sh(C)`. -/
#check (MorphismOfTopoiIn J typesGrothendieckTopology.{w})

variable {J}

namespace MorphismOfTopoiIn

/-- The inverse-image functor of a topos point, viewed as a `Type`-valued functor via
`typeEquiv`. -/
abbrev typeInverseImage (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    Sheaf J (Type w) ⥤ Type w :=
  p⁻¹ ⋙ typeEquiv.{w}.inverse

/-- The direct-image functor of a topos point, viewed as a functor out of `Type` via
`typeEquiv`. -/
abbrev typePushforward (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    Type w ⥤ Sheaf J (Type w) :=
  typeEquiv.{w}.functor ⋙ (p _*)

/-- The `Type`-valued inverse and direct images of a topos point form the adjunction obtained by
transporting `p.adjunction` across `typeEquiv`. -/
abbrev typeAdjunction (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typeInverseImage ⊣ p.typePushforward :=
  p.adjunction.comp typeEquiv.{w}.symm.toAdjunction

instance (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    (p.typePushforward).IsRightAdjoint :=
  p.typeAdjunction.isRightAdjoint

end MorphismOfTopoiIn

end CategoryTheory
