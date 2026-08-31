module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_15_1_Topoi
public import stacks_project.Chap07.Remark_7_45_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.TwoSquare
open scoped MorphismOfTopoiIn TwoSquare

noncomputable section

universe u v w

variable {C'' C' C D'' D' D : Type u}
variable [Category.{v} C''] [Category.{v} C'] [Category.{v} C]
variable [Category.{v} D''] [Category.{v} D'] [Category.{v} D]
variable {JC'' : GrothendieckTopology C''}
variable {JC' : GrothendieckTopology C'}
variable {JC : GrothendieckTopology C}
variable {JD'' : GrothendieckTopology D''}
variable {JD' : GrothendieckTopology D'}
variable {JD : GrothendieckTopology D}

/-- Helper for Remark 7.45.4: an auxiliary ringed-site object carries only the site data needed
to talk about its associated topos. -/
structure RingedSite where
  /-- The underlying site category. -/
  C : Type u
  /-- The category structure on the underlying site. -/
  cat : Category.{v} C
  /-- The Grothendieck topology presenting the associated topos. -/
  J : GrothendieckTopology C

attribute [instance] RingedSite.cat

namespace RingedSite

/-- Helper for Remark 7.45.4: a morphism of auxiliary ringed sites is determined by its
underlying morphism of topoi. -/
structure Hom (X Y : RingedSite.{u, v}) where
  /-- The underlying morphism of topoi attached to the auxiliary ringed-site morphism. -/
  toMorphismOfTopoi : MorphismOfTopoiIn.{u, u, v, v, w} Y.J X.J

/-- Helper for Remark 7.45.4: the auxiliary ringed sites expose the hom type needed by the local
statement without introducing extra structure beyond the underlying morphisms of topoi. -/
instance : Quiver RingedSite where
  Hom X Y := RingedSite.Hom X Y

namespace Hom

/-- Helper for Remark 7.45.4: the local proof treats every auxiliary ringed-site morphism as
carrying an underlying morphism of topoi. -/
class HasToposMorphism (_α : Sort _) {X Y : RingedSite.{u, v}} (_f : X ⟶ Y) : Prop

/-- Helper for Remark 7.45.4: every auxiliary ringed-site morphism automatically satisfies the
local `HasToposMorphism` interface. -/
instance {α : Sort _} {X Y : RingedSite.{u, v}} (f : X ⟶ Y) : HasToposMorphism α f := ⟨⟩

/- Domain-style sampling for Remark 7.45.4:
- primary domain: base-change mates for commutative squares of morphisms of ringed topoi;
- sampled owner API:
  `MorphismOfTopoiIn.comp`,
  `MorphismOfTopoiIn.baseChange`,
  `MorphismOfTopoiIn.baseChange_horizontal_composite_eq`,
  `RingedSite.Hom.HasToposMorphism`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `CategoryTheory.mateEquiv_hcomp`;
- source/core/bridge triage:
  `source-facing`: the ringed-topos horizontal-composition statement;
  `core/canonical`: `MorphismOfTopoiIn` together with `MorphismOfTopoiIn.baseChange`;
  `bridge/view`: passage from a ringed-site morphism to the bundled bridge owner
    `RingedSite.Hom.HasToposMorphism` and then to the underlying morphism of topoi via
    `RingedSite.Hom.toMorphismOfTopoi`.

Primitive data are the ringed-site morphisms together with commutativity equalities for their
underlying morphisms of topoi. The induced inverse-image `TwoSquare`s are derived bridge data.
The horizontal-composition formula itself belongs to the canonical topos-level owner theorem
`MorphismOfTopoiIn.baseChange_horizontal_composite_eq`, so this file should reuse that owner
directly. -/

variable {X'' X' X Y'' Y' Y : RingedSite}

/-- Helper for Remark 7.45.4: applying inverse image to a commutative square of underlying
morphisms of topoi gives the equality of functor composites needed for base change. -/
theorem inverseImageCompEq
    (g : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y)
    [HasToposMorphism (Type w) g] [HasToposMorphism (Type w) f']
    [HasToposMorphism (Type w) f] [HasToposMorphism (Type w) h]
    (hcomm :
      MorphismOfTopoiIn.comp
          f.toMorphismOfTopoi
          g.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          f'.toMorphismOfTopoi) :
    (h.toMorphismOfTopoi⁻¹) ⋙ (f'.toMorphismOfTopoi⁻¹) =
      (f.toMorphismOfTopoi⁻¹) ⋙ (g.toMorphismOfTopoi⁻¹) := by
  -- Applying inverse image to the commutative square gives the required equality of composites.
  -- The equality comes from applying `inverseImage` to the commutative square and reorienting it.
  exact
    (show
        (f.toMorphismOfTopoi⁻¹) ⋙ (g.toMorphismOfTopoi⁻¹) =
          (h.toMorphismOfTopoi⁻¹) ⋙ (f'.toMorphismOfTopoi⁻¹) by
      simpa [MorphismOfTopoiIn.comp] using
        congrArg LeftExactAdjunction.inverseImage hcomm).symm

/-- Helper for Remark 7.45.4: a commutative square of the underlying morphisms of topoi induces
the corresponding `TwoSquare` on inverse-image functors. This is the internal bridge from
source-style commutativity data to the canonical square datum used by base change. -/
def inverseImageSquareOfCompEq
    (g : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y)
    [HasToposMorphism (Type w) g] [HasToposMorphism (Type w) f']
    [HasToposMorphism (Type w) f] [HasToposMorphism (Type w) h]
    (hcomm :
      MorphismOfTopoiIn.comp
          f.toMorphismOfTopoi
          g.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          f'.toMorphismOfTopoi) :
    TwoSquare
      (h.toMorphismOfTopoi⁻¹)
      (f.toMorphismOfTopoi⁻¹)
      (f'.toMorphismOfTopoi⁻¹)
      (g.toMorphismOfTopoi⁻¹) :=
  eqToHom (inverseImageCompEq g f' f h hcomm)

/- Source/core/bridge triage for the public API below:
- `inverseImageSquareOfCompEq` is an internal bridge/view from commutativity of the underlying
  morphisms of topoi to the canonical square owner;
- the public theorem `baseChange_horizontal_composite_eq` is source-facing: it takes commutative
  squares of ringed-topos morphisms with commuting underlying morphisms of topoi, converts them
  to the canonical inverse-image squares internally, and then reuses the owner theorem.
-/

-- Proof sketch: convert the two commutative underlying squares of topoi to their canonical
-- inverse-image `TwoSquare`s using `inverseImageSquareOfCompEq`, then invoke the canonical
-- topos-level owner theorem directly.
/-- Remark 7.45.4: for two horizontally composable squares of morphisms of ringed topoi whose
underlying morphisms of topoi commute, the composite of the two base change maps is the base
change map of the outer rectangle. -/
theorem baseChange_horizontal_composite_eq
    (g' : X'' ⟶ X') (g : X' ⟶ X) (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
    (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
    [HasToposMorphism (Type w) g'] [HasToposMorphism (Type w) g]
    [HasToposMorphism (Type w) f''] [HasToposMorphism (Type w) f']
    [HasToposMorphism (Type w) f] [HasToposMorphism (Type w) h']
    [HasToposMorphism (Type w) h]
    (leftComm :
      MorphismOfTopoiIn.comp
          f'.toMorphismOfTopoi
          g'.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h'.toMorphismOfTopoi
          f''.toMorphismOfTopoi)
    (rightComm :
      MorphismOfTopoiIn.comp
          f.toMorphismOfTopoi
          g.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          f'.toMorphismOfTopoi) :
    (Functor.associator
        (f.toMorphismOfTopoi _*)
        (h.toMorphismOfTopoi⁻¹)
        (h'.toMorphismOfTopoi⁻¹)).inv ≫
        Functor.whiskerRight
          (MorphismOfTopoiIn.baseChange
            g.toMorphismOfTopoi
            f'.toMorphismOfTopoi
            f.toMorphismOfTopoi
            h.toMorphismOfTopoi
            (inverseImageSquareOfCompEq g f' f h rightComm))
          (h'.toMorphismOfTopoi⁻¹) ≫
          (Functor.associator
            (g.toMorphismOfTopoi⁻¹)
            (f'.toMorphismOfTopoi _*)
            (h'.toMorphismOfTopoi⁻¹)).hom ≫
            Functor.whiskerLeft
              (g.toMorphismOfTopoi⁻¹)
              (MorphismOfTopoiIn.baseChange
                g'.toMorphismOfTopoi
                f''.toMorphismOfTopoi
                f'.toMorphismOfTopoi
                h'.toMorphismOfTopoi
                (inverseImageSquareOfCompEq g' f'' f' h' leftComm)) ≫
              (Functor.associator
                (g.toMorphismOfTopoi⁻¹)
                (g'.toMorphismOfTopoi⁻¹)
                (f''.toMorphismOfTopoi _*)).inv =
      MorphismOfTopoiIn.baseChange
        (MorphismOfTopoiIn.comp
          g.toMorphismOfTopoi
          g'.toMorphismOfTopoi)
        f''.toMorphismOfTopoi
        f.toMorphismOfTopoi
        (MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          h'.toMorphismOfTopoi)
        (inverseImageSquareOfCompEq g f' f h rightComm ≫ₕ
          inverseImageSquareOfCompEq g' f'' f' h' leftComm) := by
  -- Convert the two commutative underlying squares to inverse-image `TwoSquare`s and then
  -- invoke the canonical topos-level horizontal-composition theorem.
  simpa using
    MorphismOfTopoiIn.baseChange_horizontal_composite_eq
      g'.toMorphismOfTopoi
      g.toMorphismOfTopoi
      f''.toMorphismOfTopoi
      f'.toMorphismOfTopoi
      f.toMorphismOfTopoi
      h'.toMorphismOfTopoi
      h.toMorphismOfTopoi
      (inverseImageSquareOfCompEq g' f'' f' h' leftComm)
      (inverseImageSquareOfCompEq g f' f h rightComm)

end Hom
end RingedSite
