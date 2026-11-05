module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import stacks_project.Chap07.Definition_7_15_1_Topoi
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.TwoSquare
open scoped MorphismOfTopoiIn TwoSquare

noncomputable section

universe u v w

namespace CategoryTheory

variable {B' B C'' C' C D'' D' D : Type u}
variable [Category.{v} B'] [Category.{v} B] [Category.{v} C''] [Category.{v} C'] [Category.{v} C]
variable [Category.{v} D''] [Category.{v} D'] [Category.{v} D]
variable {JB' : GrothendieckTopology B'}
variable {JB : GrothendieckTopology B}
variable {JC'' : GrothendieckTopology C''}
variable {JC' : GrothendieckTopology C'}
variable {JC : GrothendieckTopology C}
variable {JD'' : GrothendieckTopology D''}
variable {JD' : GrothendieckTopology D'}
variable {JD : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.45.3:
- primary domain: base-change morphisms for commutative squares of topoi;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `MorphismOfTopoiIn.baseChange`,
  `MorphismOfTopoiIn.comp`,
  `CategoryTheory.mateEquiv_hcomp`,
  `CategoryTheory.mateEquiv_vcomp`;
- source/core/bridge triage:
  `source-facing`: the vertical-composition law for base change morphisms of topoi;
  `core/canonical`: `MorphismOfTopoiIn.baseChange`, `CategoryTheory.mateEquiv_hcomp`, and
    `MorphismOfTopoiIn.comp`;
  `bridge/view`: the inverse-image `TwoSquare` of one square of topoi.

Primitive data are the four morphisms of topoi in one square together with the inverse-image
square `TwoSquare (g⁻¹) (f⁻¹) (f'⁻¹) (g'⁻¹)`. The base change morphism itself is the owner
declaration `MorphismOfTopoiIn.baseChange`; this remark keeps only the source-facing
vertical-composition formula. Raw equalities of inverse-image composites are therefore only a
bridge into `TwoSquare`, not the public API of this remark. The horizontal-composition formula
below is retained only as a minimal auxiliary companion for `Remark_7_45_4`.
-/

namespace MorphismOfTopoiIn

-- Proof sketch: the composite of the two source-facing base change maps is the horizontal
-- composition of the mates of the lower and upper inverse-image squares. Then `mateEquiv_hcomp`
-- identifies that horizontal composition with the mate of the outer rectangle.
/-- Remark 7.45.3: for two vertically composable commutative squares of topoi, the composite of
their two base change maps is the base change map of the outer rectangle. -/
theorem baseChange_vertical_composite_eq
    (k : MorphismOfTopoiIn JB JB')
    (l : MorphismOfTopoiIn JC JC')
    (m : MorphismOfTopoiIn JD JD')
    (g' : MorphismOfTopoiIn JD' JC')
    (g : MorphismOfTopoiIn JD JC)
    (f' : MorphismOfTopoiIn JC' JB')
    (f : MorphismOfTopoiIn JC JB)
    (upper : TwoSquare (l⁻¹) (f⁻¹) (f'⁻¹) (k⁻¹))
    (lower : TwoSquare (m⁻¹) (g⁻¹) (g'⁻¹) (l⁻¹)) :
    (Functor.associator (f _*) (g _*) (m⁻¹)).hom ≫
        Functor.whiskerLeft
          (f _*)
          (baseChange l g' g m lower) ≫
          (Functor.associator (f _*) (l⁻¹) (g' _*)).inv ≫
            Functor.whiskerRight
              (baseChange k f' f l upper)
              (g' _*) ≫
                (Functor.associator (k⁻¹) (f' _*) (g' _*)).hom =
      baseChange k (g'.comp f') (g.comp f) m (lower ≫ᵥ upper) := by
  change
    ((mateEquiv f.adjunction f'.adjunction upper) ≫ₕ
      (mateEquiv g.adjunction g'.adjunction lower)).natTrans =
      baseChange k (g'.comp f') (g.comp f) m (lower ≫ᵥ upper)
  simpa [baseChange, comp] using
    congrArg TwoSquare.natTrans
      (mateEquiv_hcomp
        g.adjunction
        g'.adjunction
        f.adjunction
        f'.adjunction
        lower
        upper).symm

-- Auxiliary companion: this horizontal-composition formula is not the source statement of
-- Remark 7.45.3. It is kept as minimal canonical topos-level API for `Remark_7_45_4`.
-- Proof sketch: the composite of the two base change maps is the vertical composition of the
-- mates of the right and left inverse-image squares. Then `mateEquiv_vcomp` identifies that
-- vertical composition with the mate of the outer rectangle.
/-- Auxiliary horizontal-composition formula for base change morphisms of topoi. -/
theorem baseChange_horizontal_composite_eq
    (g' : MorphismOfTopoiIn JC' JC'')
    (g : MorphismOfTopoiIn JC JC')
    (f'' : MorphismOfTopoiIn JD'' JC'')
    (f' : MorphismOfTopoiIn JD' JC')
    (f : MorphismOfTopoiIn JD JC)
    (h' : MorphismOfTopoiIn JD' JD'')
    (h : MorphismOfTopoiIn JD JD')
    (left : TwoSquare (h'⁻¹) (f'⁻¹) (f''⁻¹) (g'⁻¹))
    (right : TwoSquare (h⁻¹) (f⁻¹) (f'⁻¹) (g⁻¹)) :
    (Functor.associator (f _*) (h⁻¹) (h'⁻¹)).inv ≫
        Functor.whiskerRight
          (baseChange g f' f h right)
          (h'⁻¹) ≫
          (Functor.associator (g⁻¹) (f' _*) (h'⁻¹)).hom ≫
            Functor.whiskerLeft
              (g⁻¹)
              (baseChange g' f'' f' h' left) ≫
              (Functor.associator (g⁻¹) (g'⁻¹) (f'' _*)).inv =
      baseChange (g.comp g') f'' f (h.comp h') (right ≫ₕ left) := by
  change
    ((mateEquiv f.adjunction f'.adjunction right) ≫ᵥ
      (mateEquiv f'.adjunction f''.adjunction left)).natTrans =
      baseChange (g.comp g') f'' f (h.comp h') (right ≫ₕ left)
  simpa [baseChange, comp] using
    congrArg TwoSquare.natTrans
      (mateEquiv_vcomp
        f.adjunction
        f'.adjunction
        f''.adjunction
        right
        left).symm

end MorphismOfTopoiIn

end CategoryTheory
