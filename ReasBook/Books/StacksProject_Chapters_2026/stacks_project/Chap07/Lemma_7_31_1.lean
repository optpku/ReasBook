module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import stacks_project.Chap07.Definition_7_15_1_Topoi

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.31.1:
- primary domain: localized geometric morphisms on slice topoi and the canonical `Over`
  adjunctions attached to a left adjoint;
- sampled owner API:
  `LeftExactAdjunction`,
  `LeftExactAdjunction.inverseImage`,
  `Over.postAdjunctionLeft`,
  `Over.forgetAdjStar`;
- source/core/bridge triage:
  `source-facing`: the induced localized morphism of topoi
    `Sh(𝒞) / f⁻¹ 𝒢 ⟶ Sh(𝒟) / 𝒢`;
  `core/canonical`: the generic owner `LeftExactAdjunction.localization` on the slice categories;
  `bridge/view`: the objectwise inverse-image formula and the canonical comparison of the two
    composite right adjoints, specialized to `MorphismOfTopoiIn`.

Primitive data for the core construction are only a left-exact adjunction `f⁻¹ ⊣ f_*` and an
object `Y` of the target category. In the source-facing specialization these become a morphism of
topoi `f` and a target sheaf `𝒢`. The refined API therefore promotes the construction to the
generic owner `LeftExactAdjunction.localization`; the sheaf-topos statement is then just its
specialization to `MorphismOfTopoiIn`.
-/

namespace LeftExactAdjunction

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/-- The canonical slice localization attached to a left-exact adjunction `f⁻¹ ⊣ f_*`. Its inverse
image is `Over.post f.inverseImage`, and its direct image is the corresponding slice right adjoint
obtained from `Over.postAdjunctionLeft`. -/
def localization
    [HasPullbacks B]
    (f : LeftExactAdjunction A B)
    (Y : B) :
    LeftExactAdjunction (Over (f.inverseImage.obj Y)) (Over Y) :=
  let η := f.adjunction.unit
  { inverseImageFunctor := by
      let inverseImage : Over Y ⥤ Over (f.inverseImage.obj Y) := Over.post f.inverseImage
      let _ : PreservesFiniteLimits inverseImage := by
        let _ : PreservesFiniteLimits f.inverseImage := inferInstance
        infer_instance
      exact LeftExactFunctor.of inverseImage
    pushforward := Over.post f.pushforward ⋙ Over.pullback (η.app Y)
    adjunction := by
      simpa using Over.postAdjunctionLeft f.adjunction }

-- Proof sketch: by definition the localized inverse image is `Over.post f.inverseImage`.
/-- The localized inverse image sends `(Z ⟶ Y)` to `(f⁻¹ Z ⟶ f⁻¹ Y)`. -/
@[simp] theorem localization_inverseImage_obj
    [HasPullbacks B]
    (f : LeftExactAdjunction A B)
    (Y : B)
    (Z : Over Y) :
    (f.localization Y).inverseImage.obj Z = Over.mk (f.inverseImage.map Z.hom) := by
  change (Over.post f.inverseImage).obj Z = Over.mk (f.inverseImage.map Z.hom)
  rfl

-- Proof sketch: both functors are right adjoint to
-- `Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) = Over.forget Y ⋙ f.inverseImage`,
-- so the comparison is the
-- canonical uniqueness isomorphism of right adjoints.
/-- Restricting to `f⁻¹ Y` and then pushing forward along the localized morphism is naturally
isomorphic to pushing forward along `f` and then restricting to `Y`. -/
noncomputable def localization_pushforwardStarIso
    [HasBinaryProducts A] [HasPullbacks B] [HasBinaryProducts B]
    (f : LeftExactAdjunction A B)
    (Y : B) :
    Over.star (f.inverseImage.obj Y) ⋙ (f.localization Y).pushforward ≅
      f.pushforward ⋙ Over.star Y := by
  let localizedAdj :
      Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ⊣
        Over.star (f.inverseImage.obj Y) ⋙ (f.localization Y).pushforward :=
    (Over.postAdjunctionLeft f.adjunction).comp (Over.forgetAdjStar (f.inverseImage.obj Y))
  let globalAdj :
      Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ⊣
        f.pushforward ⋙ Over.star Y :=
    ((Over.forgetAdjStar Y).comp f.adjunction).ofNatIsoLeft
      (eqToIso (by rfl) :
        Over.post f.inverseImage ⋙ Over.forget (f.inverseImage.obj Y) ≅
          Over.forget Y ⋙ f.inverseImage)
  exact Adjunction.rightAdjointUniq localizedAdj globalAdj

end LeftExactAdjunction

namespace MorphismOfTopoiIn

section

variable (f : MorphismOfTopoiIn JD JC) (𝒢 : Sheaf JD (Type w))

/- Lemma 7.31.1 specialized to morphisms of topoi: for
`f : Sh(𝒞) ⟶ Sh(𝒟)` and `𝒢 : Sh(𝒟)`, the induced morphism
`Sh(𝒞) / f⁻¹ 𝒢 ⟶ Sh(𝒟) / 𝒢` is the generic slice-localization owner
`LeftExactAdjunction.localization` applied to `f`. -/
#check (f.localization 𝒢)

/- Companion specialization: on an object `(ℋ ⟶ 𝒢)`, the localized inverse image applies `f⁻¹`
to the structure morphism, giving `(f⁻¹ ℋ ⟶ f⁻¹ 𝒢)`. -/
#check (LeftExactAdjunction.localization_inverseImage_obj f 𝒢)

/- Companion specialization: restricting to `f⁻¹ 𝒢` and then pushing forward along the localized
morphism is canonically isomorphic to pushing forward along `f` and then restricting to `𝒢`. -/
#check (LeftExactAdjunction.localization_pushforwardStarIso f 𝒢)

end

end MorphismOfTopoiIn

end CategoryTheory
