module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_32_1
public import stacks_project.Chap07.Lemma_7_12_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor

universe u v w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn
open scoped GrothendieckTopology.SheafifiedRepresentable

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

/-- A point of the site `(C, J)` canonically defines a point of the topos `Sh(C)`. -/
noncomputable def toToposPoint
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    MorphismOfTopoiIn J typesGrothendieckTopology.{w} where
  inverseImageFunctor :=
    let _ : PreservesFiniteLimits (p.sheafFiber ⋙ typeEquiv.{w}.functor) := inferInstance
    LeftExactFunctor.of (p.sheafFiber ⋙ typeEquiv.{w}.functor)
  pushforward := typeEquiv.{w}.inverse ⋙ p.skyscraperSheafFunctor
  adjunction := p.skyscraperSheafAdjunction.comp typeEquiv.{w}.toAdjunction

/-- The `Type`-valued inverse-image functor of the point induced by a site point recovers the
usual stalk functor. -/
noncomputable def toToposPoint_pointInverseImageIso
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    p.toToposPoint.typeInverseImage ≅ p.sheafFiber :=
  (Functor.associator p.sheafFiber typeEquiv.{w}.functor typeEquiv.{w}.inverse).symm ≪≫
    (Functor.isoWhiskerLeft p.sheafFiber typeEquiv.{w}.unitIso.symm) ≪≫
      Functor.rightUnitor p.sheafFiber

/-- The `Type`-valued direct-image functor of the point induced by a site point recovers the
usual skyscraper functor. -/
noncomputable def toToposPoint_pointPushforwardIso
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    p.toToposPoint.typePushforward ≅ p.skyscraperSheafFunctor :=
  (Functor.associator typeEquiv.{w}.functor typeEquiv.{w}.inverse p.skyscraperSheafFunctor).symm ≪≫
    (Functor.isoWhiskerRight typeEquiv.{w}.unitIso.symm p.skyscraperSheafFunctor) ≪≫
      Functor.leftUnitor p.skyscraperSheafFunctor

/-- The canonical point of the jointly surjective site on `Type`. -/
noncomputable def typesPoint : Point.{w} typesGrothendieckTopology.{w} where
  fiber := 𝟭 (Type w)
  isCofiltered := by
    let X : (𝟭 (Type w)).Elements := Functor.elementsMk _ PUnit PUnit.unit
    have hX : IsInitial X := by
      refine IsInitial.ofUniqueHom (fun Y ↦ ?_) (fun Y f ↦ ?_)
      · exact ⟨fun _ : PUnit ↦ Y.2, rfl⟩
      · apply CategoryOfElements.ext (𝟭 (Type w)) f _
        funext u
        cases u
        exact f.property
    exact IsCofiltered.of_isInitial (C := (𝟭 (Type w)).Elements) hX
  initiallySmall := by
    let X : (𝟭 (Type w)).Elements := Functor.elementsMk _ PUnit PUnit.unit
    have hX : IsInitial X := by
      refine IsInitial.ofUniqueHom (fun Y ↦ ?_) (fun Y f ↦ ?_)
      · exact ⟨fun _ : PUnit ↦ Y.2, rfl⟩
      · apply CategoryOfElements.ext (𝟭 (Type w)) f _
        funext u
        cases u
        exact f.property
    haveI : HasInitial (𝟭 (Type w)).Elements := hX.hasInitial
    infer_instance
  jointly_surjective {X} R hR x :=
    ⟨PUnit, fun _ ↦ x, hR x, PUnit.unit, rfl⟩

noncomputable abbrev typesPointBaseObj : typesPoint.fiber.Elements :=
  typesPoint.fiber.elementsMk PUnit PUnit.unit

instance (Y : typesPoint.fiber.Elements) : Unique (typesPointBaseObj ⟶ Y) := by
  let g : typesPointBaseObj ⟶ Y := ⟨fun _ ↦ Y.2, rfl⟩
  refine { default := g, uniq := ?_ }
  intro f
  apply CategoryOfElements.ext typesPoint.fiber f g
  funext u
  cases u
  simpa [g] using f.2

noncomputable def typesPointInitial : IsInitial typesPointBaseObj :=
  IsInitial.ofUnique _

noncomputable abbrev typesPointTerminalObj : typesPoint.fiber.Elementsᵒᵖ :=
  op typesPointBaseObj

noncomputable def typesPointTerminal : IsTerminal typesPointTerminalObj :=
  terminalOpOfInitial typesPointInitial

noncomputable def typesPointPresheafFiberObjIso (P : Type wᵒᵖ ⥤ Type w) :
    typesPoint.presheafFiber.obj P ≅ P.obj (op PUnit) := by
  let Q := (CategoryOfElements.π typesPoint.fiber).op ⋙ P
  change colimit Q ≅ Q.obj typesPointTerminalObj
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal typesPointTerminal Q)

lemma toPresheafFiber_typesPointPresheafFiberObjIso_hom
    (P : Type wᵒᵖ ⥤ Type w) (X : Type w) (x : X) :
    typesPoint.toPresheafFiber X x P ≫ (typesPointPresheafFiberObjIso P).hom =
      P.map (show PUnit ⟶ X from fun _ ↦ x).op := by
  simpa [typesPointPresheafFiberObjIso, GrothendieckTopology.Point.presheafFiber,
    typesPointTerminalObj, typesPointTerminal] using
    (colimit.comp_coconePointUniqueUpToIso_hom
      (hc := colimitOfDiagramTerminal typesPointTerminal
        ((CategoryOfElements.π typesPoint.fiber).op ⋙ P))
      (op (typesPoint.fiber.elementsMk X x)))

noncomputable def typesPointPresheafFiberIso :
    typesPoint.presheafFiber ≅ (evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit) := by
  refine NatIso.ofComponents (fun P ↦ typesPointPresheafFiberObjIso P) ?_
  intro P Q f
  apply typesPoint.presheafFiber_hom_ext
  intro X x
  rw [toPresheafFiber_naturality_assoc]
  calc
    (f.app (op X) ≫ typesPoint.toPresheafFiber X x Q) ≫ (typesPointPresheafFiberObjIso Q).hom =
        f.app (op X) ≫
          (typesPoint.toPresheafFiber X x Q ≫ (typesPointPresheafFiberObjIso Q).hom) := by
            simp [Category.assoc]
    _ = f.app (op X) ≫ Q.map (show PUnit ⟶ X from fun _ ↦ x).op := by
      rw [toPresheafFiber_typesPointPresheafFiberObjIso_hom]
    _ = P.map (show PUnit ⟶ X from fun _ ↦ x).op ≫
          ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f := by
            simpa using
              (NatTrans.naturality f
                (show op X ⟶ op PUnit from (show PUnit ⟶ X from fun _ ↦ x).op)).symm
    _ = typesPoint.toPresheafFiber X x P ≫ (typesPointPresheafFiberObjIso P).hom ≫
          ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  k ≫ ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f)
                (toPresheafFiber_typesPointPresheafFiberObjIso_hom P X x).symm

/-- The sheaf fiber of the canonical point on the jointly surjective site of types is evaluation
at `PUnit`, i.e. `typeEquiv.inverse`. -/
noncomputable def typesPointSheafFiberIso :
    typesPoint.sheafFiber ≅ typeEquiv.{w}.inverse := by
  simpa [GrothendieckTopology.Point.sheafFiber] using
    Functor.isoWhiskerLeft (sheafToPresheaf typesGrothendieckTopology (Type w))
      typesPointPresheafFiberIso

/-- The skyscraper functor of the canonical point on the jointly surjective site of types is the
canonical equivalence `typeEquiv.functor`. -/
noncomputable def typesPointSkyscraperSheafFunctorIso :
    typeEquiv.{w}.functor ≅ typesPoint.skyscraperSheafFunctor :=
  (conjugateIsoEquiv typeEquiv.{w}.symm.toAdjunction typesPoint.skyscraperSheafAdjunction)
    typesPointSheafFiberIso

/-- Comapping the canonical point of the jointly surjective site of types along the fiber functor
of a site point recovers the original point. -/
theorem typesPoint_comap_eq
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    (p : Point.{w} K)
    [RepresentablyFlat p.fiber]
    (hcover : CoverPreserving K typesGrothendieckTopology p.fiber)
    [InitiallySmall (p.fiber ⋙ typesPoint.fiber).Elements] :
    typesPoint.comap p.fiber hcover = p := by
  apply
    (show
      (typesPoint.comap p.fiber hcover = p) =
        ((typesPoint.comap p.fiber hcover).fiber = p.fiber) from
          mk.injEq _ _ _ _ _ _ _ _).mpr
  rfl

end GrothendieckTopology.Point

/- Lemma 7.32.7 (1): a point of the site `(C, J)` canonically defines a point of the topos
`Sh(C)`, and the inverse-image functor of the resulting point of the topos is the stalk functor. -/
#check GrothendieckTopology.Point.toToposPoint_pointInverseImageIso

-- Proof sketch: apply the inverse-image functor of the given topos point to the sheafified
-- representables `h_U^#` to obtain the site fiber functor `U ↦ p^{-1}(h_U^#)`, then prove this
-- functor is a site point and that its sheaf fiber recovers the original inverse-image functor.
namespace MorphismOfTopoiIn

open GrothendieckTopology.Point

/- Domain-style sampling for Lemma 7.32.7 (2):
- primary domain: points of a site and points of the associated topos, organized around the
  sheafified-representable owner layer and inverse image of points along a site morphism;
- sampled owner declarations:
  `GrothendieckTopology.Point.typesPoint`,
  `GrothendieckTopology.sheafifiedRepresentableFunctor`,
  `GrothendieckTopology.Point.comap`,
  `GrothendieckTopology.Point.sheafFiberComapIso`,
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.toToposPoint_pointInverseImageIso`;
- source/core/bridge triage:
  `source-facing`: the site point attached to a topos point by the fibers `U ↦ p^{-1}(h[U]^#[J])`;
  `core/canonical`: the chapter owners `J.sheafifiedRepresentableFunctor`, `p.typeInverseImage`,
  and `GrothendieckTopology.Point.comap`;
  `bridge/view`: the composite `J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage`, together
  with the comparison isomorphism identifying the resulting site-point sheaf fiber with the
  original inverse-image functor.

Primitive data are only the topos point `p`; the functor `U ↦ p^{-1}(h[U]^#[J])` is derived API
from the existing owners `J.sheafifiedRepresentableFunctor` and `p.typeInverseImage`, and the
associated site point should be built through the canonical point-comap owner rather than by
restating the primitive `Point` fields. -/

theorem typePresentationFunctor_coverPreserving
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    CoverPreserving J typesGrothendieckTopology
      (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage) := by
  constructor
  intro U S hS x
  let T : J.Cover U := ⟨S, hS⟩
  let π : ∐ (fun I : T.Arrow ↦ h[I.Y]^#[J]) ⟶ h[U]^#[J] :=
    J.sheafifiedRepresentableCoverMap T
  let _ : p.typeInverseImage.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction p.typeAdjunction
  -- The source proof starts from the canonical cover map on sheafified representables.
  have hsurj : Function.Surjective (p.typeInverseImage.map π) := by
    have hπ : Epi π := by
      simpa [π] using GrothendieckTopology.sheafifiedRepresentableCoverMap_epi (J := J) T
    exact (CategoryTheory.epi_iff_surjective _).1 (p.typeInverseImage.map_epi π)
  obtain ⟨z, hz⟩ := hsurj x
  let X : Discrete T.Arrow ⥤ Sheaf J (Type (max u v)) :=
    Discrete.functor (fun I : T.Arrow ↦ h[I.Y]^#[J])
  let _ : PreservesColimitsOfSize p.typeInverseImage := p.typeAdjunction.leftAdjoint_preservesColimits
  let hc : IsColimit (Functor.mapCocone p.typeInverseImage (colimit.cocone X)) :=
    isColimitOfPreserves p.typeInverseImage (colimit.isColimit X)
  -- Decompose the chosen preimage through the preserved coproduct, then read off one cover leg.
  obtain ⟨I, y, rfl⟩ := Types.jointly_surjective_of_isColimit hc z
  have hz' :
      (p⁻¹.map π).hom.app (op PUnit.{(max u v) + 1})
        ((p⁻¹.map (colimit.ι X I)).hom.app (op PUnit.{(max u v) + 1}) y) = x := by
    simpa [MorphismOfTopoiIn.typeInverseImage, X, π] using hz
  refine ⟨I.as.Y, I.as.f, fun _ ↦ y, I.as.hf, ?_⟩
  funext u
  -- The `I`-th coproduct injection into the cover map is exactly the `I.f`-component.
  have hι := congrArg
    (fun α => (p⁻¹.map α).hom.app (op PUnit.{(max u v) + 1}) y)
    (Limits.Sigma.ι_desc (fun I : T.Arrow ↦ J.sheafifiedRepresentableMap I.f) I.as)
  have hι' :
      (p⁻¹.map π).hom.app (op PUnit.{(max u v) + 1})
        ((p⁻¹.map (colimit.ι X I)).hom.app (op PUnit.{(max u v) + 1}) y) =
      (p⁻¹.map (J.sheafifiedRepresentableMap I.as.f)).hom.app (op PUnit.{(max u v) + 1}) y := by
    simpa [GrothendieckTopology.sheafifiedRepresentableCoverMap, π, X, Functor.map_comp] using hι
  simpa [MorphismOfTopoiIn.typeInverseImage] using hz'.symm.trans hι'

/-- Helper for Lemma 7.32.7: covering sieves act jointly surjectively on the fibers
`U ↦ p^{-1}(h_U^#)`. -/
theorem typePresentationFunctor_jointly_surjective
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    ∀ {U : C} (R : Sieve U) (hR : R ∈ J U)
      (x : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).obj U),
      ∃ (Y : C) (f : Y ⟶ U) (_ : R f)
        (y : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).obj Y),
        (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map f y = x := by
  intro U R hR x
  let S := R.functorPushforward (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage)
  have hS : S ∈ typesGrothendieckTopology
      ((J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).obj U) :=
    (typePresentationFunctor_coverPreserving (J := J) p).cover_preserve hR
  -- Read the pushed-forward covering sieve through the canonical point of the type site.
  obtain ⟨T, f, hf, t, ht⟩ := typesPoint.jointly_surjective S hS x
  let hs := Presieve.getFunctorPushforwardStructure
    (F := J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage) hf
  refine ⟨hs.preobj, hs.premap, hs.cover, hs.lift t, ?_⟩
  simpa [hs.fac] using ht

/-- Helper for Lemma 7.32.7: the comparison functor from representable neighborhoods to
arbitrary sheaf neighborhoods. -/
noncomputable def typePresentationFunctor_elements_toInverseImageElements
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements ⥤
      p.typeInverseImage.Elements where
  obj X := Functor.elementsMk _ (J.sheafifiedRepresentableFunctor.obj X.1) X.2
  map {X Y} f := CategoryOfElements.homMk _ _ (J.sheafifiedRepresentableFunctor.map f.1) (by
    exact f.2)

/-- Helper for Lemma 7.32.7: evaluating a morphism out of `h[U]^#` on the identity section
recovers the section corresponding to that morphism. -/
theorem sheafifiedRepresentable_component_eq_section
    [HasWeakSheafify J (Type (max u v))]
    {ℱ : Sheaf J (Type (max u v))} {U : C} (α : h[U]^#[J] ⟶ ℱ) :
    α.hom.app (op U)
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) =
      J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
  -- Rewrite evaluation on the identity section through naturality in the sheaf variable.
  have hcomp :=
    J.uliftSheafifiedRepresentableHomEquiv_comp
      (𝟙 (h[U]^#[J])) α
  -- The identity of `h[U]^#` corresponds to the canonical identity section.
  simpa using hcomp.symm

/-- Helper for Lemma 7.32.7: the section of `h[U]^#` corresponding to a site morphism `f` is the
sheafification of the Yoneda section `f`. -/
theorem sheafifiedRepresentable_section_eq_toSheafify_app
    [HasWeakSheafify J (Type (max u v))]
    {U' U : C} (f : U' ⟶ U) :
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
        (J.sheafifiedRepresentableFunctor.map f) =
      ((sheafificationAdjunction J (Type (max u v))).unit.app
        (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U') (ULift.up f) := by
  have hId :
      J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J])) =
        ((sheafificationAdjunction J (Type (max u v))).unit.app
          (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U) (ULift.up (𝟙 U)) := by
    rfl
  -- Evaluate the morphism `h[U']^# ⟶ h[U]^#` by transporting the identity section along `f`.
  calc
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
        (J.sheafifiedRepresentableFunctor.map f) =
      (h[U]^#[J]).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) := by
          simpa using
            GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality
              (J := J) f (h[U]^#[J]) (𝟙 (h[U]^#[J]))
    _ = (h[U]^#[J]).obj.map f.op
        (((sheafificationAdjunction J (Type (max u v))).unit.app
          (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U) (ULift.up (𝟙 U))) := by
            rw [hId]
    _ = ((sheafificationAdjunction J (Type (max u v))).unit.app
        (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U') (ULift.up f) := by
          let η :
              CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
            (sheafificationAdjunction J (Type (max u v))).unit.app
              (CategoryTheory.uliftYoneda.{max u v}.obj U)
          have hnat := congrFun (NatTrans.naturality η f.op) (ULift.up (𝟙 U))
          simpa [η, CategoryTheory.uliftYoneda] using hnat.symm

/-- Helper for Lemma 7.32.7: every morphism into a sheafified representable is locally induced by
an actual site morphism. -/
theorem sheafifiedRepresentableFunctor_imageSieve_mem
    [HasWeakSheafify J (Type (max u v))]
    {U' U : C} (c : h[U']^#[J] ⟶ h[U]^#[J]) :
    J.sheafifiedRepresentableFunctor.imageSieve c ∈ J U' := by
  let η :
      CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
    (sheafificationAdjunction J (Type (max u v))).unit.app
      (CategoryTheory.uliftYoneda.{max u v}.obj U)
  let x : (h[U]^#[J]).obj.obj (op U') :=
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U' c
  have hx :
      J.sheafifiedRepresentableFunctor.imageSieve c = Presheaf.imageSieve η x := by
    -- Compare the source image sieve with the sheafification image sieve sectionwise.
    ext W g
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨ULift.up l, ?_⟩
      calc
        η.app (op W) (ULift.up l) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (J.sheafifiedRepresentableFunctor.map l) := by
              exact (sheafifiedRepresentable_section_eq_toSheafify_app (J := J) l).symm
        _ = J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (J.sheafifiedRepresentableFunctor.map g ≫ c) := by
              exact congrArg (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W) hl
        _ = (h[U]^#[J]).obj.map g.op x := by
              simpa [x, GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
                (J.uliftSheafifiedRepresentableHomEquiv_naturality g (h[U]^#[J]) c)
    · rintro ⟨l, hl⟩
      refine ⟨ULift.down l, ?_⟩
      apply (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W).injective
      calc
        J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (J.sheafifiedRepresentableFunctor.map (ULift.down l)) =
          η.app (op W) l := by
            exact sheafifiedRepresentable_section_eq_toSheafify_app
              (J := J) (ULift.down l)
        _ = (h[U]^#[J]).obj.map g.op x := hl
        _ = J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (J.sheafifiedRepresentableFunctor.map g ≫ c) := by
              simpa [x, GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
                (J.uliftSheafifiedRepresentableHomEquiv_naturality g (h[U]^#[J]) c).symm
  -- The standard presheaf image-sieve cover becomes exactly the source image sieve.
  simpa [hx] using (Presheaf.imageSieve_mem J η x)

/-- Helper for Lemma 7.32.7: if two source arrows induce the same sheafified-representable map,
their equalizer sieve is covering. -/
theorem sheafifiedRepresentableFunctor_equalizer_mem
    [HasWeakSheafify J (Type (max u v))]
    {U' U : C} (a b : U' ⟶ U)
    (h : J.sheafifiedRepresentableFunctor.map a = J.sheafifiedRepresentableFunctor.map b) :
    Sieve.equalizer a b ∈ J U' := by
  let η :
      CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
    (sheafificationAdjunction J (Type (max u v))).unit.app
      (CategoryTheory.uliftYoneda.{max u v}.obj U)
  have hsection :
      η.app (op U') (ULift.up a) = η.app (op U') (ULift.up b) := by
    -- Equality after sheafification gives equality of the corresponding sheafification sections.
    have h' := congrArg
      (fun α : h[U']^#[J] ⟶ h[U]^#[J] ↦
        α.hom.app (op U')
          (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
            (𝟙 (h[U']^#[J])))) h
    have ha :
        (J.sheafifiedRepresentableFunctor.map a).hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          η.app (op U') (ULift.up a) := by
      calc
        (J.sheafifiedRepresentableFunctor.map a).hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
            (J.sheafifiedRepresentableFunctor.map a) := by
              exact sheafifiedRepresentable_component_eq_section
                (J := J) (α := J.sheafifiedRepresentableFunctor.map a)
        _ = η.app (op U') (ULift.up a) := by
              exact sheafifiedRepresentable_section_eq_toSheafify_app (J := J) a
    have hb :
        (J.sheafifiedRepresentableFunctor.map b).hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          η.app (op U') (ULift.up b) := by
      calc
        (J.sheafifiedRepresentableFunctor.map b).hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
            (J.sheafifiedRepresentableFunctor.map b) := by
              exact sheafifiedRepresentable_component_eq_section
                (J := J) (α := J.sheafifiedRepresentableFunctor.map b)
        _ = η.app (op U') (ULift.up b) := by
              exact sheafifiedRepresentable_section_eq_toSheafify_app (J := J) b
    exact ha.symm.trans (h'.trans hb)
  let xa : ToType ((CategoryTheory.uliftYoneda.{max u v}.obj U).obj (op U')) := ULift.up a
  let xb : ToType ((CategoryTheory.uliftYoneda.{max u v}.obj U).obj (op U')) := ULift.up b
  have hEqSieve :
      Presheaf.equalizerSieve (F := CategoryTheory.uliftYoneda.{max u v}.obj U) xa xb =
        Sieve.equalizer a b := by
    ext W g
    change (CategoryTheory.uliftYoneda.{max u v}.obj U).map g.op xa =
        (CategoryTheory.uliftYoneda.{max u v}.obj U).map g.op xb ↔
      g ≫ a = g ≫ b
    simpa [CategoryTheory.uliftYoneda, xa, xb]
  -- The presheaf equalizer sieve for the sheafification unit is exactly the source equalizer sieve.
  simpa [hEqSieve] using
    (Presheaf.equalizerSieve_mem (J := J) (φ := η) (X := op U') xa xb hsection)

/-- Helper for Lemma 7.32.7: every sheaf admits a locally surjective map from a coproduct of
sheafified representables indexed by all of its local sections. -/
theorem exists_locally_surjective_map_from_sheafified_representables
    [HasWeakSheafify J (Type (max u v))]
    (ℱ : Sheaf J (Type (max u v))) :
    ∃ ι : Type (max u v), ∃ Y : ι → C,
      let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
        Sheaf.instHasColimitsOfShape
      ∃ π : (∐ fun i : ι ↦ h[Y i]^#[J]) ⟶ ℱ,
        Sheaf.IsLocallySurjective π := by
  let ι : Type (max u v) := Σ U : C, (h[U]^#[J] ⟶ ℱ)
  let Y : ι → C := fun i ↦ i.1
  refine ⟨ι, Y, ?_⟩
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let π : (∐ fun i : ι ↦ h[Y i]^#[J]) ⟶ ℱ :=
    Limits.Sigma.desc (fun i : ι ↦ i.2)
  refine ⟨π, ?_⟩
  refine ⟨fun {U} x ↦ ?_⟩
  let α : h[U]^#[J] ⟶ ℱ :=
    (J.uliftSheafifiedRepresentableHomEquiv ℱ U).symm x
  let i : ι := ⟨U, α⟩
  let t :
      ((∐ fun j : ι ↦ h[Y j]^#[J]).obj).obj (op U) :=
    (Limits.Sigma.ι (fun j : ι ↦ h[Y j]^#[J]) i).hom.app (op U)
      (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J])))
  -- Evaluate the chosen coproduct inclusion on the identity section of `h[U]^#`.
  have hι : Limits.Sigma.ι (fun j : ι ↦ h[Y j]^#[J]) i ≫ π = α := by
    simpa [π, i, Y] using
      (Limits.Sigma.ι_desc (fun j : ι ↦ j.2) i)
  have ht : π.hom.app (op U) t = x := by
    calc
    π.hom.app (op U)
        t =
      α.hom.app (op U)
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                k.hom.app (op U)
                  (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U
                    (𝟙 (h[U]^#[J])))) hι
    _ = J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
      rw [sheafifiedRepresentable_component_eq_section (J := J) α]
    _ = x := by
      rw [(J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply]
  have htop : Presheaf.imageSieve π.hom x = ⊤ := by
    calc
      Presheaf.imageSieve π.hom x =
          Presheaf.imageSieve π.hom (π.hom.app (op U) t) := by rw [ht]
      _ = ⊤ := Presheaf.imageSieve_app π.hom t
  rw [htop]
  exact J.top_mem U

/-- Helper for Lemma 7.32.7: every sheaf neighborhood of the point is refined by a representable
neighborhood. -/
theorem typePresentationFunctor_elements_toInverseImageElements_obj_lift
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (Y : p.typeInverseImage.Elements) :
    ∃ X : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements,
      Nonempty
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X ⟶ Y) := by
  obtain ⟨ι, Y₀, π, hπ₀⟩ :=
    exists_locally_surjective_map_from_sheafified_representables (J := J) Y.1
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let X₀ : Discrete ι ⥤ Sheaf J (Type (max u v)) :=
    Discrete.functor (fun i : ι ↦ h[Y₀ i]^#[J])
  let _ : Sheaf.IsLocallySurjective π := hπ₀
  let _ : Epi π := by infer_instance
  let _ : p.typeInverseImage.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction p.typeAdjunction
  have hsurj : Function.Surjective (p.typeInverseImage.map π) := by
    exact (CategoryTheory.epi_iff_surjective _).1 (p.typeInverseImage.map_epi π)
  obtain ⟨z, hz⟩ := hsurj Y.2
  let _ : PreservesColimitsOfSize p.typeInverseImage := p.typeAdjunction.leftAdjoint_preservesColimits
  let hc : IsColimit (Functor.mapCocone p.typeInverseImage (colimit.cocone X₀)) :=
    isColimitOfPreserves p.typeInverseImage (colimit.isColimit X₀)
  -- Decompose the chosen preimage through the preserved coproduct.
  obtain ⟨I, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc z
  let X :
      (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements :=
    Functor.elementsMk _ (Y₀ I.as) x
  refine ⟨X, ⟨CategoryOfElements.homMk _ _ ((colimit.ι X₀ I) ≫ π) ?_⟩⟩
  -- The chosen coproduct component maps exactly to the original target element.
  simpa [X, X₀, MorphismOfTopoiIn.typeInverseImage] using hz

/-- Helper for Lemma 7.32.7: a morphism between two representable neighborhoods lifts locally to
an actual morphism in the source element category after refining the domain neighborhood. -/
theorem typePresentationFunctor_elements_lift_hom
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    {X Y : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements}
    (φ :
      (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X ⟶
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj Y) :
    ∃ Z : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements,
      ∃ t : Z ⟶ X, ∃ u : Z ⟶ Y,
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map t ≫ φ =
          (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map u := by
  let R : Sieve X.1 := J.sheafifiedRepresentableFunctor.imageSieve φ.1
  have hR : R ∈ J X.1 := sheafifiedRepresentableFunctor_imageSieve_mem (J := J) φ.1
  obtain ⟨W, g, hg, w, hw⟩ :=
    typePresentationFunctor_jointly_surjective (J := J) p R hR X.2
  rcases hg with ⟨l, hl⟩
  let Z : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements :=
    Functor.elementsMk _ W w
  let t : Z ⟶ X := CategoryOfElements.homMk _ _ g hw
  have hu :
      (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map l w = Y.2 := by
    -- The chosen local lift lands in the target neighborhood because it factors `φ`.
    have hfactor :
        (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map l w =
          (p.typeInverseImage.map φ.1)
            ((J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map g w) := by
      simpa [Functor.map_comp] using congrArg
        (fun α => (p.typeInverseImage.map α) w) hl
    have hsource :
        (p.typeInverseImage.map φ.1)
            ((J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map g w) =
          (p.typeInverseImage.map φ.1) X.2 := by
      exact congrArg (p.typeInverseImage.map φ.1) hw
    have htarget : (p.typeInverseImage.map φ.1) X.2 = Y.2 := by
      exact φ.2
    exact hfactor.trans (hsource.trans htarget)
  let u : Z ⟶ Y := CategoryOfElements.homMk _ _ l hu
  refine ⟨Z, t, u, ?_⟩
  -- After refinement, the target morphism is literally induced by the lifted source arrow.
  apply CategoryOfElements.ext p.typeInverseImage
  exact hl.symm

/-- Helper for Lemma 7.32.7: if two source morphisms become equal after comparison, they are equal
after refining the domain neighborhood by a covering sieve. -/
theorem typePresentationFunctor_elements_equalize_of_map_eq
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    {X Y : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements}
    (f g : X ⟶ Y)
    (h :
      (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f =
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g) :
    ∃ Z : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements,
      ∃ t : Z ⟶ X, t ≫ f = t ≫ g := by
  let R : Sieve X.1 := Sieve.equalizer f.1 g.1
  have hmap :
      J.sheafifiedRepresentableFunctor.map f.1 =
        J.sheafifiedRepresentableFunctor.map g.1 := by
    simpa using congrArg Subtype.val h
  have hR : R ∈ J X.1 := sheafifiedRepresentableFunctor_equalizer_mem (J := J) f.1 g.1 hmap
  obtain ⟨W, t, ht, w, hw⟩ :=
    typePresentationFunctor_jointly_surjective (J := J) p R hR X.2
  let Z : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements :=
    Functor.elementsMk _ W w
  let k : Z ⟶ X := CategoryOfElements.homMk _ _ t hw
  refine ⟨Z, k, ?_⟩
  apply CategoryOfElements.ext (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage)
  exact ht

/-- Helper for Lemma 7.32.7: the neighborhood category of
`U ↦ p^{-1}(h_U^#)` is cofiltered. -/
instance typePresentationFunctor_elements_isCofiltered
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    IsCofiltered (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements := by
  let _ : PreservesFiniteLimits (p⁻¹) := by
    simpa using MorphismOfTopoiIn.inverseImage_preservesFiniteLimits p
  let _ : PreservesFiniteLimits p.typeInverseImage := by infer_instance
  letI : IsCofiltered p.typeInverseImage.Elements :=
    Functor.isCofiltered_elements p.typeInverseImage
  refine
    { cone_objs := ?_
      cone_maps := ?_
      nonempty := ?_ }
  · intro X Y
    -- Start from the target-side common predecessor and then refine it back to a representable
    -- neighborhood so both comparison arrows come from actual source neighborhoods.
    let Zt : p.typeInverseImage.Elements :=
      IsCofiltered.min
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X)
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj Y)
    let α : Zt ⟶ (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X :=
      IsCofiltered.minToLeft _ _
    let β : Zt ⟶ (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj Y :=
      IsCofiltered.minToRight _ _
    obtain ⟨Z₀, ⟨m⟩⟩ :=
      typePresentationFunctor_elements_toInverseImageElements_obj_lift (J := J) p Zt
    obtain ⟨Z₁, t₁, u₁, hu₁⟩ :=
      typePresentationFunctor_elements_lift_hom (J := J) p (φ := m ≫ α)
    obtain ⟨Z₂, t₂, u₂, hu₂⟩ :=
      typePresentationFunctor_elements_lift_hom (J := J) p
        (φ := (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map t₁ ≫
          m ≫ β)
    exact ⟨Z₂, t₂ ≫ u₁, u₂, trivial⟩
  · intro X Y f g
    -- Equalize the compared arrows in the target element category, then pull that equality back
    -- along the refined representable neighborhood to equalize the original source arrows.
    let Zt : p.typeInverseImage.Elements :=
      IsCofiltered.eq
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f)
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g)
    let α : Zt ⟶ (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X :=
      IsCofiltered.eqHom
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f)
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g)
    obtain ⟨Z₀, ⟨m⟩⟩ :=
      typePresentationFunctor_elements_toInverseImageElements_obj_lift (J := J) p Zt
    obtain ⟨Z₁, t₁, u₁, hu₁⟩ :=
      typePresentationFunctor_elements_lift_hom (J := J) p (φ := m ≫ α)
    have hEq :
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map (u₁ ≫ f) =
          (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map (u₁ ≫ g) := by
      calc
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map (u₁ ≫ f) =
          (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map u₁ ≫
            (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f := by
              simp
        _ = (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map t₁ ≫
            m ≫ α ≫
              (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f := by
                simpa [Category.assoc] using congrArg
                  (fun k =>
                    k ≫ (typePresentationFunctor_elements_toInverseImageElements
                      (J := J) p).map f) hu₁.symm
        _ = (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map t₁ ≫
            m ≫ α ≫
              (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g := by
                rw [IsCofiltered.eq_condition]
        _ = (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map u₁ ≫
            (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g := by
                simpa [Category.assoc] using congrArg
                  (fun k =>
                    k ≫ (typePresentationFunctor_elements_toInverseImageElements
                      (J := J) p).map g) hu₁
        _ = (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map (u₁ ≫ g) := by
              simp
    obtain ⟨Z₂, t₂, ht₂⟩ :=
      typePresentationFunctor_elements_equalize_of_map_eq (J := J) p (u₁ ≫ f) (u₁ ≫ g) hEq
    exact ⟨Z₂, t₂ ≫ u₁, by simpa [Category.assoc] using ht₂⟩
  · obtain ⟨Y⟩ := IsCofiltered.nonempty (C := p.typeInverseImage.Elements)
    obtain ⟨X, -⟩ :=
      typePresentationFunctor_elements_toInverseImageElements_obj_lift (J := J) p Y
    exact ⟨X⟩

/-- Helper for Lemma 7.32.7: the element category of `U ↦ p^{-1}(h_U^#)` is initially small. -/
instance typePresentationFunctor_elements_initiallySmall
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    InitiallySmall.{max u v} (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements := by
  classical
  exact initiallySmall_of_essentiallySmall _

/-- For a point `p` of the topos `Sh(C)`, the functor `U ↦ p^{-1}(h_U^#)` defines the
associated point of the site `(C, J)`. -/
noncomputable def toSitePoint
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    GrothendieckTopology.Point.{max u v} J := by
  -- Route correction: the site point only needs cofilteredness of the category of elements of
  -- `U ↦ p^{-1}(h_U^#)`, not the stronger representably-flat packaging from `typesPoint.comap`.
  refine
    { fiber := J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage
      jointly_surjective := ?_ }
  intro U R hR x
  simpa using typePresentationFunctor_jointly_surjective (J := J) p R hR x

/-- Helper for Lemma 7.32.7: on sheafified representables, the stalk functor of `p.toSitePoint`
agrees with `p.typeInverseImage`. -/
noncomputable def toSitePoint_comparison_sheafifiedRepresentableIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    :
    J.sheafifiedRepresentableFunctor ⋙ p.toSitePoint.sheafFiber ≅
      J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage := by
  -- Compare the sheaf fiber on `h_U^#` with the presheaf fiber on `uliftYoneda.obj U`,
  -- then identify that presheaf fiber with the defining fiber functor of `p.toSitePoint`.
  simpa [GrothendieckTopology.sheafifiedRepresentable, GrothendieckTopology.sheafifiedRepresentableFunctor,
    MorphismOfTopoiIn.typeInverseImage, toSitePoint] using
    (Functor.associator CategoryTheory.uliftYoneda.{max u v}
      (presheafToSheaf J (Type (max u v))) p.toSitePoint.sheafFiber) ≪≫
      (Functor.isoWhiskerLeft CategoryTheory.uliftYoneda.{max u v}
        (p.toSitePoint.presheafToSheafCompSheafFiberIso (Type (max u v)))) ≪≫
      ((Functor.isoWhiskerRight CategoryTheory.uliftYonedaIsoShrinkYoneda
        p.toSitePoint.presheafFiber) ≪≫
          p.toSitePoint.shrinkYonedaCompPresheafFiberIso)

/-- Helper for Lemma 7.32.7: on sheafified representables, the stalk functor of `p.toSitePoint`
agrees with `p.typeInverseImage`. -/
noncomputable def toSitePoint_comparison_app_sheafifiedRepresentable
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (U : C) :
    (p.toSitePoint.sheafFiber.obj (h[U]^#[J])) ≅
      p.typeInverseImage.obj (h[U]^#[J]) :=
  (toSitePoint_comparison_sheafifiedRepresentableIso (J := J) p).app U

/-- Helper for Lemma 7.32.7: sections of `p_* E` over a sheafified representable are functions on
the corresponding fiber of `p.toSitePoint`. -/
noncomputable def toSitePoint_typePushforward_sectionEquiv
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) (U : C) :
    ((p.typePushforward.obj E).obj.obj (op U)) ≃
      (((toSitePoint (J := J) p).fiber.obj U) → E) := by
  -- Rewrite sections of `p_* E` as morphisms from `h_U^#`, transpose them across the
  -- adjunction `p⁻¹ ⊣ p_*`, and then read the result as the defining fiber of `p.toSitePoint`.
  let e₁ :=
    (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm
  let e₂ := (p.typeAdjunction.homEquiv (h[U]^#[J]) E).symm
  simpa [MorphismOfTopoiIn.typeInverseImage, toSitePoint] using e₁.trans e₂

/-- Helper for Lemma 7.32.7: restricting a section of `p_* E` corresponds to precomposing the
associated function with the map on fibers of `p.toSitePoint`. -/
theorem toSitePoint_typePushforward_sectionEquiv_naturality_left
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) {U V : C} (g : V ⟶ U)
    (s : ((p.typePushforward.obj E).obj.obj (op U))) :
    toSitePoint_typePushforward_sectionEquiv (J := J) p E V
        (((p.typePushforward.obj E).obj.map g.op) s) =
      fun x ↦
        toSitePoint_typePushforward_sectionEquiv (J := J) p E U s
          (((toSitePoint (J := J) p).fiber.map g) x) := by
  let t : ((toSitePoint (J := J) p).fiber.obj V) → E :=
    ((toSitePoint (J := J) p).fiber.map g) ≫
      toSitePoint_typePushforward_sectionEquiv (J := J) p E U s
  let αV :
      h[V]^#[J] ⟶ p.typePushforward.obj E :=
    (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) V).symm
      (((p.typePushforward.obj E).obj.map g.op) s)
  -- First identify the restricted section with precomposition on the sheafified representable.
  apply (p.typeAdjunction.homEquiv (h[V]^#[J]) E).injective
  have hsection :
      αV =
      (J.sheafifiedRepresentableFunctor.map g) ≫
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
    -- This is exactly naturality of `Hom(h_U^#, -) ≃ sections over U`.
    apply (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) V).injective
    calc
      J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) V
          αV =
        ((p.typePushforward.obj E).obj.map g.op) s := by
            exact Equiv.apply_symm_apply _ _
      _ = ((p.typePushforward.obj E).obj.map g.op)
            (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U
              ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s)) := by
            rw [Equiv.apply_symm_apply]
      _ = J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) V
            ((J.sheafifiedRepresentableFunctor.map g) ≫
              (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s) := by
            symm
            exact
              J.uliftSheafifiedRepresentableHomEquiv_naturality g
                (p.typePushforward.obj E)
                ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s)
  have happlyU :
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
          (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s) =
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
    simpa [toSitePoint_typePushforward_sectionEquiv] using
      (Equiv.apply_symm_apply
        (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
        ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s))
  have hadj :
      (p.typeAdjunction.homEquiv (h[V]^#[J]) E) t =
        (J.sheafifiedRepresentableFunctor.map g) ≫
          (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
    -- Then move the left action across the adjunction equivalence.
    calc
      (p.typeAdjunction.homEquiv (h[V]^#[J]) E) t =
        (J.sheafifiedRepresentableFunctor.map g) ≫
          (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
            (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s) := by
              simpa [t, GrothendieckTopology.sheafifiedRepresentable,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                MorphismOfTopoiIn.typeInverseImage, toSitePoint] using
                (p.typeAdjunction.homEquiv_naturality_left
                  ((J.uliftSheafifiedRepresentableFunctor).map g)
                  (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s))
      _ =
        (J.sheafifiedRepresentableFunctor.map g) ≫
          (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
              rw [happlyU]
  calc
    (p.typeAdjunction.homEquiv (h[V]^#[J]) E)
        (toSitePoint_typePushforward_sectionEquiv (J := J) p E V
          (((p.typePushforward.obj E).obj.map g.op) s)) =
      (p.typeAdjunction.homEquiv (h[V]^#[J]) E)
        ((p.typeAdjunction.homEquiv (h[V]^#[J]) E).symm αV) := by
          rfl
    _ = αV := by
          exact Equiv.apply_symm_apply _ _
    _ = (p.typeAdjunction.homEquiv (h[V]^#[J]) E) t := by
          rw [hsection, hadj.symm]
    _ = (p.typeAdjunction.homEquiv (h[V]^#[J]) E)
          (fun x ↦
            toSitePoint_typePushforward_sectionEquiv (J := J) p E U s
              (((toSitePoint (J := J) p).fiber.map g) x)) := by
          rfl

/-- Helper for Lemma 7.32.7: the sectionwise description of `p_* E` packages into an isomorphism
of underlying presheaves. -/
noncomputable def toSitePoint_typePushforward_presheafObjIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) :
    (p.typePushforward.obj E).obj ≅ (toSitePoint (J := J) p).skyscraperPresheaf E := by
  let q := toSitePoint (J := J) p
  let e :
      ∀ U : Cᵒᵖ,
        ((p.typePushforward.obj E).obj.obj U) ≅ (q.skyscraperPresheaf E).obj U :=
    fun U ↦
      (Equiv.toIso (toSitePoint_typePushforward_sectionEquiv (J := J) p E U.unop)) ≪≫
        (Types.productIso (fun _ : q.fiber.obj U.unop ↦ E)).symm
  -- Package the pointwise section equivalences into a presheaf isomorphism.
  refine NatIso.ofComponents e ?_
  intro U V f
  funext s
  apply Types.limit_ext
  intro x
  cases x with
  | mk x =>
  -- After rewriting the skyscraper sections as functions, naturality is exactly the left
  -- sectionwise naturality statement proved above.
  calc
    Pi.π (fun _ : q.fiber.obj V.unop ↦ E) x
        ((e V).hom (((p.typePushforward.obj E).obj.map f) s)) =
      toSitePoint_typePushforward_sectionEquiv (J := J) p E V.unop
        (((p.typePushforward.obj E).obj.map f) s) x := by
          change
            ((Types.productIso (fun _ : q.fiber.obj V.unop ↦ E)).inv ≫
              Pi.π (fun _ : q.fiber.obj V.unop ↦ E) x)
              (toSitePoint_typePushforward_sectionEquiv (J := J) p E V.unop
                (((p.typePushforward.obj E).obj.map f) s)) =
              _
          rw [Types.productIso_inv_comp_π]
    _ =
      toSitePoint_typePushforward_sectionEquiv (J := J) p E U.unop s
        (q.fiber.map f.unop x) := by
          simpa [q] using
            congrFun
              (toSitePoint_typePushforward_sectionEquiv_naturality_left
                (J := J) p E f.unop s) x
    _ =
      Pi.π (fun _ : q.fiber.obj V.unop ↦ E) x
        ((q.skyscraperPresheaf E).map f ((e U).hom s)) := by
          change
            (p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s
                (q.fiber.map f.unop x) =
              (((Pi.map' (q.fiber.map f.unop) (fun _ ↦ 𝟙 E)) ≫
                  Pi.π (fun _ : q.fiber.obj V.unop ↦ E) x)
                (((Types.productIso (fun _ : q.fiber.obj U.unop ↦ E)).inv
                  ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s))))
          rw [Pi.map'_comp_π]
          rw [Category.comp_id]
          symm
          simpa using
            congrFun
              (Types.productIso_inv_comp_π
                (fun _ : q.fiber.obj U.unop ↦ E) (q.fiber.map f.unop x))
              ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s)

/-- Helper for Lemma 7.32.7: maps `E ⟶ E'` act on the sectionwise comparison by postcomposition
on the target functions. -/
theorem toSitePoint_typePushforward_sectionEquiv_naturality_right
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    {E E' : Type (max u v)} (f : E ⟶ E') (U : C)
    (s : ((p.typePushforward.obj E).obj.obj (op U))) :
    toSitePoint_typePushforward_sectionEquiv (J := J) p E' U
        (((p.typePushforward.map f).hom.app (op U)) s) =
      fun x ↦ f (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s x) := by
  let t : ((toSitePoint (J := J) p).fiber.obj U) → E' :=
    toSitePoint_typePushforward_sectionEquiv (J := J) p E U s ≫ f
  let αU' :
      h[U]^#[J] ⟶ p.typePushforward.obj E' :=
    (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E') U).symm
      (((p.typePushforward.map f).hom.app (op U)) s)
  -- First identify the action of `f` on sections with postcomposition in the Hom-set.
  apply (p.typeAdjunction.homEquiv (h[U]^#[J]) E').injective
  have hsection :
      αU' =
      (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s ≫
        (p.typePushforward.map f) := by
    -- This is naturality of `Hom(h_U^#, -) ≃ sections over U` in the sheaf variable.
    apply (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E') U).injective
    calc
      J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E') U
          αU' =
        ((p.typePushforward.map f).hom.app (op U)) s := by
            exact Equiv.apply_symm_apply _ _
      _ = ((p.typePushforward.map f).hom.app (op U))
            (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U
              ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s)) := by
            rw [Equiv.apply_symm_apply]
      _ = J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E') U
            ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s ≫
              (p.typePushforward.map f)) := by
            symm
            exact
              J.uliftSheafifiedRepresentableHomEquiv_comp
                ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s)
                (p.typePushforward.map f)
  have happlyU :
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
          (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s) =
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
    simpa [toSitePoint_typePushforward_sectionEquiv] using
      (Equiv.apply_symm_apply
        (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
        ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s))
  have hadj :
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E') t =
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s ≫
          (p.typePushforward.map f) := by
    -- Finally move postcomposition across the transported adjunction.
    calc
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E') t =
        (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
            (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s) ≫
          (p.typePushforward.map f) := by
              simpa [t, GrothendieckTopology.sheafifiedRepresentable,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                MorphismOfTopoiIn.typeInverseImage, toSitePoint] using
                (p.typeAdjunction.homEquiv_naturality_right
                  (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s)
                  f)
      _ =
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s ≫
          (p.typePushforward.map f) := by
              rw [happlyU]
  calc
    (p.typeAdjunction.homEquiv (h[U]^#[J]) E')
        (toSitePoint_typePushforward_sectionEquiv (J := J) p E' U
          (((p.typePushforward.map f).hom.app (op U)) s)) =
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E')
        ((p.typeAdjunction.homEquiv (h[U]^#[J]) E').symm αU') := by
          rfl
    _ = αU' := by
          exact Equiv.apply_symm_apply _ _
    _ = (p.typeAdjunction.homEquiv (h[U]^#[J]) E') t := by
          rw [hsection, hadj.symm]
    _ = (p.typeAdjunction.homEquiv (h[U]^#[J]) E')
          (fun x ↦ f (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s x)) := by
          rfl

/-- Helper for Lemma 7.32.7: the direct image of a topos point agrees with the skyscraper sheaf
functor of the associated site point. -/
noncomputable def toSitePoint_typePushforwardIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    p.typePushforward ≅ (toSitePoint (J := J) p).skyscraperSheafFunctor := by
  let q := toSitePoint (J := J) p
  let ePresheaf :
      p.typePushforward ⋙ sheafToPresheaf J (Type (max u v)) ≅ q.skyscraperPresheafFunctor := by
    refine NatIso.ofComponents (toSitePoint_typePushforward_presheafObjIso (J := J) p) ?_
    intro E E' f
    ext U s
    apply Types.limit_ext
    intro x
    cases x with
    | mk x =>
    -- After rewriting the skyscraper sections as functions, naturality is exactly the right
    -- sectionwise naturality statement proved above.
    calc
      Pi.π (fun _ : q.fiber.obj U.unop ↦ E') x
          ((toSitePoint_typePushforward_presheafObjIso (J := J) p E').hom.app U
            (((p.typePushforward.map f).hom.app U) s)) =
        toSitePoint_typePushforward_sectionEquiv (J := J) p E' U.unop
          (((p.typePushforward.map f).hom.app U) s) x := by
            change
              ((Types.productIso (fun _ : q.fiber.obj U.unop ↦ E')).inv ≫
                Pi.π (fun _ : q.fiber.obj U.unop ↦ E') x)
                (toSitePoint_typePushforward_sectionEquiv (J := J) p E' U.unop
                  (((p.typePushforward.map f).hom.app U) s)) =
                _
            rw [Types.productIso_inv_comp_π]
      _ = f (toSitePoint_typePushforward_sectionEquiv (J := J) p E U.unop s x) := by
            simpa using
              congrFun
                (toSitePoint_typePushforward_sectionEquiv_naturality_right
                  (J := J) p f U.unop s) x
      _ =
        Pi.π (fun _ : q.fiber.obj U.unop ↦ E') x
          ((q.skyscraperPresheafFunctor.map f).app U
            ((toSitePoint_typePushforward_presheafObjIso (J := J) p E).hom.app U s)) := by
            change
              f ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s x) =
                Pi.π (fun _ : q.fiber.obj U.unop ↦ E') x
                  ((Limits.Pi.map (fun _ : q.fiber.obj U.unop ↦ f))
                    (((Types.productIso (fun _ : q.fiber.obj U.unop ↦ E)).inv
                      ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s))))
            rw [Types.pi_map_π_apply']
            exact congrArg f <|
              (congrFun
                (Types.productIso_inv_comp_π
                  (fun _ : q.fiber.obj U.unop ↦ E) x)
                ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s)).symm
  -- Reflect the presheaf comparison back to sheaves through the fully faithful forgetful functor.
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf J (Type (max u v))) ePresheaf

/-- Lemma 7.32.7: for a point `p` of the topos `Sh(C)`, the functor
`U ↦ p^{-1}(h_U^#)` defines a point of the site `(C, J)`, and the stalk functor of that site
point recovers the inverse-image functor of `p`. -/
noncomputable def toSitePoint_sheafFiberIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    (toSitePoint (J := J) p).sheafFiber ≅ p.typeInverseImage :=
  -- Compare the two right adjoints first, then recover the left-adjoint comparison by the
  -- uniqueness of left adjoints to a fixed right adjoint.
  Adjunction.leftAdjointUniq
    ((toSitePoint (J := J) p).skyscraperSheafAdjunction)
    (p.typeAdjunction.ofNatIsoRight (toSitePoint_typePushforwardIso (J := J) p))

-- Proof sketch: evaluate the canonical natural isomorphism
-- `p.toSitePoint_sheafFiberIso` on a sheaf and use the identity law for isomorphisms.
/-- The component of `toSitePoint_sheafFiberIso` followed by its inverse is the identity. -/
theorem toSitePoint_sheafFiberIso_hom_inv_app
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (F : Sheaf J (Type (max u v))) :
    (MorphismOfTopoiIn.toSitePoint_sheafFiberIso (J := J) p).hom.app F ≫
        (MorphismOfTopoiIn.toSitePoint_sheafFiberIso (J := J) p).inv.app F =
      𝟙 _ := by
  -- Once the natural isomorphism is fixed, the componentwise identity is formal.
  simpa using Iso.hom_inv_id_app (MorphismOfTopoiIn.toSitePoint_sheafFiberIso (J := J) p) F

end MorphismOfTopoiIn

end CategoryTheory
