module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_15_2
public import stacks_project.Chap07.Lemma_7_32_7

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor
open GrothendieckTopology
open GrothendieckTopology.Point

universe u v w w'

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.32.8:
- primary domain: points of Grothendieck sites and the induced points of the associated topoi;
- sampled owner API:
  `Functor.IsContinuous`,
  `Point.skyscraperPresheaf`,
  `MorphismOfTopoiIn.typePushforward`,
  `MorphismOfTopoiIn.typeInverseImage`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`, together with the
  topos-point bridge functors `typePushforward` and `typeInverseImage` from Definition 7.32.1;
- source/core/bridge triage:
  `source-facing`: the fiber functor of a site point `p : J.Point` and the induced composite
    point of `Sh(C)`;
  `core/canonical`: the canonical equivalence `typeEquiv`, the skyscraper sheaf functor of a
    site point, and adjoint uniqueness;
  `bridge/view`: the comparison isomorphisms identifying the composite point determined by
    `p.fiber` with `p.toToposPoint`.

Primitive data are only the site point `p`. The source proof computes the direct image on a set
`E` as the sheaf `U ↦ (p.fiber.obj U → E)`, proves continuity from that explicit formula, and then
recovers the inverse-image comparison formally from uniqueness of left adjoints.
-/

/- Lemma 7.32.8 (1): after replacing the powerset site from Remark 7.15.3 by the canonically
equivalent jointly surjective site on `Type`, the corresponding sheaf category is equivalent to
`Sh(pt)`, identified here with `Type`, via the standard equivalence `typeEquiv`. -/
recall typeEquiv : Type w ≌ Sheaf typesGrothendieckTopology (Type w)

private theorem pointFiber_typesSite_coverPreserving
    (p : Point.{w} J) :
    CoverPreserving J typesGrothendieckTopology p.fiber :=
  ⟨fun {X} {S} hS x ↦ by
    rcases p.jointly_surjective S hS x with ⟨Y, f, hf, y, hy⟩
    exact ⟨Y, f, fun _ ↦ y, hf, funext fun _ ↦ hy.symm⟩⟩

/-- Helper for Lemma 7.32.8: compatibility over the jointly surjective site on `Type` is checked
by evaluating sections pointwise and refining equalized points through the cofiltered category of
elements of `p.fiber`. -/
private theorem typesSheaf_section_ext
    (ℱ : Sheaf typesGrothendieckTopology.{w} (Type w')) {X : Type w}
    {s t : ℱ.obj.obj (op X)}
    (h : ∀ x : X,
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x)) s =
        ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x)) t) :
    s = t := by
  -- Separatedness for the covering sieve of constant maps reduces equality to all points of `X`.
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.2).isSeparated
    (discreteSieve X) (discreteSieve_mem X)).ext
  intro Y f hf
  rcases hf with ⟨x, hx⟩
  have hf' : f = (↾fun _ : Y => PUnit.unit) ≫ (↾fun _ : PUnit => x) := by
    funext y
    exact hx y
  rw [hf', op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply]
  exact congrArg (fun z ↦ ℱ.obj.map (Opposite.op (↾fun _ : Y => PUnit.unit)) z) (h x)

/-- Helper for Lemma 7.32.8: two fiber elements with the same image in `p.fiber.obj Z`
admit a common refinement in the category of elements of `p.fiber`. -/
private theorem pointFiber_common_refinement
    (p : Point.{w} J) {Y₁ Y₂ Z : C}
    {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z}
    {y₁ : p.fiber.obj Y₁} {y₂ : p.fiber.obj Y₂}
    (h : p.fiber.map g₁ y₁ = p.fiber.map g₂ y₂) :
    ∃ (V : C) (a₁ : V ⟶ Y₁) (a₂ : V ⟶ Y₂) (v : p.fiber.obj V),
      p.fiber.map a₁ v = y₁ ∧ p.fiber.map a₂ v = y₂ ∧ a₁ ≫ g₁ = a₂ ≫ g₂ := by
  let α₁ : p.fiber.elementsMk Y₁ y₁ ⟶ p.fiber.elementsMk Z (p.fiber.map g₂ y₂) := ⟨g₁, h⟩
  let α₂ : p.fiber.elementsMk Y₂ y₂ ⟶ p.fiber.elementsMk Z (p.fiber.map g₂ y₂) := ⟨g₂, rfl⟩
  -- Cofilteredness of the category of elements produces the required comparison square.
  obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
  rw [Subtype.ext_iff] at fac
  have hq₁ : p.fiber.map q₁.1 z.2 = y₁ := by
    exact q₁.2
  have hq₂ : p.fiber.map q₂.1 z.2 = y₂ := by
    exact q₂.2
  exact ⟨z.1, q₁.1, q₂.1, z.2, hq₁, hq₂, fac⟩

/-- Helper for Lemma 7.32.8: compatibility over the jointly surjective site on `Type` is checked
by evaluating sections pointwise and refining equalized points through the cofiltered category of
elements of `p.fiber`. -/
private theorem pointFiber_typesSite_compatiblePreserving
    (p : Point.{w} J) :
    CompatiblePreserving typesGrothendieckTopology p.fiber := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- Equality of sections on the type-site is detected pointwise on the indexing type `X`.
  apply typesSheaf_section_ext ℱ
  intro x₀
  let y₁ : p.fiber.obj Y₁ := f₁ x₀
  let y₂ : p.fiber.obj Y₂ := f₂ x₀
  have hy : p.fiber.map g₁ y₁ = p.fiber.map g₂ y₂ := by
    simpa [y₁, y₂] using congrFun e x₀
  obtain ⟨V, a₁, a₂, v, hv₁, hv₂, fac⟩ := pointFiber_common_refinement p hy
  -- After refining to an actual square in `C`, the compatibility hypothesis applies directly.
  have hcomp :
      ℱ.obj.map (p.fiber.map a₁).op (x g₁ hg₁) =
        ℱ.obj.map (p.fiber.map a₂).op (x g₂ hg₂) := by
    simpa using hx a₁ a₂ hg₁ hg₂ fac
  -- Pulling back along the refined point `v : PUnit ⟶ p.fiber.obj V` recovers the value at `x₀`.
  have hleft :
      (↾fun _ : PUnit => v) ≫ p.fiber.map a₁ =
        (↾fun _ : PUnit => x₀) ≫ f₁ := by
    funext _
    simp [y₁, hv₁]
  have hright :
      (↾fun _ : PUnit => v) ≫ p.fiber.map a₂ =
        (↾fun _ : PUnit => x₀) ≫ f₂ := by
    funext _
    simp [y₂, hv₂]
  have hcomp_point :
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
          (ℱ.obj.map (p.fiber.map a₁).op (x g₁ hg₁)) =
        ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
          (ℱ.obj.map (p.fiber.map a₂).op (x g₂ hg₂)) :=
    congrArg (fun s ↦ ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v)) s) hcomp
  have hrewrite_left :
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
          (ℱ.obj.map (p.fiber.map a₁).op (x g₁ hg₁)) =
        ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x₀))
          (ℱ.obj.map f₁.op (x g₁ hg₁)) := by
    simpa [op_comp, FunctorToTypes.map_comp_apply] using
      congrArg (fun k ↦ ℱ.obj.map k.op (x g₁ hg₁)) hleft
  have hrewrite_right :
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
          (ℱ.obj.map (p.fiber.map a₂).op (x g₂ hg₂)) =
        ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x₀))
          (ℱ.obj.map f₂.op (x g₂ hg₂)) := by
    simpa [op_comp, FunctorToTypes.map_comp_apply] using
      congrArg (fun k ↦ ℱ.obj.map k.op (x g₂ hg₂)) hright
  calc
    ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x₀))
        (ℱ.obj.map f₁.op (x g₁ hg₁)) =
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
        (ℱ.obj.map (p.fiber.map a₁).op (x g₁ hg₁)) := hrewrite_left.symm
    _ =
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
        (ℱ.obj.map (p.fiber.map a₂).op (x g₂ hg₂)) := hcomp_point
    _ =
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x₀))
        (ℱ.obj.map f₂.op (x g₂ hg₂)) := hrewrite_right

/-- Helper for Lemma 7.32.8: after evaluating the type-site equivalence at a set `E` and
precomposing along the fiber functor of `p`, one obtains the skyscraper presheaf
`U ↦ (p.fiber.obj U → E)`. -/
noncomputable def pointFiber_typesSite_typeEquiv_obj_presheafIso
    (p : Point.{w} J) (E : Type w) :
    p.fiber.op ⋙ ((typeEquiv.{w}.functor).obj E).obj ≅ p.skyscraperPresheaf E := by
  -- Evaluate the canonical type-site equivalence on `E`, then precompose with `p.fiber.op`.
  simpa [GrothendieckTopology.Point.skyscraperPresheaf,
    GrothendieckTopology.Point.skyscraperPresheafFunctor,
    GrothendieckTopology.Point.typesPoint] using
    ((Functor.isoWhiskerRight typesPointSkyscraperSheafFunctorIso
      (sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
        (Functor.whiskeringLeft _ _ _).obj p.fiber.op)).app E)

/-- Helper for Lemma 7.32.8: the fiber functor of a site point is continuous for the canonical
site on `Type`. -/
instance pointFiber_typesSite_isContinuous (p : Point.{w} J) :
    Functor.IsContinuous p.fiber J typesGrothendieckTopology := by
  exact Functor.isContinuous_of_coverPreserving
    (pointFiber_typesSite_compatiblePreserving p) (pointFiber_typesSite_coverPreserving p)

section

variable (p : Point.{w} J)
variable [LocallySmall.{w} C]
variable [HasSheafify J (Type w)]
variable [HasSheafify typesGrothendieckTopology (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, HasLeftKanExtension p.fiber.op P]
variable [PreservesFiniteLimits
  (lan p.fiber.op : (Cᵒᵖ ⥤ Type w) ⥤ Type wᵒᵖ ⥤ Type w)]

/-- Helper for Lemma 7.32.8: the morphism of topoi induced by the point fiber functor, with the
`Type w` universe fixed explicitly for module-mode elaboration. -/
noncomputable def pointFiber_typesSite_morphism (p : Point.{w} J)
    [∀ P : Cᵒᵖ ⥤ Type w, p.fiber.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (lan p.fiber.op : (Cᵒᵖ ⥤ Type w) ⥤ Type wᵒᵖ ⥤ Type w)] :
    MorphismOfTopoiIn J typesGrothendieckTopology.{w} := by
  letI : PreservesFiniteLimits
      (p.fiber.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Type wᵒᵖ ⥤ Type w) := by
    infer_instance
  letI : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback p.fiber (Type w) J
        typesGrothendieckTopology) :=
    Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
      p.fiber (Type w) J typesGrothendieckTopology
  exact
    { inverseImageFunctor := LeftExactFunctor.of
        (Functor.sheafPullbackConstruction.sheafPullback p.fiber (Type w) J
          typesGrothendieckTopology)
      pushforward := p.fiber.sheafPushforwardContinuous (Type w) J typesGrothendieckTopology
      adjunction := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous p.fiber
        (Type w) J typesGrothendieckTopology }

/-- Helper for Lemma 7.32.8: the composite point after identifying the terminal topos with the
canonical type site, with its universe fixed explicitly. -/
noncomputable def pointFiber_typesSite_compositeToposPoint (p : Point.{w} J)
    [∀ P : Cᵒᵖ ⥤ Type w, p.fiber.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (lan p.fiber.op : (Cᵒᵖ ⥤ Type w) ⥤ Type wᵒᵖ ⥤ Type w)] :
    MorphismOfTopoiIn J typesGrothendieckTopology.{w} :=
  (pointFiber_typesSite_morphism p).comp (MorphismOfTopoiIn.id typesGrothendieckTopology.{w})

/-- Helper for Lemma 7.32.8: on sheaves, the direct image along `p.fiber` sends the canonical
type-site sheaf attached to `E` to the skyscraper sheaf of `p`. -/
noncomputable def pointFiber_typesSite_pushforwardIso_to_skyscraper
    :
    typeEquiv.{w}.functor ⋙ p.fiber.sheafPushforwardContinuous (Type w) J
        typesGrothendieckTopology ≅
      p.skyscraperSheafFunctor := by
  -- Compare the underlying presheaves first; fully faithfulness of `sheafToPresheaf` then lifts
  -- the source-level computation to a sheaf-level comparison.
  refine ((fullyFaithfulSheafToPresheaf J (Type w)).whiskeringRight (Type w)).preimageIso ?_
  let h₁ :
      typeEquiv.{w}.functor ⋙ p.fiber.sheafPushforwardContinuous (Type w) J
          typesGrothendieckTopology ⋙ sheafToPresheaf J (Type w) ≅
        typeEquiv.{w}.functor ⋙ sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
          (Functor.whiskeringLeft _ _ _).obj p.fiber.op :=
    Functor.isoWhiskerLeft typeEquiv.{w}.functor
      (p.fiber.sheafPushforwardContinuousCompSheafToPresheafIso
        (Type w) J typesGrothendieckTopology)
  let h₂ :
      typeEquiv.{w}.functor ⋙ sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
          (Functor.whiskeringLeft _ _ _).obj p.fiber.op ≅
        p.skyscraperSheafFunctor ⋙ sheafToPresheaf J (Type w) := by
    simpa [GrothendieckTopology.Point.skyscraperSheafFunctor,
      GrothendieckTopology.Point.skyscraperPresheafFunctor,
      GrothendieckTopology.Point.typesPoint] using
      Functor.isoWhiskerRight typesPointSkyscraperSheafFunctorIso
        (sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
          (Functor.whiskeringLeft _ _ _).obj p.fiber.op)
  exact h₁ ≪≫ h₂

-- Proof sketch: clause (2) yields a morphism of topoi from sheaves on the canonical type site to
-- `Sh(C)`, and composing this with the canonical point of `Sh(pt)` coming from `typeEquiv`
-- produces the point `p.toToposPoint` from Lemma 7.32.7. The companion isomorphism identifies
-- the inverse-image functor of the composite with that of `p.toToposPoint`.
/-- Lemma 7.32.8: after identifying `Sh(pt)` with sheaves on `Type` via `typeEquiv`, the
composite of the morphism of topoi induced by `p.fiber` with this canonical point of `Sh(pt)` is
canonically identified with the point `p.toToposPoint` of `Sh(C)`. -/
noncomputable def pointFiber_typesSite_compositeToposPoint_pushforwardIso
      :
      (pointFiber_typesSite_compositeToposPoint p).typePushforward ≅
        (p.toToposPoint).typePushforward := by
  -- Route correction: compare the direct images on the explicit generators `E ↦ (U ↦ U → E)`.
  simpa [pointFiber_typesSite_compositeToposPoint, pointFiber_typesSite_morphism,
    MorphismOfTopoiIn.comp, MorphismOfTopoiIn.id, LeftExactAdjunction.comp,
    MorphismOfTopoiIn.typePushforward] using
    pointFiber_typesSite_pushforwardIso_to_skyscraper p ≪≫
      (toToposPoint_pointPushforwardIso p).symm

-- Proof sketch: the comparison produced by `pointFiber_typesSite_compositeToposPoint_pushforwardIso`
-- is itself an isomorphism, so its forward natural transformation is an isomorphism.
/-- The forward natural transformation in Lemma 7.32.8 is an isomorphism. -/
theorem pointFiber_typesSite_compositeToposPoint_pushforwardIso_hom_isIso :
    IsIso (pointFiber_typesSite_compositeToposPoint_pushforwardIso p).hom := by
  -- The comparison is a natural isomorphism, so its hom is an isomorphism in the functor category.
  simpa using
    (show IsIso (pointFiber_typesSite_compositeToposPoint_pushforwardIso p).hom by infer_instance)

/-- Helper for Lemma 7.32.8: uniqueness of left adjoints turns the direct-image comparison into
the corresponding inverse-image comparison. -/
noncomputable def pointFiber_typesSite_pullbackIso_to_inverseImage
    :
    Functor.sheafPullbackConstruction.sheafPullback p.fiber (Type w) J
        typesGrothendieckTopology ⋙ typeEquiv.{w}.inverse ≅
      (p.toToposPoint).typeInverseImage := by
  -- Compare the right adjoints first, then recover the left adjoints by uniqueness.
  exact Adjunction.leftAdjointUniq
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous p.fiber
      (Type w) J typesGrothendieckTopology).comp typeEquiv.{w}.symm.toAdjunction)
    (p.toToposPoint.typeAdjunction.ofNatIsoRight
      (pointFiber_typesSite_pushforwardIso_to_skyscraper p ≪≫
        (toToposPoint_pointPushforwardIso p).symm).symm)

/-- Helper for Lemma 7.32.8: after reintroducing the sheaf-valued realization of the terminal
topos, the pullback along `p.fiber` agrees with the left exact inverse-image functor of
`p.toToposPoint`. -/
noncomputable def pointFiber_typesSite_pullbackIso_to_sheafFiberFunctor
    :
    p.fiber.sheafPullback (Type w) J typesGrothendieckTopology ≅
      p.sheafFiber ⋙ typeEquiv.{w}.functor := by
  -- Reinsert the `Sh(pt) ≃ Type` equivalence and then compare with the stalk functor.
  refine (Functor.sheafPullbackConstruction.sheafPullbackIso p.fiber
      (Type w) J typesGrothendieckTopology) ≪≫
    (Functor.rightUnitor _).symm ≪≫
    (Functor.isoWhiskerLeft
      (Functor.sheafPullbackConstruction.sheafPullback p.fiber (Type w) J
        typesGrothendieckTopology)
      typeEquiv.{w}.counitIso.symm) ≪≫
    (Functor.associator
      (Functor.sheafPullbackConstruction.sheafPullback p.fiber (Type w) J
        typesGrothendieckTopology)
      typeEquiv.{w}.inverse typeEquiv.{w}.functor).symm ≪≫
    (Functor.isoWhiskerRight
      (pointFiber_typesSite_pullbackIso_to_inverseImage p) typeEquiv.{w}.functor) ≪≫
    (Functor.isoWhiskerRight (toToposPoint_pointInverseImageIso p) typeEquiv.{w}.functor)

/-- Helper for Lemma 7.32.8: the pullback on sheaves induced by `p.fiber` preserves finite
limits because it agrees with the inverse image of the topos point `p.toToposPoint`. -/
instance pointFiber_typesSite_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (p.fiber.sheafPullback (Type w) J typesGrothendieckTopology) := by
  -- Transport finite-limit preservation across the comparison with the stalk-based realization.
  let _ : PreservesFiniteLimits (p.sheafFiber ⋙ typeEquiv.{w}.functor) := inferInstance
  exact preservesFiniteLimits_of_natIso
    (pointFiber_typesSite_pullbackIso_to_sheafFiberFunctor p).symm

/-- The inverse-image functor of the composite point from Lemma 7.32.8 is canonically
identified with the inverse-image functor of `p.toToposPoint`. -/
noncomputable def pointFiber_typesSite_compositeToposPoint_inverseImageIso
      :
      (pointFiber_typesSite_compositeToposPoint p).typeInverseImage ≅
        (p.toToposPoint).typeInverseImage := by
  -- Route correction: this is the left-adjoint comparison forced by the direct-image comparison.
  simpa [pointFiber_typesSite_compositeToposPoint, pointFiber_typesSite_morphism,
    MorphismOfTopoiIn.comp, MorphismOfTopoiIn.id, LeftExactAdjunction.comp,
    MorphismOfTopoiIn.typeInverseImage] using pointFiber_typesSite_pullbackIso_to_inverseImage p

end

end CategoryTheory
