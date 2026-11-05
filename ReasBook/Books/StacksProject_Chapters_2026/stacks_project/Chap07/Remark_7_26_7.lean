module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_25_8
public import stacks_project.Chap07.Lemma_7_26_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe v u

noncomputable section

namespace CategoryTheory
namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/- Domain-style sampling for Remark 7.26.7:
- primary domain: glueing data for sheaves on the localized slice sites `U_τ ⊂ C/U`;
- sampled owner API:
  `GrothendieckTopology.overMapPullback`,
  `GrothendieckTopology.overMapPullbackId`,
  `GrothendieckTopology.overMapPullbackComp`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
- source-facing owner: `LocalizedSliceGlueing J τ`, whose primitive data are the sheaves on the
  sites `U_τ` and the comparison morphisms `f_τ⁻¹ ℱ_U ⟶ ℱ_{U'}`;
- core/canonical owner for inverse image: the slice-site pullback
  `J.overMapPullback (Type (max u v)) f`;
- bridge/view: `LocalizedSliceSheaf.equiv`, the transported localized pullback
  `LocalizedSliceSheaf.pullback`, and `AbsoluteGlueing.toLocalizedSliceGlueing`, which restricts
  the stronger owner `AbsoluteGlueing J`.

Primitive data in this remark are the family `τ`, the induced topologies on the localized slice
sites, and the localized glueing morphisms. The owner-level pullback functor is obtained by
transporting `J.overMapPullback` across `LocalizedSliceSheaf.equiv`, so the file should not keep a
parallel localized inverse-image owner. Since Remark 7.26.7 weakens Lemma 7.26.6 by requiring the
comparison map `c_f` to be an isomorphism only when `f` is an object of `U_τ`, the main entry here
must stay source-facing rather than collapsing back to `AbsoluteGlueing J`.
-/

/-- A family `U ↦ U_τ ⊂ C/U` of full subcategories satisfying the hypotheses of
Remark 7.26.7. -/
class LocalizedSliceFamily (J : GrothendieckTopology C)
    (τ : ∀ U : C, ObjectProperty (Over U)) : Prop where
  /-- The identity object `U/U` belongs to `U_τ`. -/
  id_mem (U : C) : τ U (Over.mk (𝟙 U))
  /-- If `X/U` belongs to `U_τ`, then every member of a covering family of `X` again defines an
  object of `U_τ` by composition with `X ⟶ U`. -/
  cover_mem {U : C} {X : Over U} (_ : τ U X) {S : Sieve X.left} (_ : S ∈ J X.left)
      {Y : C} (g : Y ⟶ X.left) (_ : S g) : τ U (Over.mk (g ≫ X.hom))
  /-- The family is stable under base change. -/
  pullback_mem {U V : C} (f : V ⟶ U) {X : Over U} (_ : τ U X) :
      τ V ((Over.pullback f).obj X)

variable (J : GrothendieckTopology C) (τ : ∀ U : C, ObjectProperty (Over U))

/-- Helper for Remark 7.26.7: any member of a covering sieve on `U` defines an object of the
localized slice site `U_τ`. -/
lemma localized_cover_arrow_mem [LocalizedSliceFamily J τ] {U V : C} {S : Sieve U}
    (hS : S ∈ J U) (f : V ⟶ U) (hf : S f) : τ U (Over.mk f) := by
  -- Apply the stability-under-covers axiom to the terminal object `U/U`.
  simpa using
    (LocalizedSliceFamily.cover_mem (J := J) (τ := τ) (U := U) (X := Over.mk (𝟙 U))
      (LocalizedSliceFamily.id_mem (J := J) (τ := τ) U) (S := S) hS f hf)

/-- Under the hypotheses of Remark 7.26.7, the inclusion `U_τ ⥤ C/U` is cover-dense. -/
instance localizedSliceInclusion_isCoverDense [LocalizedSliceFamily J τ] (U : C) :
    ((τ U).ι).IsCoverDense (J.over U) := by
  constructor
  intro X
  -- Every arrow into `X/U` already comes from an object of `U_τ`, so the image sieve is `⊤`.
  refine (J.over U).superset_covering ?_ ((J.over U).top_mem X)
  intro Y g _
  have hY : τ U Y := by
    change τ U (Over.mk Y.hom)
    simpa using
      localized_cover_arrow_mem (J := J) (τ := τ) (U := U) (J.top_mem U) Y.hom
        (show (⊤ : Sieve U) Y.hom by trivial)
  exact Presieve.in_coverByImage ((τ U).ι) (Y := ⟨Y, hY⟩) (f := g)

/-- A sheaf of types on the induced topology of the localized slice site `U_τ`. -/
abbrev LocalizedSliceSheaf [LocalizedSliceFamily J τ] (U : C) :=
  Sheaf (((τ U).ι).inducedTopology (J.over U)) (Type (max u v))

namespace LocalizedSliceSheaf

/-- Helper for Remark 7.26.7: evaluating the slice map functor on the terminal object `V/V`
recovers the slice object classified by `f : V ⟶ U`. -/
theorem localized_over_pullback_terminal_obj {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) = Over.mk f := by
  -- This is just the identity law in the base category.
  change Over.mk ((𝟙 V) ≫ f) = Over.mk f
  simpa using congrArg Over.mk (Category.id_comp f)

/-- The canonical comparison equivalence between sheaves on `U_τ` with the induced topology and
sheaves on the full slice site `C/U`. -/
abbrev equiv [LocalizedSliceFamily J τ] (U : C) :
    LocalizedSliceSheaf J τ U ≌ Sheaf (J.over U) (Type (max u v)) :=
  ((τ U).ι).sheafInducedTopologyEquivOfIsCoverDense (J.over U) (Type (max u v))

/-- Pullback of localized sheaves along the morphism of sites attached to `f : V ⟶ U`. This is a
bridge/view obtained by transporting the canonical owner `J.overMapPullback` across
`LocalizedSliceSheaf.equiv`. -/
noncomputable abbrev pullback [LocalizedSliceFamily J τ] {U V : C} (f : V ⟶ U) :
    LocalizedSliceSheaf J τ U ⥤ LocalizedSliceSheaf J τ V :=
  ((equiv J τ U).functor ⋙ J.overMapPullback (Type (max u v)) f) ⋙
    (equiv J τ V).inverse

/-- Pullback on the localized subsite along `𝟙 U` is canonically the identity functor. This is
the localized bridge/view obtained from the owner isomorphism `J.overMapPullbackId`. -/
noncomputable def pullbackId [LocalizedSliceFamily J τ] (U : C) :
    pullback J τ (𝟙 U) ≅ 𝟭 (LocalizedSliceSheaf J τ U) :=
  let e := equiv J τ U
  (Functor.associator e.functor (J.overMapPullback (Type (max u v)) (𝟙 U)) e.inverse).symm ≪≫
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft e.functor (J.overMapPullbackId (Type (max u v)) U))
      e.inverse) ≪≫
    (Functor.isoWhiskerRight (Functor.rightUnitor e.functor) e.inverse) ≪≫
      e.unitIso.symm

/-- Pullback on the localized subsites along a composite is canonically the composite of the
pullback functors. -/
def pullbackComp [LocalizedSliceFamily J τ] {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    pullback J τ f ⋙ pullback J τ g ≅ pullback J τ (g ≫ f) :=
  let eU := equiv J τ U
  let eV := equiv J τ V
  let eW := equiv J τ W
  let Ff := J.overMapPullback (Type (max u v)) f
  let Fg := J.overMapPullback (Type (max u v)) g
  (Functor.associator (((eU.functor ⋙ Ff) ⋙ eV.inverse)) (eV.functor ⋙ Fg) eW.inverse).symm ≪≫
    (Functor.isoWhiskerRight
      (Functor.associator (eU.functor ⋙ Ff) eV.inverse (eV.functor ⋙ Fg))
      eW.inverse) ≪≫
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (eU.functor ⋙ Ff) (eV.invFunIdAssoc Fg))
        eW.inverse) ≪≫
        (Functor.isoWhiskerRight (Functor.associator eU.functor Ff Fg) eW.inverse) ≪≫
          (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft eU.functor (J.overMapPullbackComp (Type (max u v)) g f))
            eW.inverse)

end LocalizedSliceSheaf

/-- The source-facing localized glueing datum of Remark 7.26.7: sheaves on the induced sites
`U_τ`, comparison morphisms for every map in `C`, the identity and cocycle compatibilities, and
the requirement that the comparison is an isomorphism whenever the map itself is an object of
`U_τ`. -/
structure LocalizedSliceGlueing [LocalizedSliceFamily J τ] where
  /-- The sheaf on the induced site `U_τ`. -/
  obj (U : C) : LocalizedSliceSheaf J τ U
  /-- The comparison morphism `f_τ⁻¹ ℱ_U ⟶ ℱ_{U'}`. -/
  transition {U V : C} (f : V ⟶ U) :
      (LocalizedSliceSheaf.pullback J τ f).obj (obj U) ⟶ obj V
  /-- The comparison attached to an identity morphism is the canonical localized identity
  pullback comparison. -/
  transition_id (U : C) :
      transition (𝟙 U) = (LocalizedSliceSheaf.pullbackId J τ U).hom.app (obj U)
  /-- The comparison morphisms satisfy the source cocycle square expressing
  `c_g ∘ g_τ⁻¹(c_f) = c_{f ∘ g}`. -/
  transition_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
      CommSq ((LocalizedSliceSheaf.pullbackComp J τ f g).hom.app (obj U))
        ((LocalizedSliceSheaf.pullback J τ g).map (transition f)) (transition (g ≫ f))
        (transition g)
  /-- If `f : V ⟶ U` is itself an object of `U_τ`, then the comparison map `c_f` is an
  isomorphism. -/
  isIso_transition_of_mem {U V : C} (f : V ⟶ U) (_ : τ U (Over.mk f)) :
      IsIso (transition f)

namespace LocalizedSliceGlueing

variable [LocalizedSliceFamily J τ]

/-- A morphism of localized glueings is a family of local sheaf morphisms compatible with the
transition morphisms. -/
@[ext] structure Hom (F G : LocalizedSliceGlueing J τ) where
  /-- The local component on `U_τ`. -/
  app (U : C) : F.obj U ⟶ G.obj U
  /-- Compatibility of the local components with localized pullback. -/
  naturality {U V : C} (f : V ⟶ U) :
      CommSq ((LocalizedSliceSheaf.pullback J τ f).map (app U))
        (F.transition f) (G.transition f) (app V)

theorem localizedSliceGlueing_id_naturality (F : LocalizedSliceGlueing J τ) :
    ∀ {U V : C} (f : V ⟶ U),
      CommSq ((LocalizedSliceSheaf.pullback J τ f).map (𝟙 (F.obj U)))
        (F.transition f) (F.transition f) (𝟙 (F.obj V)) := by
  intro U V f
  exact .mk (by simp)

def localizedSliceGlueingId (F : LocalizedSliceGlueing J τ) :
    LocalizedSliceGlueing.Hom J τ F F where
  app U := 𝟙 (F.obj U)
  naturality := localizedSliceGlueing_id_naturality J τ F

theorem localizedSliceGlueing_comp_naturality
    {F G H : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G)
    (β : LocalizedSliceGlueing.Hom J τ G H) :
    ∀ {U V : C} (f : V ⟶ U),
      CommSq ((LocalizedSliceSheaf.pullback J τ f).map (α.app U ≫ β.app U))
        (F.transition f) (H.transition f) (α.app V ≫ β.app V) := by
  intro U V f
  exact .mk <| by
    rw [Functor.map_comp, Category.assoc, (β.naturality f).w]
    rw [← Category.assoc, (α.naturality f).w]
    simp [Category.assoc]

def localizedSliceGlueingComp
    {F G H : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G)
    (β : LocalizedSliceGlueing.Hom J τ G H) :
    LocalizedSliceGlueing.Hom J τ F H where
  app U := α.app U ≫ β.app U
  naturality := localizedSliceGlueing_comp_naturality J τ α β

theorem localizedSliceGlueing_id_comp
    {F G : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G) :
    localizedSliceGlueingComp J τ (localizedSliceGlueingId J τ F) α = α := by
  ext U
  simp [localizedSliceGlueingComp, localizedSliceGlueingId]

theorem localizedSliceGlueing_comp_id
    {F G : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G) :
    localizedSliceGlueingComp J τ α (localizedSliceGlueingId J τ G) = α := by
  ext U
  simp [localizedSliceGlueingComp, localizedSliceGlueingId]

theorem localizedSliceGlueing_assoc
    {F G H K : LocalizedSliceGlueing J τ} (α : LocalizedSliceGlueing.Hom J τ F G)
    (β : LocalizedSliceGlueing.Hom J τ G H) (γ : LocalizedSliceGlueing.Hom J τ H K) :
    localizedSliceGlueingComp J τ (localizedSliceGlueingComp J τ α β) γ =
      localizedSliceGlueingComp J τ α (localizedSliceGlueingComp J τ β γ) := by
  ext U
  simp [localizedSliceGlueingComp, Category.assoc]

/-- The category of localized glueing data from Remark 7.26.7. -/
instance : Category (LocalizedSliceGlueing J τ) where
  Hom F G := LocalizedSliceGlueing.Hom J τ F G
  id := localizedSliceGlueingId J τ
  comp α β := localizedSliceGlueingComp J τ α β
  id_comp := localizedSliceGlueing_id_comp J τ
  comp_id := localizedSliceGlueing_comp_id J τ
  assoc := localizedSliceGlueing_assoc J τ

end LocalizedSliceGlueing

/-- Helper for Remark 7.26.7: every localized transition map is an isomorphism because every arrow
already lies in the localized slice site by applying `localized_cover_arrow_mem` to the maximal
covering sieve. -/
lemma localizedSliceGlueing_transition_isIso [LocalizedSliceFamily J τ]
    {F : LocalizedSliceGlueing J τ} {U V : C} (f : V ⟶ U) :
    IsIso (F.transition f) := by
  -- The site axioms force `f` itself to belong to `U_τ`, so the structure field applies.
  have hf : τ U (Over.mk f) := by
    simpa using
      localized_cover_arrow_mem (J := J) (τ := τ) (U := U) (J.top_mem U) f
        (show (⊤ : Sieve U) f by trivial)
  exact F.isIso_transition_of_mem f hf

/-- Helper for Remark 7.26.7: transport an absolute transition map through the localized slice-site
equivalences. -/
noncomputable def absoluteGlueingToLocalizedSlice_transition
    [LocalizedSliceFamily J τ] (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    (LocalizedSliceSheaf.pullback J τ f).obj
        ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)) ⟶
      (LocalizedSliceSheaf.equiv J τ V).inverse.obj (F.obj V) :=
  ((LocalizedSliceSheaf.equiv J τ V).inverse.mapIso
      ((J.overMapPullback (Type (max u v)) f).mapIso
        ((LocalizedSliceSheaf.equiv J τ U).counitIso.app (F.obj U))) ≪≫
    (LocalizedSliceSheaf.equiv J τ V).inverse.mapIso (F.transition f)).hom

/-- Helper for Remark 7.26.7: the transported absolute transition satisfies the localized identity
compatibility. -/
theorem absoluteGlueingToLocalizedSlice_transition_id [LocalizedSliceFamily J τ]
    (F : AbsoluteGlueing J) (U : C) :
    absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F (𝟙 U) =
      (LocalizedSliceSheaf.pullbackId J τ U).hom.app
        ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)) := by
  let e := LocalizedSliceSheaf.equiv J τ U
  let ε := e.counitIso.hom
  let η := e.unitIso.inv
  -- Rewrite the absolute identity comparison and then collapse the counit transport.
  rw [absoluteGlueingToLocalizedSlice_transition, F.transition_id]
  change e.inverse.map ((J.overMapPullback (Type (max u v)) (𝟙 U)).map (ε.app (F.obj U))) ≫
      e.inverse.map ((J.overMapPullbackId (Type (max u v)) U).hom.app (F.obj U)) =
    e.inverse.map
        ((J.overMapPullbackId (Type (max u v)) U).hom.app
          (e.functor.obj (e.inverse.obj (F.obj U)))) ≫
      η.app (e.inverse.obj (F.obj U))
  rw [show η.app (e.inverse.obj (F.obj U)) = e.inverse.map (e.counit.app (F.obj U)) by
    simpa [η] using e.unitInv_app_inverse (F.obj U)]
  rw [← e.inverse.map_comp]
  change e.inverse.map
      ((J.overMapPullback (Type (max u v)) (𝟙 U)).map (ε.app (F.obj U)) ≫
        (J.overMapPullbackId (Type (max u v)) U).hom.app (F.obj U)) =
    e.inverse.map
      ((J.overMapPullbackId (Type (max u v)) U).hom.app
          (e.functor.obj (e.inverse.obj (F.obj U))) ≫
        e.counit.app (F.obj U))
  exact congrArg e.inverse.map <|
    (J.overMapPullbackId (Type (max u v)) U).hom.naturality (ε.app (F.obj U))

/-- Helper for Remark 7.26.7: after applying the owner-side equivalence functor, the transported
absolute transition is the expected owner pullback map followed by the original absolute
transition. -/
theorem absoluteGlueingToLocalizedSlice_transition_functor_map [LocalizedSliceFamily J τ]
    (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    (LocalizedSliceSheaf.equiv J τ V).functor.map
        (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f) ≫
      (LocalizedSliceSheaf.equiv J τ V).counit.app (F.obj V) =
      (LocalizedSliceSheaf.equiv J τ V).counit.app
          ((J.overMapPullback (Type (max u v)) f).obj
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj
              ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)))) ≫
        (J.overMapPullback (Type (max u v)) f).map
          ((LocalizedSliceSheaf.equiv J τ U).counit.app (F.obj U)) ≫
        (F.transition f).hom := by
  -- Expanding the transported transition exposes the owner-side counit comparison and the
  -- original absolute transition.
  simpa [absoluteGlueingToLocalizedSlice_transition, LocalizedSliceSheaf.pullback,
    Functor.map_comp, Category.assoc] using
    (LocalizedSliceSheaf.equiv J τ V).counit_naturality
      ((J.overMapPullback (Type (max u v)) f).map
          ((LocalizedSliceSheaf.equiv J τ U).counit.app (F.obj U)) ≫
        (F.transition f).hom)

/-- Helper for Remark 7.26.7: transporting the absolute cocycle square through the localized
slice-site equivalences gives the localized cocycle square. -/
theorem absoluteGlueingToLocalizedSlice_transition_comp [LocalizedSliceFamily J τ]
    (F : AbsoluteGlueing J) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    CommSq
      ((LocalizedSliceSheaf.pullbackComp J τ f g).hom.app
        ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)))
      ((LocalizedSliceSheaf.pullback J τ g).map
        (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f))
      (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F (g ≫ f))
      (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F g) := by
  -- Route correction: this should come from transporting `F.transition_comp` through the
  -- equivalences `LocalizedSliceSheaf.equiv J τ _` and cancelling the inserted counit pairs.
  have hcomp :
      (J.overMapPullbackComp (Type (max u v)) g f).hom.app (F.obj U) ≫
          (F.transition (g ≫ f)).hom =
        (J.overMapPullback (Type (max u v)) g).map (F.transition f).hom ≫
          (F.transition g).hom := by
    simpa using congrArg Iso.hom (F.transition_comp f g)
  have hnat :
      (J.overMapPullbackComp (Type (max u v)) g f).hom.app
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj
              ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U))) ≫
          (J.overMapPullback (Type (max u v)) (g ≫ f)).map
            ((LocalizedSliceSheaf.equiv J τ U).counitIso.hom.app (F.obj U)) =
        (J.overMapPullback (Type (max u v)) g).map
            ((J.overMapPullback (Type (max u v)) f).map
              ((LocalizedSliceSheaf.equiv J τ U).counitIso.hom.app (F.obj U))) ≫
          (J.overMapPullbackComp (Type (max u v)) g f).hom.app (F.obj U) := by
    simpa [Functor.comp_map] using
      ((J.overMapPullbackComp (Type (max u v)) g f).hom.naturality
        ((LocalizedSliceSheaf.equiv J τ U).counitIso.hom.app (F.obj U))).symm
  have hpair :
      (J.overMapPullback (Type (max u v)) g).map
          ((LocalizedSliceSheaf.equiv J τ V).counitInv.app (F.obj V)) ≫
        (J.overMapPullback (Type (max u v)) g).map
          ((LocalizedSliceSheaf.equiv J τ V).counitIso.hom.app (F.obj V)) =
      𝟙 _ := by
    rw [← Functor.map_comp]
    simpa using congrArg (fun k ↦ (J.overMapPullback (Type (max u v)) g).map k)
      ((LocalizedSliceSheaf.equiv J τ V).counitIso_inv_hom_id_app (F.obj V))
  let ownerPrefix :=
    (LocalizedSliceSheaf.equiv J τ W).counit.app
        ((J.overMapPullback (Type (max u v)) g).obj
          ((LocalizedSliceSheaf.equiv J τ V).functor.obj
            ((LocalizedSliceSheaf.equiv J τ V).inverse.obj
              ((J.overMapPullback (Type (max u v)) f).obj
                ((LocalizedSliceSheaf.equiv J τ U).functor.obj
                  ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U))))))) ≫
      (J.overMapPullback (Type (max u v)) g).map
        ((LocalizedSliceSheaf.equiv J τ V).counit.app
          ((J.overMapPullback (Type (max u v)) f).obj
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj
              ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)))))
  let ownerMiddle :=
    (J.overMapPullback (Type (max u v)) g).map
      ((J.overMapPullback (Type (max u v)) f).map
        ((LocalizedSliceSheaf.equiv J τ U).counitIso.hom.app (F.obj U)))
  have hnat' :
      ownerPrefix ≫
          (J.overMapPullbackComp (Type (max u v)) g f).hom.app
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj
              ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U))) ≫
          (J.overMapPullback (Type (max u v)) (g ≫ f)).map
            ((LocalizedSliceSheaf.equiv J τ U).counitIso.hom.app (F.obj U)) ≫
          (F.transition (g ≫ f)).hom ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W) =
        ownerPrefix ≫ ownerMiddle ≫
          (J.overMapPullbackComp (Type (max u v)) g f).hom.app (F.obj U) ≫
          (F.transition (g ≫ f)).hom ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W) := by
    simpa [ownerPrefix, ownerMiddle, Category.assoc] using
      congrArg
        (fun k ↦ ownerPrefix ≫ k ≫ (F.transition (g ≫ f)).hom ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W))
        hnat
  have hcomp' :
      ownerPrefix ≫ ownerMiddle ≫
          (J.overMapPullbackComp (Type (max u v)) g f).hom.app (F.obj U) ≫
          (F.transition (g ≫ f)).hom ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W) =
        ownerPrefix ≫ ownerMiddle ≫
          (J.overMapPullback (Type (max u v)) g).map (F.transition f).hom ≫
          (F.transition g).hom ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W) := by
    simpa [ownerPrefix, ownerMiddle, Category.assoc] using
      congrArg
        (fun k ↦ ownerPrefix ≫ ownerMiddle ≫ k ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W))
        hcomp
  have hpair' :
      ownerPrefix ≫ ownerMiddle ≫
          (J.overMapPullback (Type (max u v)) g).map (F.transition f).hom ≫
          (J.overMapPullback (Type (max u v)) g).map
            ((LocalizedSliceSheaf.equiv J τ V).counitInv.app (F.obj V)) ≫
          (J.overMapPullback (Type (max u v)) g).map
            ((LocalizedSliceSheaf.equiv J τ V).counitIso.hom.app (F.obj V)) ≫
          (F.transition g).hom ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W) =
        ownerPrefix ≫ ownerMiddle ≫
          (J.overMapPullback (Type (max u v)) g).map (F.transition f).hom ≫
          (F.transition g).hom ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W) := by
    simpa [ownerPrefix, ownerMiddle, Category.assoc] using
      congrArg
        (fun k ↦ ownerPrefix ≫ ownerMiddle ≫
          (J.overMapPullback (Type (max u v)) g).map (F.transition f).hom ≫
          k ≫ (F.transition g).hom ≫
          (LocalizedSliceSheaf.equiv J τ W).counitInv.app (F.obj W))
        hpair
  refine CommSq.mk ?_
  apply (LocalizedSliceSheaf.equiv J τ W).functor.map_injective
  simp [LocalizedSliceSheaf.pullback, LocalizedSliceSheaf.pullbackComp,
    absoluteGlueingToLocalizedSlice_transition, Functor.map_comp, Category.assoc]
  simpa [ownerPrefix, ownerMiddle, Category.assoc] using
    Eq.trans hnat' (Eq.trans hcomp' hpair'.symm)

/-- Helper for Remark 7.26.7: morphisms of absolute glueings transport to morphisms of localized
glueings by applying the inverse local equivalences objectwise. -/
theorem absoluteGlueingToLocalizedSlice_map_naturality [LocalizedSliceFamily J τ]
    {F G : AbsoluteGlueing J} (η : F ⟶ G) {U V : C} (f : V ⟶ U) :
    CommSq
      ((LocalizedSliceSheaf.pullback J τ f).map
        ((LocalizedSliceSheaf.equiv J τ U).inverse.map (η.app U)))
      (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f)
      (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) G f)
      ((LocalizedSliceSheaf.equiv J τ V).inverse.map (η.app V)) := by
  -- This is the morphism-level analogue of `absoluteGlueingToLocalizedSlice_transition_comp`.
  -- TODO: transport `η.naturality f` across `LocalizedSliceSheaf.equiv` and simplify the counit
  -- transports on the `U`- and `V`-sides.
  have hnat := (η.naturality f).w
  have hpair :
      (J.overMapPullback (Type (max u v)) f).map
          ((LocalizedSliceSheaf.equiv J τ U).counitInv.app (G.obj U)) ≫
        (J.overMapPullback (Type (max u v)) f).map
          ((LocalizedSliceSheaf.equiv J τ U).counitIso.hom.app (G.obj U)) =
      𝟙 _ := by
    rw [← Functor.map_comp]
    simpa using congrArg (fun k ↦ (J.overMapPullback (Type (max u v)) f).map k)
      ((LocalizedSliceSheaf.equiv J τ U).counitIso_inv_hom_id_app (G.obj U))
  let ownerPrefix :=
    (LocalizedSliceSheaf.equiv J τ V).counit.app
        ((J.overMapPullback (Type (max u v)) f).obj
          ((LocalizedSliceSheaf.equiv J τ U).functor.obj
            ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)))) ≫
      (J.overMapPullback (Type (max u v)) f).map
        ((LocalizedSliceSheaf.equiv J τ U).counit.app (F.obj U))
  have hpair' :
      ownerPrefix ≫
          (J.overMapPullback (Type (max u v)) f).map (η.app U) ≫
          (J.overMapPullback (Type (max u v)) f).map
            ((LocalizedSliceSheaf.equiv J τ U).counitInv.app (G.obj U)) ≫
          (J.overMapPullback (Type (max u v)) f).map
            ((LocalizedSliceSheaf.equiv J τ U).counitIso.hom.app (G.obj U)) ≫
          (G.transition f).hom ≫
          (LocalizedSliceSheaf.equiv J τ V).counitInv.app (G.obj V) =
        ownerPrefix ≫
          (J.overMapPullback (Type (max u v)) f).map (η.app U) ≫
          (G.transition f).hom ≫
          (LocalizedSliceSheaf.equiv J τ V).counitInv.app (G.obj V) := by
    simpa [ownerPrefix, Category.assoc] using
      congrArg
        (fun k ↦ ownerPrefix ≫ (J.overMapPullback (Type (max u v)) f).map (η.app U) ≫
          k ≫ (G.transition f).hom ≫
          (LocalizedSliceSheaf.equiv J τ V).counitInv.app (G.obj V))
        hpair
  have hnat' :
      ownerPrefix ≫
          (J.overMapPullback (Type (max u v)) f).map (η.app U) ≫
          (G.transition f).hom ≫
          (LocalizedSliceSheaf.equiv J τ V).counitInv.app (G.obj V) =
        ownerPrefix ≫
          (F.transition f).hom ≫ η.app V ≫
          (LocalizedSliceSheaf.equiv J τ V).counitInv.app (G.obj V) := by
    simpa [ownerPrefix, Category.assoc] using
      congrArg
        (fun k ↦ ownerPrefix ≫ k ≫
          (LocalizedSliceSheaf.equiv J τ V).counitInv.app (G.obj V))
        hnat
  refine CommSq.mk ?_
  apply (LocalizedSliceSheaf.equiv J τ V).functor.map_injective
  simp [LocalizedSliceSheaf.pullback, absoluteGlueingToLocalizedSlice_transition,
    Functor.map_comp, Category.assoc]
  simpa [ownerPrefix, Category.assoc] using Eq.trans hpair' hnat'

/-- Helper for Remark 7.26.7: the transported absolute transition is an isomorphism. -/
theorem absoluteGlueingToLocalizedSlice_transition_isIso [LocalizedSliceFamily J τ]
    (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    IsIso (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f) := by
  -- The transition is built as the hom of a composite of transported isomorphisms.
  let e :
      (LocalizedSliceSheaf.pullback J τ f).obj
          ((LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)) ≅
        (LocalizedSliceSheaf.equiv J τ V).inverse.obj (F.obj V) :=
    (LocalizedSliceSheaf.equiv J τ V).inverse.mapIso
        ((J.overMapPullback (Type (max u v)) f).mapIso
          ((LocalizedSliceSheaf.equiv J τ U).counitIso.app (F.obj U))) ≪≫
      (LocalizedSliceSheaf.equiv J τ V).inverse.mapIso (F.transition f)
  change IsIso e.hom
  infer_instance

/-- Helper for Remark 7.26.7: absolute glueing data transport objectwise to localized glueing data
along the localized slice-site equivalences. -/
def absoluteGlueingToLocalizedSliceGlueingFunctor [LocalizedSliceFamily J τ] :
    AbsoluteGlueing J ⥤ LocalizedSliceGlueing J τ where
  obj F :=
    { obj := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).inverse.obj (F.obj U)
      transition := fun {U V} f ↦
        absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f
      transition_id := absoluteGlueingToLocalizedSlice_transition_id (J := J) (τ := τ) F
      transition_comp := fun f g ↦
        absoluteGlueingToLocalizedSlice_transition_comp (J := J) (τ := τ) F f g
      isIso_transition_of_mem := fun f _ ↦
        absoluteGlueingToLocalizedSlice_transition_isIso (J := J) (τ := τ) F f }
  map η :=
    { app := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).inverse.map (η.app U)
      naturality := fun f ↦
        absoluteGlueingToLocalizedSlice_map_naturality (J := J) (τ := τ) η f }
  map_id F := by
    apply LocalizedSliceGlueing.Hom.ext
    funext U
    rfl
  map_comp η θ := by
    apply LocalizedSliceGlueing.Hom.ext
    funext U
    rfl

/-- Helper for Remark 7.26.7: every localized transition can be regarded as an isomorphism once
the maximal-cover argument has shown that every arrow lies in the localized subsite. -/
noncomputable def localizedSliceGlueing_transition_iso [LocalizedSliceFamily J τ]
    (F : LocalizedSliceGlueing J τ) {U V : C} (f : V ⟶ U) :
    (LocalizedSliceSheaf.pullback J τ f).obj (F.obj U) ≅ F.obj V :=
  let h : IsIso (F.transition f) :=
    localizedSliceGlueing_transition_isIso (J := J) (τ := τ) (F := F) f
  @asIso _ _ _ _ (F.transition f) h

/-- Helper for Remark 7.26.7: applying the local equivalences to a localized glueing recovers an
absolute glueing because every localized transition is already an isomorphism. -/
noncomputable def localizedSliceGlueingToAbsolute_transition
    [LocalizedSliceFamily J τ] (F : LocalizedSliceGlueing J τ) {U V : C} (f : V ⟶ U) :
    (J.overMapPullback (Type (max u v)) f).obj
        ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)) ≅
      (LocalizedSliceSheaf.equiv J τ V).functor.obj (F.obj V) :=
  let A :=
    (J.overMapPullback (Type (max u v)) f).obj
      ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))
  ((LocalizedSliceSheaf.equiv J τ V).counitIso.app A).symm ≪≫
    (LocalizedSliceSheaf.equiv J τ V).functor.mapIso
      (localizedSliceGlueing_transition_iso (J := J) (τ := τ) F f)

/-- Helper for Remark 7.26.7: after inverse-mapping a transported owner transition and
postcomposing with the unit inverse, the localized transition reappears literally. -/
theorem localizedSliceGlueingToAbsolute_transition_inverse_map_assoc
    [LocalizedSliceFamily J τ] (F : LocalizedSliceGlueing J τ) {U V : C} (f : V ⟶ U) :
    ((LocalizedSliceSheaf.equiv J τ V).inverse.map
        ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom)) ≫
      (LocalizedSliceSheaf.equiv J τ V).unitInv.app (F.obj V) =
        F.transition f := by
  let eV := LocalizedSliceSheaf.equiv J τ V
  let A :=
    (J.overMapPullback (Type (max u v)) f).obj
      ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))
  -- Expand the transported owner morphism and cancel the unit pair inserted by `inv_fun_map`.
  have hCounit :
      eV.inverse.map (eV.counitInv.app A) =
        eV.unit.app ((LocalizedSliceSheaf.pullback J τ f).obj (F.obj U)) := by
    simpa [LocalizedSliceSheaf.pullback, A] using (Equivalence.unit_app_inverse eV A).symm
  have hTransition :
      eV.inverse.map (eV.functor.map (F.transition f)) =
        eV.unitInv.app ((LocalizedSliceSheaf.pullback J τ f).obj (F.obj U)) ≫
          F.transition f ≫ eV.unit.app (F.obj V) := by
    simpa [LocalizedSliceSheaf.pullback] using
      (Equivalence.inv_fun_map eV
        ((LocalizedSliceSheaf.pullback J τ f).obj (F.obj U)) (F.obj V) (F.transition f))
  change (eV.inverse.map (eV.counitInv.app A) ≫ eV.inverse.map (eV.functor.map (F.transition f))) ≫
      eV.unitInv.app (F.obj V) = F.transition f
  rw [hCounit]
  change (eV.unit.app (eV.inverse.obj A) ≫ eV.inverse.map (eV.functor.map (F.transition f))) ≫
      eV.unitInv.app (F.obj V) = F.transition f
  have hComposite :
      (eV.unit.app (eV.inverse.obj A) ≫ eV.inverse.map (eV.functor.map (F.transition f))) ≫
          eV.unitInv.app (F.obj V) =
        (eV.unit.app (eV.inverse.obj A) ≫
            (eV.unitInv.app (eV.inverse.obj A) ≫ F.transition f ≫ eV.unit.app (F.obj V))) ≫
          eV.unitInv.app (F.obj V) := by
    exact
      congrArg
        (fun k ↦ (eV.unit.app (eV.inverse.obj A) ≫ k) ≫ eV.unitInv.app (F.obj V))
        hTransition
  rw [hComposite]
  simp [Category.assoc]

/-- Helper for Remark 7.26.7: the transported localized transition satisfies the owner identity
compatibility. -/
theorem localizedSliceGlueingToAbsolute_transition_id [LocalizedSliceFamily J τ]
    (F : LocalizedSliceGlueing J τ) (U : C) :
    localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F (𝟙 U) =
      (J.overMapPullbackId (Type (max u v)) U).app
        ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)) := by
  let e := LocalizedSliceSheaf.equiv J τ U
  -- Move the owner identity comparison back to the localized site and compare there.
  apply Iso.ext
  apply e.inverse.map_injective
  refine (cancel_mono (e.unitInv.app (F.obj U))).1 ?_
  have hLeft :
      e.inverse.map (localizedSliceGlueingToAbsolute_transition
          (J := J) (τ := τ) F (𝟙 U)).hom ≫ e.unitInv.app (F.obj U) =
        F.transition (𝟙 U) := by
    simpa using localizedSliceGlueingToAbsolute_transition_inverse_map_assoc
      (J := J) (τ := τ) F (𝟙 U)
  have hRight :
      (LocalizedSliceSheaf.pullbackId J τ U).hom.app (F.obj U) =
        e.inverse.map
          (((J.overMapPullbackId (Type (max u v)) U).app
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))).hom) ≫
          e.unitInv.app (F.obj U) := by
    simpa [e, LocalizedSliceSheaf.pullback, LocalizedSliceSheaf.pullbackId, Category.assoc]
  exact hLeft.trans ((F.transition_id U).trans hRight)

/-- Helper for Remark 7.26.7: inverse-mapping the whole owner right cocycle composite and
postcomposing with the unit inverse leaves exactly the owner-side source comparison followed by
the localized right cocycle composite. -/
theorem localizedSliceGlueingToAbsolute_transition_right_inverse_map_assoc
    [LocalizedSliceFamily J τ] (F : LocalizedSliceGlueing J τ) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) :
    ((LocalizedSliceSheaf.equiv J τ W).inverse.map
        (((J.overMapPullback (Type (max u v)) g).map
          ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom)) ≫
            (localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F g).hom)) ≫
      (LocalizedSliceSheaf.equiv J τ W).unitInv.app (F.obj W) =
        ((LocalizedSliceSheaf.equiv J τ W).inverse.map
          ((J.overMapPullback (Type (max u v)) g).map
            ((LocalizedSliceSheaf.equiv J τ V).counitInv.app
              ((J.overMapPullback (Type (max u v)) f).obj
                ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))))) ≫
          ((LocalizedSliceSheaf.pullback J τ g).map (F.transition f)) ≫
          F.transition g := by
  let eV := LocalizedSliceSheaf.equiv J τ V
  let eW := LocalizedSliceSheaf.equiv J τ W
  -- Expand the right owner composite and then collapse only the transported `g`-transition.
  rw [Functor.map_comp, Category.assoc]
  have hTransition :
      eW.inverse.map
          ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F g).hom) ≫
        eW.unitInv.app (F.obj W) =
      F.transition g := by
    simpa using
      localizedSliceGlueingToAbsolute_transition_inverse_map_assoc
        (J := J) (τ := τ) F g
  have hComposite :
      (eW.inverse.map
          ((J.overMapPullback (Type (max u v)) g).map
            ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom)) ≫
          eW.inverse.map
            ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F g).hom)) ≫
        eW.unitInv.app (F.obj W) =
      eW.inverse.map
          ((J.overMapPullback (Type (max u v)) g).map
            ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom)) ≫
        F.transition g := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          eW.inverse.map
              ((J.overMapPullback (Type (max u v)) g).map
                ((localizedSliceGlueingToAbsolute_transition
                  (J := J) (τ := τ) F f).hom)) ≫
            k)
        hTransition
  have hFirst :
      (LocalizedSliceSheaf.equiv J τ W).inverse.map
            ((J.overMapPullback (Type (max u v)) g).map
              ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom)) ≫
          (LocalizedSliceSheaf.equiv J τ W).inverse.map
            ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F g).hom) ≫
          (LocalizedSliceSheaf.equiv J τ W).unitInv.app (F.obj W) =
        eW.inverse.map
          ((J.overMapPullback (Type (max u v)) g).map
            ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom)) ≫
          F.transition g := by
    simpa [Category.assoc] using hComposite
  have hSecond :
      eW.inverse.map
          ((J.overMapPullback (Type (max u v)) g).map
            ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom)) ≫
        F.transition g =
      eW.inverse.map
          ((J.overMapPullback (Type (max u v)) g).map
            (eV.counitInv.app
              ((J.overMapPullback (Type (max u v)) f).obj
                ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))))) ≫
        ((LocalizedSliceSheaf.pullback J τ g).map (F.transition f)) ≫
          F.transition g := by
    -- Unfolding the transported `f`-transition isolates the source comparison inserted by the
    -- counit of `LocalizedSliceSheaf.equiv J τ V`.
    simpa [eV, eW, localizedSliceGlueingToAbsolute_transition,
      localizedSliceGlueing_transition_iso, LocalizedSliceSheaf.pullback, Functor.map_comp,
      Category.assoc]
  exact hFirst.trans hSecond

/-- Helper for Remark 7.26.7: inverse-mapping the owner comparison for pullback composition and
postcomposing with the unit inverse yields the localized pullback-composition comparison followed
by the localized transition for `g ≫ f`. -/
theorem localizedSliceGlueingToAbsolute_transition_left_inverse_map_assoc
    [LocalizedSliceFamily J τ] (F : LocalizedSliceGlueing J τ) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) :
    ((LocalizedSliceSheaf.equiv J τ W).inverse.map
        (((J.overMapPullbackComp (Type (max u v)) g f).hom.app
          ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))) ≫
            (localizedSliceGlueingToAbsolute_transition
              (J := J) (τ := τ) F (g ≫ f)).hom)) ≫
      (LocalizedSliceSheaf.equiv J τ W).unitInv.app (F.obj W) =
        ((LocalizedSliceSheaf.equiv J τ W).inverse.map
          ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))) ≫
          F.transition (g ≫ f) := by
  let eW := LocalizedSliceSheaf.equiv J τ W
  -- Normalize the direct owner transition and leave the owner pullback-composition comparison
  -- explicit as the common source prefix.
  rw [Functor.map_comp, Category.assoc]
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        eW.inverse.map
            ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
              ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))) ≫
          k)
      (localizedSliceGlueingToAbsolute_transition_inverse_map_assoc
        (J := J) (τ := τ) F (g ≫ f))

/-- Helper for Remark 7.26.7: the owner pullback-composition comparison becomes the localized
pullback-composition comparison after inserting the same counit-based source normalization used on
the right-hand cocycle composite. -/
theorem localizedSliceGlueingToAbsolute_transition_comp_source_assoc
    [LocalizedSliceFamily J τ] (F : LocalizedSliceGlueing J τ) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) :
    ((LocalizedSliceSheaf.equiv J τ W).inverse.map
        ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
          ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))) =
      ((LocalizedSliceSheaf.equiv J τ W).inverse.map
        ((J.overMapPullback (Type (max u v)) g).map
          ((LocalizedSliceSheaf.equiv J τ V).counitInv.app
            ((J.overMapPullback (Type (max u v)) f).obj
              ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))))) ≫
        (LocalizedSliceSheaf.pullbackComp J τ f g).hom.app (F.obj U) := by
  let eU := LocalizedSliceSheaf.equiv J τ U
  let eV := LocalizedSliceSheaf.equiv J τ V
  let eW := LocalizedSliceSheaf.equiv J τ W
  let A :=
    (J.overMapPullback (Type (max u v)) f).obj
      ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))
  let sourceInv :=
    eW.inverse.map ((J.overMapPullback (Type (max u v)) g).map (eV.counitInv.app A))
  let sourceHom :=
    eW.inverse.map ((J.overMapPullback (Type (max u v)) g).map (eV.counit.app A))
  let compMap :=
    eW.inverse.map
      ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
        ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))
  have hpair :
      sourceInv ≫ sourceHom =
      𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    simpa [A] using
      congrArg
        (fun k ↦ eW.inverse.map ((J.overMapPullback (Type (max u v)) g).map k))
        (eV.counitIso_inv_hom_id_app A)
  -- Unfolding `pullbackComp` inserts a cancellable `counitInv ≫ counit` pair in front of the
  -- owner pullback-composition comparison.
  simp [A, sourceInv, sourceHom, compMap, eU, eV, eW, LocalizedSliceSheaf.pullback,
    LocalizedSliceSheaf.pullbackComp, Functor.map_comp, Category.assoc]
  have hpair_assoc : (sourceInv ≫ sourceHom) ≫ compMap = 𝟙 _ ≫ compMap := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ compMap) hpair
  simpa [compMap] using hpair_assoc.symm

/-- Helper for Remark 7.26.7: transporting the localized cocycle square through the localized
slice-site equivalences gives the owner cocycle square. -/
theorem localizedSliceGlueingToAbsolute_transition_comp [LocalizedSliceFamily J τ]
    (F : LocalizedSliceGlueing J τ) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (J.overMapPullbackComp (Type (max u v)) g f).app
          ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)) ≪≫
        localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F (g ≫ f) =
      (J.overMapPullback (Type (max u v)) g).mapIso
          (localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f) ≪≫
        localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F g := by
  let eW := LocalizedSliceSheaf.equiv J τ W
  -- Move the owner cocycle identity back to the localized site and compare there.
  apply Iso.ext
  apply eW.inverse.map_injective
  refine (cancel_mono (eW.unitInv.app (F.obj W))).1 ?_
  have hLeft :
      eW.inverse.map
          (((J.overMapPullbackComp (Type (max u v)) g f).hom.app
              ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))) ≫
            (localizedSliceGlueingToAbsolute_transition
              (J := J) (τ := τ) F (g ≫ f)).hom) ≫
        eW.unitInv.app (F.obj W) =
      eW.inverse.map
          ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))) ≫
        F.transition (g ≫ f) := by
    simpa [Category.assoc] using
      localizedSliceGlueingToAbsolute_transition_left_inverse_map_assoc
        (J := J) (τ := τ) F f g
  have hRight :
      eW.inverse.map
          (((J.overMapPullback (Type (max u v)) g).map
              ((localizedSliceGlueingToAbsolute_transition
                (J := J) (τ := τ) F f).hom)) ≫
            (localizedSliceGlueingToAbsolute_transition
              (J := J) (τ := τ) F g).hom) ≫
        eW.unitInv.app (F.obj W) =
      ((LocalizedSliceSheaf.equiv J τ W).inverse.map
          ((J.overMapPullback (Type (max u v)) g).map
            ((LocalizedSliceSheaf.equiv J τ V).counitInv.app
              ((J.overMapPullback (Type (max u v)) f).obj
                ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))))) ≫
        ((LocalizedSliceSheaf.pullback J τ g).map (F.transition f)) ≫
          F.transition g := by
    simpa [Category.assoc] using
      localizedSliceGlueingToAbsolute_transition_right_inverse_map_assoc
        (J := J) (τ := τ) F f g
  -- The localized cocycle square becomes the transported owner square after inserting the common
  -- source comparison coming from the counit of `LocalizedSliceSheaf.equiv J τ V`.
  have hPrefix :
      eW.inverse.map
          ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))) =
        ((LocalizedSliceSheaf.equiv J τ W).inverse.map
          ((J.overMapPullback (Type (max u v)) g).map
            ((LocalizedSliceSheaf.equiv J τ V).counitInv.app
              ((J.overMapPullback (Type (max u v)) f).obj
                ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))))) ≫
          (LocalizedSliceSheaf.pullbackComp J τ f g).hom.app (F.obj U) := by
    simpa using
      localizedSliceGlueingToAbsolute_transition_comp_source_assoc
        (J := J) (τ := τ) F f g
  have hStep2 :
      eW.inverse.map
          ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
            ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))) ≫
        F.transition (g ≫ f) =
      ((LocalizedSliceSheaf.equiv J τ W).inverse.map
        ((J.overMapPullback (Type (max u v)) g).map
          ((LocalizedSliceSheaf.equiv J τ V).counitInv.app
            ((J.overMapPullback (Type (max u v)) f).obj
              ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))))) ≫
        (LocalizedSliceSheaf.pullbackComp J τ f g).hom.app (F.obj U) ≫
          F.transition (g ≫ f) := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ F.transition (g ≫ f)) hPrefix
  have hStep3 :
      ((LocalizedSliceSheaf.equiv J τ W).inverse.map
        ((J.overMapPullback (Type (max u v)) g).map
          ((LocalizedSliceSheaf.equiv J τ V).counitInv.app
            ((J.overMapPullback (Type (max u v)) f).obj
              ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))))) ≫
        (LocalizedSliceSheaf.pullbackComp J τ f g).hom.app (F.obj U) ≫
          F.transition (g ≫ f) =
      ((LocalizedSliceSheaf.equiv J τ W).inverse.map
        ((J.overMapPullback (Type (max u v)) g).map
          ((LocalizedSliceSheaf.equiv J τ V).counitInv.app
            ((J.overMapPullback (Type (max u v)) f).obj
              ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)))))) ≫
        ((LocalizedSliceSheaf.pullback J τ g).map (F.transition f)) ≫
          F.transition g := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          ((LocalizedSliceSheaf.equiv J τ W).inverse.map
              ((J.overMapPullback (Type (max u v)) g).map
                ((LocalizedSliceSheaf.equiv J τ V).counitInv.app
                  ((J.overMapPullback (Type (max u v)) f).obj
                    ((LocalizedSliceSheaf.equiv J τ U).functor.obj
                      (F.obj U)))))) ≫
            k)
        (F.transition_comp f g).w
  exact hLeft.trans (hStep2.trans (hStep3.trans hRight.symm))

/-- Helper for Remark 7.26.7: morphisms of localized glueings transport to morphisms of absolute
glueings by applying the local equivalences objectwise. -/
theorem localizedSliceGlueingToAbsolute_map_left_inverse_map_assoc
    [LocalizedSliceFamily J τ] {F G : LocalizedSliceGlueing J τ} (η : F ⟶ G)
    {U V : C} (f : V ⟶ U) :
    ((LocalizedSliceSheaf.equiv J τ V).inverse.map
        (((J.overMapPullback (Type (max u v)) f).map
          ((LocalizedSliceSheaf.equiv J τ U).functor.map (η.app U))) ≫
            (localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) G f).hom)) ≫
      (LocalizedSliceSheaf.equiv J τ V).unitInv.app (G.obj V) =
        ((LocalizedSliceSheaf.pullback J τ f).map (η.app U)) ≫ G.transition f := by
  let eV := LocalizedSliceSheaf.equiv J τ V
  -- Normalize the whole transported left composite before simplifying the transition factor.
  rw [Functor.map_comp, Category.assoc]
  simpa [LocalizedSliceSheaf.pullback, Functor.map_comp, Category.assoc] using
    congrArg
      (fun k ↦ eV.inverse.map
        ((J.overMapPullback (Type (max u v)) f).map
          ((LocalizedSliceSheaf.equiv J τ U).functor.map (η.app U))) ≫ k)
      (localizedSliceGlueingToAbsolute_transition_inverse_map_assoc
        (J := J) (τ := τ) G f)

/-- Helper for Remark 7.26.7: inverse-mapping the right owner naturality composite and
postcomposing with the unit inverse recovers the localized right-hand naturality composite. -/
theorem localizedSliceGlueingToAbsolute_map_right_inverse_map_assoc
    [LocalizedSliceFamily J τ] {F G : LocalizedSliceGlueing J τ} (η : F ⟶ G)
    {U V : C} (f : V ⟶ U) :
    ((LocalizedSliceSheaf.equiv J τ V).inverse.map
        (((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom) ≫
          ((LocalizedSliceSheaf.equiv J τ V).functor.map (η.app V)))) ≫
      (LocalizedSliceSheaf.equiv J τ V).unitInv.app (G.obj V) =
        F.transition f ≫ η.app V := by
  let eV := LocalizedSliceSheaf.equiv J τ V
  -- Expand only the transported right factor so the unit pair cancels in one place.
  rw [Functor.map_comp, Category.assoc]
  have hη :
      eV.inverse.map (eV.functor.map (η.app V)) ≫ eV.unitInv.app (G.obj V) =
        eV.unitInv.app (F.obj V) ≫ η.app V := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ eV.unitInv.app (G.obj V))
        (Equivalence.inv_fun_map eV (F.obj V) (G.obj V) (η.app V))
  have hComposite :
      ((eV.inverse.map ((localizedSliceGlueingToAbsolute_transition
            (J := J) (τ := τ) F f).hom)) ≫
          eV.inverse.map (eV.functor.map (η.app V))) ≫
        eV.unitInv.app (G.obj V) =
          (eV.inverse.map ((localizedSliceGlueingToAbsolute_transition
              (J := J) (τ := τ) F f).hom) ≫
            eV.unitInv.app (F.obj V)) ≫
              η.app V := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ eV.inverse.map ((localizedSliceGlueingToAbsolute_transition
          (J := J) (τ := τ) F f).hom) ≫ k)
        hη
  have hTransition :
      (eV.inverse.map ((localizedSliceGlueingToAbsolute_transition
            (J := J) (τ := τ) F f).hom) ≫
          eV.unitInv.app (F.obj V)) ≫
        η.app V =
          F.transition f ≫ η.app V := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ η.app V)
        (localizedSliceGlueingToAbsolute_transition_inverse_map_assoc
          (J := J) (τ := τ) F f)
  simpa [Category.assoc] using hComposite.trans hTransition

/-- Helper for Remark 7.26.7: morphisms of localized glueings transport to morphisms of absolute
glueings by applying the local equivalences objectwise. -/
theorem localizedSliceGlueingToAbsolute_map_naturality [LocalizedSliceFamily J τ]
    {F G : LocalizedSliceGlueing J τ} (η : F ⟶ G) {U V : C} (f : V ⟶ U) :
    CommSq ((J.overMapPullback (Type (max u v)) f).map
        ((LocalizedSliceSheaf.equiv J τ U).functor.map (η.app U)))
      (localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom
      (localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) G f).hom
      ((LocalizedSliceSheaf.equiv J τ V).functor.map (η.app V)) := by
  let eV := LocalizedSliceSheaf.equiv J τ V
  -- Move the owner naturality square back to the localized site and compare there.
  refine CommSq.mk ?_
  apply eV.inverse.map_injective
  refine (cancel_mono (eV.unitInv.app (G.obj V))).1 ?_
  have hLeft :
      eV.inverse.map
          (((J.overMapPullback (Type (max u v)) f).map
              ((LocalizedSliceSheaf.equiv J τ U).functor.map (η.app U))) ≫
            (localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) G f).hom) ≫
        eV.unitInv.app (G.obj V) =
          ((LocalizedSliceSheaf.pullback J τ f).map (η.app U)) ≫ G.transition f := by
    simpa [Category.assoc] using
      localizedSliceGlueingToAbsolute_map_left_inverse_map_assoc
        (J := J) (τ := τ) η f
  have hRight :
      eV.inverse.map
          (((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom) ≫
            ((LocalizedSliceSheaf.equiv J τ V).functor.map (η.app V))) ≫
        eV.unitInv.app (G.obj V) =
          F.transition f ≫ η.app V := by
    exact localizedSliceGlueingToAbsolute_map_right_inverse_map_assoc
      (J := J) (τ := τ) η f
  exact hLeft.trans ((η.naturality f).w.trans hRight.symm)

/-- Helper for Remark 7.26.7: localized glueing data transport objectwise to absolute glueing data
along the localized slice-site equivalences. -/
def localizedSliceGlueingToAbsoluteGlueingFunctor [LocalizedSliceFamily J τ] :
    LocalizedSliceGlueing J τ ⥤ AbsoluteGlueing J where
  obj F :=
    { obj := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U)
      transition := fun {U V} f ↦
        localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f
      transition_id := localizedSliceGlueingToAbsolute_transition_id (J := J) (τ := τ) F
      transition_comp := fun f g ↦
        localizedSliceGlueingToAbsolute_transition_comp (J := J) (τ := τ) F f g }
  map η :=
    { app := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).functor.map (η.app U)
      naturality := fun f ↦
        localizedSliceGlueingToAbsolute_map_naturality (J := J) (τ := τ) η f }
  map_id F := by
    apply AbsoluteGlueing.Hom.ext
    funext U
    change (LocalizedSliceSheaf.equiv J τ U).functor.map (𝟙 (F.obj U)) = 𝟙 _
    simp
  map_comp η θ := by
    apply AbsoluteGlueing.Hom.ext
    funext U
    change (LocalizedSliceSheaf.equiv J τ U).functor.map (η.app U ≫ θ.app U) =
      (LocalizedSliceSheaf.equiv J τ U).functor.map (η.app U) ≫
        (LocalizedSliceSheaf.equiv J τ U).functor.map (θ.app U)
    simp

/-- Helper for Remark 7.26.7: the absolute-side roundtrip transition becomes the original
transition after postcomposing with the local counit component. -/
theorem absoluteLocalizedSliceGlueing_unit_transition_compat
    [LocalizedSliceFamily J τ] (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    CommSq
      ((J.overMapPullback (Type (max u v)) f).map
        ((LocalizedSliceSheaf.equiv J τ U).counit.app (F.obj U)))
      (((absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ) ⋙
          localizedSliceGlueingToAbsoluteGlueingFunctor (J := J) (τ := τ)).obj F).transition f).hom
      (F.transition f).hom
      ((LocalizedSliceSheaf.equiv J τ V).counit.app (F.obj V)) := by
  let eU := LocalizedSliceSheaf.equiv J τ U
  let eV := LocalizedSliceSheaf.equiv J τ V
  let A :=
    (J.overMapPullback (Type (max u v)) f).obj (eU.functor.obj (eU.inverse.obj (F.obj U)))
  have htransition :=
    absoluteGlueingToLocalizedSlice_transition_functor_map (J := J) (τ := τ) F f
  have hpair : eV.counitInv.app A ≫ eV.counit.app A = 𝟙 A := by
    exact eV.counitIso_inv_hom_id_app A
  have hround :
      (((absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ) ⋙
          localizedSliceGlueingToAbsoluteGlueingFunctor (J := J) (τ := τ)).obj F).transition f).hom =
        eV.counitInv.app A ≫
          eV.functor.map (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f) := by
    simp [A, eU, eV, absoluteGlueingToLocalizedSliceGlueingFunctor,
      localizedSliceGlueingToAbsoluteGlueingFunctor, localizedSliceGlueingToAbsolute_transition,
      localizedSliceGlueing_transition_iso, Category.assoc]
  refine CommSq.mk ?_
  -- Prefix the normalized transport identity by the inserted counit inverse and cancel the pair.
  rw [hround]
  have hpref :
      (eV.counitInv.app A ≫ eV.functor.map
          (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f)) ≫
        eV.counit.app (F.obj V) =
      (J.overMapPullback (Type (max u v)) f).map (eU.counit.app (F.obj U)) ≫
        (F.transition f).hom := by
    have hprefix :
        (eV.counitInv.app A ≫ eV.functor.map
            (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f)) ≫
            eV.counit.app (F.obj V) =
          eV.counitInv.app A ≫
            (eV.counit.app A ≫
              (J.overMapPullback (Type (max u v)) f).map (eU.counit.app (F.obj U)) ≫
                (F.transition f).hom) := by
      have hassoc :
          (eV.counitInv.app A ≫ eV.functor.map
              (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f)) ≫
              eV.counit.app (F.obj V) =
            eV.counitInv.app A ≫
              (eV.functor.map (absoluteGlueingToLocalizedSlice_transition (J := J) (τ := τ) F f) ≫
                eV.counit.app (F.obj V)) := by
        simp [Category.assoc]
      exact hassoc.trans (congrArg (fun k ↦ eV.counitInv.app A ≫ k) htransition)
    have hcancel :
        eV.counitInv.app A ≫
          (eV.counit.app A ≫
            (J.overMapPullback (Type (max u v)) f).map (eU.counit.app (F.obj U)) ≫
              (F.transition f).hom) =
          (J.overMapPullback (Type (max u v)) f).map (eU.counit.app (F.obj U)) ≫
            (F.transition f).hom := by
      rw [← Category.assoc]
      rw [hpair]
      simp
    exact hprefix.trans hcancel
  exact hpref.symm

/-- Helper for Remark 7.26.7: the localized-side roundtrip transition becomes the original
transition after postcomposing with the local unit inverse component. -/
theorem absoluteLocalizedSliceGlueing_counit_transition_compat
    [LocalizedSliceFamily J τ] (F : LocalizedSliceGlueing J τ) {U V : C} (f : V ⟶ U) :
    CommSq
      ((LocalizedSliceSheaf.pullback J τ f).map
        ((LocalizedSliceSheaf.equiv J τ U).unitInv.app (F.obj U)))
      (((localizedSliceGlueingToAbsoluteGlueingFunctor (J := J) (τ := τ) ⋙
          absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ)).obj F).transition f)
      (F.transition f)
      ((LocalizedSliceSheaf.equiv J τ V).unitInv.app (F.obj V)) := by
  let eU := LocalizedSliceSheaf.equiv J τ U
  let eV := LocalizedSliceSheaf.equiv J τ V
  have htransition :=
    localizedSliceGlueingToAbsolute_transition_inverse_map_assoc
      (J := J) (τ := τ) F f
  have hsource :
      (LocalizedSliceSheaf.pullback J τ f).map (eU.unitInv.app (F.obj U)) =
        eV.inverse.map
          ((J.overMapPullback (Type (max u v)) f).map
            (eU.counit.app (eU.functor.obj (F.obj U)))) := by
    rw [show ((LocalizedSliceSheaf.pullback J τ f).map (eU.unitInv.app (F.obj U))) =
        eV.inverse.map
          ((J.overMapPullback (Type (max u v)) f).map
            (eU.functor.map (eU.unitInv.app (F.obj U)))) by
          rfl]
    rw [show eU.functor.map (eU.unitInv.app (F.obj U)) =
        eU.counit.app (eU.functor.obj (F.obj U)) by
          exact (eU.counit_app_functor (F.obj U)).symm]
    rfl
  have hround :
      (((localizedSliceGlueingToAbsoluteGlueingFunctor (J := J) (τ := τ) ⋙
          absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ)).obj F).transition f) =
        (LocalizedSliceSheaf.pullback J τ f).map (eU.unitInv.app (F.obj U)) ≫
          eV.inverse.map
            ((localizedSliceGlueingToAbsolute_transition (J := J) (τ := τ) F f).hom) := by
    rw [hsource]
    rw [show ((LocalizedSliceSheaf.equiv J τ U).counitIso.hom.app
        ((LocalizedSliceSheaf.equiv J τ U).functor.obj (F.obj U))) =
      eU.counit.app (eU.functor.obj (F.obj U)) by
        rfl]
    rfl
  refine CommSq.mk ?_
  -- Expand the roundtrip transition and reuse the inverse-mapped owner transition identity.
  rw [hround]
  simpa [Category.assoc] using
    congrArg (fun k ↦ (LocalizedSliceSheaf.pullback J τ f).map (eU.unitInv.app (F.obj U)) ≫ k)
      htransition.symm

/-- Helper for Remark 7.26.7: the objectwise counit components of
`LocalizedSliceSheaf.equiv J τ U` assemble into the unit for the equivalence between absolute and
localized glueings. -/
noncomputable def absoluteLocalizedSliceGlueing_unitIso
    [LocalizedSliceFamily J τ] :
    𝟭 (AbsoluteGlueing J) ≅
      absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ) ⋙
        localizedSliceGlueingToAbsoluteGlueingFunctor (J := J) (τ := τ) := by
  -- Assemble the objectwise counit isomorphisms into the unit on absolute glueings.
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · refine
      { hom :=
          { app := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).counitInv.app (F.obj U)
            naturality := by
              intro U V f
              simpa using
                (CommSq.horiz_inv
                  (f := (J.overMapPullback (Type (max u v)) f).mapIso
                    ((LocalizedSliceSheaf.equiv J τ U).counitIso.app (F.obj U)))
                  (i := (LocalizedSliceSheaf.equiv J τ V).counitIso.app (F.obj V))
                  (absoluteLocalizedSliceGlueing_unit_transition_compat
                    (J := J) (τ := τ) F f)) }
        inv :=
          { app := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).counit.app (F.obj U)
            naturality := by
              intro U V f
              simpa using
                absoluteLocalizedSliceGlueing_unit_transition_compat
                  (J := J) (τ := τ) F f
            }
        hom_inv_id := by
          -- The objectwise counit inverse identities give the glueing identity.
          apply AbsoluteGlueing.Hom.ext
          funext U
          exact (LocalizedSliceSheaf.equiv J τ U).counitIso_inv_hom_id_app (F.obj U)
        inv_hom_id := by
          -- The objectwise counit identities give the opposite glueing identity.
          apply AbsoluteGlueing.Hom.ext
          funext U
          exact (LocalizedSliceSheaf.equiv J τ U).counitIso_hom_inv_id_app (F.obj U) }
  · intro F G η
    -- Naturality is checked objectwise via the counit naturality square.
    apply AbsoluteGlueing.Hom.ext
    funext U
    exact ((LocalizedSliceSheaf.equiv J τ U).counitInv_naturality (η.app U)).symm

/-- Helper for Remark 7.26.7: the objectwise unit components of
`LocalizedSliceSheaf.equiv J τ U` assemble into the counit for the equivalence between absolute
and localized glueings. -/
noncomputable def absoluteLocalizedSliceGlueing_counitIso
    [LocalizedSliceFamily J τ] :
    localizedSliceGlueingToAbsoluteGlueingFunctor (J := J) (τ := τ) ⋙
        absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ) ≅
      𝟭 (LocalizedSliceGlueing J τ) := by
  -- Assemble the objectwise unit isomorphisms into the counit on localized glueings.
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · refine
      { hom :=
          { app := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).unitInv.app (F.obj U)
            naturality := by
              intro U V f
              simpa using
                absoluteLocalizedSliceGlueing_counit_transition_compat
                  (J := J) (τ := τ) F f }
        inv :=
          { app := fun U ↦ (LocalizedSliceSheaf.equiv J τ U).unit.app (F.obj U)
            naturality := by
              intro U V f
              simpa using
                (CommSq.horiz_inv
                  (f := ((LocalizedSliceSheaf.pullback J τ f).mapIso
                    ((LocalizedSliceSheaf.equiv J τ U).unitIso.app (F.obj U))).symm)
                  (i := ((LocalizedSliceSheaf.equiv J τ V).unitIso.app (F.obj V)).symm)
                  (absoluteLocalizedSliceGlueing_counit_transition_compat
                    (J := J) (τ := τ) F f)) }
        hom_inv_id := by
          -- The objectwise unit inverse identities give the glueing identity.
          apply LocalizedSliceGlueing.Hom.ext
          funext U
          exact (LocalizedSliceSheaf.equiv J τ U).unitIso_inv_hom_id_app (F.obj U)
        inv_hom_id := by
          -- The objectwise unit identities give the opposite glueing identity.
          apply LocalizedSliceGlueing.Hom.ext
          funext U
          exact (LocalizedSliceSheaf.equiv J τ U).unitIso_hom_inv_id_app (F.obj U) }
  · intro F G η
    -- Naturality is checked objectwise via the unit naturality square.
    apply LocalizedSliceGlueing.Hom.ext
    funext U
    exact (LocalizedSliceSheaf.equiv J τ U).unitInv_naturality (η.app U)

/-- Helper for Remark 7.26.7: the localized glueing category is obtained from the absolute glueing
category by transporting along the equivalences `LocalizedSliceSheaf.equiv J τ U`. -/
def absoluteLocalizedSliceGlueingEquivalence [LocalizedSliceFamily J τ] :
    AbsoluteGlueing J ≌ LocalizedSliceGlueing J τ :=
  Equivalence.mk
    (absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ))
    (localizedSliceGlueingToAbsoluteGlueingFunctor (J := J) (τ := τ))
    (absoluteLocalizedSliceGlueing_unitIso (J := J) (τ := τ))
    (absoluteLocalizedSliceGlueing_counitIso (J := J) (τ := τ))

/-- The sheaf on `(C, J)` determines the localized glueing datum of Remark 7.26.7 by first forming
its absolute glueing and then transporting those local sheaves to the localized slice sites. -/
def sheafToLocalizedSliceGlueingFunctor [LocalizedSliceFamily J τ] :
    Sheaf J (Type (max u v)) ⥤ LocalizedSliceGlueing J τ :=
  sheafToAbsoluteGlueingFunctor J ⋙
    absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ)

/-- Remark 7.26.7 (tag `0GWL`): for a family `U ↦ U_τ ⊂ C/U` satisfying the localized-slice
hypotheses, the canonical functor from sheaves on `(C, J)` to localized glueing data is an
equivalence. This is the source-faithful localized variant of Lemma 7.26.6: the transition maps
are required to be isomorphisms only for arrows lying in the corresponding localized subsite. -/
instance sheafToLocalizedSliceGlueingFunctor_isEquivalence [LocalizedSliceFamily J τ] :
    Functor.IsEquivalence (sheafToLocalizedSliceGlueingFunctor J τ) := by
  -- Route correction: the localized remark is now proved by transporting Lemma 7.26.6 across the
  -- objectwise equivalence `LocalizedSliceSheaf.equiv`, rather than by rebuilding the sheaf from
  -- localized terminal sections.
  let _ :
      Functor.IsEquivalence
        (absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ)) :=
    (absoluteLocalizedSliceGlueingEquivalence (J := J) (τ := τ)).isEquivalence_functor
  simpa [sheafToLocalizedSliceGlueingFunctor] using
    (show Functor.IsEquivalence
      (sheafToAbsoluteGlueingFunctor J ⋙
        absoluteGlueingToLocalizedSliceGlueingFunctor (J := J) (τ := τ)) from inferInstance)

end GrothendieckTopology
end CategoryTheory
