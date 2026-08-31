module

public import Mathlib.CategoryTheory.Sites.CoversTop
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Over
public import stacks_project.Chap06.Definition_6_31_2
public import stacks_project.Chap06.Lemma_6_21_6
public import stacks_project.Chap06.Glueing_data_for_sheaves_on_an_open_cover

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Presheaf
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u v

/-
Domain-style sampling for Lemma 6.33.1:
- primary domain: gluing morphisms of sheaves on an open cover of `X`;
- sampled owner declarations:
  `sheafHom`,
  `TopCat.Presheaf.IsCompatible`,
  `sheafHomSectionsEquiv`,
  `sheafHomSectionsEquiv_symm_apply_coe_apply`,
  `FamilyOfElementsOnObjects.IsCompatible.existsUnique_section`,
  `GrothendieckTopology.CoversTop.sections_ext`,
  and the restriction notations `↾` and `↾ₘ`;
- owner abstraction: the core/canonical owner is the sheaf `sheafHom ℱ 𝒢`, whose value on
  `U i` is definitionally the type of morphisms `ℱ ↾ U i ⟶ 𝒢 ↾ U i`;
- primitive data: an open cover `U` with `TopologicalSpace.IsOpenCover U` and a family of local
  morphisms `φ i : ℱ ↾ U i ⟶ 𝒢 ↾ U i`;
- derived API: the canonical local Hom section `localHomSection (U i) ℱ 𝒢 (φ i)` of
  `sheafHom ℱ 𝒢`, pairwise compatibility via `TopCat.Presheaf.IsCompatible`, the glued global
  section from `existsUnique_section`, and the bridge
  `sheafHomSectionsEquiv ℱ 𝒢 : (sheafHom ℱ 𝒢).1.sections ≃ (ℱ ⟶ 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that compatible local morphisms glue uniquely;
- `core/canonical`: the owner sheaf `sheafHom ℱ 𝒢`;
- `bridge/view`: the equivalence `sheafHomSectionsEquiv ℱ 𝒢`.

The refinement target is therefore the source-facing gluing theorem, implemented directly through
the owner-level compatibility and gluing API of `sheafHom ℱ 𝒢` rather than by parallel overlap
transport definitions.
-/

private theorem open_cover_coversTop
    {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    (Opens.grothendieckTopology X).CoversTop U := by
  intro W x hx
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, ⟨hx, hxi⟩⟩
  exact ⟨i, ⟨homOfLE inf_le_right⟩⟩

private theorem exists_unique_hom_of_open_cover_sections
    {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U)
    (ℱ 𝒢 : X.Sheaf (Type u))
    (φ : FamilyOfElementsOnObjects (sheafHom ℱ 𝒢).1 U)
    (hφ : φ.IsCompatible) :
    ∃! ψ : ℱ ⟶ 𝒢, ∀ i,
      ((Opens.grothendieckTopology X).overPullback (Type u) (U i)).map ψ = φ i := by
  let hcover := open_cover_coversTop U hU
  let s := hφ.section_ hcover (sheafHom ℱ 𝒢).2
  let e := sheafHomSectionsEquiv ℱ 𝒢
  refine ⟨e s, ?_, ?_⟩
  · intro i
    rw [← sheafHomSectionsEquiv_symm_apply_coe_apply (e s) (op (U i))]
    rw [Equiv.symm_apply_apply]
    exact hφ.section_apply hcover (sheafHom ℱ 𝒢).2 i
  · intro ψ hψ
    apply e.symm.injective
    apply hcover.sections_ext (sheafHom ℱ 𝒢)
    intro i
    have hψ' : (e.symm ψ).1 (op (U i)) = φ i := by
      simpa [e] using hψ i
    have hs : (e.symm (e s)).1 (op (U i)) = φ i := by
      rw [Equiv.symm_apply_apply]
      exact hφ.section_apply hcover (sheafHom ℱ 𝒢).2 i
    exact hψ'.trans hs.symm

abbrev overEquiv {X : TopCat.{u}} (U : Opens X) : Over U ≌ Opens (TopCat.of U) :=
  U.overEquivalence

abbrev overFunctor {X : TopCat.{u}} (U : Opens X) : Over U ⥤ Opens (TopCat.of U) :=
  (overEquiv U).functor

abbrev inclusionFunctor {X : TopCat.{u}} (U : Opens X) : Opens (TopCat.of U) ⥤ Opens X :=
  (Opens.isOpenEmbedding U).functor

noncomputable def openEmbedding_sheafPullbackIso
    {Y Z : TopCat.{u}} {f : Y ⟶ Z} (hf : Topology.IsOpenEmbedding f) :
    TopCat.Sheaf.pullback (Type u) f ≅ hf.sheafPullback (Type u) :=
  haveI := hf.functor_isContinuous
  Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
    (hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z))

theorem overEquivalence_functor_obj_eq
    {X : TopCat.{u}} (U : Opens X) (V : Over U) :
    (inclusionFunctor U).obj ((overFunctor U).obj V) = V.left := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, (leOfHom V.hom) hx⟩, hx, rfl⟩

noncomputable def overEquivalenceFunctorCompInclusionIso
    {X : TopCat.{u}} (U : Opens X) :
    overFunctor U ⋙ inclusionFunctor U ≅ Over.forget U :=
  NatIso.ofComponents
    (fun V ↦ eqToIso (overEquivalence_functor_obj_eq U V))
    (fun {V W} f ↦ by apply Subsingleton.elim)

noncomputable def overEquivalenceFunctorCompInclusionIsoOp
    {X : TopCat.{u}} (U : Opens X) :
    (overFunctor U).op ⋙ (inclusionFunctor U).op ≅ (Over.forget U).op :=
  NatIso.ofComponents
    (fun V ↦ eqToIso (congrArg Opposite.op (overEquivalence_functor_obj_eq U V.unop)))
    (fun {V W} f ↦ by apply Subsingleton.elim)

noncomputable def restrictOpenToOverPullbackIso
    {X : TopCat.{u}} (U : Opens X) (ℱ : X.Sheaf (Type u)) :
    (overFunctor U).op ⋙ (ℱ ↾ U).1 ≅ (((Opens.grothendieckTopology X).overPullback (Type u) U).obj ℱ).1 := by
  let e :=
    (TopCat.Sheaf.forget (Type u) (TopCat.of U)).mapIso
      ((openEmbedding_sheafPullbackIso U.isOpenEmbedding).app ℱ)
  refine Functor.isoWhiskerLeft (overFunctor U).op e ≪≫ ?_
  simpa [Topology.IsOpenEmbedding.sheafPullback,
    CategoryTheory.GrothendieckTopology.overPullback] using
    (Functor.associator ((overFunctor U).op) ((inclusionFunctor U).op) ℱ.1).symm ≪≫
      Functor.isoWhiskerRight (overEquivalenceFunctorCompInclusionIsoOp U) ℱ.1

/-- The canonical section of `sheafHom ℱ 𝒢` on `U` corresponding to a local morphism
`ℱ ↾ U ⟶ 𝒢 ↾ U`. -/
noncomputable def localHomSection
    {X : TopCat.{u}} (U : Opens X) (ℱ 𝒢 : X.Sheaf (Type u))
    (φ : ℱ ↾ U ⟶ 𝒢 ↾ U) :
    (((Opens.grothendieckTopology X).overPullback (Type u) U).obj ℱ ⟶
      ((Opens.grothendieckTopology X).overPullback (Type u) U).obj 𝒢) := by
    let e := (overEquiv U).op
    let F : ((Opens (TopCat.of U))ᵒᵖ ⥤ Type u) ⥤ ((Over U)ᵒᵖ ⥤ Type u) :=
      e.congrLeft.inverse
    let αℱ := restrictOpenToOverPullbackIso U ℱ
    let α𝒢 := restrictOpenToOverPullbackIso U 𝒢
    exact ⟨αℱ.inv ≫ F.map φ.hom ≫ α𝒢.hom⟩

private theorem localHomSection_injective
    {X : TopCat.{u}} (U : Opens X) (ℱ 𝒢 : X.Sheaf (Type u)) :
    Function.Injective (localHomSection U ℱ 𝒢) := by
  intro φ ψ h
  apply CategoryTheory.Sheaf.hom_ext
  let e := (overEquiv U).op
  let F : ((Opens (TopCat.of U))ᵒᵖ ⥤ Type u) ⥤ ((Over U)ᵒᵖ ⥤ Type u) :=
    e.congrLeft.inverse
  let αℱ := restrictOpenToOverPullbackIso U ℱ
  let α𝒢 := restrictOpenToOverPullbackIso U 𝒢
  have h' : F.map φ.hom = F.map ψ.hom := by
    simpa [localHomSection, Category.assoc] using
      congrArg (fun f ↦ αℱ.hom ≫ f.hom ≫ α𝒢.inv) h
  exact F.map_injective h'

@[simp] private theorem localHomSection_restrictOpenHom
    {X : TopCat.{u}} {U : Opens X} {ℱ 𝒢 : X.Sheaf (Type u)} (ψ : ℱ ⟶ 𝒢) :
    localHomSection U ℱ 𝒢 (ψ ↾ₘ U) =
      ((Opens.grothendieckTopology X).overPullback (Type u) U).map ψ := by
  apply CategoryTheory.Sheaf.hom_ext
  ext V x
  simp [localHomSection, restrictOpenToOverPullbackIso, TopCat.Sheaf.forget,
    Category.assoc]
  let W : (Opens (TopCat.of U))ᵒᵖ := op ((overFunctor U).obj (unop V))
  let η :=
    Functor.isoWhiskerRight (openEmbedding_sheafPullbackIso U.isOpenEmbedding)
      (TopCat.Sheaf.forget (Type u) (TopCat.of U))
  let f := (overEquivalenceFunctorCompInclusionIsoOp U).inv.app V
  let z := ℱ.obj.map f x
  have hη' :
      (((TopCat.Sheaf.pullback (Type u) U.inclusion').map ψ).hom.app W) ≫
          (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).hom.app 𝒢).hom.app W) =
        (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).hom.app ℱ).hom.app W) ≫
          (ψ.hom.app (((overFunctor U).op ⋙ (inclusionFunctor U).op).obj V)) := by
    simpa [η, W, Topology.IsOpenEmbedding.sheafPullback, TopCat.Sheaf.forget,
      Functor.sheafPushforwardContinuous, Functor.comp_map,
      ObjectProperty.FullSubcategory.comp_hom, Presheaf.comp_app, Sheaf.comp_app,
      Category.assoc] using congrArg (fun t ↦ t.app W) (η.hom.naturality ψ)
  have hηsimp :
      (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).hom.app 𝒢).hom.app W)
        (((TopCat.Sheaf.pullback (Type u) U.inclusion').map ψ).hom.app W
          (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).inv.app ℱ).hom.app W z)) =
        ψ.hom.app (((overFunctor U).op ⋙ (inclusionFunctor U).op).obj V) z := by
    let e := (TopCat.Sheaf.forget (Type u) (TopCat.of U)).mapIso
      ((openEmbedding_sheafPullbackIso U.isOpenEmbedding).app ℱ)
    have hz :
        (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).hom.app ℱ).hom.app W)
          (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).inv.app ℱ).hom.app W z) = z := by
      simpa [e] using
        CategoryTheory.FunctorToTypes.inv_hom_id_app_apply
          (((TopCat.Sheaf.pullback (Type u) U.inclusion').obj ℱ).obj)
          (((U.isOpenEmbedding.sheafPullback (Type u)).obj ℱ).obj) e W z
    simpa [hz] using congrFun hη'
          (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).inv.app ℱ).hom.app W z)
  have hηsimp' :
      (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).hom.app 𝒢).hom.app
        (op ((overFunctor U).obj (unop V))))
        (((TopCat.Sheaf.pullback (Type u) U.inclusion').map ψ).hom.app
          (op ((overFunctor U).obj (unop V)))
          (((openEmbedding_sheafPullbackIso U.isOpenEmbedding).inv.app ℱ).hom.app
            (op ((overFunctor U).obj (unop V))) (ℱ.obj.map f x))) =
        ψ.hom.app (((overFunctor U).op ⋙ (inclusionFunctor U).op).obj V)
          (ℱ.obj.map f x) := by
    simpa [W, z]
      using hηsimp
  have hηouter := congrArg (𝒢.obj.map ((overEquivalenceFunctorCompInclusionIsoOp U).hom.app V))
    hηsimp'
  refine hηouter.trans ?_
  have h :
      ψ.hom.app (((overFunctor U).op ⋙ (inclusionFunctor U).op).obj V) z =
        𝒢.obj.map f (ψ.hom.app ((Over.forget U).op.obj V) x) := by
    simpa [z, FunctorToTypes.map_comp_apply] using congrFun (ψ.hom.naturality f) x
  rw [h]
  let y := ψ.hom.app ((Over.forget U).op.obj V) x
  have hy :
      𝒢.obj.map ((overEquivalenceFunctorCompInclusionIsoOp U).hom.app V) (𝒢.obj.map f y) = y := by
    refine (FunctorToTypes.map_comp_apply 𝒢.obj f
      ((overEquivalenceFunctorCompInclusionIsoOp U).hom.app V) y).symm.trans ?_
    have hf : f ≫ (overEquivalenceFunctorCompInclusionIsoOp U).hom.app V = 𝟙 _ :=
      Iso.inv_hom_id_app (overEquivalenceFunctorCompInclusionIsoOp U) V
    rw [hf]
    exact congrFun (𝒢.obj.map_id ((Over.forget U).op.obj V)) y
  simpa [y] using hy

/-- A family of local morphisms on an open cover is compatible on pairwise overlaps if the
associated local sections of the owner sheaf `sheafHom ℱ 𝒢` agree after restriction to each
intersection `U i ∩ U j`. -/
def IsCompatibleOnOverlaps
    {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X) (ℱ 𝒢 : X.Sheaf (Type u))
    (φ : ∀ i, ℱ ↾ U i ⟶ 𝒢 ↾ U i) : Prop :=
  TopCat.Presheaf.IsCompatible (sheafHom ℱ 𝒢).1 U
    (fun i ↦ localHomSection (U i) ℱ 𝒢 (φ i))

/-- The source-facing overlap condition is exactly pairwise equality of the restricted local Hom
sections on `U i ∩ U j`. -/
theorem isCompatibleOnOverlaps_iff
    {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X) (ℱ 𝒢 : X.Sheaf (Type u))
    (φ : ∀ i, ℱ ↾ U i ⟶ 𝒢 ↾ U i) :
    IsCompatibleOnOverlaps U ℱ 𝒢 φ ↔
      ∀ i j,
        (sheafHom ℱ 𝒢).1.map (infLELeft (U i) (U j)).op
            (localHomSection (U i) ℱ 𝒢 (φ i)) =
          (sheafHom ℱ 𝒢).1.map (infLERight (U i) (U j)).op
            (localHomSection (U j) ℱ 𝒢 (φ j)) := by
  rfl

theorem localHomSection_eq_iff
    {X : TopCat.{u}} (U : Opens X) (ℱ 𝒢 : X.Sheaf (Type u))
    {φ ψ : ℱ ↾ U ⟶ 𝒢 ↾ U} :
    localHomSection U ℱ 𝒢 φ = localHomSection U ℱ 𝒢 ψ ↔ φ = ψ := by
  constructor
  · intro h
    exact localHomSection_injective U ℱ 𝒢 h
  · intro h
    simpa [h]

private theorem isCompatibleOnOverlaps_iff_familyIsCompatible
    {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X) (ℱ 𝒢 : X.Sheaf (Type u))
    (φ : ∀ i, ℱ ↾ U i ⟶ 𝒢 ↾ U i) :
    IsCompatibleOnOverlaps U ℱ 𝒢 φ ↔
      FamilyOfElementsOnObjects.IsCompatible
        (show FamilyOfElementsOnObjects (sheafHom ℱ 𝒢).1 U from
          fun i ↦ localHomSection (U i) ℱ 𝒢 (φ i)) := by
  constructor
  · intro h Z i j f g
    let hfg : Z ⟶ U i ⊓ U j := homOfLE <| le_inf (leOfHom f) (leOfHom g)
    have hf : f = hfg ≫ infLELeft (U i) (U j) := Subsingleton.elim _ _
    have hg : g = hfg ≫ infLERight (U i) (U j) := Subsingleton.elim _ _
    calc
      (sheafHom ℱ 𝒢).1.map f.op (localHomSection (U i) ℱ 𝒢 (φ i))
          = (sheafHom ℱ 𝒢).1.map hfg.op
              ((sheafHom ℱ 𝒢).1.map (infLELeft (U i) (U j)).op
                (localHomSection (U i) ℱ 𝒢 (φ i))) := by
                  rw [hf, op_comp, FunctorToTypes.map_comp_apply]
      _ = (sheafHom ℱ 𝒢).1.map hfg.op
            ((sheafHom ℱ 𝒢).1.map (infLERight (U i) (U j)).op
              (localHomSection (U j) ℱ 𝒢 (φ j))) := by
                exact congrArg ((sheafHom ℱ 𝒢).1.map hfg.op) (h i j)
      _ = (sheafHom ℱ 𝒢).1.map g.op (localHomSection (U j) ℱ 𝒢 (φ j)) := by
            rw [hg, op_comp, FunctorToTypes.map_comp_apply]
  · intro h i j
    exact h (U i ⊓ U j) i j (infLELeft (U i) (U j)) (infLERight (U i) (U j))

private theorem restrict_eq_iff_overPullback_eq_localHomSection
    {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X) (ℱ 𝒢 : X.Sheaf (Type u))
    (φ : ∀ i, ℱ ↾ U i ⟶ 𝒢 ↾ U i) (ψ : ℱ ⟶ 𝒢) :
    (∀ i, ψ ↾ₘ U i = φ i) ↔
      (∀ i, ((Opens.grothendieckTopology X).overPullback (Type u) (U i)).map ψ =
        localHomSection (U i) ℱ 𝒢 (φ i)) := by
  constructor
  · intro h i
    simpa using congrArg (localHomSection (U i) ℱ 𝒢) (h i)
  · intro h i
    exact localHomSection_injective (U i) ℱ 𝒢 (by simpa using h i)

-- Proof sketch: regard the local morphisms as a compatible family of sections of `sheafHom ℱ 𝒢`,
-- glue that family by `exists_unique_hom_of_open_cover_sections`, and translate the resulting
-- global section back to a morphism `ℱ ⟶ 𝒢` using `sheafHomSectionsEquiv`.
/-- Lemma 6.33.1: a family of local morphisms `ℱ|_{U i} ⟶ 𝒢|_{U i}` on an open cover of `X`
which agrees on pairwise overlaps glues uniquely to a global morphism `ℱ ⟶ 𝒢`. -/
theorem exists_unique_hom_of_open_cover
    {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U)
    (ℱ 𝒢 : X.Sheaf (Type u))
    (φ : ∀ i, ℱ ↾ U i ⟶ 𝒢 ↾ U i)
    (hφ : IsCompatibleOnOverlaps U ℱ 𝒢 φ) :
    ∃! ψ : ℱ ⟶ 𝒢, ∀ i, ψ ↾ₘ U i = φ i := by
  obtain ⟨ψ, hψ, huniq⟩ :=
    exists_unique_hom_of_open_cover_sections U hU ℱ 𝒢
      (fun i ↦ localHomSection (U i) ℱ 𝒢 (φ i))
      ((isCompatibleOnOverlaps_iff_familyIsCompatible U ℱ 𝒢 φ).1 hφ)
  refine ⟨ψ, (restrict_eq_iff_overPullback_eq_localHomSection U ℱ 𝒢 φ ψ).2 hψ, ?_⟩
  intro ψ hψloc
  exact huniq ψ ((restrict_eq_iff_overPullback_eq_localHomSection U ℱ 𝒢 φ ψ).1 hψloc)
