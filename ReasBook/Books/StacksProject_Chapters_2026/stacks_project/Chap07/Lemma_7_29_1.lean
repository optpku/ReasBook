module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- A functor is source-locally faithful for a topology on the source if equal arrows become equal
after restricting along a covering sieve in the source site. -/
class IsSourceLocallyFaithful (u : C ⥤ D) (J : GrothendieckTopology C) : Prop where
  equalizer_mem {U' U : C} (a b : U' ⟶ U) (h : u.map a = u.map b) :
    Sieve.equalizer a b ∈ J U'

/-- A functor is source-locally full for a topology on the source if every arrow between objects in
the image locally comes from an arrow in the source site. -/
class IsSourceLocallyFull (u : C ⥤ D) (J : GrothendieckTopology C) : Prop where
  imageSieve_mem {U' U : C} (c : u.obj U' ⟶ u.obj U) : u.imageSieve c ∈ J U'

end CategoryTheory.Functor

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace Functor

/-- Helper for Lemma 7.29.1: over an object of the form `u(U)`, the counit of the
right-Kan-extension adjunction is an isomorphism because source-local fullness supplies local
lifts and source-local faithfulness supplies the overlap equalities needed for sheaf glueing. -/
private theorem source_local_isIso_ranCounit_app
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]
    (Y : Sheaf J (Type w)) (U : C) (X : Type w) :
    IsIso ((yoneda.map ((u.op.ranCounit.app Y.obj).app (op U))).app (op X)) := by
  set_option backward.isDefEq.respectTransparency false in
    -- Route correction: this is the dense-subsite counit proof with the image/equalizer covers
    -- supplied directly by the source-local hypotheses rather than by an `IsDenseSubsite` owner.
    rw [isIso_iff_bijective]
    constructor
    · intro f₁ f₂ e
      -- Two candidate sections agree once they agree after every source-local lift of `g`.
      apply (isPointwiseRightKanExtensionRanCounit u.op Y.1 (.op (u.obj U))).hom_ext
      rintro ⟨⟨⟨⟩⟩, ⟨W⟩, g⟩
      obtain ⟨g, rfl⟩ : ∃ g' : u.obj W ⟶ u.obj U, g = g'.op := ⟨g.unop, rfl⟩
      apply (Y.2 X _ (IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) g)).isSeparatedFor.ext
      dsimp
      rintro V iVW ⟨iVU, e'⟩
      have := congr($e ≫ Y.1.map iVU.op)
      simp only [comp_obj, yoneda_map_app, Category.assoc, comp_map,
        ← NatTrans.naturality, op_obj, op_map, Quiver.Hom.unop_op, ← map_comp_assoc,
        ← op_comp, ← e'] at this ⊢
      simpa [← NatTrans.naturality] using this
    · intro f
      -- We glue the source-local lifts of `f` to build the universal cone element.
      have (X Y Z) (f : X ⟶ Y) (g : u.obj Y ⟶ u.obj Z) (hf : u.imageSieve g f) : Exists _ := hf
      choose l hl using this
      let c : Limits.Cone (StructuredArrow.proj (op (u.obj U)) u.op ⋙ Y.obj) := by
        refine ⟨X, ⟨fun g ↦ ?_, ?_⟩⟩
        · refine Y.2.amalgamate ⟨_, IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) g.hom.unop⟩
            (fun I ↦ f ≫ Y.1.map (l _ _ _ _ _ I.hf).op) fun I₁ I₂ r ↦ ?_
          apply (Y.2 X _ (IsSourceLocallyFaithful.equalizer_mem (u := u) (J := J)
            (r.g₁ ≫ l _ _ _ _ _ I₁.hf) (r.g₂ ≫ l _ _ _ _ _ I₂.hf) ?_)).isSeparatedFor.ext
              fun V iUV (hiUV : _ = _) ↦ ?_
          · simp only [const_obj_obj, op_obj, map_comp, hl]
            simp only [← map_comp_assoc, r.w]
          · simp [← map_comp, ← op_comp, hiUV]
        · dsimp
          rintro ⟨⟨⟨⟩⟩, ⟨W₁⟩, g₁⟩ ⟨⟨⟨⟩⟩, ⟨W₂⟩, g₂⟩ ⟨⟨⟨⟨⟩⟩⟩, i, hi⟩
          dsimp at g₁ g₂ i hi
          have h : g₂ = g₁ ≫ (u.map i.unop).op := by simpa only [Category.id_comp] using hi
          rcases h with ⟨rfl⟩
          have h : ∃ g' : u.obj W₁ ⟶ u.obj U, g₁ = g'.op := ⟨g₁.unop, rfl⟩
          rcases h with ⟨g, rfl⟩
          have h : ∃ i' : W₂ ⟶ W₁, i = i'.op := ⟨i.unop, rfl⟩
          rcases h with ⟨i, rfl⟩
          simp only [unop_comp, Quiver.Hom.unop_op, Category.id_comp]
          apply Y.2.hom_ext ⟨_, IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) (u.map i ≫ g)⟩
          intro I
          simp only [Presheaf.IsSheaf.amalgamate_map, Category.assoc, ← Functor.map_comp, ← op_comp]
          let I' :
              GrothendieckTopology.Cover.Arrow
                ⟨_, IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) g⟩ :=
            ⟨_, I.f ≫ i, ⟨l _ _ _ _ _ I.hf, by simp [hl]⟩⟩
          refine Eq.trans ?_ (Y.2.amalgamate_map _ _ _ I').symm
          apply (Y.2 X _ (IsSourceLocallyFaithful.equalizer_mem (u := u) (J := J)
            (l _ _ _ _ _ I.hf) (l _ _ _ _ _ I'.hf) (by simp [I', hl]))).isSeparatedFor.ext
              fun V iUV (hiUV : _ = _) ↦ ?_
          simp [I', ← Functor.map_comp, ← op_comp, hiUV]
      refine ⟨(isPointwiseRightKanExtensionRanCounit u.op Y.1 (.op (u.obj U))).lift c, ?_⟩
      -- The glued cone is forced to recover the original section at the identity object.
      have := (isPointwiseRightKanExtensionRanCounit u.op Y.1 (.op (u.obj U))).fac c (.mk (𝟙 _))
      simp only [id_obj, comp_obj, StructuredArrow.proj_obj, StructuredArrow.mk_right,
        RightExtension.coneAt_pt, RightExtension.mk_left, RightExtension.coneAt_π_app,
        const_obj_obj, op_obj, StructuredArrow.mk_hom_eq_self, map_id, whiskeringLeft_obj_obj,
        RightExtension.mk_hom, Category.id_comp] at this
      simp only [c, id_obj, yoneda_map_app, this]
      apply Y.2.hom_ext ⟨_, IsSourceLocallyFull.imageSieve_mem (u := u) (J := J) (𝟙 (u.obj U))⟩
      intro I
      apply (Y.2 X _ (IsSourceLocallyFaithful.equalizer_mem (u := u) (J := J)
        (l _ _ _ _ _ I.hf) I.f (by simp [hl]))).isSeparatedFor.ext fun V iUV (hiUV : _ = _) ↦ ?_
      simp [← Functor.map_comp, ← op_comp, hiUV]

/-- Helper for Lemma 7.29.1: the source-local computation on `u(U)` upgrades to the counit
isomorphism for the sheaf adjunction itself by reflecting through `sheafToPresheaf` and `yoneda`. -/
private instance source_local_counit_isIso
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]
    (Y : Sheaf J (Type w)) :
    IsIso ((u.sheafAdjunctionCocontinuous (Type w) J K).counit.app Y) := by
  -- Reflect the objectwise counit through the faithful forgetful functors to presheaves.
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects (sheafToPresheaf J (Type w))
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨U⟩
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects yoneda
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨X⟩
  simpa [Functor.sheafAdjunctionCocontinuous_counit_app_hom]
    using source_local_isIso_ranCounit_app (J := J) (K := K) u Y U X

/-- Helper for Lemma 7.29.1: after the source-local counit computation, the unit evaluated on an
object of the form `u(U)` is bijective because the right adjoint is fully faithful. -/
private theorem source_local_unit_bijective_on_image
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf K (Type w)) (U : C) :
    Function.Bijective (((u.sheafAdjunctionCocontinuous (Type w) J K).unit.app F).hom.app
      (op (u.obj U))) := by
  let adj := u.sheafAdjunctionCocontinuous (Type w) J K
  letI : IsIso adj.counit := by
    exact NatIso.isIso_of_isIso_app _
  -- Since the counit is invertible, the right adjoint is fully faithful, hence the unit becomes
  -- invertible after applying the left adjoint.
  let ff : (u.sheafPushforwardCocontinuous (Type w) J K).FullyFaithful :=
    CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit (h := adj)
  letI : (u.sheafPushforwardCocontinuous (Type w) J K).Full := ff.full
  letI : (u.sheafPushforwardCocontinuous (Type w) J K).Faithful := ff.faithful
  haveI : IsIso ((u.sheafPushforwardContinuous (Type w) J K).map (adj.unit.app F)) := by
    infer_instance
  let e := (asIso ((sheafToPresheaf J (Type w)).map
    ((u.sheafPushforwardContinuous (Type w) J K).map (adj.unit.app F)))).app (op U)
  have he : e.hom = ((adj.unit.app F).hom.app (op (u.obj U))) := rfl
  rw [← he]
  exact (isIso_iff_bijective _).mp inferInstance

/-- Helper for Lemma 7.29.1: the unit is an isomorphism because sections of the target sheaf are
locally determined on image covers, and the local inverse on those image objects glues uniquely. -/
private instance source_local_unit_isIso
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf K (Type w)) :
    IsIso ((u.sheafAdjunctionCocontinuous (Type w) J K).unit.app F) := by
  let adj := u.sheafAdjunctionCocontinuous (Type w) J K
  let F' :=
    (u.sheafPushforwardCocontinuous (Type w) J K).obj
      ((u.sheafPushforwardContinuous (Type w) J K).obj F)
  let η := ((adj.unit.app F).hom : F.obj ⟶ F'.obj)
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects (sheafToPresheaf K (Type w))
  rw [NatTrans.isIso_iff_isIso_app]
  intro ⟨V⟩
  rw [isIso_iff_bijective]
  constructor
  · intro s t hst
    -- Injectivity is checked on the cover by image objects, where the unit is already bijective.
    apply Functor.IsCoverDense.ext u F V
    intro U f
    apply (source_local_unit_bijective_on_image (J := J) (K := K) u F U).1
    have hs : η.app (op (u.obj U)) (F.obj.map f.op s) = F'.obj.map f.op (η.app (op V) s) :=
      congrFun (η.naturality f.op) s
    have hmid : F'.obj.map f.op (η.app (op V) s) = F'.obj.map f.op (η.app (op V) t) :=
      congrArg (F'.obj.map f.op) hst
    have ht : F'.obj.map f.op (η.app (op V) t) = η.app (op (u.obj U)) (F.obj.map f.op t) := by
      simpa using (congrFun (η.naturality f.op) t).symm
    exact hs.trans (hmid.trans ht)
  · intro y
    -- We first choose inverse images on every image object and then assemble them by sheaf glueing.
    let imagePreimage : ∀ U : C, F'.obj.obj (op (u.obj U)) → F.obj.obj (op (u.obj U)) :=
      fun U z ↦ ((source_local_unit_bijective_on_image (J := J) (K := K) u F U).2 z).choose
    have imagePreimage_spec :
        ∀ U : C, ∀ z : F'.obj.obj (op (u.obj U)),
          η.app (op (u.obj U)) (imagePreimage U z) = z := by
      intro U z
      exact ((source_local_unit_bijective_on_image (J := J) (K := K) u F U).2 z).choose_spec
    let localFamily :
        CategoryTheory.Presieve.FamilyOfElements F.obj (CategoryTheory.Presieve.coverByImage u V) :=
      fun Y g hg ↦
        let l := Nonempty.some hg
        F.obj.map l.lift.op (imagePreimage l.obj (F'.obj.map l.map.op y))
    have localFamily_spec :
        ∀ {Y : D} (g : Y ⟶ V) (hg : Presieve.coverByImage u V g),
          η.app (op Y) (localFamily g hg) = F'.obj.map g.op y := by
      intro Y g hg
      let l := Nonempty.some hg
      calc
        η.app (op Y) (F.obj.map l.lift.op (imagePreimage l.obj (F'.obj.map l.map.op y)))
            = F'.obj.map l.lift.op
                (η.app (op (u.obj l.obj)) (imagePreimage l.obj (F'.obj.map l.map.op y))) := by
                  exact congrFun (η.naturality l.lift.op) _
        _ = F'.obj.map l.lift.op (F'.obj.map l.map.op y) := by
          rw [imagePreimage_spec]
        _ = F'.obj.map g.op y := by
          rw [← FunctorToTypes.map_comp_apply]
          simp [← op_comp, l.fac]
    have localFamily_compatible : localFamily.Compatible := by
      intro Y₁ Y₂ Z iZY₁ iZY₂ g₁ g₂ hg₁ hg₂ e
      -- Compatibility is reduced to image objects, where injectivity is already available.
      apply Functor.IsCoverDense.ext u F Z
      intro W k
      apply (source_local_unit_bijective_on_image (J := J) (K := K) u F W).1
      have h₁ :
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₁).op) (localFamily g₁ hg₁)) =
            F'.obj.map (k ≫ iZY₁).op (F'.obj.map g₁.op y) := by
        calc
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₁).op) (localFamily g₁ hg₁))
              = F'.obj.map (k ≫ iZY₁).op (η.app (op Y₁) (localFamily g₁ hg₁)) := by
                  exact congrFun (η.naturality ((k ≫ iZY₁).op)) (localFamily g₁ hg₁)
          _ = F'.obj.map (k ≫ iZY₁).op (F'.obj.map g₁.op y) := by rw [localFamily_spec]
      have h₂ :
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₂).op) (localFamily g₂ hg₂)) =
            F'.obj.map (k ≫ iZY₂).op (F'.obj.map g₂.op y) := by
        calc
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₂).op) (localFamily g₂ hg₂))
              = F'.obj.map (k ≫ iZY₂).op (η.app (op Y₂) (localFamily g₂ hg₂)) := by
                  exact congrFun (η.naturality ((k ≫ iZY₂).op)) (localFamily g₂ hg₂)
          _ = F'.obj.map (k ≫ iZY₂).op (F'.obj.map g₂.op y) := by rw [localFamily_spec]
      have hk₁' :
          F.obj.map k.op (F.obj.map iZY₁.op (localFamily g₁ hg₁)) =
            F.obj.map ((k ≫ iZY₁).op) (localFamily g₁ hg₁) := by
        rw [← FunctorToTypes.map_comp_apply]
        simp [← op_comp]
      have hk₁ :
          η.app (op (u.obj W)) (F.obj.map k.op (F.obj.map iZY₁.op (localFamily g₁ hg₁))) =
            η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₁).op) (localFamily g₁ hg₁)) :=
        congrArg (η.app (op (u.obj W))) hk₁'
      have hk₂' :
          F.obj.map ((k ≫ iZY₂).op) (localFamily g₂ hg₂) =
            F.obj.map k.op (F.obj.map iZY₂.op (localFamily g₂ hg₂)) := by
        symm
        rw [← FunctorToTypes.map_comp_apply]
        simp [← op_comp]
      have hk₂ :
          η.app (op (u.obj W)) (F.obj.map ((k ≫ iZY₂).op) (localFamily g₂ hg₂)) =
            η.app (op (u.obj W)) (F.obj.map k.op (F.obj.map iZY₂.op (localFamily g₂ hg₂))) :=
        congrArg (η.app (op (u.obj W))) hk₂'
      have hm :
          F'.obj.map (k ≫ iZY₁).op (F'.obj.map g₁.op y) =
            F'.obj.map (k ≫ iZY₂).op (F'.obj.map g₂.op y) := by
        rw [← FunctorToTypes.map_comp_apply]
        rw [← FunctorToTypes.map_comp_apply]
        simpa [Category.assoc, ← op_comp] using congrArg (fun h => F'.obj.map (k ≫ h).op y) e
      exact hk₁.trans (h₁.trans (hm.trans (h₂.symm.trans hk₂)))
    let hFsheaf := ((isSheaf_iff_isSheaf_of_type K F.obj).mp F.property) _
      (u.is_cover_of_isCoverDense K V)
    let x := hFsheaf.amalgamate localFamily localFamily_compatible
    refine ⟨x, ?_⟩
    -- The glued section recovers the prescribed target section because this can be checked on the
    -- same image cover, where the local inverse was chosen by construction.
    apply Functor.IsCoverDense.ext u F' V
    intro U f
    have hx : F.obj.map f.op x = localFamily f (CategoryTheory.Presieve.in_coverByImage u f) :=
      hFsheaf.valid_glue localFamily_compatible f (CategoryTheory.Presieve.in_coverByImage u f)
    have hη :
        F'.obj.map f.op (η.app (op V) x) = η.app (op (u.obj U)) (F.obj.map f.op x) := by
      simpa using (congrFun (η.naturality f.op) x).symm
    have hglue :
        η.app (op (u.obj U)) (F.obj.map f.op x) =
          η.app (op (u.obj U)) (localFamily f (CategoryTheory.Presieve.in_coverByImage u f)) := by
      rw [hx]
    exact hη.trans (hglue.trans (localFamily_spec f (CategoryTheory.Presieve.in_coverByImage u f)))

/-- Helper for Lemma 7.29.1: once the counit is invertible, the adjunction shows that the
continuous pushforward is an equivalence. -/
private theorem sheafPushforwardContinuous_isEquivalence_of_source_local
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [IsSourceLocallyFaithful u J] [IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P] :
    (u.sheafPushforwardContinuous (Type w) J K).IsEquivalence := by
  let adj := u.sheafAdjunctionCocontinuous (Type w) J K
  -- Both the counit and the unit are now known objectwise, so the adjunction upgrades to an
  -- equivalence of categories.
  letI : IsIso adj.counit := by
    exact NatIso.isIso_of_isIso_app _
  letI : IsIso adj.unit := by
    exact NatIso.isIso_of_isIso_app _
  exact adj.toEquivalence.isEquivalence_functor

end Functor

-- Proof sketch: the source-local hypotheses upgrade to mathlib's canonical dense-subsite owner,
-- whose comparison-lemma API gives the continuous pushforward equivalence after the required
-- right-Kan-extension bridge is supplied. Applying the adjunction between continuous inverse image
-- and cocontinuous direct image then shows that the right adjoint is also an equivalence.
/-- Lemma 7.29.1: if `u : C ⥤ D` is continuous, cocontinuous, source-locally faithful,
source-locally full, and cover-dense, then the direct-image functor on sheaves of sets attached to
`u` is an equivalence of categories; equivalently, the morphism of topoi associated to `u` is an
equivalence. -/
lemma comparison_directImage_isEquivalence
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
    [Functor.IsSourceLocallyFaithful u J] [Functor.IsSourceLocallyFull u J] [u.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P] :
    (u.sheafPushforwardCocontinuous (Type w) J K).IsEquivalence := by
  letI : (u.sheafPushforwardContinuous (Type w) J K).IsEquivalence :=
    Functor.sheafPushforwardContinuous_isEquivalence_of_source_local u
  exact (u.sheafAdjunctionCocontinuous (Type w) J K).isEquivalence_right_of_isEquivalence_left

end

end CategoryTheory
