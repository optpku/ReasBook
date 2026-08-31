module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_29_6
public import stacks_project.Chap07.Lemma_7_28_5.TypeSheafification

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.29.8:
- primary domain: equivalences of sheaf topoi presented by dense-subsite comparison functors to a
  common site;
- sampled owner API:
  `Functor.IsDenseSubsite`,
  `MorphismOfTopoiIn`,
  `MorphismOfTopoiIn.id`,
  `CatCommSq`,
  `Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension`;
- best owner abstraction: the main statement should live directly over the common site, the two
  dense-subsite functors into it, and the factorization square through the identity morphism of
  the common sheaf topos; the pointwise right-Kan-extension witnesses belong only to a separate
  bridge theorem realizing the dense-subsite cocontinuous direct-image functors as equivalences on
  sheaves of sets;
- primitive data: the common site `(C', J')`, the dense-subsite functors from `(C, J)` and
  `(D, K)`, and the comparison square expressing `f` through `MorphismOfTopoiIn.id J'`;
- derived API: the equivalence instances for the two cocontinuous sheaf pushforwards and the
  resulting canonical natural isomorphism
  `f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous ≅
    targetFunctor.sheafPushforwardCocontinuous`;
  the public theorem surfaces should end with `Nonempty` of the square owner or of the comparison
  natural isomorphism, with no extra tautological payload, because those owners already contain the
  relevant comparison data.

Source/core/bridge triage:
- `source-facing`: the existence of a common site presenting an equivalence of topoi;
- `core/canonical`: `Functor.IsDenseSubsite`, `MorphismOfTopoiIn`, `MorphismOfTopoiIn.id`, and
  `CatCommSq`;
- `bridge/view`: the pointwise right Kan extension hypotheses used to realize the two
  dense-subsite cocontinuous direct-image functors as equivalences on set-valued sheaves and turn
  the square through `MorphismOfTopoiIn.id J'` into a canonical natural isomorphism of functors to
  `Sh(C', J')`.
-/

/-- Helper for Remark 7.29.8: once a square through the identity on the common sheaf topos is
available, horizontally inverting the two dense-subsite equivalences identifies the two canonical
functors from `Sh(K)` to `Sh(J')`. -/
private theorem identity_square_induces_canonical_iso
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (f : MorphismOfTopoiIn K J)
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    [sourceFunctor.IsContinuous J J']
    [∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P]
    (targetFunctor : D ⥤ C') [targetFunctor.IsDenseSubsite K J']
    [targetFunctor.IsContinuous K J']
    [∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasPointwiseRightKanExtension P]
    (sq :
      CatCommSq
        (targetFunctor.sheafPushforwardContinuous (Type w) K J')
        ((MorphismOfTopoiIn.id J')⁻¹)
        (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous (Type w) J J')) :
    Nonempty
      (f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous (Type w) J J' ≅
        targetFunctor.sheafPushforwardCocontinuous (Type w) K J') := by
  -- Equip the two continuous pushforwards with the canonical equivalence structures whose
  -- inverses are the cocontinuous pushforwards.
  let sourceAdj := sourceFunctor.sheafAdjunctionCocontinuous (Type w) J J'
  let targetAdj := targetFunctor.sheafAdjunctionCocontinuous (Type w) K J'
  letI :
      (sourceFunctor.sheafPushforwardCocontinuous (Type w) J J').IsEquivalence :=
    Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
      (J := J) (K := J') sourceFunctor
  letI :
      (targetFunctor.sheafPushforwardCocontinuous (Type w) K J').IsEquivalence :=
    Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
      (J := K) (K := J') targetFunctor
  letI : IsIso sourceAdj.unit := by
    exact NatIso.isIso_of_isIso_app _
  letI : IsIso sourceAdj.counit := by
    exact NatIso.isIso_of_isIso_app _
  letI : IsIso targetAdj.unit := by
    exact NatIso.isIso_of_isIso_app _
  letI : IsIso targetAdj.counit := by
    exact NatIso.isIso_of_isIso_app _
  let sourceEquiv := sourceAdj.toEquivalence
  let targetEquiv := targetAdj.toEquivalence
  -- Horizontal inversion turns the square on continuous pushforwards into the desired comparison
  -- between the cocontinuous pushforwards.
  let sqInv :=
    CatCommSq.hInv targetEquiv ((MorphismOfTopoiIn.id J')⁻¹) (f⁻¹) sourceEquiv sq
  refine ⟨?_⟩
  simpa [sourceEquiv, targetEquiv] using sqInv.iso.symm

-- Proof sketch: this helper isolates the source-facing existential package from Remark `7.29.8`.
-- The remaining work is the source-faithful replay of the common full-subcategory construction
-- from Lemma `7.29.6`, but now with the D-side functor upgraded to a dense subsite and the middle
-- comparison fixed to the identity on the common site.
/-- Helper for Remark 7.29.8: once the source-side dense-subsite comparison is already known to be
an equivalence on sheaves of sets, the canonical square from Lemma `7.29.6` forces the
target-side continuous pullback functor to be an equivalence as soon as `f⁻¹` is. -/
private theorem target_pullback_isEquivalence_of_canonical_factorization
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence]
    (v : C ⥤ C') [v.IsDenseSubsite J J']
    [(v.sheafPushforwardContinuous (Type w) J J').IsEquivalence]
    (u : D ⥤ C')
    [IsMorphismOfSites K J' u]
    [HasWeakSheafify J' (Type w)]
    [∀ P : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    (sq :
      CatCommSq
        (𝟭 (Sheaf K (Type w)))
        (u.sheafPullback (Type w) K J')
        (f⁻¹)
        (v.sheafPushforwardContinuous (Type w) J J')) :
    (u.sheafPullback (Type w) K J').IsEquivalence := by
  have hcomp :
      (u.sheafPullback (Type w) K J' ⋙ v.sheafPushforwardContinuous (Type w) J J').IsEquivalence := by
    -- The square identifies the composite `u.sheafPullback ⋙ v.sheafPushforwardContinuous`
    -- with `f⁻¹`.
    rw [Functor.isEquivalence_iff_of_iso
      ((CatCommSq.iso
          (𝟭 (Sheaf K (Type w)))
          (u.sheafPullback (Type w) K J')
          (f⁻¹)
          (v.sheafPushforwardContinuous (Type w) J J')).symm ≪≫
        Functor.leftUnitor (f⁻¹))]
    infer_instance
  -- Cancel the known equivalence on the right to recover the equivalence of `u.sheafPullback`.
  exact Functor.isEquivalence_of_comp_right
    (u.sheafPullback (Type w) K J')
    (v.sheafPushforwardContinuous (Type w) J J')

/-- Helper for Remark 7.29.8: once the `Type w` pointwise right-Kan-extension bridge is supplied
for a dense-subsite functor, its continuous pushforward on sheaves of sets is an equivalence. -/
private theorem denseSubsite_pushforwardContinuous_isEquivalence_of_pointwise_right_kan
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (v : C ⥤ C') [v.IsDenseSubsite J J']
    [v.IsContinuous J J']
    [∀ P : Cᵒᵖ ⥤ Type w, v.op.HasPointwiseRightKanExtension P] :
    (v.sheafPushforwardContinuous (Type w) J J').IsEquivalence := by
  -- First upgrade the cocontinuous pushforward to an equivalence using the dense-subsite API.
  letI :
      (v.sheafPushforwardCocontinuous (Type w) J J').IsEquivalence :=
    Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
      (J := J) (K := J') v
  -- Then the adjunction identifies the continuous pushforward as the inverse equivalence.
  exact
    (v.sheafAdjunctionCocontinuous (Type w) J J').isEquivalence_left_of_isEquivalence_right

/-- Helper for Remark 7.29.8: in the canonical factorization from Lemma `7.29.6`, once the
source-side `Type w` pointwise right-Kan-extension bridge is available, the target-side pullback
is an equivalence whenever `f⁻¹` is. -/
private theorem site_factorization_target_pullback_isEquivalence_of_source_pointwise_right_kan
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence]
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    [sourceFunctor.IsContinuous J J']
    [∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P]
    (targetFunctor : D ⥤ C')
    [IsMorphismOfSites K J' targetFunctor]
    [HasWeakSheafify J' (Type w)]
    [∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasLeftKanExtension P]
    (sq :
      CatCommSq
        (𝟭 (Sheaf K (Type w)))
        (targetFunctor.sheafPullback (Type w) K J')
        (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous (Type w) J J')) :
    (targetFunctor.sheafPullback (Type w) K J').IsEquivalence := by
  -- The source-side comparison functor becomes an equivalence after inserting the Kan bridge.
  letI :
      (sourceFunctor.sheafPushforwardContinuous (Type w) J J').IsEquivalence :=
    denseSubsite_pushforwardContinuous_isEquivalence_of_pointwise_right_kan
      (J := J) (J' := J') sourceFunctor
  -- With the source comparison inverted, the canonical square forces the target pullback to be an
  -- equivalence as well.
  exact target_pullback_isEquivalence_of_canonical_factorization f sourceFunctor targetFunctor sq

/-- Helper for Remark 7.29.8: the lower inverse image in a canonical source-side
factorization is an equivalence when `f⁻¹` is an equivalence and the source dense-subsite
comparison is realized as an equivalence on sheaves. -/
private theorem lower_inverseImage_isEquivalence_of_source_square
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence]
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    [sourceFunctor.IsContinuous J J']
    [∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P]
    (g : MorphismOfTopoiIn K J')
    (sq :
      CatCommSq
        (𝟭 (Sheaf K (Type w)))
        (g⁻¹)
        (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous (Type w) J J')) :
    (g⁻¹).IsEquivalence := by
  -- First realize the source dense-subsite comparison as an equivalence on sheaves.
  letI :
      (sourceFunctor.sheafPushforwardContinuous (Type w) J J').IsEquivalence :=
    denseSubsite_pushforwardContinuous_isEquivalence_of_pointwise_right_kan
      (J := J) (J' := J') sourceFunctor
  have hcomp :
      (g⁻¹ ⋙ sourceFunctor.sheafPushforwardContinuous (Type w) J J').IsEquivalence := by
    -- The commutative square identifies this composite with the already-equivalent functor `f⁻¹`.
    rw [Functor.isEquivalence_iff_of_iso
      ((CatCommSq.iso
          (𝟭 (Sheaf K (Type w)))
          (g⁻¹)
          (f⁻¹)
          (sourceFunctor.sheafPushforwardContinuous (Type w) J J')).symm ≪≫
        Functor.leftUnitor (f⁻¹))]
    infer_instance
  -- Cancel the source comparison equivalence from the right.
  exact Functor.isEquivalence_of_comp_right
    (g⁻¹)
    (sourceFunctor.sheafPushforwardContinuous (Type w) J J')

/-- Helper for Remark 7.29.8: the dense-subsite sheaf equivalence for a composite dense
subsite is naturally isomorphic to the composite of the two stage equivalences. -/
private noncomputable def sheafEquivCompFunctorIso
    {C₀ : Type u₁} [Category.{v₁} C₀]
    {D₀ : Type u₂} [Category.{v₂} D₀]
    {E₀ : Type u₃} [Category.{v₃} E₀]
    {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
    {L₀ : GrothendieckTopology E₀}
    (v0 : C₀ ⥤ D₀) (v1 : D₀ ⥤ E₀)
    [v0.IsDenseSubsite J₀ K₀] [v1.IsDenseSubsite K₀ L₀]
    [(v0 ⋙ v1).IsDenseSubsite J₀ L₀]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X v0.op) (Type w)]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X v1.op) (Type w)]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X (v0 ⋙ v1).op) (Type w)] :
    (Functor.IsDenseSubsite.sheafEquiv J₀ L₀ (v0 ⋙ v1) (Type w)).functor ≅
      (Functor.IsDenseSubsite.sheafEquiv J₀ K₀ v0 (Type w)).functor ⋙
        (Functor.IsDenseSubsite.sheafEquiv K₀ L₀ v1 (Type w)).functor :=
  (conjugateIsoEquiv
    ((Functor.IsDenseSubsite.sheafEquiv J₀ K₀ v0 (Type w)).toAdjunction.comp
      (Functor.IsDenseSubsite.sheafEquiv K₀ L₀ v1 (Type w)).toAdjunction)
    (Functor.IsDenseSubsite.sheafEquiv J₀ L₀ (v0 ⋙ v1) (Type w)).toAdjunction).symm
    (Functor.sheafPushforwardContinuousComp v0 v1 (Type w) J₀ K₀ L₀)

/-- Helper for Remark 7.29.8: the Yoneda presentation of the replacement target functor
identifies the transported equivalence as a right inverse to the target dense-subsite
restriction. -/
private theorem targetPush_comp_transport_nonempty_iso_of_yonedaPresentation
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    (targetFunctor : D ⥤ C') [targetFunctor.IsDenseSubsite K J']
    (Efun : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤
      Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))))
    [Efun.IsEquivalence]
    (ρ :
      targetFunctor ⋙ J'.yoneda ≅
        GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          Efun) :
    Nonempty
      (targetFunctor.sheafPushforwardContinuous
          (Type (max (max u₁ v₁) (max u₂ v₂))) K J' ⋙ Efun ≅
        𝟭 (Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))))) := by
  let targetPush :=
    targetFunctor.sheafPushforwardContinuous
      (Type (max (max u₁ v₁) (max u₂ v₂))) K J'
  letI : targetFunctor.IsCoverDense J' :=
    Functor.IsDenseSubsite.isCoverDense (J := K) (K := J') (G := targetFunctor)
  letI : targetFunctor.IsLocallyFull J' :=
    Functor.IsDenseSubsite.isLocallyFull (J := K) (K := J') (G := targetFunctor)
  let pointIso :
      (H : Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))) →
        targetFunctor.op ⋙ (Efun.obj ((targetPush).obj H)).obj ≅
          targetFunctor.op ⋙ H.obj := by
    intro H
    refine NatIso.ofComponents (fun Vop ↦ ?_) ?_
    · let V : D := unop Vop
      let repr :=
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₁ v₁, u₂, v₂} K
          ((targetPush).obj H) V
      let yon :=
        J'.yonedaEquiv
          (X := targetFunctor.obj V)
          (F := Efun.obj ((targetPush).obj H))
      change
        (Efun.obj ((targetPush).obj H)).obj.obj (op (targetFunctor.obj V)) ≅
          H.obj.obj (op (targetFunctor.obj V))
      refine Equiv.toIso ?_
      refine
        { toFun := fun s ↦
            repr
              (Efun.preimage ((ρ.app V).inv ≫ yon.symm s))
          invFun := fun t ↦
            yon ((ρ.app V).hom ≫ Efun.map (repr.symm t))
          left_inv := ?_
          right_inv := ?_ }
      · intro s
        change
          yon ((ρ.app V).hom ≫
            Efun.map (repr.symm (repr
              (Efun.preimage ((ρ.app V).inv ≫ yon.symm s))))) = s
        rw [Equiv.symm_apply_apply]
        have hmap :
            Efun.map (Efun.preimage ((ρ.app V).inv ≫ yon.symm s)) =
              (ρ.app V).inv ≫ yon.symm s :=
          Efun.map_preimage _
        rw [← Equiv.apply_symm_apply yon s]
        apply congrArg yon
        rw [Equiv.symm_apply_apply]
        calc
          (ρ.app V).hom ≫ Efun.map (Efun.preimage ((ρ.app V).inv ≫ yon.symm s)) =
              (ρ.app V).hom ≫ ((ρ.app V).inv ≫ yon.symm s) := by
            exact congrArg (fun k ↦ (ρ.app V).hom ≫ k) hmap
          _ = yon.symm s := by
            simpa [Category.assoc] using
              Iso.hom_inv_id_assoc (ρ.app V) (yon.symm s)
      · intro t
        change
          repr
            (Efun.preimage ((ρ.app V).inv ≫
              yon.symm (yon ((ρ.app V).hom ≫ Efun.map (repr.symm t))))) = t
        rw [Equiv.symm_apply_apply]
        have hρcomp :
            (ρ.app V).inv ≫ (ρ.app V).hom ≫ Efun.map (repr.symm t) =
              Efun.map (repr.symm t) := by
          simpa [Category.assoc] using
            Iso.inv_hom_id_assoc (ρ.app V) (Efun.map (repr.symm t))
        have hpre :
            Efun.preimage ((ρ.app V).inv ≫ (ρ.app V).hom ≫ Efun.map (repr.symm t)) =
              Efun.preimage (Efun.map (repr.symm t)) :=
          congrArg Efun.preimage hρcomp
        rw [← Equiv.apply_symm_apply repr t]
        apply congrArg repr
        rw [Equiv.symm_apply_apply]
        calc
          Efun.preimage ((ρ.app V).inv ≫ (ρ.app V).hom ≫ Efun.map (repr.symm t)) =
              Efun.preimage (Efun.map (repr.symm t)) := hpre
          _ = repr.symm t := by
            exact Functor.preimage_map (F := Efun) (repr.symm t)
    · intro Vop Wop g
      let V : D := unop Vop
      let W : D := unop Wop
      let l : W ⟶ V := g.unop
      let reprV :=
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₁ v₁, u₂, v₂} K
          ((targetPush).obj H) V
      let reprW :=
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₁ v₁, u₂, v₂} K
          ((targetPush).obj H) W
      let yonV :=
        J'.yonedaEquiv
          (X := targetFunctor.obj V)
          (F := Efun.obj ((targetPush).obj H))
      let yonW :=
        J'.yonedaEquiv
          (X := targetFunctor.obj W)
          (F := Efun.obj ((targetPush).obj H))
      ext s
      change
        reprW
          (Efun.preimage ((ρ.app W).inv ≫
            yonW.symm
                ((Efun.obj ((targetPush).obj H)).obj.map
                  (targetFunctor.map l).op s))) =
            (targetPush.obj H).obj.map l.op
              (reprV (Efun.preimage ((ρ.app V).inv ≫ yonV.symm s)))
      rw [← GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality.{max u₁ v₁, u₂, v₂}
        (J := K) l ((targetPush).obj H)
        (Efun.preimage ((ρ.app V).inv ≫ yonV.symm s))]
      change
        reprW
          (Efun.preimage ((ρ.app W).inv ≫
            yonW.symm
              ((Efun.obj ((targetPush).obj H)).obj.map
                (targetFunctor.map l).op s))) =
        reprW
          ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l ≫
            Efun.preimage ((ρ.app V).inv ≫ yonV.symm s))
      apply congrArg reprW
      apply Efun.map_injective
      have hmapW :
          Efun.map
              (Efun.preimage ((ρ.app W).inv ≫
                yonW.symm
                  ((Efun.obj ((targetPush).obj H)).obj.map
                    (targetFunctor.map l).op s))) =
            (ρ.app W).inv ≫
              yonW.symm
                ((Efun.obj ((targetPush).obj H)).obj.map
                  (targetFunctor.map l).op s) :=
        Efun.map_preimage _
      have hyon :
          yonW.symm
              ((Efun.obj ((targetPush).obj H)).obj.map
                (targetFunctor.map l).op s) =
            J'.yoneda.map (targetFunctor.map l) ≫ yonV.symm s := by
        simpa [yonV, yonW] using
          GrothendieckTopology.yonedaEquiv_symm_map (J := J')
            ((targetFunctor.map l).op)
            (F := Efun.obj ((targetPush).obj H)) (t := s)
      have hleft :
          Efun.map
              (Efun.preimage ((ρ.app W).inv ≫
                yonW.symm
                  ((Efun.obj ((targetPush).obj H)).obj.map
                    (targetFunctor.map l).op s))) =
            ((ρ.app W).inv ≫ J'.yoneda.map (targetFunctor.map l)) ≫ yonV.symm s :=
        hmapW.trans (by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (ρ.app W).inv ≫ k) hyon)
      have hnat :
          Efun.map
              ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) ≫
            (ρ.app V).inv =
          (ρ.app W).inv ≫ J'.yoneda.map (targetFunctor.map l) := by
        simpa [Functor.comp_map] using (ρ.inv.naturality l)
      have hmiddle :
          ((ρ.app W).inv ≫ J'.yoneda.map (targetFunctor.map l)) ≫ yonV.symm s =
            (Efun.map
                ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) ≫
              (ρ.app V).inv) ≫ yonV.symm s := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ yonV.symm s) hnat.symm
      have hmapV :
          Efun.map (Efun.preimage ((ρ.app V).inv ≫ yonV.symm s)) =
            (ρ.app V).inv ≫ yonV.symm s :=
        Efun.map_preimage _
      have hright :
          (Efun.map
              ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) ≫
            (ρ.app V).inv) ≫ yonV.symm s =
          Efun.map
            ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l ≫
              Efun.preimage ((ρ.app V).inv ≫ yonV.symm s)) := by
        rw [Functor.map_comp]
        simpa [Category.assoc] using
          (congrArg (fun k ↦
            Efun.map
                ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) ≫
              k) hmapV).symm
      exact hleft.trans (hmiddle.trans hright)
  refine ⟨NatIso.ofComponents (fun H ↦ ?_) ?_⟩
  · exact Functor.IsCoverDense.sheafIso (G := targetFunctor) (pointIso H)
  · intro H H' α
    apply (targetPush).map_injective
    ext Vop s
    rcases Vop with ⟨V⟩
    rw [Functor.map_comp, Functor.map_comp]
    simp only [Functor.comp_map]
    change
      ((targetPush.map ((Functor.IsCoverDense.sheafIso (G := targetFunctor)
          (pointIso H')).hom)).hom.app (op V))
        (((targetPush.map (Efun.map ((targetPush).map α))).hom.app (op V)) s) =
      ((targetPush.map α).hom.app (op V))
        (((targetPush.map ((Functor.IsCoverDense.sheafIso (G := targetFunctor)
          (pointIso H)).hom)).hom.app (op V)) s)
    have hsheafIso_app :
        ∀ F : Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))),
          (targetPush.map ((Functor.IsCoverDense.sheafIso (G := targetFunctor)
            (pointIso F)).hom)).hom.app (op V) =
            (pointIso F).hom.app (op V) := by
      intro F
      rw [Functor.sheafPushforwardContinuous_map_hom_app]
      rw [Functor.IsCoverDense.sheafIso_hom_hom]
      dsimp [Functor.IsCoverDense.presheafIso]
      simpa using congr_app
        (Functor.IsCoverDense.sheafHom_restrict_eq (G := targetFunctor)
          (pointIso F).hom) (op V)
    rw [hsheafIso_app H, hsheafIso_app H']
    have hEapp :
        (targetPush.map (Efun.map ((targetPush).map α))).hom.app (op V) s =
          (Efun.map ((targetPush).map α)).hom.app (op (targetFunctor.obj V)) s := by
      rw [Functor.sheafPushforwardContinuous_map_hom_app]
    rw [hEapp]
    dsimp [pointIso]
    have hyon :
        J'.yonedaEquiv.symm
            ((Efun.map ((targetPush).map α)).hom.app (op (targetFunctor.obj V)) s) =
          J'.yonedaEquiv.symm s ≫ Efun.map ((targetPush).map α) := by
      simpa using
        (GrothendieckTopology.yonedaEquiv_symm_naturality_right
          (J := J') (X := targetFunctor.obj V)
          (f := Efun.map ((targetPush).map α)) s).symm
    have hmap :
        Efun.map (Efun.preimage (ρ.inv.app V ≫ J'.yonedaEquiv.symm s)) =
          ρ.inv.app V ≫ J'.yonedaEquiv.symm s :=
      Efun.map_preimage _
    have hpre :
        Efun.preimage (ρ.inv.app V ≫
            J'.yonedaEquiv.symm
              ((Efun.map ((targetPush).map α)).hom.app (op (targetFunctor.obj V)) s)) =
          Efun.preimage (ρ.inv.app V ≫ J'.yonedaEquiv.symm s) ≫ (targetPush).map α := by
      apply Efun.map_injective
      have hleft :
          Efun.map
              (Efun.preimage (ρ.inv.app V ≫
                J'.yonedaEquiv.symm
                  ((Efun.map ((targetPush).map α)).hom.app
                    (op (targetFunctor.obj V)) s))) =
            (ρ.inv.app V ≫ J'.yonedaEquiv.symm s) ≫
              Efun.map ((targetPush).map α) := by
        calc
          Efun.map
              (Efun.preimage (ρ.inv.app V ≫
                J'.yonedaEquiv.symm
                  ((Efun.map ((targetPush).map α)).hom.app
                    (op (targetFunctor.obj V)) s))) =
              ρ.inv.app V ≫
                J'.yonedaEquiv.symm
                  ((Efun.map ((targetPush).map α)).hom.app
                    (op (targetFunctor.obj V)) s) := by
            exact Efun.map_preimage _
          _ = (ρ.inv.app V ≫ J'.yonedaEquiv.symm s) ≫
                Efun.map ((targetPush).map α) := by
            rw [hyon]
            simp [Category.assoc]
      have hmiddle :
          (ρ.inv.app V ≫ J'.yonedaEquiv.symm s) ≫
              Efun.map ((targetPush).map α) =
            Efun.map (Efun.preimage (ρ.inv.app V ≫ J'.yonedaEquiv.symm s)) ≫
              Efun.map ((targetPush).map α) := by
        exact congrArg (fun k ↦ k ≫ Efun.map ((targetPush).map α)) hmap.symm
      have hright :
          Efun.map (Efun.preimage (ρ.inv.app V ≫ J'.yonedaEquiv.symm s)) ≫
              Efun.map ((targetPush).map α) =
            Efun.map
              (Efun.preimage (ρ.inv.app V ≫ J'.yonedaEquiv.symm s) ≫
                (targetPush).map α) := by
        rw [Functor.map_comp]
      exact hleft.trans (hmiddle.trans hright)
    calc
      GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₁ v₁, u₂, v₂} K
          ((targetPush).obj H') V
          (Efun.preimage (ρ.inv.app V ≫
            J'.yonedaEquiv.symm
              ((Efun.map ((targetPush).map α)).hom.app (op (targetFunctor.obj V)) s))) =
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₁ v₁, u₂, v₂} K
          ((targetPush).obj H') V
          (Efun.preimage (ρ.inv.app V ≫ J'.yonedaEquiv.symm s) ≫ (targetPush).map α) := by
        exact congrArg
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₁ v₁, u₂, v₂} K
            ((targetPush).obj H') V) hpre
      _ = (targetPush.map α).hom.app (op V)
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₁ v₁, u₂, v₂} K
            ((targetPush).obj H) V
            (Efun.preimage (ρ.inv.app V ≫ J'.yonedaEquiv.symm s))) := by
        simpa using
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_comp.{max u₁ v₁, u₂, v₂}
            (J := K)
            (Efun.preimage (ρ.inv.app V ≫ J'.yonedaEquiv.symm s))
            ((targetPush).map α))

/-- Helper for Remark 7.29.8: the Yoneda presentation from Lemma `7.29.6` makes the replacement
target functor preserve covering sieves. -/
private theorem factorizationTarget_coverPreserving_of_yonedaPresentation
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    (hcover :
      ∀ ⦃X : C'⦄ (R : Presieve X),
        R ∈ J'.toPrecoverage X ↔
          ∃ (ι : Type (max (max u₁ v₁) (max u₂ v₂))) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
            R = Presieve.ofArrows Y π ∧
              Presheaf.IsLocallySurjective J'
                (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)))
    (targetFunctor : D ⥤ C')
    (ρ :
      targetFunctor ⋙ J'.yoneda ≅
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (Functor.IsDenseSubsite.sheafEquiv J J0Small a
            (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
            (Functor.IsDenseSubsite.sheafEquiv J0Small J' v0
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) :
    CoverPreserving K J' targetFunctor := by
  refine ⟨?_⟩
  intro V S hS
  let T : K.Cover V := ⟨S, hS⟩
  have hT :
      Presieve.ofArrows (fun I : T.Arrow ↦ targetFunctor.obj I.Y)
          (fun I ↦ targetFunctor.map I.f) ∈
        J'.toPrecoverage (targetFunctor.obj V) := by
    -- The source-package cover theorem transports the `K`-cover through the stored Yoneda
    -- presentation of the replacement target functor.
    exact
      factorization_target_cover_mem_precoverage
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 hcover
        targetFunctor ρ T
  have hT_arrows :
      Presieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f) = S.arrows := by
    -- The indexing category of a cover records exactly the arrows of its underlying sieve.
    funext Y
    funext g
    apply propext
    constructor
    · rintro ⟨I⟩
      exact I.hf
    · intro hg
      simpa using
        (Presieve.ofArrows.mk
          (Y := fun I : T.Arrow ↦ I.Y) (f := fun I : T.Arrow ↦ I.f)
          (⟨Y, g, hg⟩ : T.Arrow))
  have hT_map :
      Presieve.ofArrows (fun I : T.Arrow ↦ targetFunctor.obj I.Y)
          (fun I ↦ targetFunctor.map I.f) =
        S.arrows.map targetFunctor := by
    -- Mapping the indexed cover family is the presieve image of the original cover sieve.
    simpa [hT_arrows] using
      (Presieve.map_ofArrows (F := targetFunctor) (Y := fun I : T.Arrow ↦ I.Y)
        (f := fun I : T.Arrow ↦ I.f)).symm
  have hT_sieve :
      Sieve.generate
          (Presieve.ofArrows (fun I : T.Arrow ↦ targetFunctor.obj I.Y)
            (fun I ↦ targetFunctor.map I.f)) ∈
        J' (targetFunctor.obj V) :=
    (GrothendieckTopology.mem_toPrecoverage_iff J'
      (Presieve.ofArrows (fun I : T.Arrow ↦ targetFunctor.obj I.Y)
        (fun I ↦ targetFunctor.map I.f))).1 hT
  -- Convert the precoverage statement into the functor-pushforward covering sieve.
  simpa [hT_map, Sieve.generate_map_eq_functorPushforward] using hT_sieve

/-- Helper for Remark 7.29.8: an equivalence of sheaf categories carries locally surjective maps
to locally surjective maps. -/
private theorem sheaf_isLocallySurjective_map_of_equivalence
    {E₀ : Type u₁} [Category.{v₁} E₀] {L₀ : GrothendieckTopology E₀}
    {E₁ : Type u₂} [Category.{v₂} E₁] {L₁ : GrothendieckTopology E₁}
    [HasSheafify L₁ (Type w)]
    (G : Sheaf L₀ (Type w) ⥤ Sheaf L₁ (Type w)) [G.IsEquivalence]
    {F H : Sheaf L₀ (Type w)} (η : F ⟶ H) (hη : Sheaf.IsLocallySurjective η) :
    Sheaf.IsLocallySurjective (G.map η) := by
  -- Local surjectivity of sheaf morphisms gives epimorphy, and equivalences preserve epis.
  letI : Sheaf.IsLocallySurjective η := hη
  letI : Epi η := inferInstance
  rw [Sheaf.isLocallySurjective_iff_epi]
  infer_instance

/-- Helper for Remark 7.29.8: if a functor carries a coproduct map to a locally surjective
map, then the componentwise sigma-desc after applying the functor is locally surjective. -/
private theorem sheaf_isLocallySurjective_sigma_desc_of_functor_map
    {E₀ : Type u₁} [Category.{v₁} E₀] {L₀ : GrothendieckTopology E₀}
    {E₁ : Type u₂} [Category.{v₂} E₁] {L₁ : GrothendieckTopology E₁}
    {ι : Type*} (G : Sheaf L₀ (Type w) ⥤ Sheaf L₁ (Type w))
    [HasSheafify L₁ (Type w)] [PreservesColimitsOfShape (Discrete ι) G]
    (X : ι → Sheaf L₀ (Type w)) [HasCoproduct X]
    [HasCoproduct fun i : ι ↦ G.obj (X i)]
    {A : Sheaf L₀ (Type w)} (α : ∀ i : ι, X i ⟶ A)
    (hmap : Sheaf.IsLocallySurjective (G.map (Limits.Sigma.desc α))) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i : ι ↦ G.map (α i))) := by
  -- Insert the canonical coproduct comparison and then rewrite it to the componentwise desc map.
  have hmap_epi : Epi (G.map (Limits.Sigma.desc α)) :=
    (Sheaf.isLocallySurjective_iff_epi _).1 hmap
  have hcomp_epi :
      Epi (Limits.sigmaComparison G X ≫ G.map (Limits.Sigma.desc α)) := by
    exact
      (epi_comp_iff_of_epi (Limits.sigmaComparison G X) (G.map (Limits.Sigma.desc α))).2
        hmap_epi
  have hcomp :
      Sheaf.IsLocallySurjective (Limits.sigmaComparison G X ≫ G.map (Limits.Sigma.desc α)) :=
    (Sheaf.isLocallySurjective_iff_epi _).2 hcomp_epi
  simpa [Limits.sigmaComparison_map_desc] using hcomp

/-- Helper for Remark 7.29.8: every large-valued sheaf is locally covered by a coproduct of
large sheafified representables. -/
private theorem existsLocallySurjectiveMapFromUliftSheafifiedRepresentables
    {E : Type u} [Category.{v} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w u v))]
    (F : Sheaf L (Type (max w u v))) :
    ∃ (ι : Type (max w u v)) (Y : ι → E),
      let _ : HasColimitsOfShape (Discrete ι) (Sheaf L (Type (max w u v))) :=
        Sheaf.instHasColimitsOfShape
      ∃ π : (∐ fun i : ι ↦ L.uliftSheafifiedRepresentableFunctor.obj (Y i)) ⟶ F,
        Sheaf.IsLocallySurjective π := by
  let ι : Type (max w u v) := Σ U : E, F.obj.obj (op U)
  let Y : ι → E := fun i ↦ i.1
  refine ⟨ι, Y, ?_⟩
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf L (Type (max w u v))) :=
    Sheaf.instHasColimitsOfShape
  let X : ι → Sheaf L (Type (max w u v)) :=
    fun i ↦ L.uliftSheafifiedRepresentableFunctor.obj (Y i)
  let α : ∀ i : ι, X i ⟶ F :=
    fun i ↦ (L.uliftSheafifiedRepresentableHomEquiv F (Y i)).symm i.2
  let π : (∐ fun i : ι ↦ L.uliftSheafifiedRepresentableFunctor.obj (Y i)) ⟶ F :=
    Limits.Sigma.desc α
  refine ⟨π, ?_⟩
  refine ⟨?_⟩
  intro U s
  -- The top sieve is enough: after any restriction, choose the summand indexed by the
  -- restricted section itself.
  refine L.superset_covering ?_ (L.top_mem U)
  intro V g _
  let i : ι := ⟨V, F.obj.map g.op s⟩
  refine ⟨(Limits.Sigma.ι X i).hom.app (op V)
    (L.uliftSheafifiedRepresentableHomEquiv (X i) V (𝟙 (X i))), ?_⟩
  have hι : (Limits.Sigma.ι X i) ≫ π = α i := by
    simpa [π, α, X] using (Limits.Sigma.ι_desc α i)
  -- Evaluating the chosen coproduct component at the identity section recovers the required
  -- restricted section of `F`.
  calc
    π.hom.app (op V)
        ((Limits.Sigma.ι X i).hom.app (op V)
          (L.uliftSheafifiedRepresentableHomEquiv (X i) V (𝟙 (X i)))) =
      (α i).hom.app (op V)
        (L.uliftSheafifiedRepresentableHomEquiv (X i) V (𝟙 (X i))) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k.hom.app (op V)
              (L.uliftSheafifiedRepresentableHomEquiv (X i) V (𝟙 (X i)))) hι
    _ = L.uliftSheafifiedRepresentableHomEquiv F V (α i) := by
      have hcomp := L.uliftSheafifiedRepresentableHomEquiv_comp (𝟙 (X i)) (α i)
      simpa [X] using hcomp.symm
    _ = F.obj.map g.op s := by
      change (L.uliftSheafifiedRepresentableHomEquiv F V)
        ((L.uliftSheafifiedRepresentableHomEquiv F V).symm (F.obj.map g.op s)) =
          F.obj.map g.op s
      exact (L.uliftSheafifiedRepresentableHomEquiv F V).apply_symm_apply (F.obj.map g.op s)

/-- Helper for Remark 7.29.8: an epimorphic sigma-desc remains epimorphic after replacing the
source summands and target by isomorphic objects. -/
private theorem sigmaDesc_epi_of_componentwise_iso
    {E : Type*} [Category E] {ι : Type*}
    {X Y : ι → E} {Z W : E}
    [HasCoproduct X] [HasCoproduct Y]
    (e : ∀ i, X i ≅ Y i) (eZ : Z ≅ W)
    (p : ∀ i, X i ⟶ Z) (q : ∀ i, Y i ⟶ W)
    (hsq : ∀ i, (e i).hom ≫ q i = p i ≫ eZ.hom)
    (hp : Epi (Limits.Sigma.desc p)) :
    Epi (Limits.Sigma.desc q) := by
  have hcompare :
      Limits.Sigma.map (fun i ↦ (e i).hom) ≫ Limits.Sigma.desc q =
        Limits.Sigma.desc p ≫ eZ.hom := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc_assoc]
    exact hsq i
  have hcomp : Epi (Limits.Sigma.desc p ≫ eZ.hom) := epi_comp _ _
  rw [← hcompare] at hcomp
  exact epi_of_epi (Limits.Sigma.map (fun i ↦ (e i).hom)) (Limits.Sigma.desc q)

/-- Helper for Remark 7.29.8: the concrete plus construction is locally injective for
type-valued presheaves in any sufficiently large universe. -/
private theorem typeToPlus_isLocallyInjective
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    (P : Eᵒᵖ ⥤ Type (max w u₂ v₂)) :
    Presheaf.IsLocallyInjective L (L.toPlus P) := by
  let _ : Presheaf.IsLocallyInjective L (L.toPlus P) := {
    equalizerSieve_mem := by
      intro X x y h
      open GrothendieckTopology.Plus in
      rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
      obtain ⟨W, _h₁, _h₂, eq⟩ := h
      exact L.superset_covering
        (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2 }
  infer_instance

/-- Helper for Remark 7.29.8: the concrete plus construction is locally surjective for
type-valued presheaves in any sufficiently large universe. -/
private theorem typeToPlus_isLocallySurjective
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    (P : Eᵒᵖ ⥤ Type (max w u₂ v₂)) :
    Presheaf.IsLocallySurjective L (L.toPlus P) := by
  let _ : Presheaf.IsLocallySurjective L (L.toPlus P) := {
    imageSieve_mem := by
      intro X x
      open GrothendieckTopology.Plus in
      obtain ⟨S, x, rfl⟩ := exists_rep x
      refine L.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
      rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
      refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
      ext ⟨Z, g, hg⟩
      simpa using
        x.2
          { fst.hf := hf
            snd.hf := S.1.downward_closed hf g
            r.g₁ := g
            r.g₂ := 𝟙 Z
            .. } }
  infer_instance

/-- Helper for Remark 7.29.8: the concrete plus-plus sheafification unit is locally injective for
large type-valued presheaves. -/
private theorem topologyToSheafify_isLocallyInjective
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    (P : Eᵒᵖ ⥤ Type (max w u₂ v₂)) :
    Presheaf.IsLocallyInjective L (L.toSheafify P) := by
  let _ : Presheaf.IsLocallyInjective L (L.toPlus P) :=
    typeToPlus_isLocallyInjective (L := L) P
  let _ : Presheaf.IsLocallyInjective L (L.toPlus (L.plusObj P)) :=
    typeToPlus_isLocallyInjective (L := L) (L.plusObj P)
  -- The concrete sheafification unit is the composite of the two plus maps.
  change Presheaf.IsLocallyInjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Remark 7.29.8: the concrete plus-plus sheafification unit is locally surjective for
large type-valued presheaves. -/
private theorem topologyToSheafify_isLocallySurjective
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    (P : Eᵒᵖ ⥤ Type (max w u₂ v₂)) :
    Presheaf.IsLocallySurjective L (L.toSheafify P) := by
  let _ : Presheaf.IsLocallySurjective L (L.toPlus P) :=
    typeToPlus_isLocallySurjective (L := L) P
  let _ : Presheaf.IsLocallySurjective L (L.toPlus (L.plusObj P)) :=
    typeToPlus_isLocallySurjective (L := L) (L.plusObj P)
  -- The concrete sheafification unit is the composite of the two plus maps.
  change Presheaf.IsLocallySurjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Remark 7.29.8: the abstract sheafification unit is locally injective in the large
type universe used for the common-site construction. -/
private theorem largeToSheafify_isLocallyInjective
    {E : Type u₂} [Category.{v₂} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w u₂ v₂))]
    (P : Eᵒᵖ ⥤ Type (max w u₂ v₂)) :
    Presheaf.IsLocallyInjective L (toSheafify L P) := by
  exact CategoryTheory.toSheafify_isLocallyInjective_type_of_univLE (L := L) P

/-- Helper for Remark 7.29.8: the abstract sheafification unit is locally surjective in the large
type universe used for the common-site construction. -/
private theorem largeToSheafify_isLocallySurjective
    {E : Type u₂} [Category.{v₂} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w u₂ v₂))]
    (P : Eᵒᵖ ⥤ Type (max w u₂ v₂)) :
    Presheaf.IsLocallySurjective L (toSheafify L P) := by
  exact CategoryTheory.toSheafify_isLocallySurjective_type_of_hasWeakSheafify (L := L) P

/-- Helper for Remark 7.29.8: the large type-valued sheafification weak equivalences are exactly
the locally bijective morphisms. -/
private theorem largeType_WEqualsLocallyBijective
    {E : Type u₂} [Category.{v₂} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w u₂ v₂))] :
    L.WEqualsLocallyBijective (Type (max w u₂ v₂)) := by
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type (max w u₂ v₂),
        Presheaf.IsLocallyInjective L (toSheafify L P) := fun P ↦
    largeToSheafify_isLocallyInjective L P
  let _ :
      ∀ P : Eᵒᵖ ⥤ Type (max w u₂ v₂),
        Presheaf.IsLocallySurjective L (toSheafify L P) := fun P ↦
    largeToSheafify_isLocallySurjective L P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L)
    (A := Type (max w u₂ v₂))

/-- Helper for Remark 7.29.8: local surjectivity of a large sigma-desc of sheafified
representables is equivalent to local surjectivity of the underlying `uliftYoneda` sigma-desc. -/
private theorem large_isLocallySurjective_sigmaDesc_uliftSheafifiedRepresentableMap_iff
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    [HasWeakSheafify L (Type (max w u₂ v₂))]
    {ι : Type*} [Small.{max w u₂ v₂} ι] {U : E} (Y : ι → E)
    (f : ∀ i : ι, Y i ⟶ U)
    [HasCoproduct (fun i : ι ↦ CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj (Y i))]
    [HasCoproduct (fun i : ι ↦
      (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).obj (Y i))] :
    Sheaf.IsLocallySurjective
        (Limits.Sigma.desc (fun i : ι ↦
          (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map
            (f i))) ↔
      Presheaf.IsLocallySurjective L
        (Limits.Sigma.desc (fun i : ι ↦
          CategoryTheory.uliftYoneda.{max w u₂ v₂}.map (f i))) := by
  let W := Type (max w u₂ v₂)
  let _ : L.WEqualsLocallyBijective W := largeType_WEqualsLocallyBijective L
  let G := presheafToSheaf L W
  let F : ι → Eᵒᵖ ⥤ W := fun i ↦ CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj (Y i)
  let gPres : ∐ F ⟶ CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj U :=
    Limits.Sigma.desc (fun i : ι ↦ CategoryTheory.uliftYoneda.{max w u₂ v₂}.map (f i))
  let _ : HasCoproduct F := inferInstance
  let _ : HasCoproduct (fun i : ι ↦ G.obj (F i)) := by
    simpa [F, G, W, GrothendieckTopology.uliftSheafifiedRepresentableFunctor,
      GrothendieckTopology.uliftSheafifiedRepresentable] using
      (inferInstance : HasCoproduct (fun i : ι ↦
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).obj (Y i)))
  constructor
  · intro hdesc
    have hcomp :
        Sheaf.IsLocallySurjective (Limits.sigmaComparison G F ≫ G.map gPres) := by
      simpa [F, G, W, gPres, GrothendieckTopology.uliftSheafifiedRepresentableFunctor,
        GrothendieckTopology.uliftSheafifiedRepresentable, Limits.sigmaComparison_map_desc]
        using hdesc
    have hmap : Sheaf.IsLocallySurjective (G.map gPres) := by
      rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] at hcomp ⊢
      have hcomp' :
          Presheaf.IsLocallySurjective L
            (((sheafToPresheaf L W).map (Limits.sigmaComparison G F)) ≫
              (sheafToPresheaf L W).map (G.map gPres)) := by
        simpa [Functor.map_comp] using hcomp
      let _ :
          Presheaf.IsLocallySurjective L
            ((sheafToPresheaf L W).map (Limits.sigmaComparison G F)) := by
        infer_instance
      let _ :
          Presheaf.IsLocallyInjective L
            ((sheafToPresheaf L W).map (Limits.sigmaComparison G F)) := by
        infer_instance
      exact
        (Presheaf.comp_isLocallySurjective_iff L
          ((sheafToPresheaf L W).map (Limits.sigmaComparison G F))
          ((sheafToPresheaf L W).map (G.map gPres))).1 hcomp'
    rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff] at hmap
    exact hmap
  · intro hpres
    have hmap : Sheaf.IsLocallySurjective (G.map gPres) := by
      rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
      exact hpres
    let _ : Sheaf.IsLocallySurjective (G.map gPres) := hmap
    simpa [F, G, W, gPres, GrothendieckTopology.uliftSheafifiedRepresentableFunctor,
      GrothendieckTopology.uliftSheafifiedRepresentable, Limits.sigmaComparison_map_desc] using
      (show Sheaf.IsLocallySurjective (Limits.sigmaComparison G F ≫ G.map gPres) by
        infer_instance)

/-- Helper for Remark 7.29.8: an epimorphic large sigma-desc of sheafified representables
indexed by arrows below a sieve forces that sieve to be covering. -/
private theorem sieve_mem_of_uliftSheafifiedRepresentable_desc_epi
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    [HasWeakSheafify L (Type (max w u₂ v₂))]
    {V : E} {ι : Type*} [Small.{max w u₂ v₂} ι]
    (Y : ι → E) (π : ∀ i : ι, Y i ⟶ V) (S : Sieve V)
    [HasCoproduct (fun i : ι ↦ CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj (Y i))]
    [HasCoproduct (fun i : ι ↦
      (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).obj (Y i))]
    (hdesc : Epi (Limits.Sigma.desc (fun i : ι ↦
      (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map (π i))))
    (hle : Sieve.ofArrows Y π ≤ S) :
    S ∈ L V := by
  have hsurj :
      Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i : ι ↦
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map (π i))) :=
    (Sheaf.isLocallySurjective_iff_epi _).2 hdesc
  have hpres :
      Presheaf.IsLocallySurjective L
        (Limits.Sigma.desc (fun i : ι ↦
          CategoryTheory.uliftYoneda.{max w u₂ v₂}.map (π i))) :=
    (large_isLocallySurjective_sigmaDesc_uliftSheafifiedRepresentableMap_iff
      (L := L) Y π).1 hsurj
  have hcover : Sieve.ofArrows Y π ∈ L V :=
    (L.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map π).2 hpres
  exact L.superset_covering hle hcover

/-- Helper for Remark 7.29.8: evaluating a morphism from an `ulift` sheafified representable
on the canonical identity section recovers its associated section. -/
private theorem uliftSheafifiedRepresentable_component_eq_section
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    [HasWeakSheafify L (Type (max w u₂ v₂))]
    {U : E} {ℱ : Sheaf L (Type (max w u₂ v₂))}
    (α : GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U ⟶ ℱ) :
    α.hom.app (op U)
        (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
          (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U
          (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U))) =
      GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L ℱ U α := by
  have hcomp :=
    GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_comp.{w, u₂, v₂} L
      (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U)) α
  simpa using hcomp.symm

/-- Helper for Remark 7.29.8: the section associated to a site arrow is the sheafification unit
applied to the corresponding `uliftYoneda` section. -/
private theorem uliftSheafifiedRepresentable_section_eq_toSheafify_app
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    [HasWeakSheafify L (Type (max w u₂ v₂))]
    {U' U : E} (f : U' ⟶ U) :
    GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
      (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U'
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map f) =
      ((sheafificationAdjunction L (Type (max w u₂ v₂))).unit.app
        (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj U)).app (op U') (ULift.up f) := by
  have hId :
      GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
        (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U
        (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U)) =
        ((sheafificationAdjunction L (Type (max w u₂ v₂))).unit.app
          (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj U)).app (op U) (ULift.up (𝟙 U)) := by
    rfl
  calc
    GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
        (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U'
        ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map f) =
      (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U).obj.map f.op
        (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
          (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U
          (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U))) := by
        simpa using
          GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality.{w, u₂, v₂}
            (J := L) f (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U)
            (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U))
    _ = (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U).obj.map f.op
        (((sheafificationAdjunction L (Type (max w u₂ v₂))).unit.app
          (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj U)).app (op U) (ULift.up (𝟙 U))) := by
          rw [hId]
    _ = ((sheafificationAdjunction L (Type (max w u₂ v₂))).unit.app
        (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj U)).app (op U') (ULift.up f) := by
          let η :
              CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj U ⟶
                (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U).obj :=
            (sheafificationAdjunction L (Type (max w u₂ v₂))).unit.app
              (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj U)
          have hnat := congrFun (NatTrans.naturality η f.op) (ULift.up (𝟙 U))
          simpa [η, CategoryTheory.uliftYoneda] using hnat.symm

/-- Helper for Remark 7.29.8: the source image sieve of a morphism between large `ulift`
sheafified representables is covering. -/
private theorem uliftSheafifiedRepresentable_imageSieve_mem
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    [HasWeakSheafify L (Type (max w u₂ v₂))]
    {U V : E}
    (c :
      GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U ⟶
        GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) :
    (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).imageSieve c ∈
      L U := by
  let η :
      CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V ⟶
        (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V).obj :=
    (sheafificationAdjunction L (Type (max w u₂ v₂))).unit.app
      (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V)
  let x :
      (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V).obj.obj (op U) :=
    GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
      (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) U c
  have hx :
      (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).imageSieve c =
        Presheaf.imageSieve η x := by
    -- Compare the source image sieve with the image sieve of the sheafification unit sectionwise.
    ext W g
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨ULift.up l, ?_⟩
      calc
        η.app (op W) (ULift.up l) =
          GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
            (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) W
            ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map l) := by
              exact
                (uliftSheafifiedRepresentable_section_eq_toSheafify_app
                  (L := L) l).symm
        _ = GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
            (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) W
            (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map g ≫
              c)) := by
              exact congrArg
                (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
                  (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) W) hl
        _ =
          (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V).obj.map g.op x := by
              simpa [x, GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
                (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality.{w, u₂, v₂}
                  (J := L) g
                  (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) c)
    · rintro ⟨l, hl⟩
      refine ⟨ULift.down l, ?_⟩
      apply
        (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
          (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) W).injective
      calc
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
            (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) W
            ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map
              (ULift.down l)) =
          η.app (op W) l := by
              exact uliftSheafifiedRepresentable_section_eq_toSheafify_app (L := L) (ULift.down l)
        _ =
          (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V).obj.map g.op x := hl
        _ =
          GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
            (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) W
            (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map g ≫
              c)) := by
              simpa [x, GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
                (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality.{w, u₂, v₂}
                  (J := L) g
                  (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) c).symm
  have hηsurj : Presheaf.IsLocallySurjective L η := by
    -- The sheafification unit is locally surjective in the large type universe.
    dsimp [η]
    exact largeToSheafify_isLocallySurjective L
      (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V)
  have hmem : Presheaf.imageSieve η x ∈ L U :=
    hηsurj.imageSieve_mem x
  simpa [hx] using hmem

/-- Helper for Remark 7.29.8: equality of maps of `ulift` sheafified representables is detected
on the usual equalizer sieve in the source site. -/
private theorem uliftSheafifiedRepresentable_equalizer_mem
    {E : Type u₂} [Category.{v₂} E] {L : GrothendieckTopology E}
    [HasWeakSheafify L (Type (max w u₂ v₂))]
    {U V : E} (a b : U ⟶ V)
    (h :
      (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map a =
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map b) :
    Sieve.equalizer a b ∈ L U := by
  let η :
      CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V ⟶
        (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V).obj :=
    (sheafificationAdjunction L (Type (max w u₂ v₂))).unit.app
      (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V)
  have hsection :
      η.app (op U) (ULift.up a) = η.app (op U) (ULift.up b) := by
    have h'' := congrArg
      (fun α :
          GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U ⟶
            GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V ↦
        α.hom.app (op U)
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
            (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U
            (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U)))) h
    have ha :
        ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map a).hom.app
            (op U)
            (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
              (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U
              (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U))) =
          η.app (op U) (ULift.up a) := by
      calc
        ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map a).hom.app
            (op U)
            (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
              (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U
              (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U))) =
          GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
            (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) U
            ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map a) := by
              exact uliftSheafifiedRepresentable_component_eq_section
                (L := L)
                (α := ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map a))
        _ = η.app (op U) (ULift.up a) := by
              exact uliftSheafifiedRepresentable_section_eq_toSheafify_app (L := L) a
    have hb :
        ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map b).hom.app
            (op U)
            (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
              (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U
              (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U))) =
          η.app (op U) (ULift.up b) := by
      calc
        ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map b).hom.app
            (op U)
            (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
              (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U) U
              (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L U))) =
          GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w, u₂, v₂} L
            (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₂, v₂} L V) U
            ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map b) := by
              exact uliftSheafifiedRepresentable_component_eq_section
                (L := L)
                (α := ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₂, v₂} L).map b))
        _ = η.app (op U) (ULift.up b) := by
              exact uliftSheafifiedRepresentable_section_eq_toSheafify_app (L := L) b
    exact ha.symm.trans (h''.trans hb)
  let xa : ToType ((CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V).obj (op U)) := ULift.up a
  let xb : ToType ((CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V).obj (op U)) := ULift.up b
  have hEqSieve :
      Presheaf.equalizerSieve (F := CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V) xa xb =
        Sieve.equalizer a b := by
    ext W g
    change (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V).map g.op xa =
        (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V).map g.op xb ↔
      g ≫ a = g ≫ b
    simpa [CategoryTheory.uliftYoneda, xa, xb]
  have hηinj : Presheaf.IsLocallyInjective L η := by
    -- The sheafification unit is locally injective, and `η` is exactly that unit.
    dsimp [η]
    exact largeToSheafify_isLocallyInjective L
      (CategoryTheory.uliftYoneda.{max w u₂ v₂}.obj V)
  simpa [hEqSieve] using
    hηinj.equalizerSieve_mem xa xb hsection

/-- Remark 7.29.8: a common-site factorization package with identity middle morphism. -/
private theorem exists_common_site_identity_factorization_data_of_isEquivalence
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    [(f⁻¹).IsEquivalence] :
    ∃ (C' : Type (max (max u₁ v₁) (max u₂ v₂)))
      (_ : Category.{max (max (max u₁ u₂) v₁) v₂} C')
      (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : Limits.HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (_ : sourceFunctor.IsContinuous J J')
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J')
      (_ : targetFunctor.IsContinuous K J')
      (_ :
        CatCommSq
          (targetFunctor.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) K J')
          ((MorphismOfTopoiIn.id J')⁻¹)
          (f⁻¹)
          (sourceFunctor.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) J J')),
      True := by
  -- Route correction: the public theorem is now reduced to a single helper whose only task is the
  -- common-site construction itself.
  -- The verified prefix now isolates the formal part of the source route:
  -- after inserting the eventual source-side Kan bridge,
  -- `site_factorization_target_pullback_isEquivalence_of_source_pointwise_right_kan`
  -- upgrades the target-side pullback from Lemma `7.29.6` to an equivalence.
  obtain ⟨C0Small, instC0Small, J0Small, a, haDense, haEquiv,
      C', instC', J', hsub, hfinite, v0, hv0, _hv0ff, hcover, hsubobj,
      targetFunctor, hρ, htargetPullbacks, hweakJ', htargetLan⟩ :=
    exists_special_cocontinuous_site_factorization_with_yonedaPresentation (J := J) (K := K) f
  let _ : Category.{max (max (max u₁ u₂) v₁) v₂} C0Small := instC0Small
  let _ : a.IsDenseSubsite J J0Small := haDense
  let _ : a.IsEquivalence := haEquiv
  let _ : v0.IsDenseSubsite J0Small J' := hv0
  let sourceFunctor : C ⥤ C' := a ⋙ v0
  let _ : Category.{max (max (max u₁ u₂) v₁) v₂} C' := instC'
  let _ : J'.Subcanonical := hsub
  let _ : Limits.HasFiniteLimits C' := hfinite
  have hsource : sourceFunctor.IsDenseSubsite J J' := by
    -- The source leg is the composite dense subsite exposed by the replacement package.
    simpa [sourceFunctor] using
      (dense_subsite_comp_of_equivalence_left
        (C0 := C0Small) (C' := C') (J := J) (J0 := J0Small) (J' := J') a v0)
  let _ : sourceFunctor.IsDenseSubsite J J' := hsource
  let _ : HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂))) := hweakJ'
  let _ : PreservesLimitsOfShape Limits.WalkingCospan targetFunctor := htargetPullbacks
  let _ :
      ∀ P : Dᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)),
        targetFunctor.op.HasLeftKanExtension P := htargetLan
  have hsourceCont : sourceFunctor.IsContinuous J J' := by
    -- Dense-subsite functors are canonically continuous.
    infer_instance
  have hsourceKan :
      ∀ P : Cᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)),
        sourceFunctor.op.HasPointwiseRightKanExtension P := by
    -- The displayed universe is large enough for the structured-arrow limits used by the
    -- dense-subsite comparison.
    intro P
    infer_instance
  have targetDenseAndSquare :
      ∃ (_ : targetFunctor.IsDenseSubsite K J') (_ : targetFunctor.IsContinuous K J')
        (sq :
          CatCommSq
          (targetFunctor.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) K J')
          ((MorphismOfTopoiIn.id J')⁻¹)
          (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) J J')),
        True := by
    let hcoverPreserving : CoverPreserving K J' targetFunctor :=
      factorizationTarget_coverPreserving_of_yonedaPresentation
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 hcover
        targetFunctor (Classical.choice hρ)
    have htargetCoverDense : targetFunctor.IsCoverDense J' := by
      refine ⟨?_⟩
      intro X
      let Efun : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤
          Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) :=
        (f⁻¹) ⋙
          (Functor.IsDenseSubsite.sheafEquiv J J0Small a
            (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
          (Functor.IsDenseSubsite.sheafEquiv J0Small J' v0
            (Type (max (max u₁ v₁) (max u₂ v₂)))).functor
      letI : Efun.IsEquivalence := by
        dsimp [Efun]
        infer_instance
      let F₀ : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) :=
        Efun.objPreimage (J'.yoneda.obj X)
      obtain ⟨ι, Y, π, hπ⟩ :=
        existsLocallySurjectiveMapFromUliftSheafifiedRepresentables.{max u₁ v₁, u₂, v₂} K F₀
      have hπE : Sheaf.IsLocallySurjective (Efun.map π) := by
        -- Move the presentation across the cached equivalence of sheaf categories.
        exact sheaf_isLocallySurjective_map_of_equivalence Efun π hπ
      let _ : HasColimitsOfShape (Discrete ι)
          (Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :=
        Sheaf.instHasColimitsOfShape
      let _ : HasColimitsOfShape (Discrete ι)
          (Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))) :=
        Sheaf.instHasColimitsOfShape
      let X₀ : ι → Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) :=
        fun i ↦
          (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).obj
            (Y i)
      let α : ∀ i : ι, X₀ i ⟶ F₀ := fun i ↦ Limits.Sigma.ι X₀ i ≫ π
      have hπ_desc : Limits.Sigma.desc α = π := by
        -- Repackage `π` as the sigma-desc of its coproduct components.
        apply Limits.Sigma.hom_ext
        intro i
        rw [Limits.Sigma.ι_desc]
      have hπEdesc :
          Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i : ι ↦ Efun.map (α i))) := by
        -- Replace the image of the coproduct map by the sigma-desc of the image components.
        refine sheaf_isLocallySurjective_sigma_desc_of_functor_map Efun X₀ α ?_
        simpa [hπ_desc] using hπE
      let ρ :
          targetFunctor ⋙ J'.yoneda ≅
            (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
                f.inverseImageFunctor.obj) ⋙
              (Functor.IsDenseSubsite.sheafEquiv J J0Small a
                (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
                (Functor.IsDenseSubsite.sheafEquiv J0Small J' v0
                  (Type (max (max u₁ v₁) (max u₂ v₂)))).functor :=
        Classical.choice hρ
      let τ : Efun.obj F₀ ≅ J'.yoneda.obj X :=
        Efun.objObjPreimageIso (J'.yoneda.obj X)
      let σ : ∀ i : ι, targetFunctor.obj (Y i) ⟶ X := fun i ↦
        Functor.preimage J'.yoneda ((ρ.app (Y i)).hom ≫ Efun.map (α i) ≫ τ.hom)
      have hσ :
          ∀ i : ι,
            J'.yoneda.map (σ i) = (ρ.app (Y i)).hom ≫ Efun.map (α i) ≫ τ.hom := by
        intro i
        dsimp [σ]
        rw [Functor.map_preimage]
      have hπE_epi : Epi (Limits.Sigma.desc (fun i : ι ↦ Efun.map (α i))) :=
        (Sheaf.isLocallySurjective_iff_epi _).1 hπEdesc
      have hσ_epi : Epi (Limits.Sigma.desc (fun i : ι ↦ J'.yoneda.map (σ i))) := by
        refine
          sigmaDesc_epi_of_componentwise_iso
            (X := fun i : ι ↦ Efun.obj (X₀ i))
            (Y := fun i : ι ↦ J'.yoneda.obj (targetFunctor.obj (Y i)))
            (Z := Efun.obj F₀)
            (W := J'.yoneda.obj X)
            (fun i : ι ↦ (ρ.app (Y i)).symm)
            τ
            (fun i : ι ↦ Efun.map (α i))
            (fun i : ι ↦ J'.yoneda.map (σ i))
            ?_
            hπE_epi
        intro i
        simpa [hσ i, Category.assoc] using
          (Iso.inv_hom_id_assoc (ρ.app (Y i)) (Efun.map (α i) ≫ τ.hom))
      have hσ_surj :
          Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i : ι ↦ J'.yoneda.map (σ i))) :=
        (Sheaf.isLocallySurjective_iff_epi _).2 hσ_epi
      have hσ_pres :
          Presheaf.IsLocallySurjective J'
            (Limits.Sigma.desc (fun i : ι ↦ (J'.yoneda.map (σ i)).hom)) := by
        exact
          (Sheaf.isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
            (J := J')
            (fun i : ι ↦ J'.yoneda.obj (targetFunctor.obj (Y i)))
            (fun i : ι ↦ J'.yoneda.map (σ i))).1 hσ_surj
      have hR :
          Presieve.ofArrows (fun i : ι ↦ targetFunctor.obj (Y i)) σ ∈
            J'.toPrecoverage X :=
        (hcover
          (X := X)
          (R := Presieve.ofArrows (fun i : ι ↦ targetFunctor.obj (Y i)) σ)).2
          ⟨ι, (fun i : ι ↦ targetFunctor.obj (Y i)), σ, rfl, hσ_pres⟩
      have hgen :
          Sieve.generate (Presieve.ofArrows (fun i : ι ↦ targetFunctor.obj (Y i)) σ) ∈
            J' X :=
        (GrothendieckTopology.mem_toPrecoverage_iff J'
          (Presieve.ofArrows (fun i : ι ↦ targetFunctor.obj (Y i)) σ)).1 hR
      -- The exhibited covering family lands in the cover-by-image sieve, so its generated sieve
      -- is enough for cover-density.
      exact J'.superset_covering
        ((Sieve.giGenerate.gc
          (Presieve.ofArrows (fun i : ι ↦ targetFunctor.obj (Y i)) σ)
          (Sieve.coverByImage targetFunctor X)).2
          (by
            rintro Z g ⟨i⟩
            simpa using Presieve.in_coverByImage targetFunctor (σ i)))
        hgen
    let Efun : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤
        Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) :=
      (f⁻¹) ⋙
        (Functor.IsDenseSubsite.sheafEquiv J J0Small a
          (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
        (Functor.IsDenseSubsite.sheafEquiv J0Small J' v0
          (Type (max (max u₁ v₁) (max u₂ v₂)))).functor
    let _ : Efun.IsEquivalence := by
      dsimp [Efun]
      infer_instance
    let ρ :
        targetFunctor ⋙ J'.yoneda ≅
          (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
              f.inverseImageFunctor.obj) ⋙
            (Functor.IsDenseSubsite.sheafEquiv J J0Small a
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
              (Functor.IsDenseSubsite.sheafEquiv J0Small J' v0
                (Type (max (max u₁ v₁) (max u₂ v₂)))).functor :=
      Classical.choice hρ
    have htarget : targetFunctor.IsDenseSubsite K J' := by
      refine
        { isCoverDense' := htargetCoverDense
          isLocallyFull' := ?_
          isLocallyFaithful' := ?_
          functorPushforward_mem_iff := ?_ }
      · refine ⟨?_⟩
        intro U V c
        let d :
            (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).obj U ⟶
              (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).obj V :=
          Efun.preimage ((ρ.app U).inv ≫ J'.yoneda.map c ≫ (ρ.app V).hom)
        have hd :
            Efun.map d = (ρ.app U).inv ≫ J'.yoneda.map c ≫ (ρ.app V).hom := by
          dsimp [d]
          rw [Functor.map_preimage]
          rfl
        have himageK :
            (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).imageSieve d
              ∈ K U :=
          uliftSheafifiedRepresentable_imageSieve_mem.{u₂, v₂, max u₁ v₁} (L := K) d
        have hle :
            (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).imageSieve d ≤
              targetFunctor.imageSieve c := by
          intro W g hg
          rcases hg with ⟨l, hl⟩
          refine ⟨l, ?_⟩
          apply J'.yoneda.map_injective
          apply (cancel_mono (ρ.app V).hom).1
          have hnatl :
              J'.yoneda.map (targetFunctor.map l) ≫ (ρ.app V).hom =
                (ρ.app W).hom ≫ Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) := by
            simpa [Functor.comp_map, Efun, Category.assoc] using
              (ρ.hom.naturality l)
          have hnatg :
              J'.yoneda.map (targetFunctor.map g) ≫ (ρ.app U).hom =
                (ρ.app W).hom ≫ Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map g) := by
            simpa [Functor.comp_map, Efun, Category.assoc] using
              (ρ.hom.naturality g)
          have hmap :
              Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) =
                Efun.map
                    ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map g) ≫
                  Efun.map d := by
            calc
              Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) =
                Efun.map
                    (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map g) ≫ d) := by
                  rw [hl]
              _ = Efun.map
                    ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map g) ≫
                  Efun.map d := by
                  simp [Functor.map_comp]
          have hd' :
              (ρ.app U).hom ≫ Efun.map d = J'.yoneda.map c ≫ (ρ.app V).hom := by
            rw [hd]
            simpa [Category.assoc] using
              (Iso.hom_inv_id_assoc (ρ.app U) (J'.yoneda.map c ≫ (ρ.app V).hom))
          have hstep₁ :
              J'.yoneda.map (targetFunctor.map l) ≫ (ρ.app V).hom =
                (ρ.app W).hom ≫ Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) :=
            hnatl
          have hstep₂ :
              (ρ.app W).hom ≫ Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map l) =
                (ρ.app W).hom ≫ Efun.map
                    ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map g) ≫
                  Efun.map d := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ (ρ.app W).hom ≫ k) hmap
          have hstep₃ :
              (ρ.app W).hom ≫ Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map g) ≫
                Efun.map d =
              J'.yoneda.map (targetFunctor.map g) ≫ (ρ.app U).hom ≫ Efun.map d := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ Efun.map d) hnatg.symm
          have hstep₄ :
              J'.yoneda.map (targetFunctor.map g) ≫ (ρ.app U).hom ≫ Efun.map d =
                J'.yoneda.map (targetFunctor.map g) ≫ J'.yoneda.map c ≫
                  (ρ.app V).hom := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ J'.yoneda.map (targetFunctor.map g) ≫ k) hd'
          have hstep₅ :
              J'.yoneda.map (targetFunctor.map g) ≫ J'.yoneda.map c ≫
                  (ρ.app V).hom =
                J'.yoneda.map (targetFunctor.map g ≫ c) ≫ (ρ.app V).hom := by
            simp [Functor.map_comp, Category.assoc]
          exact hstep₁.trans (hstep₂.trans (hstep₃.trans (hstep₄.trans hstep₅)))
        exact J'.superset_covering
          (Sieve.functorPushforward_monotone targetFunctor _ hle)
          (hcoverPreserving.cover_preserve himageK)
      · refine ⟨?_⟩
        intro U V a₁ a₂ h₁₂
        have hE :
            Efun.map
                ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map a₁) =
              Efun.map
                ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map a₂) := by
          have hleft :
              (ρ.app U).hom ≫ Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map a₁) =
                (ρ.app U).hom ≫ Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map a₂) := by
            have hnata₁ :
                J'.yoneda.map (targetFunctor.map a₁) ≫ (ρ.app V).hom =
                  (ρ.app U).hom ≫ Efun.map
                    ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map a₁) := by
              simpa [Functor.comp_map, Efun, Category.assoc] using
                (ρ.hom.naturality a₁)
            have hnata₂ :
                J'.yoneda.map (targetFunctor.map a₂) ≫ (ρ.app V).hom =
                  (ρ.app U).hom ≫ Efun.map
                    ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map a₂) := by
              simpa [Functor.comp_map, Efun, Category.assoc] using
                (ρ.hom.naturality a₂)
            have hmid :
                J'.yoneda.map (targetFunctor.map a₁) ≫ (ρ.app V).hom =
                  J'.yoneda.map (targetFunctor.map a₂) ≫ (ρ.app V).hom := by
              rw [h₁₂]
            exact hnata₁.symm.trans (hmid.trans hnata₂)
          exact (cancel_epi (ρ.app U).hom).1 hleft
        have hK :
            Sieve.equalizer a₁ a₂ ∈ K U :=
          uliftSheafifiedRepresentable_equalizer_mem.{u₂, v₂, max u₁ v₁} (L := K) a₁ a₂
            (Efun.map_injective hE)
        exact hcoverPreserving.cover_preserve hK
      · intro V S
        constructor
        · intro hS
          -- Reflect the pushed-forward cover through the Yoneda presentation and the cached
          -- equivalence `Efun`, then recover the original source covering sieve.
          let ι : Type (max u₂ v₂) := Σ W : D, {g : W ⟶ V // S g}
          let Y : ι → D := fun I ↦ I.1
          let π : ∀ I : ι, Y I ⟶ V := fun I ↦ I.2.1
          let _ : HasColimitsOfShape (Discrete ι)
              (Dᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂))) :=
            Limits.functorCategoryHasColimitsOfShape
          let _ : HasColimitsOfShape (Discrete ι)
              (C'ᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂))) :=
            Limits.functorCategoryHasColimitsOfShape
          let _ : HasColimitsOfShape (Discrete ι)
              (Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :=
            Sheaf.instHasColimitsOfShape
          let _ : HasColimitsOfShape (Discrete ι)
              (Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))) :=
            Sheaf.instHasColimitsOfShape
          have hS_arrows : Presieve.ofArrows Y π = S.arrows := by
            funext W
            funext g
            apply propext
            constructor
            · intro hg
              rcases hg with ⟨I⟩
              exact I.2.2
            · intro hg
              simpa [Y, π] using
                (Presieve.ofArrows.mk
                  (Y := Y) (f := π) (⟨W, g, hg⟩ : ι))
          have hS_map :
              Presieve.ofArrows (fun I : ι ↦ targetFunctor.obj (Y I))
                  (fun I : ι ↦ targetFunctor.map (π I)) =
                S.arrows.map targetFunctor := by
            simpa [hS_arrows, Y, π] using
              (Presieve.map_ofArrows (F := targetFunctor) (Y := Y) (f := π)).symm
          have hgen :
              Sieve.generate
                  (Presieve.ofArrows (fun I : ι ↦ targetFunctor.obj (Y I))
                    (fun I : ι ↦ targetFunctor.map (π I))) ∈
                J' (targetFunctor.obj V) := by
            simpa [hS_map, Sieve.generate_map_eq_functorPushforward] using hS
          have hpresJ :
              Presheaf.IsLocallySurjective J'
                (Limits.Sigma.desc (fun I : ι ↦
                  ((GrothendieckTopology.uliftYoneda.{max u₁ v₁} J').map
                    (targetFunctor.map (π I))).hom)) := by
            simpa [Y, π] using
              (J'.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
                (fun I : ι ↦ targetFunctor.map (π I))).1 hgen
          have hπJ_surj :
              Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun I : ι ↦
                (GrothendieckTopology.uliftYoneda.{max u₁ v₁} J').map
                  (targetFunctor.map (π I)))) := by
            exact
              (Sheaf.isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc_of_small
                (J := J')
                (fun I : ι ↦
                  (GrothendieckTopology.uliftYoneda.{max u₁ v₁} J').obj
                    (targetFunctor.obj (Y I)))
                (fun I : ι ↦
                  (GrothendieckTopology.uliftYoneda.{max u₁ v₁} J').map
                    (targetFunctor.map (π I)))).2 hpresJ
          have hπJ_ulift_epi :
              Epi (Limits.Sigma.desc (fun I : ι ↦
                (GrothendieckTopology.uliftYoneda.{max u₁ v₁} J').map
                  (targetFunctor.map (π I)))) :=
            (Sheaf.isLocallySurjective_iff_epi _).1 hπJ_surj
          have hπJ_epi :
              Epi (Limits.Sigma.desc (fun I : ι ↦
                J'.yoneda.map (targetFunctor.map (π I)))) := by
            refine
              sigmaDesc_epi_of_componentwise_iso
                (X := fun I : ι ↦
                  (GrothendieckTopology.uliftYoneda.{max u₁ v₁} J').obj
                    (targetFunctor.obj (Y I)))
                (Y := fun I : ι ↦ J'.yoneda.obj (targetFunctor.obj (Y I)))
                (Z := (GrothendieckTopology.uliftYoneda.{max u₁ v₁} J').obj
                  (targetFunctor.obj V))
                (W := J'.yoneda.obj (targetFunctor.obj V))
                (fun I : ι ↦
                  (GrothendieckTopology.uliftYonedaIsoYoneda J').app
                    (targetFunctor.obj (Y I)))
                ((GrothendieckTopology.uliftYonedaIsoYoneda J').app (targetFunctor.obj V))
                (fun I : ι ↦
                  (GrothendieckTopology.uliftYoneda.{max u₁ v₁} J').map
                    (targetFunctor.map (π I)))
                (fun I : ι ↦ J'.yoneda.map (targetFunctor.map (π I)))
                ?_
                hπJ_ulift_epi
            intro I
            simpa [Category.assoc] using
              ((GrothendieckTopology.uliftYonedaIsoYoneda J').hom.naturality
                (targetFunctor.map (π I)))
          /-
          have hπJ_surj :
              Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun I : ι ↦
                J'.yoneda.map (targetFunctor.map (π I)))) := by
            exact
              (Sheaf.isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
                (J := J')
                (fun I : ι ↦ J'.yoneda.obj (targetFunctor.obj (Y I)))
                (fun I : ι ↦ J'.yoneda.map (targetFunctor.map (π I)))).2 hpresJ
          have hπJ_epi :
              Epi (Limits.Sigma.desc (fun I : ι ↦
                J'.yoneda.map (targetFunctor.map (π I)))) :=
            (Sheaf.isLocallySurjective_iff_epi _).1 hπJ_surj
          -/
          let X₀ : ι → Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) := fun I ↦
            (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).obj
              (Y I)
          have hπEdesc_epi :
              Epi (Limits.Sigma.desc (fun I : ι ↦
                Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map
                    (π I)))) := by
            refine
              sigmaDesc_epi_of_componentwise_iso
                (X := fun I : ι ↦ J'.yoneda.obj (targetFunctor.obj (Y I)))
                (Y := fun I : ι ↦ Efun.obj (X₀ I))
                (Z := J'.yoneda.obj (targetFunctor.obj V))
                (W := Efun.obj
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).obj V))
                (fun I : ι ↦ ρ.app (Y I))
                (ρ.app V)
                (fun I : ι ↦ J'.yoneda.map (targetFunctor.map (π I)))
                (fun I : ι ↦ Efun.map
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map
                    (π I)))
                ?_
                hπJ_epi
            intro I
            simpa [Functor.comp_map, Efun, X₀, Category.assoc] using
              (ρ.hom.naturality (π I)).symm
          let πK :
              (∐ fun I : ι ↦ X₀ I) ⟶
                (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).obj V :=
            Limits.Sigma.desc (fun I : ι ↦
              (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K).map
                (π I))
          have hπK_map_epi : Epi (Efun.map πK) := by
            have hcomp :
                Epi (Limits.sigmaComparison Efun X₀ ≫ Efun.map πK) := by
              simpa [πK, X₀, Limits.sigmaComparison_map_desc] using hπEdesc_epi
            exact epi_of_epi (Limits.sigmaComparison Efun X₀) (Efun.map πK)
          have hπK_epi : Epi πK :=
            Efun.epi_of_epi_map hπK_map_epi
          have hle : Sieve.ofArrows Y π ≤ S := by
            intro W g hg
            rw [Sieve.mem_ofArrows_iff] at hg
            rcases hg with ⟨I, l, rfl⟩
            exact S.downward_closed I.2.2 l
          exact
            sieve_mem_of_uliftSheafifiedRepresentable_desc_epi.{u₂, v₂, max u₁ v₁}
              (L := K) Y π S (by simpa [πK, X₀] using hπK_epi) hle
        · exact hcoverPreserving.cover_preserve
    let _ : targetFunctor.IsDenseSubsite K J' := htarget
    have htargetCont : targetFunctor.IsContinuous K J' := by
      -- Once target density is available, dense-subsite continuity is canonical.
      infer_instance
    let _ : targetFunctor.IsContinuous K J' := htargetCont
    have sqIdentity :
        CatCommSq
        (targetFunctor.sheafPushforwardContinuous
          (Type (max (max u₁ v₁) (max u₂ v₂))) K J')
        ((MorphismOfTopoiIn.id J')⁻¹)
        (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous
          (Type (max (max u₁ v₁) (max u₂ v₂))) J J') := by
      -- With both legs presented as dense subsites of `J'`, the square through the identity
      -- morphism is the canonical comparison obtained by cancelling the source dense-subsite
      -- equivalence from the right.
      refine { iso := ?_ }
      let targetPush :=
        targetFunctor.sheafPushforwardContinuous
          (Type (max (max u₁ v₁) (max u₂ v₂))) K J'
      let sourcePush :=
        sourceFunctor.sheafPushforwardContinuous
          (Type (max (max u₁ v₁) (max u₂ v₂))) J J'
      let _ :
          ∀ P : Cᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)),
            sourceFunctor.op.HasPointwiseRightKanExtension P := hsourceKan
      letI : sourcePush.IsEquivalence :=
        denseSubsite_pushforwardContinuous_isEquivalence_of_pointwise_right_kan
          (J := J) (J' := J') sourceFunctor
      let sourceEquiv :=
        Functor.IsDenseSubsite.sheafEquiv J J' sourceFunctor
          (Type (max (max u₁ v₁) (max u₂ v₂)))
      have ρE :
          targetFunctor ⋙ J'.yoneda ≅
            GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
              Efun := by
        simpa [Efun] using ρ
      have htargetId : targetPush ⋙ Efun ≅
          𝟭 (Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))) := by
        simpa [targetPush] using
          Classical.choice
            (targetPush_comp_transport_nonempty_iso_of_yonedaPresentation.{u₁, u₂, v₁, v₂}
              (K := K) (C' := C') (J' := J') targetFunctor Efun ρE)
      have hsourceFunctorIso :
          sourceEquiv.functor ≅
            (Functor.IsDenseSubsite.sheafEquiv J J0Small a
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
              (Functor.IsDenseSubsite.sheafEquiv J0Small J' v0
                (Type (max (max u₁ v₁) (max u₂ v₂)))).functor := by
        simpa [sourceEquiv, sourceFunctor] using
          (sheafEquivCompFunctorIso.{u₁, max (max u₁ v₁) (max u₂ v₂),
              max (max u₁ v₁) (max u₂ v₂), v₁,
              max (max (max u₁ u₂) v₁) v₂, max (max (max u₁ u₂) v₁) v₂,
              max (max u₁ v₁) (max u₂ v₂)}
            (J₀ := J) (K₀ := J0Small) (L₀ := J') a v0)
      have hEfunSource : Efun ≅ f⁻¹ ⋙ sourceEquiv.functor := by
        simpa [Efun] using Functor.isoWhiskerLeft (f⁻¹) hsourceFunctorIso.symm
      have htargetSource :
          (targetPush ⋙ f⁻¹) ⋙ sourceEquiv.functor ≅
            𝟭 (Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))) := by
        exact
          (Functor.associator targetPush (f⁻¹) sourceEquiv.functor).symm ≪≫
            Functor.isoWhiskerLeft targetPush hEfunSource.symm ≪≫
            htargetId
      have hmain : targetPush ⋙ f⁻¹ ≅ sourcePush := by
        simpa [sourceEquiv, sourcePush] using
          Iso.isoCompInverse (H := sourceEquiv) htargetSource ≪≫
            Functor.leftUnitor sourceEquiv.inverse
      simpa [targetPush, sourcePush, MorphismOfTopoiIn.id_inverseImage] using
        hmain ≪≫ (Functor.leftUnitor sourcePush).symm
    exact ⟨htarget, htargetCont, sqIdentity, trivial⟩
  obtain ⟨htarget, htargetCont, sqIdentity, _⟩ := targetDenseAndSquare
  -- With the target dense-subsite package supplied, the existential statement is a direct
  -- repackaging of the 7.29.6 replacement site.
  exact ⟨C', instC', J', hsub, hfinite, sourceFunctor, hsource, hsourceCont,
    targetFunctor, htarget, htargetCont, sqIdentity, trivial⟩

-- Proof sketch: the dense-subsite API already provides pointwise right Kan extensions for the
-- lifted presheaf universe used elsewhere in the chapter; this isolates the usable owner while
-- the remaining blocker is to descend it to the theorem-facing `Type w` universe.
/-- Helper for Remark 7.29.8: a dense-subsite functor has pointwise right Kan extensions in the
lifted presheaf universe canonically used by the dense-subsite comparison API. -/
private theorem denseSubsite_has_lifted_pointwise_right_kan_extensions
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (u : C ⥤ C') [u.IsDenseSubsite J J'] :
    ∀ P : Cᵒᵖ ⥤ Type (max u₁ u₃ v₁ v₃ w), u.op.HasPointwiseRightKanExtension P := by
  -- The lifted-universe right Kan extension instances are already registered on dense subsites.
  intro P
  infer_instance

-- Proof sketch: apply Lemma `7.29.6` to `f`, and use the hypothesis that `f` is an equivalence
-- of topoi to replace the lower morphism by the identity morphism of a common site `(C', J')`.
-- The source-facing statement keeps only the common site, the two dense-subsite functors, and the
-- factorization square through `MorphismOfTopoiIn.id J'`; the right-Kan-extension bridge data
-- needed to realize the induced equivalences on sheaves of sets are recorded separately below.
/-- Consequence of Remark 7.29.8: if the morphism of topoi `f : Sh(J) ⟶ Sh(K)` is an equivalence,
then one can
choose a common site `(C', J')` together with special cocontinuous functors
`C ⥤ C'` and `D ⥤ C'` such that the induced equivalences of sheaf topoi identify `f` with the
factorization through the identity morphism of `Sh(C', J')`. -/
theorem exists_special_cocontinuous_common_site_factorization_of_isEquivalence
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    [(f⁻¹).IsEquivalence] :
    ∃ (C' : Type (max (max u₁ v₁) (max u₂ v₂)))
      (_ : Category.{max (max (max u₁ u₂) v₁) v₂} C')
      (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : Limits.HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (_ : sourceFunctor.IsContinuous J J')
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J')
      (_ : targetFunctor.IsContinuous K J'),
      Nonempty
        (CatCommSq
          (targetFunctor.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) K J')
          ((MorphismOfTopoiIn.id J')⁻¹)
          (f⁻¹)
          (sourceFunctor.sheafPushforwardContinuous
            (Type (max (max u₁ v₁) (max u₂ v₂))) J J')) := by
  obtain ⟨C', instC', J', hsub, hfinite, sourceFunctor, hsource, hsourceCont,
      targetFunctor, htarget, htargetCont, sq, _⟩ :=
    exists_common_site_identity_factorization_data_of_isEquivalence f
  -- The helper already packages the common-site data; only the theorem-facing `Nonempty` wrapper
  -- remains to be added.
  exact ⟨C', instC', J', hsub, hfinite, sourceFunctor, hsource, hsourceCont,
    targetFunctor, htarget, htargetCont, ⟨sq⟩⟩

-- Proof sketch: once a common-site factorization and the pointwise right-Kan-extension bridge
-- data have been supplied, the factorization square through `MorphismOfTopoiIn.id J'` identifies
-- the two canonical functors from `Sh(K)` to `Sh(C', J')`, namely
-- `f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous` and
-- `targetFunctor.sheafPushforwardCocontinuous`, by a natural isomorphism.
/-- Bridge companion to Remark 7.29.8: after supplying the pointwise right-Kan-extension
hypotheses and a chosen identity-middle factorization square, the dense-subsite cocontinuous
direct-image functors are identified by the canonical natural isomorphism
`f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous ≅
  targetFunctor.sheafPushforwardCocontinuous`. -/
theorem exists_special_cocontinuous_common_site_factorization_of_isEquivalence_canonical
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (f : MorphismOfTopoiIn K J)
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    [sourceFunctor.IsContinuous J J']
    [∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P]
    (targetFunctor : D ⥤ C') [targetFunctor.IsDenseSubsite K J']
    [targetFunctor.IsContinuous K J']
    [∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasPointwiseRightKanExtension P]
    (sq :
      CatCommSq
        (targetFunctor.sheafPushforwardContinuous (Type w) K J')
        ((MorphismOfTopoiIn.id J')⁻¹)
        (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous (Type w) J J')) :
    Nonempty (
      f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous (Type w) J J' ≅
        targetFunctor.sheafPushforwardCocontinuous (Type w) K J') := by
  -- The identity-middle square is now strong enough for the cocontinuous comparison isomorphism.
  exact identity_square_induces_canonical_iso f sourceFunctor targetFunctor sq

end

end CategoryTheory
