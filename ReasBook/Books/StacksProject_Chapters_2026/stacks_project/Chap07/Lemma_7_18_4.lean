module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import Mathlib.CategoryTheory.Filtered.Final
public import stacks_project.Chap07.Lemma_7_17_7
public import stacks_project.Chap07.Lemma_7_18_3
public import stacks_project.Chap07.Situation_7_18_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u w

namespace CategoryTheory

open CofilteredSiteDiagram

/- Source/core/bridge triage for Lemma 7.18.4:
- source-facing owner: `ColimitSiteStageFamily S`, a family of stage sheaves with the transition
  maps `f_a⁻¹ 𝒜_i ⟶ 𝒜_j` from the source text, together with its colimit sheaf on the colimit site
  and the explicit comparison indexed by arrows `a : j ⟶ i`, i.e. by `(Over i)ᵒᵖ`
- core/canonical owner: the filtered-diagram comparison map
  `((colimit.post F (sheafToPresheaf _ _)).app (op U))` from `Lemma_7_17_7`
- bridge/view layer in this file: the private pulled-back colimit-site diagram obtained by pulling
  each stage sheaf back to the colimit site and transporting the transition maps through
  `colimitStageSheafPullbackCompIso`
- primitive data: the stage sheaves and their pullback transition morphisms
- derived API: the source-facing colimit sheaf and the over-category comparison map
-/

/-- A compatible inverse system of sheaves on the stage sites of `S`, with the source-text
transition maps `f_a⁻¹ 𝒜_i ⟶ 𝒜_j` for arrows `a : j ⟶ i`. -/
structure ColimitSiteStageFamily (S : CofilteredSiteDiagram.{u, u, u}) where
  /-- The sheaf on the stage site `i`. -/
  obj (i : S.I) : Sheaf (S.stageTopology i) (Type u)
  /-- The transition morphism `f_a⁻¹ 𝒜_i ⟶ 𝒜_j` for `a : j ⟶ i`. -/
  transition {i j : S.I} (a : j ⟶ i) :
      ((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj (obj i) ⟶
        obj j
  /-- The identity transition is the canonical identity pullback map. -/
  transition_id (i : S.I) :
      transition (𝟙 i) = (S.stageSheafPullbackIdIso (Type u) i).hom.app (obj i)
  /-- The transition morphisms satisfy the usual cocycle condition. -/
  transition_comp {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
      (S.stageSheafPullbackCompIso (Type u) a b).hom.app (obj i) ≫ transition (b ≫ a) =
        ((S.stageFunctor b).sheafPullback (Type u)
          (S.stageTopology j) (S.stageTopology k)).map (transition a) ≫
          transition b

namespace ColimitSiteStageFamily

/-- The transition morphism between the pullbacks of a compatible stage family to the colimit
site. -/
noncomputable def transitionOnColimit
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i j : S.I} (a : j ⟶ i) :
    ((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj (family.obj i) ⟶
      ((S.stageCoconeFunctor j).sheafPullback (Type u)
        (S.stageTopology j) S.colimitTopology).obj (family.obj j) :=
  (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app (family.obj i) ≫
    (((S.stageCoconeFunctor j).sheafPullback (Type u)
      (S.stageTopology j) S.colimitTopology)).map (family.transition a)

/-- Helper for Lemma 7.18.4: the identity-stage functor is definitionally the identity on the
source stage. This records the owner equality used in the identity adjunction normalization. -/
theorem stage_functor_id_eq_local
    {S : CofilteredSiteDiagram.{u, u, u}}
    (i : S.I) :
    S.stageFunctor (𝟙 i) = 𝟭 (S.stage i) :=
  congrArg Cat.Hom.toFunctor (S.diagram.map_id (op i))

/-- Helper for Lemma 7.18.4: composing the identity-stage functor with the cocone functor gives
the cocone functor itself. This is the owner-level `id_comp` equality behind the source proof's
identity transition. -/
theorem stage_cocone_functor_id_comp
    {S : CofilteredSiteDiagram.{u, u, u}}
    (i : S.I) :
    S.stageFunctor (𝟙 i) ⋙ S.stageCoconeFunctor i = S.stageCoconeFunctor i :=
  S.stageCoconeFunctor_comp_eq (𝟙 i)

/-- Helper for Lemma 7.18.4: on the pushforward side, the identity-stage comparison with the
colimit cocone is the standard right-unital adjunction comparison. -/
theorem colimit_stage_sheaf_pushforward_comp_id_comp
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (i : S.I) :
    Functor.sheafPushforwardContinuousComp'
        (eqToIso (stage_cocone_functor_id_comp i))
        (Type u) (S.stageTopology i) (S.stageTopology i) S.colimitTopology =
      Functor.isoWhiskerLeft
          ((S.stageCoconeFunctor i).sheafPushforwardContinuous
            (Type u) (S.stageTopology i) S.colimitTopology)
          (Functor.sheafPushforwardContinuousId'
            (eqToIso (stage_functor_id_eq_local i))
            (Type u) (S.stageTopology i)) ≪≫
        Functor.rightUnitor
          ((S.stageCoconeFunctor i).sheafPushforwardContinuous
            (Type u) (S.stageTopology i) S.colimitTopology) := by
  -- Compare both sides on sections, then rewrite the residual transport by `eqToHom_map` for the
  -- opposite cocone functor.
  ext ℱ Y y
  have hid : ((S.stageFunctor (𝟙 i)).op.obj Y) = Y := by
    simpa using congrArg Opposite.op
      (congrArg (fun F : S.stage i ⥤ S.stage i ↦ F.obj Y.unop)
        (stage_functor_id_eq_local (S := S) i))
  have hcomp :
      ((S.stageCoconeFunctor i).op.obj (((S.stageFunctor (𝟙 i)).op.obj Y))) =
        ((S.stageCoconeFunctor i).op.obj Y) := by
    simpa using congrArg Opposite.op
      (congrArg (fun F : S.stage i ⥤ S.ColimitCategory ↦ F.obj Y.unop)
        (stage_cocone_functor_id_comp (S := S) i))
  have hcongr : congrArg ((S.stageCoconeFunctor i).op.obj) hid = hcomp := by
    apply Subsingleton.elim
  simpa [hcomp, hcongr] using
    congrArg (fun f ↦ ℱ.obj.map f y) ((eqToHom_map ((S.stageCoconeFunctor i).op) hid).symm)

/-- Helper for Lemma 7.18.4: the colimit-stage pullback comparison for the identity arrow is the
standard right-unital pullback comparison. This packages the owner-level normalization before any
evaluation on section sets. -/
theorem colimit_stage_sheaf_pullback_comp_id_comp
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (i : S.I) :
    S.colimitStageSheafPullbackCompIso (Type u) (𝟙 i) =
      Functor.isoWhiskerRight
          (S.stageSheafPullbackIdIso (Type u) i)
          ((S.stageCoconeFunctor i).sheafPullback
            (Type u) (S.stageTopology i) S.colimitTopology) ≪≫
        Functor.leftUnitor
          ((S.stageCoconeFunctor i).sheafPullback
            (Type u) (S.stageTopology i) S.colimitTopology) := by
  -- Transfer the pushforward-side `id_comp` coherence across the adjunction comparison.
  simpa [CofilteredSiteDiagram.colimitStageSheafPullbackCompIso] using
    (Adjunction.leftAdjointCompIso_id_comp
      ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology i))
      ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) S.colimitTopology)
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (stage_cocone_functor_id_comp i))
        (Type u) (S.stageTopology i) (S.stageTopology i) S.colimitTopology)
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (stage_functor_id_eq_local i))
        (Type u) (S.stageTopology i))
      (colimit_stage_sheaf_pushforward_comp_id_comp i))

/-- Helper for Lemma 7.18.4: for the identity-stage pullback adjunction, the unit followed by the
canonical identity pullback comparison is the identity. This is the sheaf-level mate used in the
section-map identity proof. -/
theorem stage_sheaf_pullback_id_unit_hom_app
    {S : CofilteredSiteDiagram.{u, u, u}}
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology i)).unit.app ℱ ≫
      ((S.stageFunctor (𝟙 i)).sheafPushforwardContinuous (Type u)
          (S.stageTopology i) (S.stageTopology i)).map
        ((S.stageSheafPullbackIdIso (Type u) i).hom.app ℱ) =
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (stage_functor_id_eq_local (S := S) i))
        (Type u) (S.stageTopology i)).inv.app ℱ := by
  -- Express the transpose of the identity pullback comparison by the adjunction unit.
  have h :=
    CategoryTheory.unit_conjugateEquiv
      CategoryTheory.Adjunction.id
      ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology i))
      ((S.stageSheafPullbackIdIso (Type u) i).hom)
      ℱ
  simpa [CofilteredSiteDiagram.stageSheafPullbackIdIso] using h.symm

/-- Helper for Lemma 7.18.4: evaluating the identity-stage transpose of the canonical pullback
comparison yields the canonical identity pushforward comparison on sections. -/
theorem identity_stage_adjunction_eval_normal_form
    {S : CofilteredSiteDiagram.{u, u, u}}
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (U : (S.stage i)ᵒᵖ) :
    ((((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology i)).homEquiv
        ℱ ℱ)
      ((S.stageSheafPullbackIdIso (Type u) i).hom.app ℱ)).1.app U =
      ((Functor.sheafPushforwardContinuousId'
        (eqToIso (stage_functor_id_eq_local (S := S) i))
        (Type u) (S.stageTopology i)).inv.app ℱ).1.app U := by
  -- First normalize the identity mate as a sheaf morphism, then evaluate at the chosen stage
  -- object.
  have hmate :
      (((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology i)).homEquiv
        ℱ ℱ)
      ((S.stageSheafPullbackIdIso (Type u) i).hom.app ℱ) =
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (stage_functor_id_eq_local (S := S) i))
        (Type u) (S.stageTopology i)).inv.app ℱ := by
    simpa [Adjunction.homEquiv_unit] using
      stage_sheaf_pullback_id_unit_hom_app (S := S) (i := i) (ℱ := ℱ)
  exact congrArg (fun f ↦ f.1.app U) hmate

/-- The colimit-site transition attached to the identity arrow is the identity morphism. -/
theorem transitionOnColimit_id
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S) (i : S.I) :
    transitionOnColimit family (𝟙 i) =
      𝟙 (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj (family.obj i)) := by
  -- Route correction: normalize the owner-level `S.colimitStageSheafPullbackCompIso` first, then
  -- collapse the remaining right-unital composite by functoriality.
  rw [transitionOnColimit, family.transition_id]
  rw [colimit_stage_sheaf_pullback_comp_id_comp]
  -- Expand the inverse unitor composite to the mapped `inv ≫ hom` identity.
  simp [Iso.trans_inv, Functor.whiskerRight_app, Functor.leftUnitor_inv_app]
  simpa [Functor.map_comp] using congrArg
    (((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).map)
    ((S.stageSheafPullbackIdIso (Type u) i).inv_hom_id_app (family.obj i))

/-- The colimit-site transitions attached to a compatible stage family compose canonically. -/
theorem colimit_stage_sheaf_pushforward_assoc_transport
    {S : CofilteredSiteDiagram.{u, u, u}}
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    (ℱ : Sheaf S.colimitTopology (Type u)) (Y : (S.stage i)ᵒᵖ)
    (p :
      (S.stageFunctor (b ≫ a)).obj Y.unop =
        (S.stageFunctor b).obj ((S.stageFunctor a).obj Y.unop))
    (q :
      (S.stageCoconeFunctor k).obj ((S.stageFunctor (b ≫ a)).obj Y.unop) =
        (S.stageCoconeFunctor i).obj Y.unop)
    (y :
      ℱ.obj.obj
        (op ((S.stageCoconeFunctor k).obj
          ((S.stageFunctor b).obj ((S.stageFunctor a).obj Y.unop))))) :
    ℱ.obj.map (eqToHom (congrArg Opposite.op q))
        (ℱ.obj.map (((S.stageCoconeFunctor k).map (eqToHom p)).op) y) =
      ℱ.obj.map
        (eqToHom
          ((congrArg Opposite.op
              (congrArg (fun Z ↦ (S.stageCoconeFunctor k).obj Z) p).symm).trans
            (congrArg Opposite.op q)))
        y := by
  -- First rewrite the mapped stage-composition equality as the corresponding opposite-side
  -- `eqToHom`, then combine the two section transports using `eqToHom_trans`.
  have hmap :
      ((S.stageCoconeFunctor k).map (eqToHom p)).op =
        eqToHom
          (congrArg Opposite.op
            (congrArg (fun Z ↦ (S.stageCoconeFunctor k).obj Z) p).symm) := by
    calc
      ((S.stageCoconeFunctor k).map (eqToHom p)).op =
          (eqToHom (congrArg (fun Z ↦ (S.stageCoconeFunctor k).obj Z) p)).op := by
            rw [CategoryTheory.eqToHom_map]
      _ =
          eqToHom
            (congrArg Opposite.op
              (congrArg (fun Z ↦ (S.stageCoconeFunctor k).obj Z) p).symm) := by
            rw [CategoryTheory.eqToHom_op]
  rw [hmap]
  exact
    (FunctorToTypes.eqToHom_map_comp_apply
      (F := ℱ.obj)
      (p := congrArg Opposite.op
        (congrArg (fun Z ↦ (S.stageCoconeFunctor k).obj Z) p).symm)
      (q := congrArg Opposite.op q) y)

/-- The colimit-site transitions attached to a compatible stage family compose canonically. -/
theorem colimit_stage_sheaf_pushforward_assoc
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    Functor.isoWhiskerLeft
        ((S.stageCoconeFunctor k).sheafPushforwardContinuous
          (Type u) (S.stageTopology k) S.colimitTopology)
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso
            (show S.stageFunctor (b ≫ a) =
                S.stageFunctor a ⋙ S.stageFunctor b from
              congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op))).symm
          (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)) ≪≫
      Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor (b ≫ a) ⋙ S.stageCoconeFunctor k =
              S.stageCoconeFunctor i from
            S.stageCoconeFunctor_comp_eq (b ≫ a)))
        (Type u) (S.stageTopology i) (S.stageTopology k) S.colimitTopology =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso
              (show S.stageFunctor b ⋙ S.stageCoconeFunctor k =
                  S.stageCoconeFunctor j from
                S.stageCoconeFunctor_comp_eq b))
            (Type u) (S.stageTopology j) (S.stageTopology k) S.colimitTopology)
          _ ≪≫
        Functor.sheafPushforwardContinuousComp'
          (eqToIso
            (show S.stageFunctor a ⋙ S.stageCoconeFunctor j =
                S.stageCoconeFunctor i from
              S.stageCoconeFunctor_comp_eq a))
          (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology := by
  -- Evaluate the owner-level pushforward coherence componentwise; both routes are definitionally
  -- the same after identifying the two colimit-object transports generated by
  -- `stageFunctor_comp` and the cocone compatibilities `colimit.w`.
  ext ℱ Y y
  -- The source-route comparison is now reduced to the explicit transport identity on sections.
  let p :
      (S.stageFunctor (b ≫ a)).obj Y.unop =
        (S.stageFunctor b).obj ((S.stageFunctor a).obj Y.unop) :=
    congrArg
      (fun F : S.stage i ⥤ S.stage k ↦ F.obj Y.unop)
      (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op))
  let q :
      (S.stageCoconeFunctor k).obj ((S.stageFunctor (b ≫ a)).obj Y.unop) =
        (S.stageCoconeFunctor i).obj Y.unop :=
    congrArg
      (fun F : S.stage i ⥤ S.ColimitCategory ↦ F.obj Y.unop)
      (S.stageCoconeFunctor_comp_eq (b ≫ a))
  simpa using
    colimit_stage_sheaf_pushforward_assoc_transport (S := S) a b ℱ Y p q y

/-- Helper for Lemma 7.18.4: the canonical pullback-composition comparisons from the stage sites
to the colimit site satisfy the standard associativity coherence. -/
theorem colimit_stage_sheaf_pullback_comp_assoc
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    Functor.isoWhiskerLeft _ (S.colimitStageSheafPullbackCompIso (Type u) b) ≪≫
      S.colimitStageSheafPullbackCompIso (Type u) a =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (S.stageSheafPullbackCompIso (Type u) a b) _ ≪≫
        S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a) := by
  -- Route correction: package the owner-level associativity once so later section-level proofs can
  -- reuse it without reopening the adjunction data inside `transitionOnColimit_comp`.
  simpa [CofilteredSiteDiagram.stageSheafPullbackCompIso,
    CofilteredSiteDiagram.colimitStageSheafPullbackCompIso] using
    (Adjunction.leftAdjointCompIso_assoc
      ((S.stageFunctor a).sheafAdjunctionContinuous
        (Type u) (S.stageTopology i) (S.stageTopology j))
      ((S.stageFunctor b).sheafAdjunctionContinuous
        (Type u) (S.stageTopology j) (S.stageTopology k))
      ((S.stageCoconeFunctor k).sheafAdjunctionContinuous
        (Type u) (S.stageTopology k) S.colimitTopology)
      ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous
        (Type u) (S.stageTopology i) (S.stageTopology k))
      ((S.stageCoconeFunctor j).sheafAdjunctionContinuous
        (Type u) (S.stageTopology j) S.colimitTopology)
      ((S.stageCoconeFunctor i).sheafAdjunctionContinuous
        (Type u) (S.stageTopology i) S.colimitTopology)
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor (b ≫ a) =
              S.stageFunctor a ⋙ S.stageFunctor b from
            congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op))).symm
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k))
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor b ⋙ S.stageCoconeFunctor k =
              S.stageCoconeFunctor j from
            S.stageCoconeFunctor_comp_eq b))
        (Type u) (S.stageTopology j) (S.stageTopology k) S.colimitTopology)
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor a ⋙ S.stageCoconeFunctor j =
              S.stageCoconeFunctor i from
            S.stageCoconeFunctor_comp_eq a))
        (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology)
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor (b ≫ a) ⋙ S.stageCoconeFunctor k =
              S.stageCoconeFunctor i from
            S.stageCoconeFunctor_comp_eq (b ≫ a)))
        (Type u) (S.stageTopology i) (S.stageTopology k) S.colimitTopology)
      (colimit_stage_sheaf_pushforward_assoc (S := S) a b))

/-- Helper for Lemma 7.18.4: after evaluating the inverse-form associativity coherence on a stage
sheaf, the direct `(b ≫ a)` comparison becomes the successive `a`-leg and `b`-leg comparisons.
This is the app-level normalization planned for `transitionOnColimit_comp`. -/
theorem colimit_stage_sheaf_pullback_comp_middle_cancel
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    (((S.stageCoconeFunctor k).sheafPullback
      (Type u) (S.stageTopology k) S.colimitTopology).map
      ((S.stageSheafPullbackCompIso (Type u) a b).inv.app ℱ)) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          ((S.stageSheafPullbackCompIso (Type u) a b).hom.app ℱ)) =
      𝟙 _ := by
  -- Combine the mapped inverse/hom pair into the image of the identity and then simplify.
  rw [← Functor.map_comp, (S.stageSheafPullbackCompIso (Type u) a b).inv_hom_id_app, Functor.map_id]

/-- Helper for Lemma 7.18.4: after evaluating the pullback associativity coherence on a fixed
stage sheaf, postcomposing with the `b`- and `a`-leg comparison maps collapses the residual outer
associator transport to the identity. -/
theorem colimit_stage_sheaf_pullback_outer_normalize_app
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app ℱ ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          ((S.stageSheafPullbackCompIso (Type u) a b).inv.app ℱ)) ≫
        eqToHom (by simp) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
          (((S.stageFunctor a).sheafPullback
            (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ =
      𝟙 _ := by
  -- Route correction: use the component of the inverse associativity isomorphism first, then
  -- cancel the `b`- and `a`-comparison inverse/hom pairs on the app level.
  have hcomp :
      (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
          (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app
            (((S.stageFunctor a).sheafPullback
              (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) =
        (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app ℱ ≫
          (((S.stageCoconeFunctor k).sheafPullback
            (Type u) (S.stageTopology k) S.colimitTopology).map
            ((S.stageSheafPullbackCompIso (Type u) a b).inv.app ℱ)) ≫
          eqToHom (by simp) := by
    -- Evaluate the inverse owner-level associativity isomorphism at `ℱ`; this exposes the direct
    -- `(b ≫ a)` comparison and the explicit associator transport.
    simpa [Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] using
      congrArg (fun α ↦ α.hom.app ℱ)
        (congrArg Iso.symm (colimit_stage_sheaf_pullback_comp_assoc (S := S) a b))
  -- Postcompose with the `b`- and `a`-leg comparison maps and cancel the resulting inverse/hom
  -- pairs in order.
  have hpost := congrArg
    (fun f ↦
      f ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
          (((S.stageFunctor a).sheafPullback
            (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ)
    hcomp
  have hpost' :
      (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app ℱ ≫
          (((S.stageCoconeFunctor k).sheafPullback
            (Type u) (S.stageTopology k) S.colimitTopology).map
            ((S.stageSheafPullbackCompIso (Type u) a b).inv.app ℱ)) ≫
          eqToHom (by simp) ≫
          (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
            (((S.stageFunctor a).sheafPullback
              (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
          (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ =
        (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
          (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app
            (((S.stageFunctor a).sheafPullback
              (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
          (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
            (((S.stageFunctor a).sheafPullback
              (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
          (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ := by
    simpa [Category.assoc] using hpost.symm
  calc
    (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app ℱ ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          ((S.stageSheafPullbackCompIso (Type u) a b).inv.app ℱ)) ≫
        eqToHom (by simp) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
          (((S.stageFunctor a).sheafPullback
            (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ =
      (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app
          (((S.stageFunctor a).sheafPullback
            (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
          (((S.stageFunctor a).sheafPullback
            (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ := hpost'
    _ = 𝟙 _ := by
      calc
        (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
            (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app
              (((S.stageFunctor a).sheafPullback
                (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
            (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
              (((S.stageFunctor a).sheafPullback
                (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
            (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ =
          (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
            ((S.colimitStageSheafPullbackCompIso (Type u) b).inv.app
                (((S.stageFunctor a).sheafPullback
                  (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) ≫
              (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
                (((S.stageFunctor a).sheafPullback
                  (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ)) ≫
            (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ := by
              simp [Category.assoc]
        _ =
          (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
            𝟙 _ ≫
            (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ := by
              exact congrArg
                (fun t ↦
                  (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
                    t ≫
                    (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ)
                ((S.colimitStageSheafPullbackCompIso (Type u) b).inv_hom_id_app
                  (((S.stageFunctor a).sheafPullback
                    (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ))
        _ =
          (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
            (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ := by
              simp
        _ = 𝟙 _ := by
              rw [(S.colimitStageSheafPullbackCompIso (Type u) a).inv_hom_id_app]

/-- Helper for Lemma 7.18.4: after evaluating the inverse-form associativity coherence on a stage
sheaf, the direct `(b ≫ a)` comparison becomes the successive `a`-leg and `b`-leg comparisons.
This is the app-level normalization planned for `transitionOnColimit_comp`. -/
theorem colimit_stage_sheaf_pullback_comp_assoc_inv_app
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app ℱ ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          ((S.stageSheafPullbackCompIso (Type u) a b).inv.app ℱ)) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
          (((S.stageFunctor a).sheafPullback
            (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ) =
      (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ := by
  -- Postcompose with the `a`-leg comparison map, use the explicit outer normalization above, and
  -- then cancel the resulting rightmost inverse/hom pair.
  apply (cancel_mono ((S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ)).1
  calc
    ((S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app ℱ ≫
          (((S.stageCoconeFunctor k).sheafPullback
            (Type u) (S.stageTopology k) S.colimitTopology).map
            ((S.stageSheafPullbackCompIso (Type u) a b).inv.app ℱ)) ≫
          (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
            (((S.stageFunctor a).sheafPullback
              (Type u) (S.stageTopology i) (S.stageTopology j)).obj ℱ)) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ =
      𝟙 _ := by
        simpa [Category.assoc] using
          colimit_stage_sheaf_pullback_outer_normalize_app (S := S) a b ℱ
    _ =
      (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ℱ ≫
        (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ := by
        symm
        exact (S.colimitStageSheafPullbackCompIso (Type u) a).inv_hom_id_app ℱ

/-- Helper for Lemma 7.18.4: conjugating a stage morphism by the `b`-leg colimit pullback
comparison is exactly the mapped `b`-pullback of that morphism. This isolates the middle
naturality step used in `transitionOnColimit_comp`. -/
theorem colimit_stage_sheaf_pullback_comp_naturality_cancel
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    {j k : S.I} (b : k ⟶ j)
    {ℱ ℱ' : Sheaf (S.stageTopology j) (Type u)} (f : ℱ ⟶ ℱ') :
    (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app ℱ ≫
        (((S.stageCoconeFunctor j).sheafPullback
          (Type u) (S.stageTopology j) S.colimitTopology).map f) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app ℱ' =
      (((S.stageCoconeFunctor k).sheafPullback
        (Type u) (S.stageTopology k) S.colimitTopology).map
        (((S.stageFunctor b).sheafPullback
          (Type u) (S.stageTopology j) (S.stageTopology k)).map f)) := by
  -- Specialize naturality of the `b`-comparison and then cancel the right `hom ≫ inv` pair.
  have hnat :=
    congrArg
      (fun t ↦ t ≫ (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app ℱ')
      ((S.colimitStageSheafPullbackCompIso (Type u) b).hom.naturality f)
  have hstep :
      (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app ℱ ≫
          (((S.stageCoconeFunctor j).sheafPullback
            (Type u) (S.stageTopology j) S.colimitTopology).map f) ≫
          (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app ℱ' =
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          (((S.stageFunctor b).sheafPullback
            (Type u) (S.stageTopology j) (S.stageTopology k)).map f)) ≫
          ((S.colimitStageSheafPullbackCompIso (Type u) b).hom.app ℱ' ≫
            (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app ℱ') := by
    simpa [Category.assoc, Functor.comp_map] using hnat.symm
  have hcollapse :
      (((S.stageCoconeFunctor k).sheafPullback
        (Type u) (S.stageTopology k) S.colimitTopology).map
        (((S.stageFunctor b).sheafPullback
          (Type u) (S.stageTopology j) (S.stageTopology k)).map f)) ≫
        ((S.colimitStageSheafPullbackCompIso (Type u) b).hom.app ℱ' ≫
          (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app ℱ') =
      (((S.stageCoconeFunctor k).sheafPullback
        (Type u) (S.stageTopology k) S.colimitTopology).map
        (((S.stageFunctor b).sheafPullback
          (Type u) (S.stageTopology j) (S.stageTopology k)).map f)) := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (((S.stageCoconeFunctor k).sheafPullback
            (Type u) (S.stageTopology k) S.colimitTopology).map
            (((S.stageFunctor b).sheafPullback
              (Type u) (S.stageTopology j) (S.stageTopology k)).map f)) ≫
            t)
        ((S.colimitStageSheafPullbackCompIso (Type u) b).hom_inv_id_app ℱ')
  exact hstep.trans hcollapse

theorem transitionOnColimit_comp
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    transitionOnColimit family (b ≫ a) =
      transitionOnColimit family a ≫ transitionOnColimit family b := by
  -- Route correction: the owner-level coherence is now packaged by
  -- `colimit_stage_sheaf_pullback_comp_assoc_inv_app`; the remaining step is to combine that
  -- normalization with naturality of the `b`-comparison and then apply `family.transition_comp`.
  have hpullback :=
    colimit_stage_sheaf_pullback_comp_assoc_inv_app (S := S) a b (family.obj i)
  have hnat :=
    colimit_stage_sheaf_pullback_comp_naturality_cancel (S := S) (b := b)
      (f := family.transition a)
  have htransition :
      (S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
          (((S.stageFunctor b).sheafPullback
            (Type u) (S.stageTopology j) (S.stageTopology k)).map
            (family.transition a)) ≫
          family.transition b =
        family.transition (b ≫ a) := by
    -- Rewrite the source-stage cocycle so the inverse/hom pair cancels before returning to the
    -- direct `(b ≫ a)` transition.
    calc
      (S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
            (((S.stageFunctor b).sheafPullback
              (Type u) (S.stageTopology j) (S.stageTopology k)).map
              (family.transition a)) ≫
            family.transition b =
          (S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
            ((S.stageSheafPullbackCompIso (Type u) a b).hom.app (family.obj i) ≫
              family.transition (b ≫ a)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ (S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫ t)
                  (family.transition_comp a b).symm
      _ =
          ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
              (S.stageSheafPullbackCompIso (Type u) a b).hom.app (family.obj i)) ≫
            family.transition (b ≫ a) := by
              simp [Category.assoc]
      _ = family.transition (b ≫ a) := by
              rw [(S.stageSheafPullbackCompIso (Type u) a b).inv_hom_id_app]
              simp
  -- Follow the source route: rewrite the outer comparison by associativity, replace the middle
  -- block by naturality of the `b`-comparison, and then map the stage cocycle relation.
  symm
  calc
    transitionOnColimit family a ≫ transitionOnColimit family b =
      (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app (family.obj i) ≫
        (((S.stageCoconeFunctor j).sheafPullback
          (Type u) (S.stageTopology j) S.colimitTopology).map
          (family.transition a)) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app (family.obj j) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          (family.transition b)) := by
            simp [transitionOnColimit, Category.assoc]
    _ =
      (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app (family.obj i) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i))) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
          (((S.stageFunctor a).sheafPullback
            (Type u) (S.stageTopology i) (S.stageTopology j)).obj (family.obj i)) ≫
        (((S.stageCoconeFunctor j).sheafPullback
          (Type u) (S.stageTopology j) S.colimitTopology).map
          (family.transition a)) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) b).inv.app (family.obj j) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          (family.transition b)) := by
            rw [← hpullback]
            simp [Category.assoc]
    _ =
      (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app (family.obj i) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i))) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          (((S.stageFunctor b).sheafPullback
            (Type u) (S.stageTopology j) (S.stageTopology k)).map
            (family.transition a))) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          (family.transition b)) := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app (family.obj i) ≫
                    (((S.stageCoconeFunctor k).sheafPullback
                      (Type u) (S.stageTopology k) S.colimitTopology).map
                      ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i))) ≫
                    t ≫
                    (((S.stageCoconeFunctor k).sheafPullback
                      (Type u) (S.stageTopology k) S.colimitTopology).map
                      (family.transition b)))
                hnat
    _ =
      (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app (family.obj i) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
            (((S.stageFunctor b).sheafPullback
              (Type u) (S.stageTopology j) (S.stageTopology k)).map
              (family.transition a)) ≫
            family.transition b)) := by
            have hmap :
                (((S.stageCoconeFunctor k).sheafPullback
                  (Type u) (S.stageTopology k) S.colimitTopology).map
                  ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i))) ≫
                  (((S.stageCoconeFunctor k).sheafPullback
                    (Type u) (S.stageTopology k) S.colimitTopology).map
                    (((S.stageFunctor b).sheafPullback
                      (Type u) (S.stageTopology j) (S.stageTopology k)).map
                      (family.transition a))) ≫
                  (((S.stageCoconeFunctor k).sheafPullback
                    (Type u) (S.stageTopology k) S.colimitTopology).map
                    (family.transition b)) =
                (((S.stageCoconeFunctor k).sheafPullback
                  (Type u) (S.stageTopology k) S.colimitTopology).map
                  ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
                    (((S.stageFunctor b).sheafPullback
                      (Type u) (S.stageTopology j) (S.stageTopology k)).map
                      (family.transition a)) ≫
                    family.transition b)) := by
              calc
                (((S.stageCoconeFunctor k).sheafPullback
                    (Type u) (S.stageTopology k) S.colimitTopology).map
                    ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i))) ≫
                    (((S.stageCoconeFunctor k).sheafPullback
                      (Type u) (S.stageTopology k) S.colimitTopology).map
                      (((S.stageFunctor b).sheafPullback
                        (Type u) (S.stageTopology j) (S.stageTopology k)).map
                        (family.transition a))) ≫
                    (((S.stageCoconeFunctor k).sheafPullback
                      (Type u) (S.stageTopology k) S.colimitTopology).map
                      (family.transition b)) =
                  (((S.stageCoconeFunctor k).sheafPullback
                    (Type u) (S.stageTopology k) S.colimitTopology).map
                    ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
                      (((S.stageFunctor b).sheafPullback
                        (Type u) (S.stageTopology j) (S.stageTopology k)).map
                        (family.transition a)))) ≫
                    (((S.stageCoconeFunctor k).sheafPullback
                      (Type u) (S.stageTopology k) S.colimitTopology).map
                      (family.transition b)) := by
                        rw [← Functor.map_comp_assoc]
                _ =
                  (((S.stageCoconeFunctor k).sheafPullback
                    (Type u) (S.stageTopology k) S.colimitTopology).map
                    (((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
                        (((S.stageFunctor b).sheafPullback
                          (Type u) (S.stageTopology j) (S.stageTopology k)).map
                          (family.transition a))) ≫
                      family.transition b)) := by
                        rw [← Functor.map_comp]
            have houter :
                (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app (family.obj i) ≫
                    (((S.stageCoconeFunctor k).sheafPullback
                      (Type u) (S.stageTopology k) S.colimitTopology).map
                      ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i))) ≫
                  (((S.stageCoconeFunctor k).sheafPullback
                    (Type u) (S.stageTopology k) S.colimitTopology).map
                    (((S.stageFunctor b).sheafPullback
                      (Type u) (S.stageTopology j) (S.stageTopology k)).map
                      (family.transition a))) ≫
                  (((S.stageCoconeFunctor k).sheafPullback
                    (Type u) (S.stageTopology k) S.colimitTopology).map
                    (family.transition b)) =
                (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app (family.obj i) ≫
                  (((S.stageCoconeFunctor k).sheafPullback
                    (Type u) (S.stageTopology k) S.colimitTopology).map
                    ((S.stageSheafPullbackCompIso (Type u) a b).inv.app (family.obj i) ≫
                      (((S.stageFunctor b).sheafPullback
                        (Type u) (S.stageTopology j) (S.stageTopology k)).map
                        (family.transition a)) ≫
                      family.transition b)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦
                    (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app (family.obj i) ≫ t)
                  hmap
            exact houter
    _ =
      (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).inv.app (family.obj i) ≫
        (((S.stageCoconeFunctor k).sheafPullback
          (Type u) (S.stageTopology k) S.colimitTopology).map
          (family.transition (b ≫ a))) := by
            rw [htransition]
    _ = transitionOnColimit family (b ≫ a) := by
            rfl

/-- The compatible family `family` determines a filtered diagram on the colimit site by pulling
each stage sheaf back along the cocone functor `u_i : \mathcal C_i \to \mathcal C`. This diagram
is only an implementation device for the filtered-colimit comparison theorem. -/
noncomputable def diagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S) :
    S.Iᵒᵖ ⥤ Sheaf S.colimitTopology (Type u) where
  obj i :=
    (((S.stageCoconeFunctor i.unop).sheafPullback (Type u)
      (S.stageTopology i.unop) S.colimitTopology).obj (family.obj i.unop))
  map a := transitionOnColimit family a.unop
  map_id := by
    intro i
    simpa using transitionOnColimit_id family i.unop
  map_comp := by
    intro i j k a b
    simpa using transitionOnColimit_comp family a.unop b.unop

/-- The colimit sheaf on the colimit site attached to a compatible stage family. -/
noncomputable def colimitSheaf
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S) :
    Sheaf S.colimitTopology (Type u) :=
  colimit (diagram family)

/- The source colimit in Lemma 7.18.4 is indexed by arrows `a : j ⟶ i`, represented in Lean by
`(Over i)ᵒᵖ`, and sends `a` to the section set `𝒜_j(u_a(X))`. -/
abbrev sectionValue
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) : Type u :=
  (family.obj A.unop.left).obj.obj
    (op (S.overImage X A))

theorem sectionMap_target_eq
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    ((((S.stageFunctor u.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
        (family.obj B.unop.left)).obj.obj
      (op (S.overImage X A))) =
      sectionValue family X B := by
  -- Rewrite the pushforward evaluation to the section at the image object, then identify that
  -- image with `S.overImage X B` using the commutative triangle `Over.w u.unop`.
  have hcomp :
      S.stageFunctor A.unop.hom ⋙ S.stageFunctor u.unop.left =
        S.stageFunctor (u.unop.left ≫ A.unop.hom) := by
    exact congrArg Cat.Hom.toFunctor
      (S.diagram.map_comp A.unop.hom.op u.unop.left.op).symm
  have h₁ :
      (S.stageFunctor u.unop.left).obj (S.overImage X A) =
        (S.stageFunctor (u.unop.left ≫ A.unop.hom)).obj X := by
    simpa [CofilteredSiteDiagram.overImage] using
      congrArg (fun F : S.stage i ⥤ S.stage B.unop.left ↦ F.obj X) hcomp
  have hw : u.unop.left ≫ A.unop.hom = B.unop.hom := by
    simpa using Over.w u.unop
  have h₂ :
      (S.stageFunctor (u.unop.left ≫ A.unop.hom)).obj X = S.overImage X B := by
    simpa [CofilteredSiteDiagram.overImage] using
      congrArg (fun a : B.unop.left ⟶ i ↦ (S.stageFunctor a).obj X) hw
  have hobj :
      (S.stageFunctor u.unop.left).obj (S.overImage X A) = S.overImage X B :=
    h₁.trans h₂
  simpa [sectionValue] using
    congrArg
      (fun Y ↦ (((family.obj B.unop.left).obj.obj (op Y))))
      hobj

noncomputable def sectionMap
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    sectionValue family X A ⟶ sectionValue family X B :=
  ((((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
      (family.obj A.unop.left)
      (family.obj B.unop.left))
    (family.transition u.unop.left)).1.app
      (op (S.overImage X A)) ≫
    eqToHom (sectionMap_target_eq family X u)

/-- Helper for Lemma 7.18.4: the identity arrow in `(Over i)ᵒᵖ` does not change the target
section type of `sectionMap`. This isolates the transport bookkeeping from the adjunction
normalization in `sectionMap_id`. -/
theorem sectionMap_target_eq_id
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    ((((S.stageFunctor (𝟙 A.unop.left)).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology A.unop.left)).obj
        (family.obj A.unop.left)).obj.obj
      (op (S.overImage X A))) =
      sectionValue family X A := by
  -- The identity-stage pushforward evaluates the same sheaf at the same stage object.
  have hstage :
      S.stageFunctor (𝟙 A.unop.left) = 𝟭 (S.stage A.unop.left) := by
    exact congrArg Cat.Hom.toFunctor (S.diagram.map_id (op A.unop.left))
  simp [sectionValue, hstage]

/-- Helper for Lemma 7.18.4: the target transport in `sectionMap_target_eq_id` is exactly the
image under the section functor of the identity-stage object equality on `S.overImage X A`. -/
theorem sectionMap_target_eq_id_eq_congrArg
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    sectionMap_target_eq_id family X A =
      congrArg ((family.obj A.unop.left).obj.obj)
        (congrArg Opposite.op
          (congrArg
            (fun F : S.stage A.unop.left ⥤ S.stage A.unop.left ↦
              F.obj (S.overImage X A))
            (stage_functor_id_eq_local (S := S) A.unop.left))) := by
  -- Both sides are equalities between the same pair of section types, so proof irrelevance
  -- identifies them before we evaluate the resulting transport.
  apply Subsingleton.elim

/-- Helper for Lemma 7.18.4: after evaluating the identity-stage pushforward comparison on
sections, the remaining target transport is exactly the identity map on the section set. -/
theorem identity_stage_pushforward_inv_eval_comp_section_transport
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    (((Functor.sheafPushforwardContinuousId'
          (eqToIso (stage_functor_id_eq_local (S := S) A.unop.left))
          (Type u) (S.stageTopology A.unop.left)).inv.app
        (family.obj A.unop.left)).1.app (op (S.overImage X A))) ≫
      eqToHom (sectionMap_target_eq_id family X A) =
        𝟙 (sectionValue family X A) := by
  -- Evaluate the owner-level identity comparison at the section object, then rewrite the target
  -- transport to the explicit object equality carried by `stage_functor_id_eq_local`.
  let hop :
      Opposite.op ((S.stageFunctor (𝟙 A.unop.left)).obj (S.overImage X A)) =
        Opposite.op (S.overImage X A) :=
    congrArg Opposite.op
      (congrArg
        (fun F : S.stage A.unop.left ⥤ S.stage A.unop.left ↦
          F.obj (S.overImage X A))
        (stage_functor_id_eq_local (S := S) A.unop.left))
  ext s
  rw [sectionMap_target_eq_id_eq_congrArg]
  -- The inverse identity pushforward comparison acts by `map (eqToHom hop.symm)`, and the
  -- postcomposed target transport is `eqToHom (congrArg _ hop)`.
  simp [Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, hop, CategoryTheory.eqToHom_map]
  simpa [hop, CategoryTheory.eqToHom_map] using
    (FunctorToTypes.eqToHom_map_comp_apply
      (F := ((((𝟭 (Sheaf (S.stageTopology A.unop.left) (Type u))).obj
          (family.obj A.unop.left)).obj) : (S.stage A.unop.left)ᵒᵖ ⥤ Type u))
      (p := hop.symm) (q := hop) s)

theorem sectionMap_id
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    sectionMap family X (𝟙 A) = 𝟙 _ := by
  -- Route correction: after isolating the section-level transport bridge, the identity proof stays
  -- on the source route by rewriting only the identity transition and its evaluated transpose.
  dsimp [sectionMap]
  -- Replace the target transport by the reflexive proof so only the adjunction mate remains.
  have htarget :
      sectionMap_target_eq family X (𝟙 A) = sectionMap_target_eq_id family X A := by
    apply Subsingleton.elim
  rw [htarget]
  -- Rewrite the identity transition and then replace the adjunction transpose by its evaluated
  -- identity-stage normal form.
  rw [family.transition_id]
  have happ :
      ((((S.stageFunctor (𝟙 A.unop.left)).sheafAdjunctionContinuous (Type u)
              (S.stageTopology A.unop.left) (S.stageTopology A.unop.left)).homEquiv
            (family.obj A.unop.left) (family.obj A.unop.left))
          ((S.stageSheafPullbackIdIso (Type u) A.unop.left).hom.app
            (family.obj A.unop.left))).1.app
          (op (S.overImage X A)) ≫
        eqToHom (sectionMap_target_eq_id family X A) =
      (((Functor.sheafPushforwardContinuousId'
            (eqToIso (stage_functor_id_eq_local (S := S) A.unop.left))
            (Type u) (S.stageTopology A.unop.left)).inv.app
          (family.obj A.unop.left)).1.app (op (S.overImage X A))) ≫
        eqToHom (sectionMap_target_eq_id family X A) := by
    -- Postcompose the evaluated adjunction normal form with the fixed target transport.
    exact congrArg
      (fun f ↦ f ≫ eqToHom (sectionMap_target_eq_id family X A))
      (identity_stage_adjunction_eval_normal_form (S := S)
        (i := A.unop.left) (ℱ := family.obj A.unop.left)
        (U := op (S.overImage X A)))
  -- The remaining composite is the explicit section-level transport bridge proved above.
  exact happ.trans (identity_stage_pushforward_inv_eval_comp_section_transport family X A)

/-- Helper for Lemma 7.18.4: stage transition functors compose in the order induced by the
inverse-system diagram. This packages `diagram.map_comp` in the direction expected by the
source-facing composite-adjunction normalization. -/
theorem stage_functor_comp_eq_local
    {S : CofilteredSiteDiagram.{u, u, u}}
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    S.stageFunctor a ⋙ S.stageFunctor b = S.stageFunctor (b ≫ a) := by
  -- Read the transition composition directly from the stored diagram law.
  exact (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op)).symm

/-- Helper for Lemma 7.18.4: the owner-facing stage composition equality used by
`stageSheafPullbackCompIso`. This is the same diagram relation as
`stage_functor_comp_eq_local`, but oriented for the pushforward-composition owner API. -/
theorem stage_functor_comp_eq_owner
    {S : CofilteredSiteDiagram.{u, u, u}}
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    S.stageFunctor (b ≫ a) = S.stageFunctor a ⋙ S.stageFunctor b := by
  -- Keep the owner-side composition equality available without ad hoc `Eq.symm`.
  exact congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op)

/-- Helper for Lemma 7.18.4: the inverse stage pullback-composition comparison is conjugate to
the direct pushforward-composition comparison on the owner side. This isolates the transport
hidden in `stageSheafPullbackCompIso` before threading it through the composite adjunction. -/
theorem stage_sheaf_pullback_comp_conjugate_inv
    {S : CofilteredSiteDiagram.{u, u, u}}
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    conjugateEquiv
        (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
            (S.stageTopology j) (S.stageTopology k)))
        ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology k))
        ((S.stageSheafPullbackCompIso (Type u) a b).inv) =
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (stage_functor_comp_eq_owner (S := S) a b).symm)
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)).hom := by
  -- Evaluate the conjugation componentwise; after unfolding the owner comparison, both sides are
  -- the same section map.
  ext ℱ Y y
  simp [CofilteredSiteDiagram.stageSheafPullbackCompIso]

/-- Helper for Lemma 7.18.4: the forward stage pullback-composition comparison is conjugate to
the inverse direct pushforward-composition comparison. This is the dual owner-side normalization
used when the source cocycle starts from `(S.stageSheafPullbackCompIso ...).hom`. -/
theorem stage_sheaf_pullback_comp_conjugate_hom
    {S : CofilteredSiteDiagram.{u, u, u}}
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    conjugateEquiv
        ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology k))
        (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
            (S.stageTopology j) (S.stageTopology k)))
        ((S.stageSheafPullbackCompIso (Type u) a b).hom) =
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (stage_functor_comp_eq_owner (S := S) a b).symm)
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)).inv := by
  let adj :=
    ((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).comp
      ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k))
  let adj_c :=
    (S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology k)
  let compIso :=
    Functor.sheafPushforwardContinuousComp'
      (eqToIso (stage_functor_comp_eq_owner (S := S) a b).symm)
      (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)
  -- Compose the forward and inverse conjugates; the inverse branch is already normalized above,
  -- and the composite is the identity because `(S.stageSheafPullbackCompIso ... )` is an
  -- isomorphism.
  apply (cancel_mono compIso.hom).1
  have hcomp :=
    CategoryTheory.conjugateEquiv_comp adj_c adj adj_c
      ((S.stageSheafPullbackCompIso (Type u) a b).hom)
      ((S.stageSheafPullbackCompIso (Type u) a b).inv)
  simpa [adj, adj_c, compIso, stage_sheaf_pullback_comp_conjugate_inv, Category.assoc] using
    hcomp

/-- Helper for Lemma 7.18.4: under the composite pullback adjunction, the staged right branch of
the source cocycle is exactly the successive `a`- then `b`-unit formula. This records the
composite-adjunction normalization before any evaluation on section sets. -/
theorem section_transition_comp_right_side_normalization
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
            (S.stageTopology j) (S.stageTopology k))).homEquiv
        (family.obj i)
        (family.obj k))
      ((((S.stageFunctor b).sheafPullback (Type u)
            (S.stageTopology j) (S.stageTopology k)).map
            (family.transition a)) ≫
          family.transition b) =
      ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
              (S.stageTopology i) (S.stageTopology j)).homEquiv
            (family.obj i)
            (family.obj j))
          (family.transition a)) ≫
        (((S.stageFunctor a).sheafPushforwardContinuous (Type u)
              (S.stageTopology i) (S.stageTopology j)).map
            ((((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
                  (S.stageTopology j) (S.stageTopology k)).homEquiv
                (family.obj j)
                (family.obj k))
              (family.transition b))) := by
  let adj_a :=
    (S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)
  let adj_b :=
    (S.stageFunctor b).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)
  -- First transpose along `adj_b`, then along `adj_a`; each step is the corresponding
  -- naturality identity for `homEquiv`.
  change
    (adj_a.homEquiv
      (family.obj i)
      (((S.stageFunctor b).sheafPushforwardContinuous (Type u)
          (S.stageTopology j) (S.stageTopology k)).obj (family.obj k)))
      ((adj_b.homEquiv
          (((S.stageFunctor a).sheafPullback (Type u)
              (S.stageTopology i) (S.stageTopology j)).obj (family.obj i))
          (family.obj k))
        ((((S.stageFunctor b).sheafPullback (Type u)
              (S.stageTopology j) (S.stageTopology k)).map
              (family.transition a)) ≫
          family.transition b)) =
      ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
              (S.stageTopology i) (S.stageTopology j)).homEquiv
            (family.obj i)
            (family.obj j))
          (family.transition a)) ≫
        (((S.stageFunctor a).sheafPushforwardContinuous (Type u)
              (S.stageTopology i) (S.stageTopology j)).map
            ((((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
                  (S.stageTopology j) (S.stageTopology k)).homEquiv
                (family.obj j)
                (family.obj k))
              (family.transition b)))
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]

/-- Helper for Lemma 7.18.4: transposing after precomposition with a left-adjoint comparison is
postcomposition with its conjugate. -/
theorem homEquiv_conjugateEquiv_exchange'
    {C₀ D : Type*} [Category C₀] [Category D]
    {L₁ L₂ : C₀ ⥤ D} {R₁ R₂ : D ⥤ C₀} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (τ : L₂ ⟶ L₁) {X : C₀} {Y : D} (f : L₁.obj X ⟶ Y) :
    (adj₂.homEquiv X Y) (τ.app X ≫ f) =
      (adj₁.homEquiv X Y) f ≫ (conjugateEquiv adj₁ adj₂ τ).app Y := by
  have h1 : (adj₂.homEquiv X Y) (τ.app X ≫ f) =
      (adj₂.unit.app X ≫ R₂.map (τ.app X)) ≫ R₂.map f := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    rfl
  have h2 : (adj₁.homEquiv X Y) f ≫ (conjugateEquiv adj₁ adj₂ τ).app Y =
      (adj₁.unit.app X ≫ (conjugateEquiv adj₁ adj₂ τ).app (L₁.obj X)) ≫ R₂.map f := by
    rw [Adjunction.homEquiv_unit, Category.assoc, Category.assoc]
    exact congrArg (fun t => adj₁.unit.app X ≫ t)
      ((conjugateEquiv adj₁ adj₂ τ).naturality f)
  rw [h1, h2, ← unit_conjugateEquiv]

/-- Helper for Lemma 7.18.4: a section cast does not depend on the equality proof. -/
theorem eqToHom_apply_irrel' {A B : Type u} (p q : A = B) (x : A) :
    eqToHom p x = eqToHom q x := by
  subst p
  rfl

/-- Helper for Lemma 7.18.4: a returning double chain of section casts is the identity. -/
theorem eqToHom_apply_collapse₂₀' {A B : Type u}
    (p₁ : A = B) (p₂ : B = A) (x : A) :
    eqToHom p₂ (eqToHom p₁ x) = x := by
  subst p₁
  rfl

/-- Helper for Lemma 7.18.4: a triple chain of section casts collapses to a single cast. -/
theorem eqToHom_apply_collapse₃₁' {A B C D : Type u}
    (p₁ : A = B) (p₂ : B = C) (p₃ : C = D) (q : A = D) (x : A) :
    eqToHom p₃ (eqToHom p₂ (eqToHom p₁ x)) = eqToHom q x := by
  subst p₁; subst p₂; subst p₃
  rfl

/-- Helper for Lemma 7.18.4: the sheaf-level cocycle for the transposed transition maps. -/
theorem section_transition_cocycle
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} {A B C : (Over i)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ C) :
    (((S.stageFunctor (u ≫ v).unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology C.unop.left)).homEquiv
      (family.obj A.unop.left) (family.obj C.unop.left))
      (family.transition (u ≫ v).unop.left) =
    ((((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
      (family.obj A.unop.left) (family.obj B.unop.left))
      (family.transition u.unop.left)) ≫
    ((S.stageFunctor u.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).map
      ((((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).homEquiv
        (family.obj B.unop.left) (family.obj C.unop.left))
        (family.transition v.unop.left)) ≫
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (stage_functor_comp_eq_owner (S := S) u.unop.left v.unop.left).symm)
      (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
      (S.stageTopology C.unop.left)).hom.app (family.obj C.unop.left) := by
  set K := (Functor.sheafPushforwardContinuousComp'
    (eqToIso (stage_functor_comp_eq_owner (S := S) u.unop.left v.unop.left).symm)
    (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
    (S.stageTopology C.unop.left)) with hK
  have hex := homEquiv_conjugateEquiv_exchange'
    ((S.stageFunctor (v.unop.left ≫ u.unop.left)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology C.unop.left))
    (((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).comp
      ((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)))
    ((S.stageSheafPullbackCompIso (Type u) u.unop.left v.unop.left).hom)
    (family.transition (v.unop.left ≫ u.unop.left))
  rw [stage_sheaf_pullback_comp_conjugate_hom] at hex
  have hcancel := congrArg (fun t => t ≫ K.hom.app (family.obj C.unop.left)) hex
  simp only [hK, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hcancel
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ K.hom.app (family.obj C.unop.left))
    (section_transition_comp_right_side_normalization family
      u.unop.left v.unop.left).symm) ?_
  refine Eq.trans (congrArg (fun t =>
    ((((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).comp
      ((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left))).homEquiv
      (family.obj A.unop.left) (family.obj C.unop.left)) t ≫
      K.hom.app (family.obj C.unop.left))
    (family.transition_comp u.unop.left v.unop.left).symm) ?_
  exact hcancel

theorem sectionMap_comp
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    {A B C : (Over i)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ C) :
    sectionMap family X (u ≫ v) =
      sectionMap family X u ≫ sectionMap family X v := by
  have hcocycle := section_transition_cocycle family u v
  have hobj : (S.stageFunctor u.unop.left).obj (S.overImage X A) = S.overImage X B := by
    have hcomp :
        S.stageFunctor A.unop.hom ⋙ S.stageFunctor u.unop.left =
          S.stageFunctor (u.unop.left ≫ A.unop.hom) :=
      congrArg Cat.Hom.toFunctor
        (S.diagram.map_comp A.unop.hom.op u.unop.left.op).symm
    have h₁ : (S.stageFunctor u.unop.left).obj (S.overImage X A) =
        (S.stageFunctor (u.unop.left ≫ A.unop.hom)).obj X := by
      simpa [CofilteredSiteDiagram.overImage] using
        congrArg (fun F : S.stage i ⥤ S.stage B.unop.left ↦ F.obj X) hcomp
    have hw : u.unop.left ≫ A.unop.hom = B.unop.hom := by simpa using Over.w u.unop
    have h₂ : (S.stageFunctor (u.unop.left ≫ A.unop.hom)).obj X = S.overImage X B := by
      simpa [CofilteredSiteDiagram.overImage] using
        congrArg (fun a : B.unop.left ⟶ i ↦ (S.stageFunctor a).obj X) hw
    exact h₁.trans h₂
  funext s
  have happ := congrArg
    (fun t => eqToHom (sectionMap_target_eq family X (u ≫ v))
      ((t.1.app (op (S.overImage X A))) s)) hcocycle
  refine happ.trans ?_
  change eqToHom (sectionMap_target_eq family X (u ≫ v))
    (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (stage_functor_comp_eq_owner (S := S) u.unop.left v.unop.left).symm)
      (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
      (S.stageTopology C.unop.left)).hom.app
      (family.obj C.unop.left)).1.app (op (S.overImage X A))
      (((((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).homEquiv
        (family.obj B.unop.left) (family.obj C.unop.left))
        (family.transition v.unop.left)).1.app
        (op ((S.stageFunctor u.unop.left).obj (S.overImage X A)))
        (((((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
          (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
          (family.obj A.unop.left) (family.obj B.unop.left))
          (family.transition u.unop.left)).1.app (op (S.overImage X A)) s))) =
    eqToHom (sectionMap_target_eq family X v)
      (((((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).homEquiv
        (family.obj B.unop.left) (family.obj C.unop.left))
        (family.transition v.unop.left)).1.app (op (S.overImage X B))
        (eqToHom (sectionMap_target_eq family X u)
          (((((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
            (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
            (family.obj A.unop.left) (family.obj B.unop.left))
            (family.transition u.unop.left)).1.app (op (S.overImage X A)) s)))
  have h₁ : ((family.obj B.unop.left).obj.obj
      (op ((S.stageFunctor u.unop.left).obj (S.overImage X A)))) =
      ((family.obj B.unop.left).obj.obj (op (S.overImage X B))) :=
    congrArg (fun Z => (family.obj B.unop.left).obj.obj (op Z)) hobj
  have h₂ : ((((S.stageFunctor v.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
      (family.obj C.unop.left)).obj.obj (op (S.overImage X B))) =
      ((((S.stageFunctor v.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
      (family.obj C.unop.left)).obj.obj
      (op ((S.stageFunctor u.unop.left).obj (S.overImage X A)))) :=
    congrArg (fun Z => (((S.stageFunctor v.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
      (family.obj C.unop.left)).obj.obj (op Z)) hobj.symm
  have hcongr : (((((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).homEquiv
      (family.obj B.unop.left) (family.obj C.unop.left))
      (family.transition v.unop.left)).1.app
      (op ((S.stageFunctor u.unop.left).obj (S.overImage X A)))) =
      eqToHom h₁ ≫ ((((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).homEquiv
        (family.obj B.unop.left) (family.obj C.unop.left))
        (family.transition v.unop.left)).1.app (op (S.overImage X B)) ≫ eqToHom h₂ := by
    have := NatTrans.congr
      (((((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).homEquiv
        (family.obj B.unop.left) (family.obj C.unop.left))
        (family.transition v.unop.left)).1) (congrArg op hobj)
    simpa [eqToHom_map] using this
  have hcongr_el := congrFun hcongr
    (((((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
      (family.obj A.unop.left) (family.obj B.unop.left))
      (family.transition u.unop.left)).1.app (op (S.overImage X A)) s)
  rw [hcongr_el]
  have hKty : ((((S.stageFunctor v.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
      (family.obj C.unop.left)).obj.obj
      (op ((S.stageFunctor u.unop.left).obj (S.overImage X A)))) =
      ((((S.stageFunctor (v.unop.left ≫ u.unop.left)).sheafPushforwardContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology C.unop.left)).obj
      (family.obj C.unop.left)).obj.obj (op (S.overImage X A))) := by
    simpa using congrArg
      (fun G : S.stage A.unop.left ⥤ S.stage C.unop.left =>
        (family.obj C.unop.left).obj.obj (op (G.obj (S.overImage X A))))
      (stage_functor_comp_eq_local (S := S) u.unop.left v.unop.left)
  have hKcast : ∀ z, (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (stage_functor_comp_eq_owner (S := S) u.unop.left v.unop.left).symm)
      (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
      (S.stageTopology C.unop.left)).hom.app
      (family.obj C.unop.left)).1.app (op (S.overImage X A))) z =
      eqToHom hKty z := by
    intro z
    simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
      CategoryTheory.eqToHom_map, eqToHom_app]
  rw [hKcast]
  refine Eq.trans (congrArg
    (fun t => eqToHom (sectionMap_target_eq family X (u ≫ v))
      (eqToHom hKty (eqToHom h₂
        (((((S.stageFunctor v.unop.left).sheafAdjunctionContinuous (Type u)
          (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).homEquiv
          (family.obj B.unop.left) (family.obj C.unop.left))
          (family.transition v.unop.left)).1.app (op (S.overImage X B)) t))))
    (eqToHom_apply_irrel' h₁ (sectionMap_target_eq family X u)
      (((((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
        (family.obj A.unop.left) (family.obj B.unop.left))
        (family.transition u.unop.left)).1.app (op (S.overImage X A)) s))) ?_
  exact eqToHom_apply_collapse₃₁' h₂ hKty
    (sectionMap_target_eq family X (u ≫ v)) (sectionMap_target_eq family X v) _

/-- The source-text indexing diagram `a : j ⟶ i ↦ 𝒜_j(u_a(X))`. -/
noncomputable def sectionDiagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj A := sectionValue family X A
  map u := sectionMap family X u
  map_id A := sectionMap_id family X A
  map_comp u v := sectionMap_comp family X u v

noncomputable abbrev pulledBackSectionDiagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
  (family : ColimitSiteStageFamily S)
  {i : S.I} (X : S.stage i) :
  (Over i)ᵒᵖ ⥤ Type u :=
  (Over.forget i).op ⋙ family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u) ⋙
    (evaluation _ (Type u)).obj (op ((S.stageCoconeFunctor i).obj X))

theorem sourceToPulledBackTarget_eq
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    (((((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
            (S.stageTopology A.unop.left) S.colimitTopology) ⋙
          (S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous (Type u)
            (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj.obj)
      (op (S.overImage X A)) =
      (pulledBackSectionDiagram family X).obj A := by
  -- Rewrite the pushforward evaluation to the literal colimit-site object-image, then collapse
  -- that image to `u_i(X)` via the cocone relation `colimit.w`.
  have hcomp :
      S.stageFunctor A.unop.hom ⋙ S.stageCoconeFunctor A.unop.left =
        S.stageCoconeFunctor i := by
    exact S.stageCoconeFunctor_comp_eq A.unop.hom
  have hobj :
      (S.stageCoconeFunctor A.unop.left).obj (S.overImage X A) =
        (S.stageCoconeFunctor i).obj X := by
    simpa [CofilteredSiteDiagram.overImage] using
      congrArg
        (fun F : S.stage i ⥤ S.ColimitCategory ↦ F.obj X)
        hcomp
  simpa [pulledBackSectionDiagram] using
    congrArg
      (fun Y ↦
        ((((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
              (S.stageTopology A.unop.left) S.colimitTopology).obj
          (family.obj A.unop.left)).obj.obj)
          (op Y))
      hobj

/-- Helper for Lemma 7.18.4: the conjugate of the colimit-stage pullback comparison is the
inverse cocone-side pushforward comparison. -/
theorem colimit_stage_pullback_comp_conjugate_hom'
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)] {i j : S.I} (a : j ⟶ i) :
    conjugateEquiv
        ((S.stageCoconeFunctor i).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) S.colimitTopology)
        (((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageCoconeFunctor j).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) S.colimitTopology))
        ((S.colimitStageSheafPullbackCompIso (Type u) a).hom) =
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq a))
        (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- Helper for Lemma 7.18.4: the sheaf-level naturality of the unit comparison against the stage
transitions. -/
theorem sourceToPulledBack_natural_sheaf
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {j k : S.I} (p : k ⟶ j) :
    (((S.stageFunctor p).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)).homEquiv
      (family.obj j) (family.obj k)) (family.transition p) ≫
      ((S.stageFunctor p).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)).map
        (((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
          (S.stageTopology k) S.colimitTopology).unit.app (family.obj k)) ≫
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq p))
        (Type u) (S.stageTopology j) (S.stageTopology k) S.colimitTopology).hom.app
        (((S.stageCoconeFunctor k).sheafPullback (Type u)
          (S.stageTopology k) S.colimitTopology).obj (family.obj k)) =
      ((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).unit.app (family.obj j) ≫
      ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).map
        (transitionOnColimit family p) := by
  set K := (Functor.sheafPushforwardContinuousComp'
    (eqToIso (S.stageCoconeFunctor_comp_eq p))
    (Type u) (S.stageTopology j) (S.stageTopology k) S.colimitTopology) with hK
  have hRHS : ((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) S.colimitTopology).unit.app (family.obj j) ≫
      ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).map (transitionOnColimit family p) =
      (((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).homEquiv
        (family.obj j)
        (((S.stageCoconeFunctor k).sheafPullback (Type u)
          (S.stageTopology k) S.colimitTopology).obj (family.obj k)))
        (transitionOnColimit family p) := by
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [hRHS]
  have hunitB : ((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
      (S.stageTopology k) S.colimitTopology).unit.app (family.obj k) =
      (((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) S.colimitTopology).homEquiv
        (family.obj k)
        (((S.stageCoconeFunctor k).sheafPullback (Type u)
          (S.stageTopology k) S.colimitTopology).obj (family.obj k)))
        (𝟙 _) :=
    (Adjunction.homEquiv_id _ _).symm
  rw [hunitB]
  have hex := homEquiv_conjugateEquiv_exchange'
    ((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) S.colimitTopology)
    (((S.stageFunctor p).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)).comp
      ((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) S.colimitTopology))
    ((S.colimitStageSheafPullbackCompIso (Type u) p).hom)
    (transitionOnColimit family p)
  rw [colimit_stage_pullback_comp_conjugate_hom'] at hex
  have hcancel := congrArg (fun t => t ≫ K.hom.app
    (((S.stageCoconeFunctor k).sheafPullback (Type u)
      (S.stageTopology k) S.colimitTopology).obj (family.obj k))) hex
  simp only [hK, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hcancel
  refine Eq.trans ?_ hcancel
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine congrArg (fun t => t ≫ K.hom.app
    (((S.stageCoconeFunctor k).sheafPullback (Type u)
      (S.stageTopology k) S.colimitTopology).obj (family.obj k))) ?_
  refine Eq.symm ?_
  have h4 : (S.colimitStageSheafPullbackCompIso (Type u) p).hom.app (family.obj j) ≫
      transitionOnColimit family p =
      ((S.stageCoconeFunctor k).sheafPullback (Type u)
        (S.stageTopology k) S.colimitTopology).map (family.transition p) := by
    rw [transitionOnColimit, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  refine Eq.trans (congrArg (fun t =>
    ((((S.stageFunctor p).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)).comp
      ((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) S.colimitTopology)).homEquiv
      (family.obj j)
      (((S.stageCoconeFunctor k).sheafPullback (Type u)
        (S.stageTopology k) S.colimitTopology).obj (family.obj k))) t) h4) ?_
  have h3 : ∀ γ : ((S.stageFunctor p).sheafPullback (Type u)
        (S.stageTopology j) (S.stageTopology k) ⋙
      (S.stageCoconeFunctor k).sheafPullback (Type u)
        (S.stageTopology k) S.colimitTopology).obj (family.obj j) ⟶
      ((S.stageCoconeFunctor k).sheafPullback (Type u)
        (S.stageTopology k) S.colimitTopology).obj (family.obj k),
      ((((S.stageFunctor p).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)).comp
        ((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
          (S.stageTopology k) S.colimitTopology)).homEquiv
        (family.obj j)
        (((S.stageCoconeFunctor k).sheafPullback (Type u)
          (S.stageTopology k) S.colimitTopology).obj (family.obj k))) γ =
      ((((S.stageFunctor p).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k))).homEquiv _ _)
        (((((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
          (S.stageTopology k) S.colimitTopology)).homEquiv _ _) γ) := by
    intro γ
    rw [Adjunction.comp_homEquiv]
    rfl
  refine Eq.trans (h3 _) ?_
  have h5 : ((((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
      (S.stageTopology k) S.colimitTopology)).homEquiv _ _)
      (((S.stageCoconeFunctor k).sheafPullback (Type u)
        (S.stageTopology k) S.colimitTopology).map (family.transition p)) =
      family.transition p ≫
      ((((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) S.colimitTopology)).homEquiv _ _) (𝟙 _) := by
    refine Eq.trans (congrArg (fun t =>
      ((((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) S.colimitTopology)).homEquiv _ _) t)
      (Category.comp_id _).symm) ?_
    exact Adjunction.homEquiv_naturality_left _ _ _
  refine Eq.trans (congrArg (fun t =>
    ((((S.stageFunctor p).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k))).homEquiv _ _) t) h5) ?_
  exact Adjunction.homEquiv_naturality_right _ _ _

noncomputable def sourceToPulledBack
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    sectionDiagram family X ⟶ pulledBackSectionDiagram family X where
  app A :=
    (((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).unit.app
        (family.obj A.unop.left)).1.app
        (op (S.overImage X A)) ≫
      eqToHom (sourceToPulledBackTarget_eq family X A)
  naturality := by
    intro A B u
    have hnat := sourceToPulledBack_natural_sheaf family u.unop.left
    have hobj : (S.stageFunctor u.unop.left).obj (S.overImage X A) = S.overImage X B := by
      have hcomp :
          S.stageFunctor A.unop.hom ⋙ S.stageFunctor u.unop.left =
            S.stageFunctor (u.unop.left ≫ A.unop.hom) :=
        congrArg Cat.Hom.toFunctor
          (S.diagram.map_comp A.unop.hom.op u.unop.left.op).symm
      have h₁ : (S.stageFunctor u.unop.left).obj (S.overImage X A) =
          (S.stageFunctor (u.unop.left ≫ A.unop.hom)).obj X := by
        simpa [CofilteredSiteDiagram.overImage] using
          congrArg (fun F : S.stage i ⥤ S.stage B.unop.left ↦ F.obj X) hcomp
      have hw : u.unop.left ≫ A.unop.hom = B.unop.hom := by simpa using Over.w u.unop
      have h₂ : (S.stageFunctor (u.unop.left ≫ A.unop.hom)).obj X = S.overImage X B := by
        simpa [CofilteredSiteDiagram.overImage] using
          congrArg (fun a : B.unop.left ⟶ i ↦ (S.stageFunctor a).obj X) hw
      exact h₁.trans h₂
    have hobjA : (S.stageCoconeFunctor A.unop.left).obj (S.overImage X A) =
        (S.stageCoconeFunctor i).obj X := by
      simpa [CofilteredSiteDiagram.overImage] using
        congrArg (fun F : S.stage i ⥤ S.ColimitCategory ↦ F.obj X)
          (S.stageCoconeFunctor_comp_eq A.unop.hom)
    funext s
    set tu := (((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
      (family.obj A.unop.left) (family.obj B.unop.left))
      (family.transition u.unop.left) with htu
    set unitB := ((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology B.unop.left) S.colimitTopology).unit.app
      (family.obj B.unop.left) with hunitB
    set unitA := ((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) S.colimitTopology).unit.app
      (family.obj A.unop.left) with hunitA
    set tOC := transitionOnColimit family u.unop.left with htOC
    set y := tu.1.app (op (S.overImage X A)) s with hy
    change eqToHom (sourceToPulledBackTarget_eq family X B)
      (unitB.1.app (op (S.overImage X B))
        (eqToHom (sectionMap_target_eq family X u) y)) =
      tOC.1.app (op ((S.stageCoconeFunctor i).obj X))
        (eqToHom (sourceToPulledBackTarget_eq family X A)
          (unitA.1.app (op (S.overImage X A)) s))
    -- cast data
    have h₁ : ((family.obj B.unop.left).obj.obj
        (op ((S.stageFunctor u.unop.left).obj (S.overImage X A)))) =
        ((family.obj B.unop.left).obj.obj (op (S.overImage X B))) :=
      congrArg (fun Z => (family.obj B.unop.left).obj.obj (op Z)) hobj
    have h₂ : ((((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).obj
          (family.obj B.unop.left))).obj.obj (op (S.overImage X B))) =
        ((((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).obj
          (family.obj B.unop.left))).obj.obj
        (op ((S.stageFunctor u.unop.left).obj (S.overImage X A)))) :=
      congrArg (fun Z => (((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous
        (Type u) (S.stageTopology B.unop.left) S.colimitTopology).obj
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).obj
          (family.obj B.unop.left))).obj.obj (op Z)) hobj.symm
    have hcongrU : unitB.1.app
        (op ((S.stageFunctor u.unop.left).obj (S.overImage X A))) =
        eqToHom h₁ ≫ unitB.1.app (op (S.overImage X B)) ≫ eqToHom h₂ := by
      have := NatTrans.congr unitB.1 (congrArg op hobj)
      simpa [eqToHom_map] using this
    have hKty : ((((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).obj
          (family.obj B.unop.left))).obj.obj
        (op ((S.stageFunctor u.unop.left).obj (S.overImage X A)))) =
        ((((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).obj
          (family.obj B.unop.left))).obj.obj (op (S.overImage X A))) := by
      simpa using congrArg
        (fun G : S.stage A.unop.left ⥤ S.ColimitCategory =>
          ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
            (S.stageTopology B.unop.left) S.colimitTopology).obj
            (family.obj B.unop.left))).obj.obj (op (G.obj (S.overImage X A))))
        (S.stageCoconeFunctor_comp_eq u.unop.left)
    have hKcast : ∀ z, (((Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq u.unop.left))
        (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
        S.colimitTopology).hom.app
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).obj
          (family.obj B.unop.left))).1.app (op (S.overImage X A))) z =
        eqToHom hKty z := by
      intro z
      simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
        Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
        CategoryTheory.eqToHom_map, eqToHom_app]
    have hpb : ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj
        (op ((S.stageCoconeFunctor A.unop.left).obj (S.overImage X A)))) =
        ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op ((S.stageCoconeFunctor i).obj X))) :=
      congrArg (fun Z => (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op Z)) hobjA
    have h₃ : ((((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj.obj
        (op ((S.stageCoconeFunctor A.unop.left).obj (S.overImage X A)))) =
        ((((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj.obj (op ((S.stageCoconeFunctor i).obj X))) :=
      congrArg (fun Z => (((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj.obj (op Z)) hobjA
    have h₄ : ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op ((S.stageCoconeFunctor i).obj X))) =
        ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj
        (op ((S.stageCoconeFunctor A.unop.left).obj (S.overImage X A)))) :=
      congrArg (fun Z => (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op Z)) hobjA.symm
    have hcongrT : tOC.1.app (op ((S.stageCoconeFunctor A.unop.left).obj
        (S.overImage X A))) =
        eqToHom h₃ ≫ tOC.1.app (op ((S.stageCoconeFunctor i).obj X)) ≫ eqToHom h₄ := by
      have := NatTrans.congr tOC.1 (congrArg op hobjA)
      simpa [eqToHom_map] using this
    -- assemble
    refine Eq.trans ((eqToHom_apply_collapse₃₁' h₂ hKty hpb
        (sourceToPulledBackTarget_eq family X B)
        (unitB.1.app (op (S.overImage X B))
          (eqToHom (sectionMap_target_eq family X u) y))).symm) ?_
    refine Eq.trans (congrArg (fun t => eqToHom hpb (eqToHom hKty (eqToHom h₂
        (unitB.1.app (op (S.overImage X B)) t))))
      (eqToHom_apply_irrel' (sectionMap_target_eq family X u) h₁ y)) ?_
    refine Eq.trans (congrArg (fun t => eqToHom hpb (eqToHom hKty t))
      (congrFun hcongrU y).symm) ?_
    refine Eq.trans (congrArg (fun t => eqToHom hpb t)
      (hKcast (unitB.1.app
        (op ((S.stageFunctor u.unop.left).obj (S.overImage X A))) y)).symm) ?_
    refine Eq.trans (congrArg (fun t => eqToHom hpb (t.1.app (op (S.overImage X A)) s))
      hnat) ?_
    refine Eq.trans (congrArg (fun t => eqToHom hpb t)
      (congrFun hcongrT (unitA.1.app (op (S.overImage X A)) s))) ?_
    refine Eq.trans (eqToHom_apply_collapse₂₀' h₄ hpb
      (tOC.1.app (op ((S.stageCoconeFunctor i).obj X))
        (eqToHom h₃ (unitA.1.app (op (S.overImage X A)) s)))) ?_
    exact congrArg (fun t => tOC.1.app (op ((S.stageCoconeFunctor i).obj X)) t)
      (eqToHom_apply_irrel' h₃ (sourceToPulledBackTarget_eq family X A)
        (unitA.1.app (op (S.overImage X A)) s))

noncomputable abbrev globalSectionDiagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
  (family : ColimitSiteStageFamily S)
  {i : S.I} (X : S.stage i) :
  S.Iᵒᵖ ⥤ Type u :=
  family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u) ⋙
    (evaluation _ (Type u)).obj (op ((S.stageCoconeFunctor i).obj X))

/-- Helper for Lemma 7.18.4: the colimit restriction intertwines the colimit-site transition
with the family transition through the stage unit. Both sides transpose to the family
transition pullback under the cocone adjunction. -/
theorem colimitRestriction_comp_transitionOnColimit
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i j : S.I} (d : j ⟶ i) :
    colimitRestriction S (family.obj i) d ≫
      ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).map (transitionOnColimit family d) =
    family.transition d ≫
      ((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).unit.app (family.obj j) := by
  apply Equiv.injective (((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
    (S.stageTopology j) S.colimitTopology).homEquiv _ _).symm
  refine Eq.trans (Adjunction.homEquiv_naturality_right_symm _ _ _) (Eq.trans ?_
    (Adjunction.homEquiv_naturality_left_symm _ _ _).symm)
  rw [show (((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) S.colimitTopology).homEquiv _ _).symm
      (colimitRestriction S (family.obj i) d) =
      (S.colimitStageSheafPullbackCompIso (Type u) d).hom.app (family.obj i) from
    Equiv.symm_apply_apply _ _]
  rw [Adjunction.homEquiv_symm_apply, Adjunction.left_triangle_components,
    Category.comp_id, transitionOnColimit, ← Category.assoc]
  have hci : (S.colimitStageSheafPullbackCompIso (Type u) d).hom.app (family.obj i) ≫
      (S.colimitStageSheafPullbackCompIso (Type u) d).inv.app (family.obj i) = 𝟙 _ := by
    rw [← NatTrans.comp_app, Iso.hom_inv_id]
    rfl
  exact (congrArg (fun z => z ≫ ((S.stageCoconeFunctor j).sheafPullback (Type u)
    (S.stageTopology j) S.colimitTopology).map (family.transition d)) hci).trans
    (Category.id_comp _)

/-- Helper for Lemma 7.18.4: pointwise form of the transition square on the representative
comparison. The colimit-site transition carries the comparison value of a stage pullback
section to the unit value of its family-transition image. -/
theorem transitionOnColimit_auxiliaryToPullback₀
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i j : S.I} (d : j ⟶ i) {V : S.ColimitCategory}
    (W : S.stage j) (hW : S.ιObj j W = V)
    (ω : ((stageSheafPullbackAlong S d).obj (family.obj i)).obj.obj (op W)) :
    (transitionOnColimit family d).1.app (op V)
        (auxiliaryToPullback₀ S (family.obj i)
          (⟨j, d, W, hW, ω⟩ : GRep S (family.obj i) V)) =
      ((((S.stageCoconeFunctor j).sheafPullback (Type u)
          (S.stageTopology j) S.colimitTopology).obj (family.obj j)).obj.map
          (eqToHom hW.symm).op)
        (((((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
            (S.stageTopology j) S.colimitTopology).unit.app (family.obj j)).1.app (op W))
          (((family.transition d).1.app (op W)) ω)) := by
  have hnat := congrFun ((transitionOnColimit family d).1.naturality
    (eqToHom hW.symm).op) (((colimitRestriction S (family.obj i) d).1.app (op W)) ω)
  have hcore := congrFun (congrArg (fun t => t.1.app (op W))
    (colimitRestriction_comp_transitionOnColimit family d)) ω
  exact hnat.trans (congrArg ((((S.stageCoconeFunctor j).sheafPullback (Type u)
    (S.stageTopology j) S.colimitTopology).obj (family.obj j)).obj.map
    (eqToHom hW.symm).op) hcore)

/-- Helper for Lemma 7.18.4: the colimit map induced by `sourceToPulledBack` is the formal
outer-colimit version of the source proof's first equality. -/
theorem sourceToPulledBack_colimMap_bijective
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    Function.Bijective (colimMap (family.sourceToPulledBack X)) := by
  -- Source-faithful route through the auxiliary-sheaf machinery of Lemma `7.18.3`: the unit
  -- components are identified with the tautological auxiliary classes (first triangle), the
  -- colimit-site transitions act on representative comparisons through the family transition
  -- (the transition square above), and both directions reduce to stage-level descent.
  constructor
  · intro z₁ z₂ hz
    obtain ⟨A₁, x₁, rfl⟩ := Types.jointly_surjective' (F := sectionDiagram family X) z₁
    obtain ⟨A₂, x₂, rfl⟩ := Types.jointly_surjective' (F := sectionDiagram family X) z₂
    have hz' : colimit.ι (pulledBackSectionDiagram family X) A₁
        ((family.sourceToPulledBack X).app A₁ x₁) =
        colimit.ι (pulledBackSectionDiagram family X) A₂
        ((family.sourceToPulledBack X).app A₂ x₂) :=
      (congrFun (ι_colimMap (family.sourceToPulledBack X) A₁) x₁).symm.trans
        (hz.trans (congrFun (ι_colimMap (family.sourceToPulledBack X) A₂) x₂))
    obtain ⟨A₃, u₁, u₂, h₃⟩ :=
      (Types.FilteredColimit.colimit_eq_iff (pulledBackSectionDiagram family X)).1 hz'
    have hy : (family.sourceToPulledBack X).app A₃ ((sectionDiagram family X).map u₁ x₁) =
        (family.sourceToPulledBack X).app A₃ ((sectionDiagram family X).map u₂ x₂) :=
      (congrFun ((family.sourceToPulledBack X).naturality u₁) x₁).trans
        (h₃.trans (congrFun ((family.sourceToPulledBack X).naturality u₂) x₂).symm)
    have hunit : (((S.stageCoconeFunctor A₃.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A₃.unop.left) S.colimitTopology).unit.app
          (family.obj A₃.unop.left)).1.app (op (S.overImage X A₃))
          ((sectionDiagram family X).map u₁ x₁) =
        (((S.stageCoconeFunctor A₃.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A₃.unop.left) S.colimitTopology).unit.app
          (family.obj A₃.unop.left)).1.app (op (S.overImage X A₃))
          ((sectionDiagram family X).map u₂ x₂) :=
      (eqToHom_apply_collapse₂₀' (sourceToPulledBackTarget_eq family X A₃)
        (sourceToPulledBackTarget_eq family X A₃).symm
        ((((S.stageCoconeFunctor A₃.unop.left).sheafAdjunctionContinuous (Type u)
          (S.stageTopology A₃.unop.left) S.colimitTopology).unit.app
          (family.obj A₃.unop.left)).1.app (op (S.overImage X A₃))
          ((sectionDiagram family X).map u₁ x₁))).symm.trans
        ((congrArg (eqToHom (sourceToPulledBackTarget_eq family X A₃).symm) hy).trans
          (eqToHom_apply_collapse₂₀' (sourceToPulledBackTarget_eq family X A₃)
            (sourceToPulledBackTarget_eq family X A₃).symm
            ((((S.stageCoconeFunctor A₃.unop.left).sheafAdjunctionContinuous (Type u)
              (S.stageTopology A₃.unop.left) S.colimitTopology).unit.app
              (family.obj A₃.unop.left)).1.app (op (S.overImage X A₃))
              ((sectionDiagram family X).map u₂ x₂))))
    have hcls : GSec.mk (⟨A₃.unop.left, 𝟙 A₃.unop.left, S.overImage X A₃, rfl,
          (((stagePullbackIdIso A₃.unop.left).inv.app (family.obj A₃.unop.left)).1.app
            (op (S.overImage X A₃))) ((sectionDiagram family X).map u₁ x₁)⟩ :
          GRep S (family.obj A₃.unop.left) (S.ιObj A₃.unop.left (S.overImage X A₃))) =
        GSec.mk (⟨A₃.unop.left, 𝟙 A₃.unop.left, S.overImage X A₃, rfl,
          (((stagePullbackIdIso A₃.unop.left).inv.app (family.obj A₃.unop.left)).1.app
            (op (S.overImage X A₃))) ((sectionDiagram family X).map u₂ x₂)⟩ :
          GRep S (family.obj A₃.unop.left) (S.ιObj A₃.unop.left (S.overImage X A₃))) := by
      apply (auxiliaryToPullbackApp_bijective S (family.obj A₃.unop.left)
        (S.ιObj A₃.unop.left (S.overImage X A₃))).injective
      have ht1 := congrFun (congrArg (fun t => t.1.app (op (S.overImage X A₃)))
        (auxiliaryUnit_comp_toPullback S (family.obj A₃.unop.left)))
      exact (ht1 _).trans (hunit.trans (ht1 _).symm)
    obtain ⟨k, b₁, b₂, ha, hw, hs⟩ := GSec.mk_eq_mk.1 hcls
    have hb : b₁ = b₂ := by simpa using ha
    subst hb
    -- the lowered sections are the stage unit values, by the identity-restriction evaluation
    have hkre₁ := stageRestriction_id_comp_eval S b₁ (family.obj A₃.unop.left)
      (S.overImage X A₃)
      (gsec_type_congr (family.obj A₃.unop.left) (Category.comp_id b₁).symm rfl)
      ((sectionDiagram family X).map u₁ x₁)
    have hkre₂ := stageRestriction_id_comp_eval S b₁ (family.obj A₃.unop.left)
      (S.overImage X A₃)
      (gsec_type_congr (family.obj A₃.unop.left) (Category.comp_id b₁).symm rfl)
      ((sectionDiagram family X).map u₂ x₂)
    have hunitb : ((((S.stageFunctor b₁).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A₃.unop.left) (S.stageTopology k)).unit.app
          (family.obj A₃.unop.left)).1.app (op (S.overImage X A₃)))
          ((sectionDiagram family X).map u₁ x₁) =
        ((((S.stageFunctor b₁).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A₃.unop.left) (S.stageTopology k)).unit.app
          (family.obj A₃.unop.left)).1.app (op (S.overImage X A₃)))
          ((sectionDiagram family X).map u₂ x₂) := by
      have hs2 : eqToHom (gsec_type_congr (family.obj A₃.unop.left) ha hw)
          (eqToHom (gsec_type_congr (family.obj A₃.unop.left)
            (Category.comp_id b₁).symm rfl)
            (((((S.stageFunctor b₁).sheafAdjunctionContinuous (Type u)
              (S.stageTopology A₃.unop.left) (S.stageTopology k)).unit.app
              (family.obj A₃.unop.left)).1.app (op (S.overImage X A₃)))
              ((sectionDiagram family X).map u₁ x₁))) =
          eqToHom (gsec_type_congr (family.obj A₃.unop.left)
            (Category.comp_id b₁).symm rfl)
            (((((S.stageFunctor b₁).sheafAdjunctionContinuous (Type u)
              (S.stageTopology A₃.unop.left) (S.stageTopology k)).unit.app
              (family.obj A₃.unop.left)).1.app (op (S.overImage X A₃)))
              ((sectionDiagram family X).map u₂ x₂)) :=
        (congrArg (eqToHom (gsec_type_congr (family.obj A₃.unop.left) ha hw))
          hkre₁).symm.trans (hs.trans hkre₂)
      have hs3 := congrArg (eqToHom (gsec_type_congr (family.obj A₃.unop.left)
        (Category.comp_id b₁).symm rfl).symm) hs2
      exact (eqToHom_apply_collapse₃₁'
        (gsec_type_congr (family.obj A₃.unop.left) (Category.comp_id b₁).symm rfl)
        (gsec_type_congr (family.obj A₃.unop.left) ha hw)
        (gsec_type_congr (family.obj A₃.unop.left)
          (Category.comp_id b₁).symm rfl).symm rfl _).symm.trans
        (hs3.trans (eqToHom_apply_collapse₂₀'
          (gsec_type_congr (family.obj A₃.unop.left) (Category.comp_id b₁).symm rfl)
          (gsec_type_congr (family.obj A₃.unop.left)
            (Category.comp_id b₁).symm rfl).symm _))
    -- transport the agreement through the family transition to the merged over-object
    have hmaps : (sectionDiagram family X).map
          ((Over.homMk b₁ rfl : Over.mk (b₁ ≫ A₃.unop.hom) ⟶ A₃.unop).op)
          ((sectionDiagram family X).map u₁ x₁) =
        (sectionDiagram family X).map
          ((Over.homMk b₁ rfl : Over.mk (b₁ ≫ A₃.unop.hom) ⟶ A₃.unop).op)
          ((sectionDiagram family X).map u₂ x₂) :=
      congrArg (fun t => eqToHom (sectionMap_target_eq family X
          ((Over.homMk b₁ rfl : Over.mk (b₁ ≫ A₃.unop.hom) ⟶ A₃.unop).op))
        (((family.transition b₁).1.app
          (op ((S.stageFunctor b₁).obj (S.overImage X A₃)))) t)) hunitb
    calc colimit.ι (sectionDiagram family X) A₁ x₁
        = colimit.ι (sectionDiagram family X) A₃ ((sectionDiagram family X).map u₁ x₁) :=
          (congrFun (colimit.w (sectionDiagram family X) u₁) x₁).symm
      _ = colimit.ι (sectionDiagram family X) (op (Over.mk (b₁ ≫ A₃.unop.hom)))
            ((sectionDiagram family X).map
              ((Over.homMk b₁ rfl : Over.mk (b₁ ≫ A₃.unop.hom) ⟶ A₃.unop).op)
              ((sectionDiagram family X).map u₁ x₁)) :=
          (congrFun (colimit.w (sectionDiagram family X)
            ((Over.homMk b₁ rfl : Over.mk (b₁ ≫ A₃.unop.hom) ⟶ A₃.unop).op))
            ((sectionDiagram family X).map u₁ x₁)).symm
      _ = colimit.ι (sectionDiagram family X) (op (Over.mk (b₁ ≫ A₃.unop.hom)))
            ((sectionDiagram family X).map
              ((Over.homMk b₁ rfl : Over.mk (b₁ ≫ A₃.unop.hom) ⟶ A₃.unop).op)
              ((sectionDiagram family X).map u₂ x₂)) :=
          congrArg (colimit.ι (sectionDiagram family X)
            (op (Over.mk (b₁ ≫ A₃.unop.hom)))) hmaps
      _ = colimit.ι (sectionDiagram family X) A₃ ((sectionDiagram family X).map u₂ x₂) :=
          congrFun (colimit.w (sectionDiagram family X)
            ((Over.homMk b₁ rfl : Over.mk (b₁ ≫ A₃.unop.hom) ⟶ A₃.unop).op))
            ((sectionDiagram family X).map u₂ x₂)
      _ = colimit.ι (sectionDiagram family X) A₂ x₂ :=
          congrFun (colimit.w (sectionDiagram family X) u₂) x₂
  · intro w
    obtain ⟨A, y, rfl⟩ := Types.jointly_surjective' (F := pulledBackSectionDiagram family X) w
    -- present the transported section by an auxiliary class and an inner colimit element
    have hV : S.ιObj A.unop.left (S.overImage X A) = S.ιObj i X :=
      S.ιObj_lower A.unop.hom X
    have hsV : (((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj.obj (op (S.ιObj i X)) =
        (((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj.obj (op (S.ιObj A.unop.left (S.overImage X A))) :=
      congrArg (fun Z => (((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj.obj (op Z)) hV.symm
    obtain ⟨cls, hcls⟩ := (auxiliaryToPullbackApp_bijective S (family.obj A.unop.left)
      (S.ιObj A.unop.left (S.overImage X A))).surjective (eqToHom hsV y)
    obtain ⟨ζ, hζ⟩ := auxiliaryClassMap_surjective S (family.obj A.unop.left)
      (S.overImage X A) cls
    obtain ⟨B, ω, rfl⟩ := Types.jointly_surjective'
      (F := colimitSiteStagePullbackSectionDiagram S (family.obj A.unop.left)
        (S.overImage X A)) ζ
    rw [auxiliaryClassMap_ι] at hζ
    -- the representative comparison computes the transported section
    have hκ : auxiliaryToPullback₀ S (family.obj A.unop.left)
        (⟨B.unop.left, B.unop.hom, S.overImage (S.overImage X A) B,
          S.ιObj_lower B.unop.hom (S.overImage X A), ω⟩ :
          GRep S (family.obj A.unop.left) (S.ιObj A.unop.left (S.overImage X A))) =
        eqToHom hsV y :=
      (congrArg (auxiliaryToPullbackApp S (family.obj A.unop.left)
        (S.ιObj A.unop.left (S.overImage X A))) hζ).trans hcls
    -- the transition square evaluation
    have hT := transitionOnColimit_auxiliaryToPullback₀ family B.unop.hom
      (S.overImage (S.overImage X A) B) (S.ιObj_lower B.unop.hom (S.overImage X A)) ω
    -- the candidate stage section at the composite over-object
    have hWobj : S.overImage (S.overImage X A) B =
        S.overImage X (op (Over.mk (B.unop.hom ≫ A.unop.hom))) := by
      simpa [CofilteredSiteDiagram.overImage] using
        S.stageFunctor_obj_comp A.unop.hom B.unop.hom X
    have hsec' : (family.obj B.unop.left).obj.obj
        (op (S.overImage (S.overImage X A) B)) =
        sectionValue family X (op (Over.mk (B.unop.hom ≫ A.unop.hom))) :=
      congrArg (fun Z => (family.obj B.unop.left).obj.obj (op Z)) hWobj
    refine ⟨colimit.ι (sectionDiagram family X) (op (Over.mk (B.unop.hom ≫ A.unop.hom)))
      (eqToHom hsec' (((family.transition B.unop.hom).1.app
        (op (S.overImage (S.overImage X A) B))) ω)), ?_⟩
    refine (congrFun (ι_colimMap (family.sourceToPulledBack X)
      (op (Over.mk (B.unop.hom ≫ A.unop.hom))))
      (eqToHom hsec' (((family.transition B.unop.hom).1.app
        (op (S.overImage (S.overImage X A) B))) ω))).trans ?_
    refine Eq.trans (congrArg (colimit.ι (pulledBackSectionDiagram family X)
      (op (Over.mk (B.unop.hom ≫ A.unop.hom)))) ?_)
      (congrFun (colimit.w (pulledBackSectionDiagram family X)
        ((Over.homMk B.unop.hom rfl :
          Over.mk (B.unop.hom ≫ A.unop.hom) ⟶ A.unop).op)) y)
    -- MAIN VALUE EQUATION: both sides are transports of the stage unit value of the
    -- family-transition image of `ω`.
    -- Right side: unfold `y` through the representative comparison and the transition square.
    have hy2 : eqToHom hsV.symm (auxiliaryToPullback₀ S (family.obj A.unop.left)
        (⟨B.unop.left, B.unop.hom, S.overImage (S.overImage X A) B,
          S.ιObj_lower B.unop.hom (S.overImage X A), ω⟩ :
          GRep S (family.obj A.unop.left) (S.ιObj A.unop.left (S.overImage X A)))) = y :=
      (congrArg (eqToHom hsV.symm) hκ).trans (eqToHom_apply_collapse₂₀' hsV hsV.symm y)
    have hp3 := presheaf_map_eqToHom_op_eval
      ((((S.stageCoconeFunctor A.unop.left).sheafPullback (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (family.obj A.unop.left)).obj) hV.symm hsV.symm
      (auxiliaryToPullback₀ S (family.obj A.unop.left)
        (⟨B.unop.left, B.unop.hom, S.overImage (S.overImage X A) B,
          S.ιObj_lower B.unop.hom (S.overImage X A), ω⟩ :
          GRep S (family.obj A.unop.left) (S.ιObj A.unop.left (S.overImage X A))))
    have hnatT := congrFun ((transitionOnColimit family B.unop.hom).1.naturality
      (eqToHom hV.symm).op)
      (auxiliaryToPullback₀ S (family.obj A.unop.left)
        (⟨B.unop.left, B.unop.hom, S.overImage (S.overImage X A) B,
          S.ιObj_lower B.unop.hom (S.overImage X A), ω⟩ :
          GRep S (family.obj A.unop.left) (S.ιObj A.unop.left (S.overImage X A))))
    -- the two pullback casts on the right side, as plain section transports
    have hq₁ : (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj
        (op (S.ιObj B.unop.left (S.overImage (S.overImage X A) B))) =
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj
        (op (S.ιObj A.unop.left (S.overImage X A))) :=
      congrArg (fun Z => (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op Z))
        (S.ιObj_lower B.unop.hom (S.overImage X A))
    have hq₂ : (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj
        (op (S.ιObj A.unop.left (S.overImage X A))) =
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op (S.ιObj i X)) :=
      congrArg (fun Z => (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op Z)) hV
    have hQ : (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj
        (op (S.ιObj B.unop.left (S.overImage (S.overImage X A) B))) =
        (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op (S.ιObj i X)) :=
      hq₁.trans hq₂
    -- right side normal form
    have hrhs : (pulledBackSectionDiagram family X).map
        ((Over.homMk B.unop.hom rfl :
          Over.mk (B.unop.hom ≫ A.unop.hom) ⟶ A.unop).op) y =
        eqToHom hQ
          (((((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
            (S.stageTopology B.unop.left) S.colimitTopology).unit.app
            (family.obj B.unop.left)).1.app
            (op (S.overImage (S.overImage X A) B)))
            (((family.transition B.unop.hom).1.app
              (op (S.overImage (S.overImage X A) B))) ω)) := by
      refine Eq.trans (congrArg ((transitionOnColimit family B.unop.hom).1.app
        (op (S.ιObj i X))) (hy2.symm.trans hp3.symm)) ?_
      refine hnatT.trans ?_
      refine Eq.trans (congrArg ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.map (eqToHom hV.symm).op) hT) ?_
      refine Eq.trans (congrArg ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.map (eqToHom hV.symm).op)
        (presheaf_map_eqToHom_op_eval
          ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
            (S.stageTopology B.unop.left) S.colimitTopology).obj
            (family.obj B.unop.left)).obj)
          (S.ιObj_lower B.unop.hom (S.overImage X A)).symm hq₁ _)) ?_
      refine Eq.trans (presheaf_map_eqToHom_op_eval
        ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).obj
          (family.obj B.unop.left)).obj) hV.symm hq₂ _) ?_
      exact eqToHom_apply_collapse₃₁' rfl hq₁ hq₂ hQ _
    -- left side normal form
    have hpA := presheaf_map_eqToHom_op_eval (family.obj B.unop.left).obj hWobj.symm hsec'
      (((family.transition B.unop.hom).1.app
        (op (S.overImage (S.overImage X A) B))) ω)
    have hnatU := congrFun ((((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous
        (Type u) (S.stageTopology B.unop.left) S.colimitTopology).unit.app
        (family.obj B.unop.left)).1.naturality (eqToHom hWobj.symm).op)
      (((family.transition B.unop.hom).1.app
        (op (S.overImage (S.overImage X A) B))) ω)
    have hsecPP : ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology ⋙
        (S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op (S.overImage (S.overImage X A) B))) =
        ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology ⋙
        (S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj
        (op (S.overImage X (op (Over.mk (B.unop.hom ≫ A.unop.hom)))))) :=
      congrArg (fun Z => (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology ⋙
        (S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj.obj (op Z)) hWobj
    have hpPP := presheaf_map_eqToHom_op_eval
      ((((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology ⋙
        (S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        (family.obj B.unop.left)).obj) hWobj.symm hsecPP
      (((((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).unit.app
        (family.obj B.unop.left)).1.app
        (op (S.overImage (S.overImage X A) B)))
        (((family.transition B.unop.hom).1.app
          (op (S.overImage (S.overImage X A) B))) ω))
    refine Eq.trans (congrArg (fun z => eqToHom (sourceToPulledBackTarget_eq family X
        (op (Over.mk (B.unop.hom ≫ A.unop.hom))))
        (((((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).unit.app
          (family.obj B.unop.left)).1.app
          (op (S.overImage X (op (Over.mk (B.unop.hom ≫ A.unop.hom)))))) z))
      hpA.symm) ?_
    refine Eq.trans (congrArg (eqToHom (sourceToPulledBackTarget_eq family X
      (op (Over.mk (B.unop.hom ≫ A.unop.hom))))) hnatU) ?_
    refine Eq.trans (congrArg (eqToHom (sourceToPulledBackTarget_eq family X
      (op (Over.mk (B.unop.hom ≫ A.unop.hom))))) hpPP) ?_
    refine Eq.trans (eqToHom_apply_collapse₃₁' rfl hsecPP
      (sourceToPulledBackTarget_eq family X (op (Over.mk (B.unop.hom ≫ A.unop.hom)))) hQ _) ?_
    exact hrhs.symm

end ColimitSiteStageFamily

/-- Every object of the colimit site is quasi-compact: each covering sieve is refined by the
image of a finite stage covering family, by the refinement property of the generated topology
and the finiteness of the chosen stage coverings. -/
theorem colimitTopology_quasiCompactObject
    (S : CofilteredSiteDiagram.{u, u, u}) (x : S.ColimitCategory) :
    S.colimitTopology.QuasiCompactObject x := by
  intro Sv
  obtain ⟨R, hR, hle⟩ :=
    Precoverage.exists_mem_generate_le_of_mem_toGrothendieck Sv.condition
  have hmem : ∀ {Z : S.ColimitCategory} {g : Z ⟶ x}, R g → (Sv : Sieve x).arrows g :=
    fun {Z g} hg => hle _ ⟨Z, 𝟙 Z, g, hg, Category.id_comp g⟩
  obtain ⟨l, X', hX', R', hR', rfl⟩ := hR
  subst hX'
  haveI : Finite R'.uncurry :=
    ((Precoverage.mem_finite_iff).1 (S.stageCov_finite hR')).to_subtype
  have hmem' : ∀ ω : R'.uncurry, (Sv : Sieve (S.ιObj l X')).arrows
      ((S.stageCoconeFunctor l).map ω.1.2) := by
    intro ω
    refine hmem ?_
    rw [S.stageCover_rfl_eq_map]
    exact Presieve.map.of ω.2
  have hself : ∀ ω : R'.uncurry,
      (S.stageCover l X' rfl R') ((S.stageCoconeFunctor l).map ω.1.2) := by
    intro ω
    rw [S.stageCover_rfl_eq_map]
    exact Presieve.map.of ω.2
  -- Every sieve arrow carried by the image covering comes from an outer member datum.
  have hdecomp : ∀ A : Sv.Arrow, (S.stageCover l X' rfl R') A.f →
      ∃ ω : R'.uncurry,
        ({ Y := _, f := (S.stageCoconeFunctor l).map ω.1.2, hf := hmem' ω } : Sv.Arrow) = A := by
    rintro ⟨AY, Af, Ahf⟩ hA
    have hA' := hA
    rw [S.stageCover_rfl_eq_map] at hA'
    obtain ⟨W, g₀, hg₀, harr⟩ := map_apply_elim _ hA'
    have hY : AY = (S.stageCoconeFunctor l).obj W := congrArg Comma.left harr
    subst hY
    have hf : Af = (S.stageCoconeFunctor l).map g₀ := eq_of_arrowMk_eq harr
    subst hf
    exact ⟨⟨⟨W, g₀⟩, hg₀⟩, rfl⟩
  classical
  refine ⟨{A : Sv.Arrow | (S.stageCover l X' rfl R') A.f}, ?_, ?_⟩
  · -- finiteness via the surjection from the finite outer member data
    have hsurj : Function.Surjective (fun ω : R'.uncurry =>
        (⟨{ Y := _, f := (S.stageCoconeFunctor l).map ω.1.2, hf := hmem' ω }, hself ω⟩ :
          {A : Sv.Arrow | (S.stageCover l X' rfl R') A.f})) := by
      rintro ⟨A, hA⟩
      obtain ⟨ω, hω⟩ := hdecomp A hA
      exact ⟨ω, Subtype.ext hω⟩
    exact Set.finite_coe_iff.1 (Finite.of_surjective _ hsurj)
  · -- the generated sieve is the sieve generated by the image covering family
    have hpre : Presieve.ofArrows
        (fun I : {A : Sv.Arrow | (S.stageCover l X' rfl R') A.f} => I.1.Y)
        (fun I => I.1.f) = S.stageCover l X' rfl R' := by
      funext Z
      funext g
      apply propext
      constructor
      · rintro ⟨I⟩
        exact I.2
      · intro hg
        exact Presieve.ofArrows.mk
          (⟨{ Y := Z, f := g, hf := hmem hg }, hg⟩ :
            {A : Sv.Arrow | (S.stageCover l X' rfl R') A.f})
    rw [Sieve.ofArrows, hpre]
    exact Precoverage.generate_mem_toGrothendieck ⟨l, X', rfl, R', hR', rfl⟩

/-- Every stage image object in the colimit site satisfies the cofinal finite overlap hypothesis
needed for Lemma `7.17.7 (4)`. -/
theorem colimitSiteStage_hasCofinalFiniteQuasiCompactOverlapCoverings
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (X : S.stage i) :
    GrothendieckTopology.HasCofinalFiniteQuasiCompactOverlapCoverings S.colimitTopology
      ((S.stageCoconeFunctor i).obj X) := by
  constructor
  intro 𝒰 h𝒰
  obtain ⟨R, hR, hle⟩ := Precoverage.exists_mem_generate_le_of_mem_toGrothendieck h𝒰
  obtain ⟨l, X', hX', R', hR', rfl⟩ := hR
  have hRcov : S.stageCover l X' hX' R' ∈
      S.colimitSite.coverings ((S.stageCoconeFunctor i).obj X) := ⟨l, X', hX', R', hR', rfl⟩
  haveI : Finite R'.uncurry :=
    ((Precoverage.mem_finite_iff).1 (S.stageCov_finite hR')).to_subtype
  classical
  -- the image members of the refining stage covering, normalized to the target object
  have hself : ∀ ω : R'.uncurry, (S.stageCover l X' hX' R')
      ((S.stageCoconeFunctor l).map ω.1.2 ≫ eqToHom hX') := by
    intro ω
    rw [S.stageCover_apply_iff]
    refine mem_of_arrowMk_eq _ ?_ (Presieve.map.of ω.2)
    exact congrArg (fun u => Arrow.mk u)
      (comp_eqToHom_symm_comp_self hX'.symm ((S.stageCoconeFunctor l).map ω.1.2))
  have hsieve : ∀ ω : R'.uncurry, (𝒰.toSieve).arrows
      ((S.stageCoconeFunctor l).map ω.1.2 ≫ eqToHom hX') :=
    fun ω => hle _ ⟨_, 𝟙 _, _, hself ω, Category.id_comp _⟩
  have hofElim : ∀ {Z₀ : S.ColimitCategory} {g : Z₀ ⟶ (S.stageCoconeFunctor i).obj X},
      𝒰.toPresieve g → ∃ idx : 𝒰.index, Arrow.mk g = Arrow.mk (𝒰.obj idx).hom := by
    rintro Z₀ g ⟨idx⟩
    exact ⟨idx, rfl⟩
  -- choose factorizations of the image members through the original family
  have hfac : ∀ ω : R'.uncurry, ∃ (idx : 𝒰.index)
      (h₀ : (S.stageCoconeFunctor l).obj ω.1.1 ⟶ (𝒰.obj idx).left),
      h₀ ≫ (𝒰.obj idx).hom = (S.stageCoconeFunctor l).map ω.1.2 ≫ eqToHom hX' := by
    intro ω
    obtain ⟨Y₀, h₀, f₀, hf₀, hcomp⟩ := hsieve ω
    obtain ⟨idx, harr⟩ := hofElim hf₀
    obtain ⟨h1, h2, hconj⟩ := (arrowMk_eq_iff _ _).1 harr
    have hf₀2 : f₀ = eqToHom h1 ≫ (𝒰.obj idx).hom := by
      have hf₀3 : f₀ = eqToHom h1 ≫ (𝒰.obj idx).hom ≫ 𝟙 _ := hconj
      rw [Category.comp_id] at hf₀3
      exact hf₀3
    refine ⟨idx, h₀ ≫ eqToHom h1, ?_⟩
    calc (h₀ ≫ eqToHom h1) ≫ (𝒰.obj idx).hom
        = h₀ ≫ eqToHom h1 ≫ (𝒰.obj idx).hom := Category.assoc _ _ _
      _ = h₀ ≫ f₀ := congrArg (fun t => h₀ ≫ t) hf₀2.symm
      _ = (S.stageCoconeFunctor l).map ω.1.2 ≫ eqToHom hX' := hcomp
  choose idxF liftF hliftF using hfac
  refine ⟨SemiRepresentableFamily.Over.ofArrows
      (fun ω : R'.uncurry => (S.stageCoconeFunctor l).obj ω.1.1)
      (fun ω => (S.stageCoconeFunctor l).map ω.1.2 ≫ eqToHom hX'),
    inferInstanceAs (Finite R'.uncurry),
    ⟨idxF, fun ω => CategoryTheory.Over.homMk (liftF ω) (hliftF ω)⟩,
    ?_, ?_, ?_⟩
  · -- pairwise pullbacks: both members lie in a single colimit-site covering family
    constructor
    rintro Y Z f ⟨ω₁⟩ g ⟨ω₂⟩
    exact (S.colimitSite.hasPullbacks_of_mem _ hRcov).hasPullback (hself ω₁)
  · -- the refining family generates the same covering sieve as the stage covering image
    have hpre : (SemiRepresentableFamily.Over.ofArrows
        (fun ω : R'.uncurry => (S.stageCoconeFunctor l).obj ω.1.1)
        (fun ω => (S.stageCoconeFunctor l).map ω.1.2 ≫ eqToHom hX')).toPresieve =
        S.stageCover l X' hX' R' := by
      funext Z g
      apply propext
      constructor
      · rintro ⟨ω⟩
        exact hself ω
      · intro hg
        have hg' := hg
        rw [S.stageCover_apply_iff] at hg'
        obtain ⟨W, g₀, hg₀, harr⟩ := map_apply_elim _ hg'
        have hZ : Z = (S.stageCoconeFunctor l).obj W := congrArg Comma.left harr
        subst hZ
        have hg2 : g = (S.stageCoconeFunctor l).map g₀ ≫ eqToHom hX' := by
          rw [← eq_of_arrowMk_eq harr]
          exact (comp_eqToHom_symm_comp_self _ _).symm
        rw [hg2]
        exact Presieve.ofArrows.mk (⟨⟨W, g₀⟩, hg₀⟩ : R'.uncurry)
    have hsieveEq : (SemiRepresentableFamily.Over.ofArrows
        (fun ω : R'.uncurry => (S.stageCoconeFunctor l).obj ω.1.1)
        (fun ω => (S.stageCoconeFunctor l).map ω.1.2 ≫ eqToHom hX')).toSieve =
        Sieve.generate (S.stageCover l X' hX' R') := congrArg Sieve.generate hpre
    rw [hsieveEq]
    exact Precoverage.generate_mem_toGrothendieck hRcov
  · -- the pairwise overlaps are quasi-compact since every colimit-site object is
    intro ω₁ ω₂
    exact colimitTopology_quasiCompactObject S _

/-- Helper for Lemma 7.18.4: the finality reindexing factor in the comparison map is bijective
because it is an isomorphism. -/
theorem over_forget_colimitIso_bijective
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    Function.Bijective
      ((Functor.Final.colimitIso ((Over.forget i).op) (family.globalSectionDiagram X)).hom) := by
  -- Apply the inverse isomorphism to obtain injectivity and surjectivity of the forward map.
  constructor
  · intro x y hxy
    simpa using congrArg
      (Functor.Final.colimitIso ((Over.forget i).op) (family.globalSectionDiagram X)).inv hxy
  · intro y
    refine ⟨(Functor.Final.colimitIso ((Over.forget i).op) (family.globalSectionDiagram X)).inv y, ?_⟩
    simp

/-- Helper for Lemma 7.18.4: the evaluation/colimit comparison contributes a bijective factor
after taking the inverse isomorphism. -/
theorem colimitObjIsoColimitCompEvaluation_inv_bijective
    {S : CofilteredSiteDiagram.{u, u, u}}
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    Function.Bijective
      ((colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).inv) := by
  -- The inverse of an isomorphism is again a bijection on underlying section types.
  constructor
  · intro x y hxy
    simpa using congrArg
      ((colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).hom) hxy
  · intro y
    refine
      ⟨(colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).hom y, ?_⟩
    simp

-- Proof sketch: map the source-text diagram `a : j ⟶ i ↦ 𝒜_j(u_a(X))` into the restriction of
-- the private pulled-back colimit-site diagram along `(Over i)ᵒᵖ ⥤ S.Iᵒᵖ`, use finality of
-- `(Over.forget i).op` to pass from arrows into `i` to the ambient filtered index category, and
-- then apply Lemma `7.17.7 (4)` to that derived diagram.
/-- Lemma 7.18.4: let `S` be a cofiltered inverse system of sites with finite covering families.
For a compatible family of stage sheaves `family : ColimitSiteStageFamily S`, the canonical map
from the source colimit
`\operatorname{colim}_{a : j \to i} \mathcal A_j(u_a(X))`
over arrows into the fixed stage `i` to the sections of the colimit sheaf at `u_i(X)` is
bijective. In Lean the indexing category is `(Over i)ᵒᵖ`. -/
noncomputable def colimitSiteStageFamilySectionsComparison
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    colimit (family.sectionDiagram X) ⟶
      (family.colimitSheaf).obj.obj (op ((S.stageCoconeFunctor i).obj X)) :=
  colimMap (family.sourceToPulledBack X) ≫
    (Functor.Final.colimitIso ((Over.forget i).op) (family.globalSectionDiagram X)).hom ≫
      (colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).inv ≫
      ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
        (op ((S.stageCoconeFunctor i).obj X)))

/-- The section comparison map restricts on each colimit summand to the evaluated unit map
followed by the corresponding stage injection of the colimit sheaf. This public bridge lets later
items compute the comparison on a chosen leg without unfolding the private cocone data. -/
theorem colimitSiteStageFamilySectionsComparison_ι
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) :
    colimit.ι (family.sectionDiagram X) A ≫
      colimitSiteStageFamilySectionsComparison S family X =
    ((((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).unit.app
        (family.obj A.unop.left)).1.app
        (op (S.overImage X A)) ≫
      eqToHom (family.sourceToPulledBackTarget_eq X A)) ≫
      (((sheafToPresheaf S.colimitTopology (Type u)).map
        (colimit.ι family.diagram (op A.unop.left))).app
        (op ((S.stageCoconeFunctor i).obj X))) := by
  rw [colimitSiteStageFamilySectionsComparison]
  calc colimit.ι (family.sectionDiagram X) A ≫
      colimMap (family.sourceToPulledBack X) ≫
      (Functor.Final.colimitIso ((Over.forget i).op) (family.globalSectionDiagram X)).hom ≫
      (colimitObjIsoColimitCompEvaluation
        (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
        (op ((S.stageCoconeFunctor i).obj X))).inv ≫
      ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
        (op ((S.stageCoconeFunctor i).obj X)))
      = (colimit.ι (family.sectionDiagram X) A ≫
          colimMap (family.sourceToPulledBack X)) ≫
        (Functor.Final.colimitIso ((Over.forget i).op)
          (family.globalSectionDiagram X)).hom ≫
        (colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).inv ≫
        ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
          (op ((S.stageCoconeFunctor i).obj X))) := by
        rw [← Category.assoc]
    _ = ((family.sourceToPulledBack X).app A ≫
          colimit.ι (family.pulledBackSectionDiagram X) A) ≫
        (Functor.Final.colimitIso ((Over.forget i).op)
          (family.globalSectionDiagram X)).hom ≫
        (colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).inv ≫
        ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
          (op ((S.stageCoconeFunctor i).obj X))) := by
        rw [ι_colimMap]
    _ = (family.sourceToPulledBack X).app A ≫
        (colimit.ι (family.pulledBackSectionDiagram X) A ≫
          (Functor.Final.colimitIso ((Over.forget i).op)
            (family.globalSectionDiagram X)).hom) ≫
        (colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).inv ≫
        ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
          (op ((S.stageCoconeFunctor i).obj X))) := by
        simp only [Category.assoc]
    _ = (family.sourceToPulledBack X).app A ≫
        colimit.ι (family.globalSectionDiagram X) (op A.unop.left) ≫
        (colimitObjIsoColimitCompEvaluation
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op ((S.stageCoconeFunctor i).obj X))).inv ≫
        ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
          (op ((S.stageCoconeFunctor i).obj X))) := by
        rw [Functor.Final.ι_colimitIso_hom]
        rfl
    _ = (family.sourceToPulledBack X).app A ≫
        (colimit.ι (family.globalSectionDiagram X) (op A.unop.left) ≫
          (colimitObjIsoColimitCompEvaluation
            (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
            (op ((S.stageCoconeFunctor i).obj X))).inv) ≫
        ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
          (op ((S.stageCoconeFunctor i).obj X))) := by
        simp only [Category.assoc]
    _ = (family.sourceToPulledBack X).app A ≫
        ((colimit.ι (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op A.unop.left)).app (op ((S.stageCoconeFunctor i).obj X))) ≫
        ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
          (op ((S.stageCoconeFunctor i).obj X))) := by
        refine congrArg (fun t => (family.sourceToPulledBack X).app A ≫ t ≫
          ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
            (op ((S.stageCoconeFunctor i).obj X)))) ?_
        exact colimitObjIsoColimitCompEvaluation_ι_inv
          (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
          (op A.unop.left) (op ((S.stageCoconeFunctor i).obj X))
    _ = (family.sourceToPulledBack X).app A ≫
        (((sheafToPresheaf S.colimitTopology (Type u)).map
          (colimit.ι family.diagram (op A.unop.left))).app
          (op ((S.stageCoconeFunctor i).obj X))) := by
        refine congrArg (fun t => (family.sourceToPulledBack X).app A ≫ t) ?_
        exact congrFun (congrArg NatTrans.app (colimit.ι_post family.diagram
          (sheafToPresheaf S.colimitTopology (Type u)) (op A.unop.left)))
          (op ((S.stageCoconeFunctor i).obj X))
    _ = _ := rfl

/-- Lemma 7.18.4, in the source-text bijectivity form. -/
theorem colimitSiteStageFamilySectionsComparison_bijective
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasWeakSheafify S.colimitTopology (Type u)]
    (family : ColimitSiteStageFamily S)
    {i : S.I} (X : S.stage i) :
    Function.Bijective (colimitSiteStageFamilySectionsComparison S family X) := by
  -- Follow the source-text factorization: source-to-pulled-back colimit map, then finality, then
  -- evaluation/colimit, and finally the filtered-colimit sections comparison from Lemma `7.17.7`.
  have h₁ : Function.Bijective (colimMap (family.sourceToPulledBack X)) :=
    family.sourceToPulledBack_colimMap_bijective X
  have h₂ :
      Function.Bijective
        ((Functor.Final.colimitIso ((Over.forget i).op) (family.globalSectionDiagram X)).hom) :=
    over_forget_colimitIso_bijective family X
  have h₃₄ :
      Function.Bijective
        ((colimitObjIsoColimitCompEvaluation
            (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
            (op ((S.stageCoconeFunctor i).obj X))).inv ≫
          ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
            (op ((S.stageCoconeFunctor i).obj X)))) := by
    have hpost :
        colimit.post family.diagram
          ((sheafSections S.colimitTopology (Type u)).obj
            (op ((S.stageCoconeFunctor i).obj X))) =
          (colimitObjIsoColimitCompEvaluation
              (family.diagram ⋙ sheafToPresheaf S.colimitTopology (Type u))
              (op ((S.stageCoconeFunctor i).obj X))).inv ≫
            ((colimit.post family.diagram (sheafToPresheaf S.colimitTopology (Type u))).app
              (op ((S.stageCoconeFunctor i).obj X))) := by
      -- The sections functor is evaluation of the underlying presheaf functor, so the comparison
      -- from Lemma `7.17.7` is exactly the two rightmost factors in this file.
      simpa [sheafSections] using
        (colimit.post_post family.diagram
          (sheafToPresheaf S.colimitTopology (Type u))
          ((evaluation _ (Type u)).obj (op ((S.stageCoconeFunctor i).obj X)))).symm
    have hsections :
        Function.Bijective
          (colimit.post family.diagram
            ((sheafSections S.colimitTopology (Type u)).obj
              (op ((S.stageCoconeFunctor i).obj X)))) :=
      sheafFilteredColimitSectionsComparison_bijective_of_cofinalFiniteQuasiCompactOverlapCoverings
        (family.diagram)
        ((S.stageCoconeFunctor i).obj X)
        (colimitSiteStage_hasCofinalFiniteQuasiCompactOverlapCoverings S X)
    rw [hpost] at hsections
    exact hsections
  simpa [colimitSiteStageFamilySectionsComparison] using h₃₄.comp (h₂.comp h₁)

end CategoryTheory
