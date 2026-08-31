module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_18_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace CategoryTheory

open CofilteredSiteDiagram

/- Domain-style sampling for Lemma 7.18.5:
- primary domain: stagewise inverse-image/pushforward comparison for sheaves on the colimit site
  of a cofiltered diagram of sites;
- sampled owner API:
  `ColimitSiteStageFamily`,
  `ColimitSiteStageFamily.diagram`,
  `ColimitSiteStageFamily.colimitSheaf`,
  `CofilteredSiteDiagram.colimitStageSheafPullbackCompIso`;
- best owner abstraction: `ColimitSiteStageFamily S`;
- primitive data: the stage sheaves `f_{i,*} ℱ` and the comparison maps
  `f_a⁻¹ f_{i,*} ℱ ⟶ f_{j,*} ℱ`;
- derived API: the pulled-back colimit-site diagram, its colimit sheaf, and the canonical colimit
  comparison to `ℱ`.

This file should therefore build the stage family once and reuse the owner-level diagram and
colimit sheaf from `Lemma_7_18_4`, rather than keeping a parallel local diagram/cocone package.
-/

section

variable (S : CofilteredSiteDiagram.{u, u, u})
variable [HasWeakSheafify S.colimitTopology (Type u)]

/-- The direct-image functor `f_{i,*}` from the colimit site to the stage site `i`. -/
abbrev stageDirectImage (i : S.I) :
    Sheaf S.colimitTopology (Type u) ⥤ Sheaf (S.stageTopology i) (Type u) :=
  (S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
    (S.stageTopology i) S.colimitTopology

/-- The inverse-image functor `f_i⁻¹` from the stage site `i` to the colimit site. -/
abbrev stageInverseImage (i : S.I) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf S.colimitTopology (Type u) :=
  (S.stageCoconeFunctor i).sheafPullback (Type u) (S.stageTopology i) S.colimitTopology

instance stageMap_isContinuous {i j : S.I} (a : j ⟶ i) :
    Functor.IsContinuous (S.diagram.map a.op).toFunctor (S.stageTopology i) (S.stageTopology j) :=
  by
    simpa [CofilteredSiteDiagram.stageFunctor] using S.stageFunctor_isContinuous a

/-- The direct-image functors `f_{i,*}` compose along a transition map as expected. -/
noncomputable def stageDirectImageCompIso
    {i j : S.I} (a : j ⟶ i) :
    stageDirectImage S j ⋙
        (S.stageFunctor a).sheafPushforwardContinuous (Type u)
          (S.stageTopology i) (S.stageTopology j) ≅
      stageDirectImage S i := by
  let F := (S.diagram.map a.op).toFunctor
  let G := S.stageCoconeFunctor j
  let FG := S.stageCoconeFunctor i
  letI : Functor.IsContinuous F (S.stageTopology i) (S.stageTopology j) :=
    stageMap_isContinuous S a
  have h :
      G.sheafPushforwardContinuous (Type u) (S.stageTopology j) S.colimitTopology ⋙
          F.sheafPushforwardContinuous (Type u) (S.stageTopology i) (S.stageTopology j) ≅
        FG.sheafPushforwardContinuous (Type u) (S.stageTopology i) S.colimitTopology :=
    @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ F G FG
      (eqToIso (S.stageCoconeFunctor_comp_eq a))
      (Type u) inferInstance (S.stageTopology i) (S.stageTopology j) S.colimitTopology
      inferInstance inferInstance inferInstance
  simpa [CofilteredSiteDiagram.stageFunctor] using h

/-- Helper for Lemma 7.18.5: the identity-stage transition functor is the identity on the source
stage. This keeps the identity comparison normalization on the owner side instead of unfolding the
diagram relation in every later proof. -/
theorem stage_functor_id_eq_local
    (i : S.I) :
    S.stageFunctor (𝟙 i) = 𝟭 (S.stage i) := by
  -- Rewrite the identity transition functor through the stored diagram identity law.
  exact congrArg Cat.Hom.toFunctor (S.diagram.map_id (op i))

/-- Helper for Lemma 7.18.5: composing the identity-stage transition with the cocone functor gives
the cocone functor itself. This is the right-adjoint equality behind the identity stage
comparison. -/
theorem stage_cocone_functor_id_comp
    (i : S.I) :
    S.stageFunctor (𝟙 i) ⋙ S.stageCoconeFunctor i = S.stageCoconeFunctor i := by
  -- Use the colimit cocone relation for the identity arrow at stage `i`.
  exact S.stageCoconeFunctor_comp_eq (𝟙 i)

/-- Helper for Lemma 7.18.5: the stage transition functors compose in the order induced by the
inverse-system diagram. This packages the `diagram.map_comp` transport once so later proofs can
rewrite with a named equality instead of re-expanding the colimit diagram law. -/
theorem stage_functor_comp_eq_local
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    S.stageFunctor a ⋙ S.stageFunctor b = S.stageFunctor (b ≫ a) := by
  -- Read the transition composition directly from the diagram functor `S.diagram`.
  exact (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op)).symm

/-- Helper for Lemma 7.18.5: the owner-facing stage-composition equality used by
`stageSheafPullbackCompIso`. This is the same diagram relation as
`stage_functor_comp_eq_local`, but in the orientation expected by the owner API. -/
theorem stage_functor_comp_eq_owner
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    S.stageFunctor (b ≫ a) = S.stageFunctor a ⋙ S.stageFunctor b := by
  -- Keep the owner-side composition equality available without inserting ad hoc `Eq.symm`s in
  -- the conjugation lemmas below.
  exact congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op)

/-- Helper for Lemma 7.18.5: a single stage transition followed by the cocone functor is the
next cocone functor. This is the owner-level form of the relation `u_j ∘ u_a = u_i`. -/
theorem stage_cocone_functor_eq_local
    {i j : S.I} (a : j ⟶ i) :
    S.stageFunctor a ⋙ S.stageCoconeFunctor j = S.stageCoconeFunctor i := by
  -- This is exactly the cocone commutativity relation for the arrow `a`.
  exact S.stageCoconeFunctor_comp_eq a

/-- Helper for Lemma 7.18.5: the two successive stage transitions `a` and `b`, followed by the
stage-`k` cocone functor, agree with the stage-`i` cocone functor. This isolates the transport
used in the pending associativity coherence for `stageDirectImageCompIso`. -/
theorem stage_cocone_functor_comp_eq_local
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    S.stageFunctor a ⋙ S.stageFunctor b ⋙ S.stageCoconeFunctor k = S.stageCoconeFunctor i := by
  -- First collapse the `b`-stage cocone relation, then collapse the remaining `a`-stage one.
  calc
    S.stageFunctor a ⋙ S.stageFunctor b ⋙ S.stageCoconeFunctor k
        = S.stageFunctor a ⋙ (S.stageFunctor b ⋙ S.stageCoconeFunctor k) := by
            rfl
    _ = S.stageFunctor a ⋙ S.stageCoconeFunctor j := by
          rw [stage_cocone_functor_eq_local (S := S) b]
    _ = S.stageCoconeFunctor i := by
          rw [stage_cocone_functor_eq_local (S := S) a]

/-- Helper for Lemma 7.18.5: on the pushforward side, the identity-stage comparison with the
colimit cocone is the standard right-unital coherence. -/
theorem stage_direct_image_pushforward_comp_id_comp
    (i : S.I) :
    Functor.sheafPushforwardContinuousComp'
        (eqToIso (stage_cocone_functor_id_comp (S := S) i))
        (Type u) (S.stageTopology i) (S.stageTopology i) S.colimitTopology =
      Functor.isoWhiskerLeft
          ((S.stageCoconeFunctor i).sheafPushforwardContinuous
            (Type u) (S.stageTopology i) S.colimitTopology)
          (Functor.sheafPushforwardContinuousId'
            (eqToIso (stage_functor_id_eq_local (S := S) i))
            (Type u) (S.stageTopology i)) ≪≫
        Functor.rightUnitor (stageDirectImage S i) := by
  -- Compare both sides on sections, then rewrite the residual transport by `eqToHom_map` for the
  -- opposite cocone functor.
  ext ℱ Y y
  have hid : ((S.stageFunctor (𝟙 i)).op.obj Y) = Y := by
    -- The identity-stage transition really is the identity on each stage object.
    simpa using congrArg Opposite.op
      (congrArg (fun F : S.stage i ⥤ S.stage i ↦ F.obj Y.unop)
        (stage_functor_id_eq_local (S := S) i))
  have hcomp :
      ((S.stageCoconeFunctor i).op.obj (((S.stageFunctor (𝟙 i)).op.obj Y))) =
        ((S.stageCoconeFunctor i).op.obj Y) := by
    -- Transport the cocone identity relation down to the chosen object.
    simpa using congrArg Opposite.op
      (congrArg (fun F : S.stage i ⥤ S.ColimitCategory ↦ F.obj Y.unop)
        (stage_cocone_functor_id_comp (S := S) i))
  have hcongr : congrArg ((S.stageCoconeFunctor i).op.obj) hid = hcomp := by
    -- Both transports compare the same equality in a skeletal category, so they agree.
    apply Subsingleton.elim
  simpa [stageDirectImage, hcomp, hcongr] using
    congrArg (fun f ↦ ℱ.obj.map f y) ((eqToHom_map ((S.stageCoconeFunctor i).op) hid).symm)

/-- The canonical stagewise comparison map
`f_a⁻¹ f_{i,*} ℱ ⟶ f_{j,*} ℱ` for a transition `a : j ⟶ i`. -/
noncomputable def stagePushforwardComparison
    (ℱ : Sheaf S.colimitTopology (Type u)) {i j : S.I} (a : j ⟶ i) :
    ((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).obj
        ((stageDirectImage S i).obj ℱ) ⟶
      (stageDirectImage S j).obj ℱ :=
  (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).homEquiv
      ((stageDirectImage S i).obj ℱ)
      ((stageDirectImage S j).obj ℱ)).symm
    ((stageDirectImageCompIso S a).inv.app ℱ)

/-- The identity stage-comparison map is the canonical identity pullback map. -/
theorem stagePushforwardComparison_id
    (ℱ : Sheaf S.colimitTopology (Type u)) (i : S.I) :
    stagePushforwardComparison S ℱ (𝟙 i) =
      (S.stageSheafPullbackIdIso (Type u) i).hom.app ((stageDirectImage S i).obj ℱ) := by
  -- Transpose the identity-stage pushforward isomorphism through the adjunction and rewrite it as
  -- the canonical identity pullback map.
  have hcomp :
      (stageDirectImageCompIso S (𝟙 i)).inv.app ℱ =
        (Functor.sheafPushforwardContinuousId'
          (eqToIso (stage_functor_id_eq_local (S := S) i))
          (Type u) (S.stageTopology i)).inv.app ((stageDirectImage S i).obj ℱ) := by
    -- Replace the composite pushforward comparison by the owner-level right-unital coherence.
    simpa [Functor.rightUnitor_inv_app, stageDirectImage] using
      congrArg (fun e ↦ e.inv.app ℱ)
        (stage_direct_image_pushforward_comp_id_comp (S := S) i)
  -- Route correction: normalize the right-adjoint identity-stage comparison first, then apply the
  -- standard unit formula for the stage pullback/pushforward adjunction.
  apply (((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology i)).homEquiv
      ((stageDirectImage S i).obj ℱ)
      ((stageDirectImage S i).obj ℱ)).injective
  -- After transport normalization, both sides are the same unit-side identity comparison.
  simpa [stagePushforwardComparison, Adjunction.homEquiv_unit, hcomp] using
    (ColimitSiteStageFamily.stage_sheaf_pullback_id_unit_hom_app
      (S := S) (i := i) ((stageDirectImage S i).obj ℱ)).symm

/-- Helper for Lemma 7.18.5: evaluating the owner-side pushforward associativity coherence at the
fixed sheaf `ℱ` removes the remaining `eqToHom` transport from the cocycle proof. This is the
source-text comparison between the direct `(b ≫ a)` pushforward route and the staged `b`-then-`a`
route on the right-adjoint side. -/
theorem stage_cocone_functor_comp_transport_sections
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
  simpa using
    (FunctorToTypes.eqToHom_map_comp_apply
      (F := ℱ.obj)
      (p := congrArg Opposite.op
        (congrArg (fun Z ↦ (S.stageCoconeFunctor k).obj Z) p).symm)
      (q := congrArg Opposite.op q) y)

/-- Helper for Lemma 7.18.5: evaluating the owner-side pushforward associativity coherence at the
fixed sheaf `ℱ` removes the remaining `eqToHom` transport from the cocycle proof. This is the
source-text comparison between the direct `(b ≫ a)` pushforward route and the staged `b`-then-`a`
route on the right-adjoint side. -/
theorem stage_direct_image_pushforward_assoc
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    Functor.isoWhiskerLeft
        (stageDirectImage S k)
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (stage_functor_comp_eq_local (S := S) a b))
          (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)) ≪≫
      stageDirectImageCompIso S (b ≫ a) =
    (Functor.associator
      (stageDirectImage S k)
      ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k))
      ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j))).symm ≪≫
      Functor.isoWhiskerRight
        (stageDirectImageCompIso S b)
        ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
          (S.stageTopology i) (S.stageTopology j)) ≪≫
      stageDirectImageCompIso S a := by
  -- Evaluate the owner-level pushforward coherence componentwise; both routes become the same
  -- after reducing the stage-composition transport to the cached section identity above.
  ext ℱ Y y
  let p :
      (S.stageFunctor (b ≫ a)).obj Y.unop =
        (S.stageFunctor b).obj ((S.stageFunctor a).obj Y.unop) :=
    congrArg
      (fun F : S.stage i ⥤ S.stage k ↦ F.obj Y.unop)
      (stage_functor_comp_eq_local (S := S) a b).symm
  let q :
      (S.stageCoconeFunctor k).obj ((S.stageFunctor (b ≫ a)).obj Y.unop) =
        (S.stageCoconeFunctor i).obj Y.unop :=
    congrArg
      (fun F : S.stage i ⥤ S.ColimitCategory ↦ F.obj Y.unop)
      (S.stageCoconeFunctor_comp_eq (b ≫ a))
  simpa [stageDirectImage, stageDirectImageCompIso, stage_functor_comp_eq_local] using
    stage_cocone_functor_comp_transport_sections (S := S) a b ℱ Y p q y

/-- Helper for Lemma 7.18.5: evaluating the owner-side pushforward associativity coherence at the
fixed sheaf `ℱ` removes the remaining `eqToHom` transport from the cocycle proof. This is the
source-text comparison between the direct `(b ≫ a)` pushforward route and the staged `b`-then-`a`
route on the right-adjoint side. -/
theorem stage_direct_image_pushforward_assoc_app
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    (stageDirectImageCompIso S a).inv.app ℱ ≫
        (((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)).map
          ((stageDirectImageCompIso S b).inv.app ℱ)) ≫
        (Functor.associator
          (stageDirectImage S k)
          ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
            (S.stageTopology j) (S.stageTopology k))
          ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j))).hom.app ℱ =
      ((Functor.isoWhiskerLeft
            (stageDirectImage S k)
            (Functor.sheafPushforwardContinuousComp'
              (eqToIso (stage_functor_comp_eq_local (S := S) a b))
              (Type u) (S.stageTopology i) (S.stageTopology j)
              (S.stageTopology k)) ≪≫
          stageDirectImageCompIso S (b ≫ a)).inv.app ℱ) := by
  -- Route correction: package the right-adjoint associativity transport after evaluating at `ℱ`,
  -- so the cocycle proof can stay on the source counit route instead of reopening `eqToIso`
  -- bookkeeping under `.app`.
  simpa using
    (congrArg (fun e ↦ e.inv.app ℱ) (stage_direct_image_pushforward_assoc (S := S) a b)).symm

/-- The stage-comparison maps satisfy the cocycle condition. -/
theorem stage_pushforward_comparison_comp_right_side_normalization
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
            (S.stageTopology j) (S.stageTopology k))).homEquiv
        ((stageDirectImage S i).obj ℱ)
        ((stageDirectImage S k).obj ℱ))
      ((((S.stageFunctor b).sheafPullback (Type u)
            (S.stageTopology j) (S.stageTopology k)).map
            (stagePushforwardComparison S ℱ a)) ≫
          stagePushforwardComparison S ℱ b) =
      (stageDirectImageCompIso S a).inv.app ℱ ≫
        (((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)).map
          ((stageDirectImageCompIso S b).inv.app ℱ)) ≫
        (Functor.associator
          (stageDirectImage S k)
          ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
            (S.stageTopology j) (S.stageTopology k))
          ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j))).hom.app ℱ := by
  let adj_a :=
    (S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)
  let adj_b :=
    (S.stageFunctor b).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)
  -- Normalize the staged counit route under the composite adjunction before comparing it with the
  -- direct `(b ≫ a)` route.
  change
    (adj_a.homEquiv
      ((stageDirectImage S i).obj ℱ)
      (((S.stageFunctor b).sheafPushforwardContinuous (Type u)
          (S.stageTopology j) (S.stageTopology k)).obj ((stageDirectImage S k).obj ℱ)))
      ((adj_b.homEquiv
          (((S.stageFunctor a).sheafPullback (Type u)
              (S.stageTopology i) (S.stageTopology j)).obj ((stageDirectImage S i).obj ℱ))
          ((stageDirectImage S k).obj ℱ))
        ((((S.stageFunctor b).sheafPullback (Type u)
              (S.stageTopology j) (S.stageTopology k)).map
              (stagePushforwardComparison S ℱ a)) ≫
    stagePushforwardComparison S ℱ b)) =
      (stageDirectImageCompIso S a).inv.app ℱ ≫
        (((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)).map
          ((stageDirectImageCompIso S b).inv.app ℱ))
  -- First transpose along `adj_b`, then along `adj_a`; each step is the corresponding naturality
  -- identity for `homEquiv`.
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  simp [adj_a, adj_b, stagePushforwardComparison]

/-- Helper for Lemma 7.18.5: a section cast is bijective. -/
theorem eqToHom_bijective' {A B : Type u} (h : A = B) :
    Function.Bijective (eqToHom h) := by
  subst h
  exact Function.bijective_id

/-- Helper for Lemma 7.18.5: a returning double chain of section casts is the identity. -/
theorem eqToHom_apply_collapse₂₀'' {A B : Type u}
    (p₁ : A = B) (p₂ : B = A) (x : A) :
    eqToHom p₂ (eqToHom p₁ x) = x := by
  subst p₁
  rfl

/-- Helper for Lemma 7.18.5: transposing after precomposition with a left-adjoint comparison is
postcomposition with its conjugate. -/
theorem homEquiv_conjugateEquiv_exchange''
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

/-- Helper for Lemma 7.18.5: under the composite pullback adjunction, the left branch of the
source cocycle condition is exactly the normalized direct pushforward comparison. This packages the
mate computation for `(S.stageSheafPullbackCompIso (Type u) a b).hom` at the fixed sheaf `ℱ`
before the main cocycle proof compares it with the staged right branch. -/
theorem stage_sheaf_pullback_comp_mate_normalization
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
            (S.stageTopology j) (S.stageTopology k))).homEquiv
        ((stageDirectImage S i).obj ℱ)
        ((stageDirectImage S k).obj ℱ))
      ((S.stageSheafPullbackCompIso (Type u) a b).hom.app ((stageDirectImage S i).obj ℱ) ≫
        stagePushforwardComparison S ℱ (b ≫ a)) =
      ((Functor.isoWhiskerLeft
            (stageDirectImage S k)
            (Functor.sheafPushforwardContinuousComp'
              (eqToIso (stage_functor_comp_eq_local (S := S) a b))
              (Type u) (S.stageTopology i) (S.stageTopology j)
              (S.stageTopology k)) ≪≫
          stageDirectImageCompIso S (b ≫ a)).inv.app ℱ) := by
  have hφ : (((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology k)).homEquiv
      ((stageDirectImage S i).obj ℱ) ((stageDirectImage S k).obj ℱ))
      (stagePushforwardComparison S ℱ (b ≫ a)) =
      (stageDirectImageCompIso S (b ≫ a)).inv.app ℱ :=
    Equiv.apply_symm_apply _ _
  have hex := homEquiv_conjugateEquiv_exchange''
    ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology k))
    (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).comp
      ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)))
    ((S.stageSheafPullbackCompIso (Type u) a b).hom)
    (stagePushforwardComparison S ℱ (b ≫ a))
  rw [stage_sheaf_pullback_comp_conjugate_hom S a b] at hex
  refine hex.trans ?_
  have hK :
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a b)).symm
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)).inv.app
          ((stageDirectImage S k).obj ℱ) =
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (stage_functor_comp_eq_local (S := S) a b))
          (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)).inv.app
            ((stageDirectImage S k).obj ℱ) := by
    ext Y y
    simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso]
  rw [hφ]
  simp [Iso.trans_inv, hK]

/-- The stage-comparison maps satisfy the cocycle condition. -/
theorem stagePushforwardComparison_comp
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    (S.stageSheafPullbackCompIso (Type u) a b).hom.app ((stageDirectImage S i).obj ℱ) ≫
        stagePushforwardComparison S ℱ (b ≫ a) =
      (((S.stageFunctor b).sheafPullback (Type u)
          (S.stageTopology j) (S.stageTopology k)).map
          (stagePushforwardComparison S ℱ a)) ≫
        stagePushforwardComparison S ℱ b := by
  -- Route correction: the diagram-side cocone equalities are now packaged in
  -- `stage_functor_comp_eq_local` and `stage_cocone_functor_comp_eq_local`. The remaining step is
  -- to rewrite both sides as transposes of the same composite pushforward identity map using the
  -- app-level transport normalization `stage_direct_image_pushforward_assoc_app`. The right-hand
  -- side is now isolated by `stage_pushforward_comparison_comp_right_side_normalization`; only the
  -- left-side mate normalization through `S.stageSheafPullbackCompIso` remains.
  let adj_a :=
    (S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)
  let adj_b :=
    (S.stageFunctor b).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)
  -- Apply the composite adjunction bijection so the cocycle reduces to a right-adjoint identity.
  apply ((adj_a.comp adj_b).homEquiv
    ((stageDirectImage S i).obj ℱ)
    ((stageDirectImage S k).obj ℱ)).injective
  -- The staged branch is already normalized to the explicit composite pushforward map.
  have hright :
      ((adj_a.comp adj_b).homEquiv
          ((stageDirectImage S i).obj ℱ)
          ((stageDirectImage S k).obj ℱ))
        ((((S.stageFunctor b).sheafPullback (Type u)
              (S.stageTopology j) (S.stageTopology k)).map
              (stagePushforwardComparison S ℱ a)) ≫
            stagePushforwardComparison S ℱ b) =
      (stageDirectImageCompIso S a).inv.app ℱ ≫
        (((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)).map
          ((stageDirectImageCompIso S b).inv.app ℱ)) ≫
        (Functor.associator
          (stageDirectImage S k)
          ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
            (S.stageTopology j) (S.stageTopology k))
          ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j))).hom.app ℱ := by
    simpa [adj_a, adj_b] using
      stage_pushforward_comparison_comp_right_side_normalization (S := S) (ℱ := ℱ) a b
  have hdirect :
      (stageDirectImageCompIso S a).inv.app ℱ ≫
          (((S.stageFunctor a).sheafPushforwardContinuous (Type u)
                (S.stageTopology i) (S.stageTopology j)).map
              ((stageDirectImageCompIso S b).inv.app ℱ)) ≫
          (Functor.associator
            (stageDirectImage S k)
            ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
              (S.stageTopology j) (S.stageTopology k))
            ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
              (S.stageTopology i) (S.stageTopology j))).hom.app ℱ =
        ((Functor.isoWhiskerLeft
              (stageDirectImage S k)
              (Functor.sheafPushforwardContinuousComp'
              (eqToIso (stage_functor_comp_eq_local (S := S) a b))
              (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)) ≪≫
            stageDirectImageCompIso S (b ≫ a)).inv.app ℱ) := by
    simpa using stage_direct_image_pushforward_assoc_app (S := S) (ℱ := ℱ) a b
  have hleft :
      ((adj_a.comp adj_b).homEquiv
          ((stageDirectImage S i).obj ℱ)
          ((stageDirectImage S k).obj ℱ))
        ((S.stageSheafPullbackCompIso (Type u) a b).hom.app ((stageDirectImage S i).obj ℱ) ≫
          stagePushforwardComparison S ℱ (b ≫ a)) =
      ((Functor.isoWhiskerLeft
            (stageDirectImage S k)
            (Functor.sheafPushforwardContinuousComp'
              (eqToIso (stage_functor_comp_eq_local (S := S) a b))
              (Type u) (S.stageTopology i) (S.stageTopology j)
              (S.stageTopology k)) ≪≫
          stageDirectImageCompIso S (b ≫ a)).inv.app ℱ) := by
    simpa [adj_a, adj_b] using
      stage_sheaf_pullback_comp_mate_normalization (S := S) (ℱ := ℱ) a b
  -- Both transposes are now the same normalized direct pushforward comparison.
  exact hleft.trans (hdirect.symm.trans hright.symm)

/-- The compatible stage family `i ↦ f_{i,*} ℱ` from Lemma 7.18.5. -/
noncomputable def stagePullbackPushforwardFamily
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    ColimitSiteStageFamily S where
  obj i := (stageDirectImage S i).obj ℱ
  transition a := stagePushforwardComparison S ℱ a
  transition_id := stagePushforwardComparison_id S ℱ
  transition_comp := stagePushforwardComparison_comp S ℱ

/-- Helper for Lemma 7.18.5: the owner-level diagram map for the family
`i ↦ f_{i,*} ℱ` is exactly the colimit-stage pullback comparison followed by the pulled-back
canonical stage comparison. -/
theorem stagePullbackPushforwardFamily_diagram_map
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i j : S.I} (a : j ⟶ i) :
    (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ)).map a.op =
      (S.colimitStageSheafPullbackCompIso (Type u) a).inv.app ((stageDirectImage S i).obj ℱ) ≫
        (((S.stageCoconeFunctor j).sheafPullback (Type u)
          (S.stageTopology j) S.colimitTopology).map
          (stagePushforwardComparison S ℱ a)) := by
  -- Unfold the owner-level pulled-back diagram once so later cocone computations can use the
  -- canonical comparison morphism directly.
  rfl

/-- The counit map `f_i⁻¹ f_{i,*} ℱ ⟶ ℱ` at a single stage. -/
abbrev stagePullbackPushforwardCounit
    (ℱ : Sheaf S.colimitTopology (Type u)) (i : S.I) :
    (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj
        ((stageDirectImage S i).obj ℱ)) ⟶
      ℱ :=
  ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
    (S.stageTopology i) S.colimitTopology).counit.app ℱ

/-- The stage counits assemble into a cocone over the owner-level pulled-back diagram attached to
`i ↦ f_{i,*} ℱ`. -/
theorem stagePullbackPushforwardCounit_naturality
    (ℱ : Sheaf S.colimitTopology (Type u)) {i j : S.I} (a : j ⟶ i) :
    (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ)).map a.op ≫
      stagePullbackPushforwardCounit S ℱ j =
        stagePullbackPushforwardCounit S ℱ i := by
  rw [stagePullbackPushforwardFamily_diagram_map]
  apply ((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
    (S.stageTopology i) S.colimitTopology)).homEquiv
    ((stageDirectImage S i).obj ℱ) ℱ).injective
  have hR : ((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology)).homEquiv
      ((stageDirectImage S i).obj ℱ) ℱ)
      (stagePullbackPushforwardCounit S ℱ i) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact Adjunction.right_triangle_components _ _
  rw [hR]
  have hconj : conjugateEquiv
      (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).comp
        ((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
          (S.stageTopology j) S.colimitTopology))
      ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) S.colimitTopology)
      ((S.colimitStageSheafPullbackCompIso (Type u) a).inv) =
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq a))
        (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology).hom := by
    simp [CofilteredSiteDiagram.colimitStageSheafPullbackCompIso]
  have hex := homEquiv_conjugateEquiv_exchange''
    (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).comp
      ((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) S.colimitTopology))
    ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology)
    ((S.colimitStageSheafPullbackCompIso (Type u) a).inv)
    (((S.stageCoconeFunctor j).sheafPullback (Type u)
      (S.stageTopology j) S.colimitTopology).map
      (stagePushforwardComparison S ℱ a) ≫ stagePullbackPushforwardCounit S ℱ j)
  rw [hconj] at hex
  refine hex.trans ?_
  have hsplit : ∀ γ : ((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j) ⋙
      (S.stageCoconeFunctor j).sheafPullback (Type u)
        (S.stageTopology j) S.colimitTopology).obj ((stageDirectImage S i).obj ℱ) ⟶ ℱ,
      ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).comp
        ((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
          (S.stageTopology j) S.colimitTopology)).homEquiv
        ((stageDirectImage S i).obj ℱ) ℱ) γ =
      (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).homEquiv _ _)
        ((((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
          (S.stageTopology j) S.colimitTopology)).homEquiv _ _ γ) := by
    intro γ
    rw [Adjunction.comp_homEquiv]
    rfl
  have hinJ : ((((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) S.colimitTopology)).homEquiv _ _)
      (((S.stageCoconeFunctor j).sheafPullback (Type u)
        (S.stageTopology j) S.colimitTopology).map
        (stagePushforwardComparison S ℱ a) ≫ stagePullbackPushforwardCounit S ℱ j) =
      stagePushforwardComparison S ℱ a := by
    rw [Adjunction.homEquiv_naturality_left]
    have hcj : ((((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) S.colimitTopology)).homEquiv _ _)
        (stagePullbackPushforwardCounit S ℱ j) = 𝟙 _ := by
      rw [Adjunction.homEquiv_unit]
      exact Adjunction.right_triangle_components _ _
    rw [hcj, Category.comp_id]
  have hmid := (hsplit _).trans (congrArg (fun t =>
    (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).homEquiv
      ((stageDirectImage S i).obj ℱ) ((stageDirectImage S j).obj ℱ)) t) hinJ)
  refine Eq.trans (congrArg (fun t => t ≫ (Functor.sheafPushforwardContinuousComp'
    (eqToIso (S.stageCoconeFunctor_comp_eq a))
    (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology).hom.app ℱ)
    (hmid.trans (Equiv.apply_symm_apply _ _))) ?_
  exact Iso.inv_hom_id_app (stageDirectImageCompIso S a) ℱ

/-- The canonical cocone from the owner-level diagram `i ↦ f_i⁻¹ f_{i,*} ℱ` to `ℱ`. -/
noncomputable def stagePullbackPushforwardCocone
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    Cocone (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ)) where
  pt := ℱ
  ι :=
    { app := fun i ↦ stagePullbackPushforwardCounit S ℱ (unop i)
      naturality := by
        intro i j a
        simpa using stagePullbackPushforwardCounit_naturality S ℱ a.unop }

/-- The filtered colimit object `colim_i f_i⁻¹ f_{i,*} ℱ` in the colimit site. -/
abbrev colimitSiteStagePullbackPushforward
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    Sheaf S.colimitTopology (Type u) :=
  ColimitSiteStageFamily.colimitSheaf (stagePullbackPushforwardFamily S ℱ)

/-- The canonical comparison morphism from the colimit of the diagram
`i ↦ f_i⁻¹ f_{i,*} ℱ` to `ℱ`. -/
abbrev colimitSiteStagePullbackPushforwardComparison
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    colimitSiteStagePullbackPushforward S ℱ ⟶ ℱ :=
  colimit.desc (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ))
    (stagePullbackPushforwardCocone S ℱ)

/-- Helper for Lemma 7.18.5: the colimit comparison restricts on each stage summand to the stage
counit map. This is the formal `colimit.ι_desc` bridge used in the represented-object argument. -/
theorem stagePullbackPushforwardComparison_ι
    (ℱ : Sheaf S.colimitTopology (Type u)) (i : S.Iᵒᵖ) :
    colimit.ι (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ)) i ≫
        colimitSiteStagePullbackPushforwardComparison S ℱ =
      stagePullbackPushforwardCounit S ℱ i.unop := by
  -- The final comparison is defined by descending the cocone of stage counits, so each colimit
  -- injection factors through the corresponding counit component.
  simpa [colimitSiteStagePullbackPushforwardComparison, stagePullbackPushforwardCocone] using
    colimit.ι_desc
      (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ))
      (stagePullbackPushforwardCocone S ℱ) i

/-- Helper for Lemma 7.18.5: after specializing Lemma `7.18.4` to the family
`i ↦ f_{i,*} ℱ`, its section-comparison map already lands in the sections of the source sheaf
`colim_i f_i⁻¹ f_{i,*} ℱ` on the represented object `u_i(X)`. -/
theorem stage_pullback_pushforward_sections_comparison_bijective
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i : S.I} (X : S.stage i) :
    Function.Bijective
      (show colimit ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X) ⟶
          ((sheafToPresheaf S.colimitTopology (Type u)).obj
            (colimitSiteStagePullbackPushforward S ℱ)).obj
              (op ((S.stageCoconeFunctor i).obj X)) from
        colimitSiteStageFamilySectionsComparison S (stagePullbackPushforwardFamily S ℱ) X) := by
  -- The target of Lemma `7.18.4` is definitionally the represented-object section set of the
  -- colimit sheaf `colim_i f_i⁻¹ f_{i,*} ℱ`, so its bijectivity transfers without further work.
  simpa using
    (colimitSiteStageFamilySectionsComparison_bijective S
      (stagePullbackPushforwardFamily S ℱ) X)

/-- Helper for Lemma 7.18.5: the identity arrow `i ⟶ i` is the initial object of the opposite
indexing category `(Over i)ᵒᵖ` used in the source colimit. -/
noncomputable def stage_pullback_pushforward_initial_object
    (i : S.I) :
    IsInitial (op (Over.mk (𝟙 i) : Over i)) :=
  Limits.initialOpOfTerminal Over.mkIdTerminal

/-- Helper for Lemma 7.18.5: at the identity object of `(Over i)ᵒᵖ`, the source stage object
`S.overImage X A₀` is just `X`. This is the source-text normalization `u_{id_i}(X) = X`. -/
theorem stage_pullback_pushforward_overImage_id
    {i : S.I} (X : S.stage i) :
    S.overImage X (op (Over.mk (𝟙 i) : Over i)) = X := by
  -- Rewrite the identity-stage transition functor to the literal identity on `S.stage i`.
  simpa [CofilteredSiteDiagram.overImage, stage_functor_id_eq_local (S := S) i]

/-- Helper for Lemma 7.18.5: the leg of the comparison cocone at the identity object of
`(Over i)ᵒᵖ` is the identity on `ℱ(u_i(X))`. This is the concrete source-text representative used
to start the inverse construction. -/
theorem stage_pullback_pushforward_initial_leg_bijective
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i : S.I} (X : S.stage i) :
    let A₀ : (Over i)ᵒᵖ := op (Over.mk (𝟙 i))
    let ψ :=
      (((sheafToPresheaf S.colimitTopology (Type u)).map
        (colimitSiteStagePullbackPushforwardComparison S ℱ)).app
          (op ((S.stageCoconeFunctor i).obj X)))
    let η :=
      (show colimit ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X) ⟶
          ((sheafToPresheaf S.colimitTopology (Type u)).obj
            (colimitSiteStagePullbackPushforward S ℱ)).obj
              (op ((S.stageCoconeFunctor i).obj X)) from
        colimitSiteStageFamilySectionsComparison S (stagePullbackPushforwardFamily S ℱ) X)
    Function.Bijective
      (colimit.ι ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X) A₀ ≫ η ≫ ψ) := by
  -- Collapse the comparison composite on the initial leg to the adjunction triangle identity.
  show Function.Bijective
    (colimit.ι ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X)
      (op (Over.mk (𝟙 i))) ≫
      (colimitSiteStageFamilySectionsComparison S (stagePullbackPushforwardFamily S ℱ) X ≫
        ((sheafToPresheaf S.colimitTopology (Type u)).map
          (colimitSiteStagePullbackPushforwardComparison S ℱ)).app
          (op ((S.stageCoconeFunctor i).obj X))))
  rw [← Category.assoc,
    colimitSiteStageFamilySectionsComparison_ι S (stagePullbackPushforwardFamily S ℱ) X
      (op (Over.mk (𝟙 i)))]
  rw [Category.assoc]
  have hobjId : S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ) = X :=
    stage_pullback_pushforward_overImage_id S X
  have hu : (S.stageCoconeFunctor i).obj
      (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ)) =
      (S.stageCoconeFunctor i).obj X :=
    congrArg (fun Z => (S.stageCoconeFunctor i).obj Z) hobjId
  have h₁ : ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj
      ((stageDirectImage S i).obj ℱ)).obj.obj (op ((S.stageCoconeFunctor i).obj X))) =
      ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj
      ((stageDirectImage S i).obj ℱ)).obj.obj
      (op ((S.stageCoconeFunctor i).obj
        (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ))))) :=
    congrArg (fun Z => (((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj
      ((stageDirectImage S i).obj ℱ)).obj.obj (op Z)) hu.symm
  have h₂ : (ℱ.obj.obj (op ((S.stageCoconeFunctor i).obj
      (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ))))) =
      (ℱ.obj.obj (op ((S.stageCoconeFunctor i).obj X))) :=
    congrArg (fun Z => ℱ.obj.obj (op Z)) hu
  have hcongr : (((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology)).counit.app ℱ).1.app
      (op ((S.stageCoconeFunctor i).obj X))) =
      eqToHom h₁ ≫ (((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) S.colimitTopology)).counit.app ℱ).1.app
        (op ((S.stageCoconeFunctor i).obj
          (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ))))) ≫ eqToHom h₂ := by
    have := NatTrans.congr
      (((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) S.colimitTopology)).counit.app ℱ).1)
      (congrArg op hu.symm)
    simpa [eqToHom_map] using this
  have htri : (((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology)).unit.app
      ((stageDirectImage S i).obj ℱ)).1.app
      (op (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ)))) ≫
      (((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) S.colimitTopology)).counit.app ℱ).1.app
        (op ((S.stageCoconeFunctor i).obj
          (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ))))) = 𝟙 _ := by
    exact congrArg (fun t => t.1.app
      (op (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ))))
      ((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) S.colimitTopology)).right_triangle_components ℱ)
  have hfun : ∀ (htgt : (((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology) ⋙
        (S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
          (S.stageTopology i) S.colimitTopology).obj
        ((stageDirectImage S i).obj ℱ)).obj.obj
        (op (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ)))) =
      (((ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ)).obj
        (op i)).1.obj (op ((S.stageCoconeFunctor i).obj X)))),
      ((((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology)).unit.app
      ((stageDirectImage S i).obj ℱ)).1.app
      (op (S.overImage X (op (Over.mk (𝟙 i))))) ≫
      eqToHom htgt) ≫
      ((((sheafToPresheaf S.colimitTopology (Type u)).map
        (colimit.ι (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ))
          (op i))).app
        (op ((S.stageCoconeFunctor i).obj X))) ≫
      (((sheafToPresheaf S.colimitTopology (Type u)).map
        (colimitSiteStagePullbackPushforwardComparison S ℱ)).app
        (op ((S.stageCoconeFunctor i).obj X))))) = eqToHom h₂ := by
    intro htgt
    funext s
    have hpt := congrFun (congrArg
      (fun t => (((sheafToPresheaf S.colimitTopology (Type u)).map t).app
        (op ((S.stageCoconeFunctor i).obj X))))
      (stagePullbackPushforwardComparison_ι S ℱ (op i)))
      (eqToHom htgt
        (((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) S.colimitTopology)).unit.app
          ((stageDirectImage S i).obj ℱ)).1.app
          (op (S.overImage X (op (Over.mk (𝟙 i))))) s))
    refine hpt.trans ?_
    have hc := congrFun hcongr
      (eqToHom htgt
        (((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) S.colimitTopology)).unit.app
          ((stageDirectImage S i).obj ℱ)).1.app
          (op (S.overImage X (op (Over.mk (𝟙 i))))) s))
    refine hc.trans ?_
    refine Eq.trans (congrArg (fun t => eqToHom h₂
      ((((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) S.colimitTopology)).counit.app ℱ).1.app
        (op ((S.stageCoconeFunctor i).obj
          (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ))))) t))
      (eqToHom_apply_collapse₂₀'' htgt h₁ _)) ?_
    exact congrArg (fun t => eqToHom h₂ t) (congrFun htri s)
  have htgt₀ : (((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology) ⋙
      (S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) S.colimitTopology).obj
      ((stageDirectImage S i).obj ℱ)).obj.obj
      (op (S.overImage X (op (Over.mk (𝟙 i)) : (Over i)ᵒᵖ)))) =
      (((ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ)).obj
        (op i)).1.obj (op ((S.stageCoconeFunctor i).obj X))) :=
    congrArg (fun Z => (((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj
      ((stageDirectImage S i).obj ℱ)).obj.obj (op Z)) hu
  show Function.Bijective
    ((((((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology)).unit.app
      ((stageDirectImage S i).obj ℱ)).1.app
      (op (S.overImage X (op (Over.mk (𝟙 i))))) ≫
      eqToHom htgt₀) ≫
      ((((sheafToPresheaf S.colimitTopology (Type u)).map
        (colimit.ι (ColimitSiteStageFamily.diagram (stagePullbackPushforwardFamily S ℱ))
          (op i))).app
        (op ((S.stageCoconeFunctor i).obj X))) ≫
      (((sheafToPresheaf S.colimitTopology (Type u)).map
        (colimitSiteStagePullbackPushforwardComparison S ℱ)).app
        (op ((S.stageCoconeFunctor i).obj X)))))
  rw [hfun htgt₀]
  exact eqToHom_bijective' h₂

/-- Helper for Lemma 7.18.5: on a represented colimit-site object `u_i(X)`, the component of the
comparison map from `colim_j f_j⁻¹ f_{j,*} ℱ` to `ℱ` is bijective. This is the source-text step
that identifies every stage section map with the identity on `ℱ(u_i(X))` and then uses
Lemma `7.18.4` for the source colimit. -/
theorem stage_pullback_pushforward_comparison_app_bijective
    (ℱ : Sheaf S.colimitTopology (Type u))
    {i : S.I} (X : S.stage i) :
    Function.Bijective
      (((sheafToPresheaf S.colimitTopology (Type u)).map
        (colimitSiteStagePullbackPushforwardComparison S ℱ)).app
          (op ((S.stageCoconeFunctor i).obj X))) := by
  -- Route correction: first reduce the represented-object source to the section colimit from
  -- Lemma `7.18.4`, then use the identity representative `𝟙 i` in `(Over i)ᵒᵖ` to show the
  -- remaining cocone map is the identity on sections.
  let ψ :=
    (((sheafToPresheaf S.colimitTopology (Type u)).map
      (colimitSiteStagePullbackPushforwardComparison S ℱ)).app
        (op ((S.stageCoconeFunctor i).obj X)))
  let η :=
    (show colimit ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X) ⟶
        ((sheafToPresheaf S.colimitTopology (Type u)).obj
          (colimitSiteStagePullbackPushforward S ℱ)).obj
            (op ((S.stageCoconeFunctor i).obj X)) from
      colimitSiteStageFamilySectionsComparison S (stagePullbackPushforwardFamily S ℱ) X)
  have hη : Function.Bijective η :=
    stage_pullback_pushforward_sections_comparison_bijective (S := S) ℱ X
  have hcomp : Function.Bijective (η ≫ ψ) := by
    -- The represented-object source route has been reduced to the identity leg in `(Over i)ᵒᵖ`.
    -- The maps out of the initial object are bijective, so bijectivity of the identity leg
    -- upgrades to bijectivity of the full colimit map.
    let A₀ : (Over i)ᵒᵖ := op (Over.mk (𝟙 i))
    let hA₀ :
        Function.Bijective
          (colimit.ι ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X) A₀ ≫ η ≫ ψ) :=
      stage_pullback_pushforward_initial_leg_bijective (S := S) ℱ X
    -- every transition map of the section diagram for this family is bijective, because the
    -- transposed transition is a component of the direct-image comparison isomorphism
    have hmapsBij : ∀ {A B : (Over i)ᵒᵖ} (u : A ⟶ B),
        Function.Bijective
          (((stagePullbackPushforwardFamily S ℱ).sectionDiagram X).map u) := by
      intro A B u
      have hbij : ∀ (h : ((((S.stageFunctor u.unop.left).sheafPushforwardContinuous (Type u)
          (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
          ((stagePullbackPushforwardFamily S ℱ).obj B.unop.left)).obj.obj
          (op (S.overImage X A))) =
          (((stagePullbackPushforwardFamily S ℱ).obj B.unop.left).obj.obj
            (op (S.overImage X B)))),
          Function.Bijective
            ((((((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
              (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
              ((stagePullbackPushforwardFamily S ℱ).obj A.unop.left)
              ((stagePullbackPushforwardFamily S ℱ).obj B.unop.left))
              ((stagePullbackPushforwardFamily S ℱ).transition u.unop.left)).1.app
              (op (S.overImage X A))) ≫ eqToHom h) := by
        intro h
        refine Function.Bijective.comp (eqToHom_bijective' h) ?_
        have hmate : (((S.stageFunctor u.unop.left).sheafAdjunctionContinuous (Type u)
            (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
            ((stagePullbackPushforwardFamily S ℱ).obj A.unop.left)
            ((stagePullbackPushforwardFamily S ℱ).obj B.unop.left))
            ((stagePullbackPushforwardFamily S ℱ).transition u.unop.left) =
            (stageDirectImageCompIso S u.unop.left).inv.app ℱ :=
          Equiv.apply_symm_apply _ _
        rw [hmate]
        have hLR₁ := congrFun (congrArg (fun t => t.1.app (op (S.overImage X A)))
          (Iso.inv_hom_id_app (stageDirectImageCompIso S u.unop.left) ℱ))
        have hLR₂ := congrFun (congrArg (fun t => t.1.app (op (S.overImage X A)))
          (Iso.hom_inv_id_app (stageDirectImageCompIso S u.unop.left) ℱ))
        constructor
        · intro a b hab
          have h₁ := hLR₁ a
          have h₂ := hLR₁ b
          simp only at h₁ h₂
          refine h₁.symm.trans (Eq.trans ?_ h₂)
          exact congrArg (((stageDirectImageCompIso S u.unop.left).hom.app ℱ).1.app
            (op (S.overImage X A))) hab
        · intro b
          refine ⟨(((stageDirectImageCompIso S u.unop.left).hom.app ℱ).1.app
            (op (S.overImage X A))) b, ?_⟩
          have := hLR₂ b
          simpa using this
      exact hbij _
    -- the initial-object injection into the section colimit is bijective
    haveI : IsFiltered ((Over i)ᵒᵖ) := by infer_instance
    have hinit := stage_pullback_pushforward_initial_object S i
    have hι₀ : Function.Bijective
        (colimit.ι ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X) A₀) := by
      constructor
      · intro s t hst
        obtain ⟨k, f, g, hfg⟩ :=
          (Types.FilteredColimit.colimit_eq_iff
            ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X)).1 hst
        have hfg' : f = g := hinit.hom_ext f g
        rw [hfg'] at hfg
        exact (hmapsBij g).injective hfg
      · intro x
        obtain ⟨A, s, rfl⟩ := Types.jointly_surjective'
          (F := (stagePullbackPushforwardFamily S ℱ).sectionDiagram X) x
        obtain ⟨s₀, hs₀⟩ := (hmapsBij (hinit.to A)).surjective s
        refine ⟨s₀, ?_⟩
        have hw := congrFun (colimit.w
          ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X) (hinit.to A)) s₀
        refine hw.symm.trans ?_
        exact congrArg (colimit.ι ((stagePullbackPushforwardFamily S ℱ).sectionDiagram X) A) hs₀
    exact (Function.Bijective.of_comp_iff _ hι₀).mp hA₀
  -- Since Lemma `7.18.4` already identifies the source colimit bijectively, it remains to strip
  -- off that bijective precomposition.
  simpa using (Function.Bijective.of_comp_iff ψ hη).mp hcomp

-- Proof sketch: evaluate the comparison map at an object `U` of the colimit site, choose a stage
-- object `U_i` mapping to `U`, and identify the source with the filtered colimit of the sections
-- `f_{j,*} ℱ(u_a(U_i))`. Lemma `7.18.4` computes this colimit, and each term is canonically
-- `ℱ(U)`, so the comparison map is bijective on every object and hence an isomorphism.
/-- Lemma 7.18.5: in Situation 7.18.1, for a sheaf `ℱ` on the colimit site, the canonical map
from the filtered colimit of the canonical diagram `i ↦ f_i⁻¹ f_{i,*} ℱ` to `ℱ` is an
isomorphism. In Lean this filtered colimit is indexed by `S.Iᵒᵖ` via the owner-level diagram
coming from the compatible stage family `i ↦ f_{i,*} ℱ`. -/
theorem colimitSiteStagePullbackPushforwardComparison_isIso
    (ℱ : Sheaf S.colimitTopology (Type u)) :
    IsIso (colimitSiteStagePullbackPushforwardComparison S ℱ) := by
  -- A sheaf morphism is an isomorphism once its underlying presheaf map is, and the latter is
  -- checked objectwise; every colimit-site object is a represented stage image.
  suffices h : IsIso ((sheafToPresheaf S.colimitTopology (Type u)).map
      (colimitSiteStagePullbackPushforwardComparison S ℱ)) by
    exact isIso_of_fully_faithful (sheafToPresheaf S.colimitTopology (Type u)) _
  suffices h : ∀ V : (S.ColimitCategory)ᵒᵖ,
      IsIso (((sheafToPresheaf S.colimitTopology (Type u)).map
        (colimitSiteStagePullbackPushforwardComparison S ℱ)).app V) by
    exact NatIso.isIso_of_isIso_app _
  intro V
  rw [isIso_iff_bijective]
  obtain ⟨i, X, hX⟩ := S.ιObj_surjective V.unop
  have hrep := stage_pullback_pushforward_comparison_app_bijective S ℱ X
  -- transport the represented-object bijectivity along the presentation
  have hVeq : (op ((S.stageCoconeFunctor i).obj X)) = V := by
    rw [show ((S.stageCoconeFunctor i).obj X) = V.unop from hX]
  have hcongr := NatTrans.congr
    ((sheafToPresheaf S.colimitTopology (Type u)).map
      (colimitSiteStagePullbackPushforwardComparison S ℱ)) hVeq.symm
  rw [hcongr]
  have hb : ∀ {P : (S.ColimitCategory)ᵒᵖ ⥤ Type u} {a b : (S.ColimitCategory)ᵒᵖ}
      (h : a = b), Function.Bijective (P.map (eqToHom h)) := by
    intro P a b h
    subst h
    rw [eqToHom_refl, P.map_id]
    exact Function.bijective_id
  exact Function.Bijective.comp (Function.Bijective.comp (hb _) hrep) (hb _)

attribute [instance] colimitSiteStagePullbackPushforwardComparison_isIso

end

end CategoryTheory
