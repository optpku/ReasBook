module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Lemma_7_14_6
public import stacks_project.Chap07.Lemma_7_18_2
public import stacks_project.Chap07.Lemma_7_18_3.AuxiliarySheaf
public import stacks_project.Chap07.Situation_7_18_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe uI uC vC u w

namespace CategoryTheory

open CofilteredSiteDiagram

/- Domain-style sampling for Lemma 7.18.3:
- primary domain: pullback of sheaves along the stage and cocone functors in a cofiltered diagram
  of sites, together with the slice indexing category `(Over i)ᵒᵖ`;
- sampled owner API:
  `CofilteredSiteDiagram.stageFunctor`,
  `CofilteredSiteDiagram.stageCoconeFunctor`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPushforwardContinuousComp'`,
  `Adjunction.leftAdjointCompIso`;
- source/core/bridge triage:
  `source-facing`: the filtered colimit comparison on section sets indexed by arrows `a : j ⟶ i`;
  `core/canonical`: the owner pullback functors attached to `S.stageFunctor a` and
    `S.stageCoconeFunctor i`;
  `bridge/view`: the private over-category section diagram used to express equation `(7.18.3.1)`.

Primitive data are the stage and cocone functors already packaged by
`CofilteredSiteDiagram`. The pullback-composition isomorphisms are derived API and should reuse the
owner-level stage and cocone functors rather than raw `diagram.map` and `colimit.ι` spellings.
-/

noncomputable abbrev stageSheafPullbackAlong
    (S : CofilteredSiteDiagram.{u, u, u})
    {i j : S.I} (a : j ⟶ i) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf (S.stageTopology j) (Type u) :=
  let _ : Functor.IsContinuous (S.stageFunctor a)
      (S.stageTopology i) (S.stageTopology j) :=
    S.stageFunctor_isContinuous a
  (S.stageFunctor a).sheafPullback (Type u) (S.stageTopology i) (S.stageTopology j)

noncomputable abbrev overStageSheafPullback
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (A : (Over i)ᵒᵖ) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf (S.stageTopology A.unop.left) (Type u) :=
  stageSheafPullbackAlong S A.unop.hom

abbrev overLeftHom
    {C : Type*} [Category C] {i : C} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    B.unop.left ⟶ A.unop.left :=
  u.unop.left

abbrev colimitSiteStagePullbackSectionValue
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) : Type u :=
  ((overStageSheafPullback S A).obj ℱ).obj.obj
    (op (S.overImage X A))

noncomputable def colimitSiteStagePullbackSectionTransition
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u))
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    let a := overLeftHom u
    (overStageSheafPullback S A).obj ℱ ⟶
      ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
      ((overStageSheafPullback S B).obj ℱ) :=
  let _ : Functor.IsContinuous (S.stageFunctor (overLeftHom u))
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left) :=
    S.stageFunctor_isContinuous (overLeftHom u)
  let e :=
    (((S.stageFunctor (overLeftHom u)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
      ((overStageSheafPullback S A).obj ℱ)
      ((overStageSheafPullback S B).obj ℱ))
  e <|
    show ((S.stageFunctor (overLeftHom u)).sheafPullback (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
          ((overStageSheafPullback S A).obj ℱ) ⟶
        (overStageSheafPullback S B).obj ℱ from by
      have h : overLeftHom u ≫ A.unop.hom = B.unop.hom := by
        simpa using Over.w u.unop
      let _ : Functor.IsContinuous (S.stageFunctor (overLeftHom u ≫ A.unop.hom))
          (S.stageTopology i) (S.stageTopology B.unop.left) :=
        S.stageFunctor_isContinuous (overLeftHom u ≫ A.unop.hom)
      have h' :
          (stageSheafPullbackAlong S (overLeftHom u ≫ A.unop.hom)).obj ℱ =
            (overStageSheafPullback S B).obj ℱ := by
        simpa [stageSheafPullbackAlong, overStageSheafPullback] using
          congrArg (fun a : B.unop.left ⟶ i ↦ (stageSheafPullbackAlong S a).obj ℱ) h
      exact
        (S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ ≫
          eqToHom h'

theorem colimitSiteStagePullbackSectionMap_target_eq
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    let a := overLeftHom u
    ((((S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
        ((overStageSheafPullback S B).obj ℱ)).obj.obj
      (op (S.overImage X A))) =
      colimitSiteStagePullbackSectionValue S ℱ X B := by
  -- Rewrite the pushforward evaluation to the section at the image object, then identify that
  -- image with `S.overImage X B` using the commutative triangle `Over.w u.unop`.
  have hcomp :
      S.stageFunctor A.unop.hom ⋙ S.stageFunctor (overLeftHom u) =
        S.stageFunctor (overLeftHom u ≫ A.unop.hom) := by
    exact congrArg Cat.Hom.toFunctor
      (S.diagram.map_comp A.unop.hom.op (overLeftHom u).op).symm
  have h₁ :
      (S.stageFunctor (overLeftHom u)).obj (S.overImage X A) =
        (S.stageFunctor (overLeftHom u ≫ A.unop.hom)).obj X := by
    simpa [CofilteredSiteDiagram.overImage] using
      congrArg (fun F : S.stage i ⥤ S.stage B.unop.left ↦ F.obj X) hcomp
  have hw : overLeftHom u ≫ A.unop.hom = B.unop.hom := by
    simpa using Over.w u.unop
  have h₂ :
      (S.stageFunctor (overLeftHom u ≫ A.unop.hom)).obj X = S.overImage X B := by
    simpa [CofilteredSiteDiagram.overImage] using
      congrArg (fun a : B.unop.left ⟶ i ↦ (S.stageFunctor a).obj X) hw
  have hobj :
      (S.stageFunctor (overLeftHom u)).obj (S.overImage X A) = S.overImage X B :=
    h₁.trans h₂
  simpa [colimitSiteStagePullbackSectionValue, overStageSheafPullback] using
    congrArg
      (fun Y ↦ (((overStageSheafPullback S B).obj ℱ).obj.obj (op Y)))
      hobj

noncomputable def colimitSiteStagePullbackSectionMap
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    colimitSiteStagePullbackSectionValue S ℱ X A ⟶
      colimitSiteStagePullbackSectionValue S ℱ X B :=
  (colimitSiteStagePullbackSectionTransition S ℱ u).1.app
      (op (S.overImage X A)) ≫
    eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u)

/-- Helper for Lemma 7.18.3: the stage functor for an identity arrow is the identity functor. -/
theorem stageFunctor_id_eq_local
    (S : CofilteredSiteDiagram.{u, u, u}) (i : S.I) :
    S.stageFunctor (𝟙 i) = 𝟭 (S.stage i) := by
  -- This is the direct functor-level identity needed before comparing pullback adjunctions.
  exact congrArg Cat.Hom.toFunctor (S.diagram.map_id (op i))

/-- Helper for Lemma 7.18.3: composing a stage functor on the right with the identity-stage
functor changes nothing. -/
theorem stageFunctor_comp_id_eq
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) = S.stageFunctor a := by
  -- This reduces the identity-arrow case of the over-category transition to the original stage
  -- functor `S.stageFunctor a`.
  calc
    S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) = S.stageFunctor ((𝟙 j) ≫ a) := by
      symm
      exact congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op (𝟙 j).op)
    _ = S.stageFunctor a := by simp

/-- Helper for Lemma 7.18.3: the identity arrow in `(Over i)ᵒᵖ` does not change the target section
type of the transition map. -/
theorem colimitSiteStagePullbackSectionMap_target_eq_id
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    let a := overLeftHom (𝟙 A)
    ((((S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology A.unop.left)).obj
        ((overStageSheafPullback S A).obj ℱ)).obj.obj
      (op (S.overImage X A))) =
      colimitSiteStagePullbackSectionValue S ℱ X A := by
  -- The identity-stage pushforward evaluates the same sheaf at the same stage object.
  simp [colimitSiteStagePullbackSectionValue, overLeftHom, overStageSheafPullback,
    stageFunctor_id_eq_local]

/-- Helper for Lemma 7.18.3: on the pushforward side, composing the stage functor `a` with the
identity-stage functor gives the standard right-unital comparison. -/
theorem stageSheafPushforwardComp_comp_id
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    Functor.sheafPushforwardContinuousComp'
        (eqToIso (stageFunctor_comp_id_eq S a))
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j) =
      Functor.isoWhiskerRight
          (Functor.sheafPushforwardContinuousId'
            (eqToIso (stageFunctor_id_eq_local S j))
            (Type u) (S.stageTopology j))
          ((S.stageFunctor a).sheafPushforwardContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j)) ≪≫
        Functor.leftUnitor
          ((S.stageFunctor a).sheafPushforwardContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j)) := by
  -- The right-adjoint comparison is definitionally the standard unital coherence.
  ext ℱ Y y
  simp

/-- Helper for Lemma 7.18.3: after identifying `S.stageFunctor ((𝟙 j) ≫ a)` with
`S.stageFunctor a`, the owner pushforward comparison for `a` followed by the identity-stage
functor becomes the standard right-unital comparison. -/
theorem stageSheafPushforwardComp_comp_id_owner_normalize
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) =
              S.stageFunctor ((𝟙 j) ≫ a) from
            (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op (𝟙 j).op)).symm))
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j) ≪≫
      Functor.sheafPushforwardContinuousIso
        (eqToIso
          (show S.stageFunctor ((𝟙 j) ≫ a) = S.stageFunctor a from by
            simpa [CofilteredSiteDiagram.stageFunctor] using
              congrArg Cat.Hom.toFunctor (Category.id_comp a)))
        (Type u) (S.stageTopology i) (S.stageTopology j) =
      Functor.sheafPushforwardContinuousComp'
        (eqToIso (stageFunctor_comp_id_eq S a))
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j) := by
  -- Compare the two owner pushforward isomorphisms directly on sections; once the target stage
  -- functor is rewritten by `id_comp`, the remaining transport is definitional.
  ext ℱ Y y
  simp

/-- Helper for Lemma 7.18.3: the composite pullback along `a` and the identity-stage pullback has
target equal to the pullback along `a` after normalizing `(𝟙 j) ≫ a = a`. -/
theorem stageSheafPullbackComp_comp_id_target_eq
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    stageSheafPullbackAlong S ((𝟙 j) ≫ a) = stageSheafPullbackAlong S a := by
  -- This is the owner-level codomain equality induced by the right-unital identity `id_comp`.
  simpa [stageSheafPullbackAlong] using
    congrArg (fun f : j ⟶ i ↦ stageSheafPullbackAlong S f) (Category.id_comp a)

/-- Helper for Lemma 7.18.3: the pushforward composition comparison does not depend on which proof
of `S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) = S.stageFunctor a` we use. -/
theorem stageSheafPushforwardComp_comp_id_proof_irrel
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    {p q : S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) = S.stageFunctor a} :
    Functor.sheafPushforwardContinuousComp'
        (eqToIso p)
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j) =
      Functor.sheafPushforwardContinuousComp'
        (eqToIso q)
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j) := by
  -- Equality proofs of the same functor identity are subsingletons, so the owner comparison is
  -- proof-irrelevant in this right-unital case.
  have hpq : p = q := Subsingleton.elim _ _
  subst hpq
  rfl

/-- Helper for Lemma 7.18.3: evaluating the target transport for the identity-stage branch at a
fixed stage object gives the explicit section-type equality induced by `Category.id_comp a`. -/
theorem stageSheafPullbackComp_comp_id_target_eq_app
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y : (S.stage j)ᵒᵖ) :
    (((stageSheafPullbackAlong S ((𝟙 j) ≫ a)).obj ℱ).obj.obj Y) =
      (((stageSheafPullbackAlong S a).obj ℱ).obj.obj Y) := by
  -- Evaluate the owner-level pullback target equality on the chosen stage object.
  simpa [stageSheafPullbackAlong] using
    congrArg (fun f : j ⟶ i ↦ ((stageSheafPullbackAlong S f).obj ℱ).obj.obj Y)
      (Category.id_comp a)

/-- Helper for Lemma 7.18.3: the pushforward-side right-unital comparison used to normalize the
evaluated identity branch. -/
noncomputable abbrev stageSheafPushforwardCompIdIso
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (S.stageFunctor (𝟙 j)).sheafPushforwardContinuous
        (Type u) (S.stageTopology j) (S.stageTopology j) ⋙
      (S.stageFunctor a).sheafPushforwardContinuous
        (Type u) (S.stageTopology i) (S.stageTopology j) ≅
    (S.stageFunctor a).sheafPushforwardContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j) :=
  Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (stageFunctor_id_eq_local S j))
        (Type u) (S.stageTopology j))
      ((S.stageFunctor a).sheafPushforwardContinuous
        (Type u) (S.stageTopology i) (S.stageTopology j)) ≪≫
    Functor.leftUnitor
      ((S.stageFunctor a).sheafPushforwardContinuous
        (Type u) (S.stageTopology i) (S.stageTopology j))

/-- Helper for Lemma 7.18.3: after evaluating the identity-branch target transport on a section,
the sheaf-level cast is exactly the explicit section-level cast coming from `Category.id_comp a`.
-/
theorem stageSheafPullbackComp_comp_id_section_cast
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y : (S.stage j)ᵒᵖ)
    (z : (((stageSheafPullbackAlong S ((𝟙 j) ≫ a)).obj ℱ).obj.obj Y)) :
    (let e : (stageSheafPullbackAlong S ((𝟙 j) ≫ a)).obj ℱ ⟶
          (stageSheafPullbackAlong S a).obj ℱ :=
        eqToHom (by
          simpa [stageSheafPullbackAlong] using
            congrArg
              (fun f : j ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
              (Category.id_comp a))
      ; ((e.1.app Y) z)) =
      eqToHom (stageSheafPullbackComp_comp_id_target_eq_app S a ℱ Y) z := by
  -- The sheaf-level `eqToHom` and the explicit section-level `eqToHom` come from the same
  -- equality proof after evaluating at `Y`, so proof irrelevance reduces the claim to reflexivity.
  let p : (stageSheafPullbackAlong S ((𝟙 j) ≫ a)).obj ℱ =
      (stageSheafPullbackAlong S a).obj ℱ := by
    simpa [stageSheafPullbackAlong] using
      congrArg
        (fun f : j ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
        (Category.id_comp a)
  have hp :
      congrArg
          (fun G : Sheaf (S.stageTopology j) (Type u) ↦ G.obj.obj Y) p =
        stageSheafPullbackComp_comp_id_target_eq_app S a ℱ Y := by
    apply Subsingleton.elim
  -- Route correction: isolate the remaining transport as a pure section cast before returning to
  -- the adjunction mate normalization.
  change (((eqToHom p).1.app Y) z) = eqToHom (stageSheafPullbackComp_comp_id_target_eq_app S a ℱ Y) z
  simpa [hp]

/-- Helper for Lemma 7.18.3: evaluating the standard right-unital adjunction comparison on a
fixed section gives the canonical right-unitor section map. -/
theorem stageSheafPullbackComp_comp_id_mate_eval
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y : (S.stage j)ᵒᵖ)
    (y :
      (((S.stageFunctor a).sheafPullback (Type u) (S.stageTopology i) (S.stageTopology j) ⋙
              (S.stageFunctor (𝟙 j)).sheafPullback (Type u)
                (S.stageTopology j) (S.stageTopology j)).obj
          ℱ).obj.obj
        Y) :
    (((Adjunction.leftAdjointCompIso
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology j))
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          (stageSheafPushforwardCompIdIso S a)).hom.app ℱ).1.app Y) y =
      (((Functor.isoWhiskerLeft (stageSheafPullbackAlong S a)
            (S.stageSheafPullbackIdIso (Type u) j) ≪≫
          Functor.rightUnitor (stageSheafPullbackAlong S a)).hom.app ℱ).1.app Y) y := by
  -- Evaluate the standard right-unital adjunction coherence before comparing section values.
  have hcomp :
      ((Adjunction.leftAdjointCompIso
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology j))
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          (stageSheafPushforwardCompIdIso S a)).hom.app ℱ) =
        ((Functor.isoWhiskerLeft (stageSheafPullbackAlong S a)
            (S.stageSheafPullbackIdIso (Type u) j) ≪≫
          Functor.rightUnitor (stageSheafPullbackAlong S a)).hom.app ℱ) := by
    exact congrArg (fun e ↦ e.hom.app ℱ) <|
      Adjunction.leftAdjointCompIso_comp_id
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology j) (S.stageTopology j))
        (stageSheafPushforwardCompIdIso S a)
        (Functor.sheafPushforwardContinuousId'
          (eqToIso (stageFunctor_id_eq_local S j))
          (Type u) (S.stageTopology j))
        rfl
  exact congrArg (fun f ↦ (f.1.app Y) y) hcomp

/-- Helper for Lemma 7.18.3: after evaluating on a section, the original identity-branch pullback
comparison agrees with the normalized right-unital comparison. -/
theorem stage_sheaf_pullback_comp_conjugate_inv_id
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    conjugateEquiv
        (((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology j))
        )
        ((S.stageFunctor ((𝟙 j) ≫ a)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        ((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).inv) =
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) =
              S.stageFunctor ((𝟙 j) ≫ a) from
            (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op (𝟙 j).op)).symm))
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j)).hom := by
  -- This is the owner-side description of `S.stageSheafPullbackCompIso` before any right-unital
  -- normalization is applied.
  ext ℱ Y y
  simp [CofilteredSiteDiagram.stageSheafPullbackCompIso]

/-- Helper for Lemma 7.18.3: before the right-unital cast is normalized, the forward identity
branch comparison is conjugate to the inverse owner pushforward comparison. -/
theorem stage_sheaf_pullback_comp_conjugate_hom_id
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    conjugateEquiv
        ((S.stageFunctor ((𝟙 j) ≫ a)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        (((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology j)))
        ((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom) =
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) =
              S.stageFunctor ((𝟙 j) ≫ a) from
            (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op (𝟙 j).op)).symm))
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j)).inv := by
  let adj :=
    ((S.stageFunctor a).sheafAdjunctionContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j)).comp
      ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
        (Type u) (S.stageTopology j) (S.stageTopology j))
  let adj_c :=
    (S.stageFunctor ((𝟙 j) ≫ a)).sheafAdjunctionContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j)
  let compIso :=
    Functor.sheafPushforwardContinuousComp'
      (eqToIso
        (show S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) =
            S.stageFunctor ((𝟙 j) ≫ a) from
          (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op (𝟙 j).op)).symm))
      (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j)
  -- Compose the forward and inverse conjugates; the inverse branch is already normalized by the
  -- previous helper, and the composite is the identity because `S.stageSheafPullbackCompIso` is an
  -- isomorphism.
  apply (cancel_mono compIso.hom).1
  have hcomp :=
    CategoryTheory.conjugateEquiv_comp adj_c adj adj_c
      ((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom)
      ((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).inv)
  simpa [adj, adj_c, compIso, stage_sheaf_pullback_comp_conjugate_inv_id, Category.assoc] using
    hcomp

/-- Helper for Lemma 7.18.3: the conjugate of an `eqToHom` between sheaf pullbacks along equal
continuous functors is the `eqToHom` between the pushforwards. -/
theorem conjugateEquiv_sheafPullback_eqToHom
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} (h : F = G)
    [F.IsContinuous J K] [G.IsContinuous J K]
    [∀ P : Cᵒᵖ ⥤ Type u, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ Type u, G.op.HasLeftKanExtension P]
    [HasWeakSheafify J (Type u)] [HasWeakSheafify K (Type u)]
    (hpull : F.sheafPullback (Type u) J K = G.sheafPullback (Type u) J K)
    (hpush : G.sheafPushforwardContinuous (Type u) J K =
      F.sheafPushforwardContinuous (Type u) J K) :
    conjugateEquiv (G.sheafAdjunctionContinuous (Type u) J K)
        (F.sheafAdjunctionContinuous (Type u) J K) (eqToHom hpull) =
      eqToHom hpush := by
  subst h
  rw [Subsingleton.elim hpull (rfl : _ = _), Subsingleton.elim hpush (rfl : _ = _),
    eqToHom_refl, eqToHom_refl, conjugateEquiv_id]

/-- Helper for Lemma 7.18.3: the pushforward comparison induced by an `eqToIso` is itself an
`eqToIso`. -/
theorem sheafPushforwardContinuousIso_eqToIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} (h : F = G)
    [F.IsContinuous J K] [G.IsContinuous J K]
    (hpush : F.sheafPushforwardContinuous (Type u) J K =
      G.sheafPushforwardContinuous (Type u) J K) :
    Functor.sheafPushforwardContinuousIso (eqToIso h) (Type u) J K = eqToIso hpush := by
  subst h
  rw [Subsingleton.elim hpush (rfl : _ = _)]
  apply Iso.ext
  ext ℱ Y y
  simp

/-- Helper for Lemma 7.18.3: the identity-branch pushforward functors along `(𝟙 j) ≫ a` and `a`
are equal. -/
theorem stageSheafPushforward_comp_id_push_eq
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (S.stageFunctor ((𝟙 j) ≫ a)).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j) =
      (S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j) := by
  exact congrArg
    (fun f : j ⟶ i => (S.stageFunctor f).sheafPushforwardContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j))
    (Category.id_comp a)

/-- Helper for Lemma 7.18.3: the right-unital pushforward comparison is the owner comparison for
the composite arrow followed by the pushforward-level transport. -/
theorem stageSheafPushforwardCompIdIso_eq_comp
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (stageSheafPushforwardCompIdIso S a) =
      Functor.sheafPushforwardContinuousComp'
          (eqToIso
            (show S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) =
                S.stageFunctor ((𝟙 j) ≫ a) from
              (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op (𝟙 j).op)).symm))
          (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j) ≪≫
        eqToIso (stageSheafPushforward_comp_id_push_eq S a) := by
  refine ((stageSheafPushforwardComp_comp_id S a).symm.trans
    (stageSheafPushforwardComp_comp_id_owner_normalize S a).symm).trans ?_
  exact congrArg
    (fun e => Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor a ⋙ S.stageFunctor (𝟙 j) =
              S.stageFunctor ((𝟙 j) ≫ a) from
            (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op (𝟙 j).op)).symm))
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology j) ≪≫ e)
    (sheafPushforwardContinuousIso_eqToIso
      (show S.stageFunctor ((𝟙 j) ≫ a) = S.stageFunctor a from by
        simpa [CofilteredSiteDiagram.stageFunctor] using
          congrArg Cat.Hom.toFunctor (Category.id_comp a))
      (stageSheafPushforward_comp_id_push_eq S a))

/-- Helper for Lemma 7.18.3: the sheaf-level normalization of the identity-branch pullback
comparison: composing with the target transport gives the right-unital comparison. -/
theorem stageSheafPullbackComp_comp_id_hom_normalize
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom ≫
        eqToHom (stageSheafPullbackComp_comp_id_target_eq S a) =
      (Adjunction.leftAdjointCompIso
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology j) (S.stageTopology j))
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        (stageSheafPushforwardCompIdIso S a)).hom := by
  set adj :=
    ((S.stageFunctor a).sheafAdjunctionContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j)).comp
      ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
        (Type u) (S.stageTopology j) (S.stageTopology j)) with hadj
  set adj_a :=
    (S.stageFunctor a).sheafAdjunctionContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j) with hadja
  set adj_c :=
    (S.stageFunctor ((𝟙 j) ≫ a)).sheafAdjunctionContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j) with hadjc
  apply (conjugateEquiv adj_a adj).injective
  have hsplit := (CategoryTheory.conjugateEquiv_comp adj_a adj_c adj
    (eqToHom (stageSheafPullbackComp_comp_id_target_eq S a))
    ((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom)).symm
  refine hsplit.trans ?_
  rw [stage_sheaf_pullback_comp_conjugate_hom_id,
    conjugateEquiv_sheafPullback_eqToHom
      (show S.stageFunctor ((𝟙 j) ≫ a) = S.stageFunctor a from by
        simpa [CofilteredSiteDiagram.stageFunctor] using
          congrArg Cat.Hom.toFunctor (Category.id_comp a))
      (stageSheafPullbackComp_comp_id_target_eq S a)
      (stageSheafPushforward_comp_id_push_eq S a).symm]
  have hrhs : conjugateEquiv adj_a adj
      (Adjunction.leftAdjointCompIso adj_a
        ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology j) (S.stageTopology j)) adj_a
        (stageSheafPushforwardCompIdIso S a)).hom =
      (stageSheafPushforwardCompIdIso S a).inv :=
    (conjugateEquiv adj_a adj).apply_symm_apply _
  refine Eq.trans ?_ hrhs.symm
  rw [stageSheafPushforwardCompIdIso_eq_comp S a]
  simp

/-- Helper for Lemma 7.18.3: after evaluating on a section, the original identity-branch pullback
comparison agrees with the normalized right-unital comparison. -/
theorem stageSheafPullbackComp_comp_id_cast_mate_eval
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y : (S.stage j)ᵒᵖ)
    (y :
      (((S.stageFunctor a).sheafPullback (Type u) (S.stageTopology i) (S.stageTopology j) ⋙
              (S.stageFunctor (𝟙 j)).sheafPullback (Type u)
                (S.stageTopology j) (S.stageTopology j)).obj
          ℱ).obj.obj
        Y) :
    eqToHom (stageSheafPullbackComp_comp_id_target_eq_app S a ℱ Y)
      ((((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ).1.app Y) y) =
      (((Adjunction.leftAdjointCompIso
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology j))
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          (stageSheafPushforwardCompIdIso S a)).hom.app ℱ).1.app Y) y := by
  have happ := congrArg (fun t => ((t.app ℱ).1.app Y) y)
    (stageSheafPullbackComp_comp_id_hom_normalize S a)
  refine Eq.trans ?_ happ
  -- The right side of `happ` evaluates the composite; identify the transport factor with the
  -- explicit section cast.
  have he : ((eqToHom (stageSheafPullbackComp_comp_id_target_eq S a) :
      stageSheafPullbackAlong S ((𝟙 j) ≫ a) ⟶ stageSheafPullbackAlong S a).app ℱ) =
      eqToHom (Functor.congr_obj (stageSheafPullbackComp_comp_id_target_eq S a) ℱ) :=
    eqToHom_app _ ℱ
  have hz :
      ((((eqToHom (stageSheafPullbackComp_comp_id_target_eq S a) :
          stageSheafPullbackAlong S ((𝟙 j) ≫ a) ⟶ stageSheafPullbackAlong S a).app ℱ).1.app Y)
        ((((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ).1.app Y) y)) =
      eqToHom (stageSheafPullbackComp_comp_id_target_eq_app S a ℱ Y)
        ((((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ).1.app Y) y) := by
    rw [he]
    exact stageSheafPullbackComp_comp_id_section_cast S a ℱ Y _
  exact hz.symm

/-- Helper for Lemma 7.18.3: after evaluating on a section, the original identity-branch pullback
comparison agrees with the normalized right-unital comparison. -/
theorem stageSheafPullbackComp_comp_id_eval_transport
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y : (S.stage j)ᵒᵖ)
    (y :
      (((S.stageFunctor a).sheafPullback (Type u) (S.stageTopology i) (S.stageTopology j) ⋙
              (S.stageFunctor (𝟙 j)).sheafPullback (Type u)
                (S.stageTopology j) (S.stageTopology j)).obj
          ℱ).obj.obj
        Y) :
    (((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ ≫
          eqToHom (by
            simpa [stageSheafPullbackAlong] using
              congrArg
                (fun f : j ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
                (Category.id_comp a))).1.app Y) y =
      (((Adjunction.leftAdjointCompIso
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology j))
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          (stageSheafPushforwardCompIdIso S a)).hom.app ℱ).1.app Y) y := by
  -- Route correction: the section-level cast is now separated from the mate calculation, so the
  -- remaining blocker is only the right-unital adjunction normalization.
  have hcast :
      (let e : (stageSheafPullbackAlong S ((𝟙 j) ≫ a)).obj ℱ ⟶
            (stageSheafPullbackAlong S a).obj ℱ :=
          eqToHom (by
            simpa [stageSheafPullbackAlong] using
              congrArg
                (fun f : j ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
                (Category.id_comp a))
        ; ((e.1.app Y)
          ((((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ).1.app Y) y))) =
        eqToHom (stageSheafPullbackComp_comp_id_target_eq_app S a ℱ Y)
          ((((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ).1.app Y) y) := by
    -- This is exactly the isolated section-cast adapter for the value produced by the pullback
    -- comparison.
    exact stageSheafPullbackComp_comp_id_section_cast
      (S := S) (a := a) (ℱ := ℱ) (Y := Y)
      (z := (((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ).1.app Y) y)
  -- First rewrite the remaining transport to the explicit section cast, then unfold the
  -- pullback-composition comparison and normalize the owner pushforward comparison.
  calc
    (((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ ≫
          eqToHom (by
            simpa [stageSheafPullbackAlong] using
              congrArg
                (fun f : j ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
                (Category.id_comp a))).1.app Y) y =
      eqToHom (stageSheafPullbackComp_comp_id_target_eq_app S a ℱ Y)
        ((((S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ).1.app Y) y) := by
          simpa using hcast
    _ =
      (((Adjunction.leftAdjointCompIso
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology j))
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          (stageSheafPushforwardCompIdIso S a)).hom.app ℱ).1.app Y) y := by
            exact stageSheafPullbackComp_comp_id_cast_mate_eval
              (S := S) (a := a) (ℱ := ℱ) (Y := Y) (y := y)

/-- Helper for Lemma 7.18.3: the stage pullback comparison for `a` followed by the identity-stage
pullback becomes the standard right-unital comparison once the target is transported along
`(𝟙 j) ≫ a = a`. -/
theorem stageSheafPullbackComp_comp_id_hom_app
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    ∀ ℱ : Sheaf (S.stageTopology i) (Type u),
      (S.stageSheafPullbackCompIso (Type u) a (𝟙 j)).hom.app ℱ ≫
          eqToHom (by
            simpa [stageSheafPullbackAlong] using
              congrArg
                (fun f : j ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
                (Category.id_comp a)) =
        ((Functor.isoWhiskerLeft (stageSheafPullbackAlong S a)
            (S.stageSheafPullbackIdIso (Type u) j) ≪≫
          Functor.rightUnitor (stageSheafPullbackAlong S a)).hom.app ℱ) := by
  intro ℱ
  -- Route correction: normalize the right-unital comparison only after evaluating on sections, so
  -- the last transport is the explicit `eqToHom` on the section type from `id_comp a`.
  ext Y y
  have hcomp :
      ((Adjunction.leftAdjointCompIso
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology j))
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          (stageSheafPushforwardCompIdIso S a)).hom.app ℱ) =
        ((Functor.isoWhiskerLeft (stageSheafPullbackAlong S a)
            (S.stageSheafPullbackIdIso (Type u) j) ≪≫
          Functor.rightUnitor (stageSheafPullbackAlong S a)).hom.app ℱ) := by
    -- This is the right-unital coherence transferred across the stage pullback adjunction.
    exact congrArg (fun e ↦ e.hom.app ℱ) <|
      Adjunction.leftAdjointCompIso_comp_id
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology j) (S.stageTopology j))
        (stageSheafPushforwardCompIdIso S a)
        (Functor.sheafPushforwardContinuousId'
          (eqToIso (stageFunctor_id_eq_local S j))
          (Type u) (S.stageTopology j))
        rfl
  -- Replace the normalized left-hand side by the standard right-unital pullback comparison.
  exact
    (stageSheafPullbackComp_comp_id_eval_transport
      (S := S) (a := a) (ℱ := ℱ) (Y := Y) (y := y)).trans <|
      congrArg (fun f ↦ (f.1.app Y) y) hcomp

/-- Helper for Lemma 7.18.3: the unit for the identity-stage pullback adjunction becomes the
identity after composing with the canonical identity pullback comparison. -/
theorem stageSheafPullbackId_unit_hom_app
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology i)).unit.app ℱ ≫
      ((S.stageFunctor (𝟙 i)).sheafPushforwardContinuous (Type u)
          (S.stageTopology i) (S.stageTopology i)).map
        ((S.stageSheafPullbackIdIso (Type u) i).hom.app ℱ) =
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (stageFunctor_id_eq_local S i))
        (Type u) (S.stageTopology i)).inv.app ℱ := by
  -- This is the mate formula for the identity-stage pullback comparison, before evaluating the
  -- identity pushforward isomorphism on sections.
  have h :=
    CategoryTheory.unit_conjugateEquiv
      CategoryTheory.Adjunction.id
      ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology i))
      ((S.stageSheafPullbackIdIso (Type u) i).hom)
      ℱ
  simpa [CofilteredSiteDiagram.stageSheafPullbackIdIso] using h.symm

/-- Helper for Lemma 7.18.3: evaluating the identity-stage transpose of the canonical pullback
comparison yields the canonical identity pushforward comparison on sections. -/
theorem identity_stage_adjunction_eval_normal_form
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (U : (S.stage i)ᵒᵖ) :
    ((((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology i)).homEquiv
        ℱ ℱ)
      ((S.stageSheafPullbackIdIso (Type u) i).hom.app ℱ)).1.app U =
      ((Functor.sheafPushforwardContinuousId'
        (eqToIso (stageFunctor_id_eq_local S i))
        (Type u) (S.stageTopology i)).inv.app ℱ).1.app U := by
  -- First normalize the identity mate as a sheaf morphism, and only then evaluate it on the
  -- chosen stage object.
  have hmate :
      (((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology i)).homEquiv
        ℱ ℱ)
      ((S.stageSheafPullbackIdIso (Type u) i).hom.app ℱ) =
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (stageFunctor_id_eq_local S i))
        (Type u) (S.stageTopology i)).inv.app ℱ := by
    simpa [Adjunction.homEquiv_unit] using
      stageSheafPullbackId_unit_hom_app (S := S) (i := i) (ℱ := ℱ)
  exact congrArg (fun f ↦ f.1.app U) hmate

/-- Helper for Lemma 7.18.3: the target transport in
`colimitSiteStagePullbackSectionMap_target_eq_id` is exactly the image under the section functor
of the identity-stage object equality on `S.overImage X A`. -/
theorem colimitSiteStagePullbackSectionMap_target_eq_id_eq_congrArg
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A =
      congrArg (((overStageSheafPullback S A).obj ℱ).obj.obj)
        (congrArg Opposite.op
          (congrArg
            (fun F : S.stage A.unop.left ⥤ S.stage A.unop.left ↦
              F.obj (S.overImage X A))
            (stageFunctor_id_eq_local S A.unop.left))) := by
  -- Both sides are equalities between the same section types, so proof irrelevance identifies
  -- them before we evaluate the resulting transport.
  apply Subsingleton.elim

/-- Helper for Lemma 7.18.3: after evaluating the identity-stage pushforward comparison on
sections, the remaining target transport is exactly the identity map on the section set. -/
theorem identity_stage_pushforward_inv_eval_comp_colimitSiteStagePullbackSection_transport
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    (((Functor.sheafPushforwardContinuousId'
          (eqToIso (stageFunctor_id_eq_local S A.unop.left))
          (Type u) (S.stageTopology A.unop.left)).inv.app
        ((overStageSheafPullback S A).obj ℱ)).1.app (op (S.overImage X A))) ≫
      eqToHom (colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A) =
        𝟙 (colimitSiteStagePullbackSectionValue S ℱ X A) := by
  -- Evaluate the owner-level identity comparison at the section object, then rewrite the target
  -- transport to the explicit object equality carried by `stageFunctor_id_eq_local`.
  let hop :
      Opposite.op ((S.stageFunctor (𝟙 A.unop.left)).obj (S.overImage X A)) =
        Opposite.op (S.overImage X A) :=
    congrArg Opposite.op
      (congrArg
        (fun F : S.stage A.unop.left ⥤ S.stage A.unop.left ↦
          F.obj (S.overImage X A))
        (stageFunctor_id_eq_local S A.unop.left))
  ext s
  rw [colimitSiteStagePullbackSectionMap_target_eq_id_eq_congrArg]
  -- The inverse identity pushforward comparison acts by `map (eqToHom hop.symm)`, and the
  -- postcomposed target transport is `eqToHom (congrArg _ hop)`.
  simp [Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, hop, CategoryTheory.eqToHom_map]
  simpa [hop, CategoryTheory.eqToHom_map] using
    (FunctorToTypes.eqToHom_map_comp_apply
      (F := ((((𝟭 (Sheaf (S.stageTopology A.unop.left) (Type u))).obj
          ((overStageSheafPullback S A).obj ℱ)).obj) :
        (S.stage A.unop.left)ᵒᵖ ⥤ Type u))
      (p := hop.symm) (q := hop) s)

theorem colimitSiteStagePullbackSectionMap_id
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    colimitSiteStagePullbackSectionMap S ℱ X (𝟙 A) = 𝟙 _ := by
  -- Route correction: the new helper isolates the easy `eqToHom` transport; the remaining blocker
  -- is the adjunction normalization turning the transpose into the identity section map.
  ext s
  dsimp [colimitSiteStagePullbackSectionMap, colimitSiteStagePullbackSectionTransition]
  -- Replace the target transport by the reflexive proof so the section computation becomes visible.
  have htarget :
      colimitSiteStagePullbackSectionMap_target_eq S ℱ X (𝟙 A) =
        colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A := by
    apply Subsingleton.elim
  rw [htarget]
  -- Rewrite the identity transition and then replace the adjunction transpose by its evaluated
  -- identity-stage normal form.
  have htransition :
      (S.stageSheafPullbackCompIso (Type u) A.unop.hom (𝟙 A.unop.left)).hom.app ℱ ≫
          eqToHom (by
            simpa [overStageSheafPullback] using
              congrArg
                (fun f : A.unop.left ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
                (Category.id_comp A.unop.hom)) =
        ((Functor.isoWhiskerLeft (stageSheafPullbackAlong S A.unop.hom)
            (S.stageSheafPullbackIdIso (Type u) A.unop.left) ≪≫
          Functor.rightUnitor (stageSheafPullbackAlong S A.unop.hom)).hom.app ℱ) := by
    -- This is the app-level right-unital comparison for the stage pullback route indexed by `A`.
    simpa [overStageSheafPullback] using
      stageSheafPullbackComp_comp_id_hom_app (S := S) (a := A.unop.hom) (ℱ := ℱ)
  have htransition_eval :
      (((((S.stageFunctor (overLeftHom (𝟙 A))).sheafAdjunctionContinuous (Type u)
                (S.stageTopology A.unop.left) (S.stageTopology A.unop.left)).homEquiv
              ((overStageSheafPullback S A).obj ℱ) ((overStageSheafPullback S A).obj ℱ))
            ((S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom (𝟙 A))).hom.app ℱ ≫
              eqToHom (by
                simpa [overLeftHom, overStageSheafPullback] using
                  congrArg
                    (fun f : A.unop.left ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
                    (Category.id_comp A.unop.hom)))).1.app
            (op (S.overImage X A)) ≫
          eqToHom (colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A)) s =
      (((((S.stageFunctor (𝟙 A.unop.left)).sheafAdjunctionContinuous (Type u)
              (S.stageTopology A.unop.left) (S.stageTopology A.unop.left)).homEquiv
            ((overStageSheafPullback S A).obj ℱ) ((overStageSheafPullback S A).obj ℱ))
          ((S.stageSheafPullbackIdIso (Type u) A.unop.left).hom.app
            ((overStageSheafPullback S A).obj ℱ))).1.app
          (op (S.overImage X A)) ≫
        eqToHom (colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A)) s := by
    -- Push the app-level comparison through the identity-stage adjunction equivalence and then
    -- evaluate it on the chosen section.
    simpa [overLeftHom, overStageSheafPullback, stageSheafPullbackAlong,
      Functor.isoWhiskerLeft_hom, Functor.rightUnitor_hom_app] using
      congrArg
        (fun f ↦
          (((((S.stageFunctor (overLeftHom (𝟙 A))).sheafAdjunctionContinuous (Type u)
                  (S.stageTopology A.unop.left) (S.stageTopology A.unop.left)).homEquiv
                ((overStageSheafPullback S A).obj ℱ) ((overStageSheafPullback S A).obj ℱ))
              f).1.app (op (S.overImage X A)) ≫
            eqToHom (colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A)) s)
        htransition
  have happ :
      ((((S.stageFunctor (𝟙 A.unop.left)).sheafAdjunctionContinuous (Type u)
              (S.stageTopology A.unop.left) (S.stageTopology A.unop.left)).homEquiv
            ((overStageSheafPullback S A).obj ℱ) ((overStageSheafPullback S A).obj ℱ))
          ((S.stageSheafPullbackIdIso (Type u) A.unop.left).hom.app
            ((overStageSheafPullback S A).obj ℱ))).1.app
          (op (S.overImage X A)) ≫
        eqToHom (colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A) =
      (((Functor.sheafPushforwardContinuousId'
            (eqToIso (stageFunctor_id_eq_local S A.unop.left))
            (Type u) (S.stageTopology A.unop.left)).inv.app
          ((overStageSheafPullback S A).obj ℱ)).1.app (op (S.overImage X A))) ≫
        eqToHom (colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A) := by
    -- Postcompose the evaluated adjunction normal form with the fixed target transport.
    exact congrArg
      (fun f ↦ f ≫ eqToHom (colimitSiteStagePullbackSectionMap_target_eq_id S ℱ X A))
      (identity_stage_adjunction_eval_normal_form (S := S)
        (i := A.unop.left) (ℱ := (overStageSheafPullback S A).obj ℱ)
        (U := op (S.overImage X A)))
  -- The remaining composite is the explicit section-level transport bridge proved above.
  exact htransition_eval.trans <|
    (congrArg (fun f ↦ f s) happ).trans <|
      congrArg (fun f ↦ f s)
        (identity_stage_pushforward_inv_eval_comp_colimitSiteStagePullbackSection_transport
          (S := S) (ℱ := ℱ) (X := X) A)

/-- Helper for Lemma 7.18.3: transposing after precomposition with a left-adjoint comparison is
postcomposition with its conjugate. -/
theorem homEquiv_conjugateEquiv_exchange
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (τ : L₂ ⟶ L₁) {X : C} {Y : D} (f : L₁.obj X ⟶ Y) :
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

/-- Helper for Lemma 7.18.3: the conjugate of the stage pullback composition comparison is the
inverse owner pushforward comparison, for an arbitrary composable pair. -/
theorem stage_sheaf_pullback_comp_conjugate_hom
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    conjugateEquiv
        ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology k))
        (((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j)).comp
          ((S.stageFunctor b).sheafAdjunctionContinuous
            (Type u) (S.stageTopology j) (S.stageTopology k)))
        ((S.stageSheafPullbackCompIso (Type u) a b).hom) =
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a b)).symm
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- Helper for Lemma 7.18.3: chains of section casts between equal types collapse. -/
theorem eqToHom_apply_collapse₃₂ {A B C D E : Type u}
    (p₁ : A = B) (p₂ : B = C) (p₃ : C = D) (q₁ : A = E) (q₂ : E = D) (y : A) :
    eqToHom p₃ (eqToHom p₂ (eqToHom p₁ y)) = eqToHom q₂ (eqToHom q₁ y) := by
  subst p₁; subst p₂; subst p₃; subst q₁
  rfl

/-- Helper for Lemma 7.18.3: a section cast does not depend on the equality proof. -/
theorem eqToHom_apply_irrel {A B : Type u} (p q : A = B) (x : A) :
    eqToHom p x = eqToHom q x := by
  subst p
  rfl

/-- Helper for Lemma 7.18.3: two double chains of section casts with common endpoints agree. -/
theorem eqToHom_apply_collapse₂₂ {A B C E : Type u}
    (p₁ : A = B) (p₂ : B = C) (q₁ : A = E) (q₂ : E = C) (y : A) :
    eqToHom p₂ (eqToHom p₁ y) = eqToHom q₂ (eqToHom q₁ y) := by
  subst p₁; subst p₂; subst q₁
  rfl

/-- Helper for Lemma 7.18.3: a triple chain of section casts collapses to a single cast. -/
theorem eqToHom_apply_collapse₃₁ {A B C D : Type u}
    (p₁ : A = B) (p₂ : B = C) (p₃ : C = D) (q : A = D) (x : A) :
    eqToHom p₃ (eqToHom p₂ (eqToHom p₁ x)) = eqToHom q x := by
  subst p₁; subst p₂; subst p₃
  rfl

/-- Helper for Lemma 7.18.3: the pushforward comparison isomorphisms satisfy the associativity
coherence required by `Adjunction.leftAdjointCompIso_assoc`. -/
theorem stageSheafPushforward_comp_coherence
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k l : S.I}
    (a : j ⟶ i) (b : k ⟶ j) (c : l ⟶ k)
    (hpush : (S.stageFunctor (c ≫ b ≫ a)).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology l) =
      (S.stageFunctor ((c ≫ b) ≫ a)).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology l)) :
    Functor.isoWhiskerLeft
        ((S.stageFunctor c).sheafPushforwardContinuous (Type u)
          (S.stageTopology k) (S.stageTopology l))
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a b)).symm
          (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)) ≪≫
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S (b ≫ a) c)).symm
        (Type u) (S.stageTopology i) (S.stageTopology k) (S.stageTopology l) ≪≫
        eqToIso hpush) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S b c)).symm
            (Type u) (S.stageTopology j) (S.stageTopology k) (S.stageTopology l))
          ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)) ≪≫
        Functor.sheafPushforwardContinuousComp'
          (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a (c ≫ b))).symm
          (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology l) := by
  apply Iso.ext
  ext ℱ Y y
  simp [CategoryTheory.eqToHom_map, eqToHom_app]
  exact eqToHom_apply_collapse₃₂ _ _ _ _ _ y

/-- Helper for Lemma 7.18.3: the assoc-normalized composite comparison is the canonical one
followed by the transport along associativity of the arrows. -/
theorem stageSheafPullbackCompIso_assoc_norm
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k l : S.I}
    (a : j ⟶ i) (b : k ⟶ j) (c : l ⟶ k)
    (hpush : (S.stageFunctor (c ≫ b ≫ a)).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology l) =
      (S.stageFunctor ((c ≫ b) ≫ a)).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology l))
    (hpull : stageSheafPullbackAlong S (c ≫ b ≫ a) =
      stageSheafPullbackAlong S ((c ≫ b) ≫ a)) :
    (Adjunction.leftAdjointCompIso
        ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology k))
        ((S.stageFunctor c).sheafAdjunctionContinuous (Type u)
          (S.stageTopology k) (S.stageTopology l))
        ((S.stageFunctor ((c ≫ b) ≫ a)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology l))
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S (b ≫ a) c)).symm
          (Type u) (S.stageTopology i) (S.stageTopology k) (S.stageTopology l) ≪≫
          eqToIso hpush)).hom =
      (S.stageSheafPullbackCompIso (Type u) (b ≫ a) c).hom ≫ eqToHom hpull := by
  set adj_comp :=
    ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology k)).comp
      ((S.stageFunctor c).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) (S.stageTopology l)) with hadjcomp
  set adj_t :=
    (S.stageFunctor ((c ≫ b) ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology l) with hadjt
  set adj_m :=
    (S.stageFunctor (c ≫ b ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology l) with hadjm
  apply (conjugateEquiv adj_t adj_comp).injective
  have hLHS : conjugateEquiv adj_t adj_comp
      (Adjunction.leftAdjointCompIso _ _ adj_t
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S (b ≫ a) c)).symm
          (Type u) (S.stageTopology i) (S.stageTopology k) (S.stageTopology l) ≪≫
          eqToIso hpush)).hom =
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S (b ≫ a) c)).symm
        (Type u) (S.stageTopology i) (S.stageTopology k) (S.stageTopology l) ≪≫
        eqToIso hpush).inv :=
    (conjugateEquiv adj_t adj_comp).apply_symm_apply _
  refine hLHS.trans ?_
  have hsplit := CategoryTheory.conjugateEquiv_comp adj_t adj_m adj_comp
    (eqToHom hpull)
    ((S.stageSheafPullbackCompIso (Type u) (b ≫ a) c).hom)
  refine Eq.trans ?_ hsplit
  rw [stage_sheaf_pullback_comp_conjugate_hom,
    conjugateEquiv_sheafPullback_eqToHom
      (show S.stageFunctor (c ≫ b ≫ a) = S.stageFunctor ((c ≫ b) ≫ a) from
        congrArg (fun f : l ⟶ i => S.stageFunctor f) (Category.assoc c b a).symm)
      hpull hpush.symm]
  simp

/-- Helper for Lemma 7.18.3: the cocycle identity for the stage pullback composition
comparisons, evaluated on a sheaf. -/
theorem stageSheafPullbackCompIso_assoc_app
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k l : S.I}
    (a : j ⟶ i) (b : k ⟶ j) (c : l ⟶ k) (ℱ : Sheaf (S.stageTopology i) (Type u))
    (hpull : stageSheafPullbackAlong S (c ≫ b ≫ a) =
      stageSheafPullbackAlong S ((c ≫ b) ≫ a)) :
    (S.stageSheafPullbackCompIso (Type u) b c).hom.app
        ((stageSheafPullbackAlong S a).obj ℱ) ≫
      (S.stageSheafPullbackCompIso (Type u) a (c ≫ b)).hom.app ℱ =
    ((S.stageFunctor c).sheafPullback (Type u) (S.stageTopology k) (S.stageTopology l)).map
        ((S.stageSheafPullbackCompIso (Type u) a b).hom.app ℱ) ≫
      (S.stageSheafPullbackCompIso (Type u) (b ≫ a) c).hom.app ℱ ≫
      (eqToHom hpull).app ℱ := by
  have hpush : (S.stageFunctor (c ≫ b ≫ a)).sheafPushforwardContinuous (Type u)
      (S.stageTopology i) (S.stageTopology l) =
    (S.stageFunctor ((c ≫ b) ≫ a)).sheafPushforwardContinuous (Type u)
      (S.stageTopology i) (S.stageTopology l) :=
    congrArg (fun f : l ⟶ i => (S.stageFunctor f).sheafPushforwardContinuous (Type u)
      (S.stageTopology i) (S.stageTopology l)) (Category.assoc c b a).symm
  have hassoc := Adjunction.leftAdjointCompIso_assoc
    ((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j))
    ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k))
    ((S.stageFunctor c).sheafAdjunctionContinuous (Type u)
      (S.stageTopology k) (S.stageTopology l))
    ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology k))
    ((S.stageFunctor (c ≫ b)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology l))
    ((S.stageFunctor ((c ≫ b) ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology l))
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a b)).symm
      (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k))
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S b c)).symm
      (Type u) (S.stageTopology j) (S.stageTopology k) (S.stageTopology l))
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a (c ≫ b))).symm
      (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology l))
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S (b ≫ a) c)).symm
      (Type u) (S.stageTopology i) (S.stageTopology k) (S.stageTopology l) ≪≫
      eqToIso hpush)
    (stageSheafPushforward_comp_coherence S a b c hpush)
  have happ := congrArg (fun t => t.hom.app ℱ) hassoc
  have hnorm := congrArg (fun t => t.app ℱ)
    (stageSheafPullbackCompIso_assoc_norm S a b c hpush hpull)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.associator_inv_app,
    Category.id_comp] at happ hnorm
  dsimp only [Functor.whiskerLeft, Functor.whiskerRight] at happ
  refine happ.trans ?_
  rw [hnorm]
  simp [CofilteredSiteDiagram.stageSheafPullbackCompIso]

/-- Helper for Lemma 7.18.3: a transport along a reflexive object equality is the identity. -/
theorem eqToHom_self_id {C : Type*} [Category C] {X : C} (h : X = X) :
    eqToHom h = 𝟙 X := by
  rw [Subsingleton.elim h (rfl : X = X), eqToHom_refl]

/-- Helper for Lemma 7.18.3: the cocycle identity for the transition comparisons, with the
`Over.w` target normalizations attached. -/
theorem colimitSiteStagePullbackSection_cocycle_core
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u))
    {j k l : S.I} (a : j ⟶ i) (p : k ⟶ j) (q : l ⟶ k) {hB : k ⟶ i} {hC : l ⟶ i}
    (hpB : p ≫ a = hB) (hqC : q ≫ hB = hC)
    (h'u : (stageSheafPullbackAlong S (p ≫ a)).obj ℱ =
      (stageSheafPullbackAlong S hB).obj ℱ)
    (h'v : (stageSheafPullbackAlong S (q ≫ hB)).obj ℱ =
      (stageSheafPullbackAlong S hC).obj ℱ)
    (h'w : (stageSheafPullbackAlong S ((q ≫ p) ≫ a)).obj ℱ =
      (stageSheafPullbackAlong S hC).obj ℱ) :
    (S.stageSheafPullbackCompIso (Type u) p q).hom.app
        ((stageSheafPullbackAlong S a).obj ℱ) ≫
      (S.stageSheafPullbackCompIso (Type u) a (q ≫ p)).hom.app ℱ ≫ eqToHom h'w =
    ((S.stageFunctor q).sheafPullback (Type u)
        (S.stageTopology k) (S.stageTopology l)).map
        ((S.stageSheafPullbackCompIso (Type u) a p).hom.app ℱ ≫ eqToHom h'u) ≫
      (S.stageSheafPullbackCompIso (Type u) hB q).hom.app ℱ ≫ eqToHom h'v := by
  subst hpB
  subst hqC
  rw [Subsingleton.elim h'u (rfl : _ = _), Subsingleton.elim h'v (rfl : _ = _),
    eqToHom_refl, eqToHom_refl, Category.comp_id, Category.comp_id]
  have hpull : stageSheafPullbackAlong S (q ≫ p ≫ a) =
      stageSheafPullbackAlong S ((q ≫ p) ≫ a) :=
    congrArg (fun f : l ⟶ i => stageSheafPullbackAlong S f) (Category.assoc q p a).symm
  have hassoc := stageSheafPullbackCompIso_assoc_app S a p q ℱ hpull
  calc (S.stageSheafPullbackCompIso (Type u) p q).hom.app
        ((stageSheafPullbackAlong S a).obj ℱ) ≫
      (S.stageSheafPullbackCompIso (Type u) a (q ≫ p)).hom.app ℱ ≫ eqToHom h'w
      = ((S.stageSheafPullbackCompIso (Type u) p q).hom.app
          ((stageSheafPullbackAlong S a).obj ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) a (q ≫ p)).hom.app ℱ) ≫ eqToHom h'w :=
        (Category.assoc
          ((S.stageSheafPullbackCompIso (Type u) p q).hom.app
            ((stageSheafPullbackAlong S a).obj ℱ))
          ((S.stageSheafPullbackCompIso (Type u) a (q ≫ p)).hom.app ℱ)
          (eqToHom h'w)).symm
    _ = (((S.stageFunctor q).sheafPullback (Type u)
          (S.stageTopology k) (S.stageTopology l)).map
          ((S.stageSheafPullbackCompIso (Type u) a p).hom.app ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) (p ≫ a) q).hom.app ℱ ≫
        (eqToHom hpull).app ℱ) ≫ eqToHom h'w :=
        congrArg (fun t => t ≫ eqToHom h'w) hassoc
    _ = ((S.stageFunctor q).sheafPullback (Type u)
          (S.stageTopology k) (S.stageTopology l)).map
          ((S.stageSheafPullbackCompIso (Type u) a p).hom.app ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) (p ≫ a) q).hom.app ℱ ≫
        ((eqToHom hpull).app ℱ ≫ eqToHom h'w) := by
        simp only [Category.assoc]
    _ = ((S.stageFunctor q).sheafPullback (Type u)
          (S.stageTopology k) (S.stageTopology l)).map
          ((S.stageSheafPullbackCompIso (Type u) a p).hom.app ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) (p ≫ a) q).hom.app ℱ ≫ 𝟙 _ := by
        refine congrArg (fun t => ((S.stageFunctor q).sheafPullback (Type u)
          (S.stageTopology k) (S.stageTopology l)).map
          ((S.stageSheafPullbackCompIso (Type u) a p).hom.app ℱ) ≫
          (S.stageSheafPullbackCompIso (Type u) (p ≫ a) q).hom.app ℱ ≫ t) ?_
        rw [eqToHom_app, eqToHom_trans]
        exact eqToHom_self_id _
    _ = ((S.stageFunctor q).sheafPullback (Type u)
          (S.stageTopology k) (S.stageTopology l)).map
          ((S.stageSheafPullbackCompIso (Type u) a p).hom.app ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) (p ≫ a) q).hom.app ℱ := by
        rw [Category.comp_id]

/-- Helper for Lemma 7.18.3: transporting the left functor of a stage pullback composition
comparison along an equality of arrows. -/
theorem stageSheafPullbackCompIso_congr_left
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k : S.I} {f g : j ⟶ i} (hfg : f = g)
    (b : k ⟶ j) (ℱ : Sheaf (S.stageTopology i) (Type u))
    (h₁ : (stageSheafPullbackAlong S f).obj ℱ = (stageSheafPullbackAlong S g).obj ℱ)
    (h₂ : (stageSheafPullbackAlong S (b ≫ f)).obj ℱ =
      (stageSheafPullbackAlong S (b ≫ g)).obj ℱ) :
    (S.stageSheafPullbackCompIso (Type u) f b).hom.app ℱ ≫ eqToHom h₂ =
      ((S.stageFunctor b).sheafPullback (Type u)
          (S.stageTopology j) (S.stageTopology k)).map (eqToHom h₁) ≫
        (S.stageSheafPullbackCompIso (Type u) g b).hom.app ℱ := by
  subst hfg
  rw [Subsingleton.elim h₁ (rfl : _ = _), Subsingleton.elim h₂ (rfl : _ = _)]
  simp

/-- Helper for Lemma 7.18.3: the sheaf-level cocycle for the transition comparisons. -/
theorem colimitSiteStagePullbackSectionTransition_comp
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u))
    {A B C : (Over i)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ C) :
    colimitSiteStagePullbackSectionTransition S ℱ (u ≫ v) =
      colimitSiteStagePullbackSectionTransition S ℱ u ≫
        ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous (Type u)
          (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).map
          (colimitSiteStagePullbackSectionTransition S ℱ v) ≫
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S
            (overLeftHom u) (overLeftHom v))).symm
          (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
          (S.stageTopology C.unop.left)).hom.app
          ((overStageSheafPullback S C).obj ℱ) := by
  -- Notation for the three adjunctions and the comparison arguments.
  have hwB : overLeftHom u ≫ A.unop.hom = B.unop.hom := by simpa using Over.w u.unop
  have hwC : overLeftHom v ≫ B.unop.hom = C.unop.hom := by simpa using Over.w v.unop
  have h'u : (stageSheafPullbackAlong S (overLeftHom u ≫ A.unop.hom)).obj ℱ =
      (overStageSheafPullback S B).obj ℱ := by
    simpa [overStageSheafPullback] using
      congrArg (fun f : B.unop.left ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ) hwB
  have h'v : (stageSheafPullbackAlong S (overLeftHom v ≫ B.unop.hom)).obj ℱ =
      (overStageSheafPullback S C).obj ℱ := by
    simpa [overStageSheafPullback] using
      congrArg (fun f : C.unop.left ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ) hwC
  have h'w : (stageSheafPullbackAlong S
      ((overLeftHom v ≫ overLeftHom u) ≫ A.unop.hom)).obj ℱ =
      (overStageSheafPullback S C).obj ℱ := by
    have hcomp : (overLeftHom v ≫ overLeftHom u) ≫ A.unop.hom = C.unop.hom := by
      rw [Category.assoc, hwB]
      exact hwC
    simpa [overStageSheafPullback] using
      congrArg (fun f : C.unop.left ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ) hcomp
  -- Definitional descriptions of the three transitions.
  have hformw : colimitSiteStagePullbackSectionTransition S ℱ (u ≫ v) =
      (((S.stageFunctor (overLeftHom v ≫ overLeftHom u)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology C.unop.left)).homEquiv
        ((overStageSheafPullback S A).obj ℱ) ((overStageSheafPullback S C).obj ℱ))
        ((S.stageSheafPullbackCompIso (Type u) A.unop.hom
          (overLeftHom v ≫ overLeftHom u)).hom.app ℱ ≫ eqToHom h'w) := rfl
  have hformu : colimitSiteStagePullbackSectionTransition S ℱ u =
      (((S.stageFunctor (overLeftHom u)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
        ((overStageSheafPullback S A).obj ℱ) ((overStageSheafPullback S B).obj ℱ))
        ((S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ ≫
          eqToHom h'u) := rfl
  have hformv : colimitSiteStagePullbackSectionTransition S ℱ v =
      (((S.stageFunctor (overLeftHom v)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).homEquiv
        ((overStageSheafPullback S B).obj ℱ) ((overStageSheafPullback S C).obj ℱ))
        ((S.stageSheafPullbackCompIso (Type u) B.unop.hom (overLeftHom v)).hom.app ℱ ≫
          eqToHom h'v) := rfl
  rw [hformw, hformu, hformv]
  set ep := ((S.stageFunctor (overLeftHom u)).sheafAdjunctionContinuous (Type u)
    (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)) with hep
  set eq' := ((S.stageFunctor (overLeftHom v)).sheafAdjunctionContinuous (Type u)
    (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)) with heq'
  set ew := ((S.stageFunctor (overLeftHom v ≫ overLeftHom u)).sheafAdjunctionContinuous (Type u)
    (S.stageTopology A.unop.left) (S.stageTopology C.unop.left)) with hew
  set K := (Functor.sheafPushforwardContinuousComp'
    (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S
      (overLeftHom u) (overLeftHom v))).symm
    (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
    (S.stageTopology C.unop.left)) with hK
  set αu := ((S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ ≫
    eqToHom h'u) with hαu
  set αv := ((S.stageSheafPullbackCompIso (Type u) B.unop.hom (overLeftHom v)).hom.app ℱ ≫
    eqToHom h'v) with hαv
  set αw := ((S.stageSheafPullbackCompIso (Type u) A.unop.hom
    (overLeftHom v ≫ overLeftHom u)).hom.app ℱ ≫ eqToHom h'w) with hαw
  -- the transpose-composition normalizations
  have h1 : (ep.homEquiv ((overStageSheafPullback S A).obj ℱ)
        ((overStageSheafPullback S B).obj ℱ)) αu ≫
      ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).map
        ((eq'.homEquiv ((overStageSheafPullback S B).obj ℱ)
          ((overStageSheafPullback S C).obj ℱ)) αv) =
      (ep.homEquiv _ _) (αu ≫ (eq'.homEquiv _ _) αv) :=
    (Adjunction.homEquiv_naturality_right _ _ _).symm
  have h2 : αu ≫ (eq'.homEquiv ((overStageSheafPullback S B).obj ℱ)
        ((overStageSheafPullback S C).obj ℱ)) αv =
      (eq'.homEquiv _ _) (((S.stageFunctor (overLeftHom v)).sheafPullback (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).map αu ≫ αv) :=
    (Adjunction.homEquiv_naturality_left _ _ _).symm
  have h3 : ∀ γ : ((S.stageFunctor (overLeftHom u)).sheafPullback (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left) ⋙
      (S.stageFunctor (overLeftHom v)).sheafPullback (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
        ((overStageSheafPullback S A).obj ℱ) ⟶ (overStageSheafPullback S C).obj ℱ,
      ((ep.comp eq').homEquiv ((overStageSheafPullback S A).obj ℱ)
        ((overStageSheafPullback S C).obj ℱ)) γ =
      (ep.homEquiv _ _) ((eq'.homEquiv _ _) γ) := by
    intro γ
    rw [Adjunction.comp_homEquiv]
    rfl
  have hcore := colimitSiteStagePullbackSection_cocycle_core S ℱ
    A.unop.hom (overLeftHom u) (overLeftHom v) hwB hwC h'u h'v h'w
  have hex := homEquiv_conjugateEquiv_exchange ew (ep.comp eq')
    ((S.stageSheafPullbackCompIso (Type u) (overLeftHom u) (overLeftHom v)).hom) αw
  rw [hep, heq', stage_sheaf_pullback_comp_conjugate_hom] at hex
  -- assemble
  refine Eq.symm ?_
  have hA : ((ep.homEquiv _ _) αu ≫ _ ≫ K.hom.app ((overStageSheafPullback S C).obj ℱ)) =
      (((ep.homEquiv _ _) αu ≫ ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous
        (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).map
        ((eq'.homEquiv _ _) αv)) ≫ K.hom.app ((overStageSheafPullback S C).obj ℱ)) :=
    (Category.assoc _ _ _).symm
  refine hA.trans ?_
  have hB : (((ep.homEquiv _ _) αu ≫ ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous
        (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).map
        ((eq'.homEquiv _ _) αv)) ≫ K.hom.app ((overStageSheafPullback S C).obj ℱ)) =
      (((ep.comp eq').homEquiv _ _) (((S.stageFunctor (overLeftHom v)).sheafPullback (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).map αu ≫ αv) ≫
        K.hom.app ((overStageSheafPullback S C).obj ℱ)) := by
    refine congrArg (fun t => t ≫ K.hom.app ((overStageSheafPullback S C).obj ℱ)) ?_
    exact h1.trans ((congrArg (fun t => (ep.homEquiv _ _) t) h2).trans (h3 _).symm)
  refine hB.trans ?_
  have hC : (((ep.comp eq').homEquiv _ _) (((S.stageFunctor (overLeftHom v)).sheafPullback
        (Type u) (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).map αu ≫ αv) ≫
        K.hom.app ((overStageSheafPullback S C).obj ℱ)) =
      (((ep.comp eq').homEquiv _ _)
        ((S.stageSheafPullbackCompIso (Type u) (overLeftHom u) (overLeftHom v)).hom.app
          ((overStageSheafPullback S A).obj ℱ) ≫ αw) ≫
        K.hom.app ((overStageSheafPullback S C).obj ℱ)) := by
    refine congrArg (fun t => ((ep.comp eq').homEquiv _ _) t ≫
      K.hom.app ((overStageSheafPullback S C).obj ℱ)) ?_
    exact hcore.symm
  refine hC.trans ?_
  have hD := congrArg (fun t => t ≫ K.hom.app ((overStageSheafPullback S C).obj ℱ)) hex
  refine hD.trans ?_
  rw [hK]
  simp only [Category.assoc]
  refine Eq.trans (congrArg
    (fun t => (ew.homEquiv _ ((overStageSheafPullback S C).obj ℱ)) αw ≫ t)
    (Iso.inv_hom_id_app _ _)) ?_
  simp only [Category.comp_id]
  rfl

theorem colimitSiteStagePullbackSectionMap_comp
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B C : (Over i)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ C) :
    colimitSiteStagePullbackSectionMap S ℱ X (u ≫ v) =
      colimitSiteStagePullbackSectionMap S ℱ X u ≫
        colimitSiteStagePullbackSectionMap S ℱ X v := by
  have hcocycle := colimitSiteStagePullbackSectionTransition_comp S ℱ u v
  -- the image object identification used by the target transports
  have hobj : (S.stageFunctor (overLeftHom u)).obj (S.overImage X A) = S.overImage X B := by
    have hcomp :
        S.stageFunctor A.unop.hom ⋙ S.stageFunctor (overLeftHom u) =
          S.stageFunctor (overLeftHom u ≫ A.unop.hom) :=
      congrArg Cat.Hom.toFunctor
        (S.diagram.map_comp A.unop.hom.op (overLeftHom u).op).symm
    have h₁ : (S.stageFunctor (overLeftHom u)).obj (S.overImage X A) =
        (S.stageFunctor (overLeftHom u ≫ A.unop.hom)).obj X := by
      simpa [CofilteredSiteDiagram.overImage] using
        congrArg (fun F : S.stage i ⥤ S.stage B.unop.left ↦ F.obj X) hcomp
    have hw : overLeftHom u ≫ A.unop.hom = B.unop.hom := by simpa using Over.w u.unop
    have h₂ : (S.stageFunctor (overLeftHom u ≫ A.unop.hom)).obj X = S.overImage X B := by
      simpa [CofilteredSiteDiagram.overImage] using
        congrArg (fun a : B.unop.left ⟶ i ↦ (S.stageFunctor a).obj X) hw
    exact h₁.trans h₂
  funext s
  -- evaluate the cocycle on the section
  have happ := congrArg
    (fun t => eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X (u ≫ v))
      ((t.1.app (op (S.overImage X A))) s)) hcocycle
  refine happ.trans ?_
  -- the right side is a composite of casts around the two transition evaluations
  -- naturality transport for the second transition across the image identification
  have h₁ : (((overStageSheafPullback S B).obj ℱ).obj.obj
      (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) =
      (((overStageSheafPullback S B).obj ℱ).obj.obj (op (S.overImage X B))) :=
    congrArg (fun Z => ((overStageSheafPullback S B).obj ℱ).obj.obj (op Z)) hobj
  have h₂ : ((((S.stageFunctor (overLeftHom v)).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
      ((overStageSheafPullback S C).obj ℱ)).obj.obj (op (S.overImage X B))) =
      ((((S.stageFunctor (overLeftHom v)).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
      ((overStageSheafPullback S C).obj ℱ)).obj.obj
      (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) :=
    congrArg (fun Z => (((S.stageFunctor (overLeftHom v)).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
      ((overStageSheafPullback S C).obj ℱ)).obj.obj (op Z)) hobj.symm
  have hcongr : (colimitSiteStagePullbackSectionTransition S ℱ v).1.app
      (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A))) =
      eqToHom h₁ ≫ (colimitSiteStagePullbackSectionTransition S ℱ v).1.app
        (op (S.overImage X B)) ≫ eqToHom h₂ := by
    have := NatTrans.congr
      (colimitSiteStagePullbackSectionTransition S ℱ v).1 (congrArg op hobj)
    simpa [eqToHom_map] using this
  -- Pass to the element form: composition and evaluation in `Type u` are definitional.
  change eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X (u ≫ v))
    (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S
        (overLeftHom u) (overLeftHom v))).symm
      (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
      (S.stageTopology C.unop.left)).hom.app
      ((overStageSheafPullback S C).obj ℱ)).1.app (op (S.overImage X A))
      ((colimitSiteStagePullbackSectionTransition S ℱ v).1.app
        (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))
        ((colimitSiteStagePullbackSectionTransition S ℱ u).1.app
          (op (S.overImage X A)) s))) =
    eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X v)
      ((colimitSiteStagePullbackSectionTransition S ℱ v).1.app (op (S.overImage X B))
        (eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u)
          ((colimitSiteStagePullbackSectionTransition S ℱ u).1.app
            (op (S.overImage X A)) s)))
  -- Apply the naturality transport to the inner transition evaluation.
  have hcongr_el := congrFun hcongr
    ((colimitSiteStagePullbackSectionTransition S ℱ u).1.app
      (op (S.overImage X A)) s)
  rw [hcongr_el]
  -- The owner comparison component is a pure section cast.
  have hKty : ((((S.stageFunctor (overLeftHom v)).sheafPushforwardContinuous (Type u)
        (S.stageTopology B.unop.left) (S.stageTopology C.unop.left)).obj
        ((overStageSheafPullback S C).obj ℱ)).obj.obj
      (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) =
    ((((S.stageFunctor (overLeftHom v ≫ overLeftHom u)).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology C.unop.left)).obj
        ((overStageSheafPullback S C).obj ℱ)).obj.obj (op (S.overImage X A))) := by
    simpa using (congrArg
      (fun G : S.stage A.unop.left ⥤ S.stage C.unop.left =>
        ((overStageSheafPullback S C).obj ℱ).obj.obj (op (G.obj (S.overImage X A))))
      (CofilteredSiteDiagram.stageFunctor_comp_eq S (overLeftHom u) (overLeftHom v))).symm
  have hKcast : ∀ z, (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S
        (overLeftHom u) (overLeftHom v))).symm
      (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
      (S.stageTopology C.unop.left)).hom.app
      ((overStageSheafPullback S C).obj ℱ)).1.app (op (S.overImage X A))) z =
      eqToHom hKty z := by
    intro z
    simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
      CategoryTheory.eqToHom_map, eqToHom_app]
  rw [hKcast]
  -- Collapse the cast chains around the common transition value.
  refine Eq.trans (congrArg
    (fun t => eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X (u ≫ v))
      (eqToHom hKty (eqToHom h₂
        ((colimitSiteStagePullbackSectionTransition S ℱ v).1.app
          (op (S.overImage X B)) t))))
    (eqToHom_apply_irrel h₁ (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u)
      ((colimitSiteStagePullbackSectionTransition S ℱ u).1.app
        (op (S.overImage X A)) s))) ?_
  exact eqToHom_apply_collapse₃₁ h₂ hKty
    (colimitSiteStagePullbackSectionMap_target_eq S ℱ X (u ≫ v))
    (colimitSiteStagePullbackSectionMap_target_eq S ℱ X v) _

/-- Lemma 7.18.3, equation `(7.18.3.1)`: the filtered diagram on `(Over i)ᵒᵖ` sending an arrow
`a : j ⟶ i` to the section set `f_a⁻¹ ℱ (u_a(X))`. -/
noncomputable def colimitSiteStagePullbackSectionDiagram
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj A := colimitSiteStagePullbackSectionValue S ℱ X A
  map u := colimitSiteStagePullbackSectionMap S ℱ X u
  map_id A := colimitSiteStagePullbackSectionMap_id S ℱ X A
  map_comp u v := colimitSiteStagePullbackSectionMap_comp S ℱ X u v

theorem colimitSiteStagePullbackSectionsComparisonTarget_eq
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    ((((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).obj
        (((S.stageCoconeFunctor i).sheafPullback
            (Type u)
            (S.stageTopology i)
            S.colimitTopology).obj
          ℱ)).obj.obj
      (op (S.overImage X A))) =
      ((((S.stageCoconeFunctor i).sheafPullback
            (Type u)
            (S.stageTopology i)
            S.colimitTopology).obj
          ℱ).obj.obj
        (op ((S.stageCoconeFunctor i).obj X))) := by
  -- Rewrite the pushforward evaluation to the literal object-image in the colimit category, then
  -- collapse that image to `u_i(X)` via the cocone relation `colimit.w`.
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
  simpa using
    congrArg
      (fun Y ↦
        (((S.stageCoconeFunctor i).sheafPullback
            (Type u)
            (S.stageTopology i)
            S.colimitTopology).obj
          ℱ).obj.obj
            (op Y))
      hobj

/-- Helper for Lemma 7.18.3: the conjugate of the colimit-stage pullback composition comparison
is the inverse cocone-side owner pushforward comparison. -/
theorem colimit_stage_pullback_comp_conjugate_hom
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
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

/-- Helper for Lemma 7.18.3: the mixed stage/cocone pushforward comparison isomorphisms satisfy
the associativity coherence. -/
theorem stageCoconePushforward_comp_coherence
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    Functor.isoWhiskerLeft
        ((S.stageCoconeFunctor k).sheafPushforwardContinuous (Type u)
          (S.stageTopology k) S.colimitTopology)
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a b)).symm
          (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)) ≪≫
      Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq (b ≫ a)))
        (Type u) (S.stageTopology i) (S.stageTopology k) S.colimitTopology =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (S.stageCoconeFunctor_comp_eq b))
            (Type u) (S.stageTopology j) (S.stageTopology k) S.colimitTopology)
          ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
            (S.stageTopology i) (S.stageTopology j)) ≪≫
        Functor.sheafPushforwardContinuousComp'
          (eqToIso (S.stageCoconeFunctor_comp_eq a))
          (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology := by
  apply Iso.ext
  ext ℱ Y y
  simp [CategoryTheory.eqToHom_map, eqToHom_app]
  exact eqToHom_apply_collapse₂₂ _ _ _ _ y

/-- Helper for Lemma 7.18.3: the mixed cocycle identity relating stage pullback comparisons and
cocone pullback comparisons, evaluated on a sheaf. No transport is needed: both routes end at the
literal cocone comparison. -/
theorem colimitStageSheafPullbackCompIso_assoc_app
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    (S.colimitStageSheafPullbackCompIso (Type u) b).hom.app
        ((stageSheafPullbackAlong S a).obj ℱ) ≫
      (S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ =
    ((S.stageCoconeFunctor k).sheafPullback (Type u)
        (S.stageTopology k) S.colimitTopology).map
        ((S.stageSheafPullbackCompIso (Type u) a b).hom.app ℱ) ≫
      (S.colimitStageSheafPullbackCompIso (Type u) (b ≫ a)).hom.app ℱ := by
  have hassoc := Adjunction.leftAdjointCompIso_assoc
    ((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j))
    ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k))
    ((S.stageCoconeFunctor k).sheafAdjunctionContinuous (Type u)
      (S.stageTopology k) S.colimitTopology)
    ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology k))
    ((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) S.colimitTopology)
    ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology)
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a b)).symm
      (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k))
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq b))
      (Type u) (S.stageTopology j) (S.stageTopology k) S.colimitTopology)
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq a))
      (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology)
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq (b ≫ a)))
      (Type u) (S.stageTopology i) (S.stageTopology k) S.colimitTopology)
    (stageCoconePushforward_comp_coherence S a b)
  have happ := congrArg (fun t => t.hom.app ℱ) hassoc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.associator_inv_app,
    Category.id_comp] at happ
  dsimp only [Functor.whiskerLeft, Functor.whiskerRight] at happ
  exact happ

/-- Helper for Lemma 7.18.3: transporting the stage arrow of a colimit-stage pullback comparison
along an equality of arrows. -/
theorem colimitStageSheafPullbackCompIso_congr
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} {f g : j ⟶ i} (hfg : f = g)
    (ℱ : Sheaf (S.stageTopology i) (Type u))
    (h₁ : (stageSheafPullbackAlong S f).obj ℱ = (stageSheafPullbackAlong S g).obj ℱ) :
    (S.colimitStageSheafPullbackCompIso (Type u) f).hom.app ℱ =
      ((S.stageCoconeFunctor j).sheafPullback (Type u)
          (S.stageTopology j) S.colimitTopology).map (eqToHom h₁) ≫
        (S.colimitStageSheafPullbackCompIso (Type u) g).hom.app ℱ := by
  subst hfg
  rw [Subsingleton.elim h₁ (rfl : _ = _)]
  simp

/-- Helper for Lemma 7.18.3: the sheaf-level naturality of the comparison cocone legs. -/
theorem colimitSiteStagePullbackSectionLeg_natural
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u))
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    colimitSiteStagePullbackSectionTransition S ℱ u ≫
      ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).map
        ((((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
          (S.stageTopology B.unop.left) S.colimitTopology).homEquiv
          ((overStageSheafPullback S B).obj ℱ)
          (((S.stageCoconeFunctor i).sheafPullback (Type u)
            (S.stageTopology i) S.colimitTopology).obj ℱ))
          ((S.colimitStageSheafPullbackCompIso (Type u) B.unop.hom).hom.app ℱ)) ≫
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq (overLeftHom u)))
        (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
        S.colimitTopology).hom.app
        (((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ) =
      (((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).homEquiv
        ((overStageSheafPullback S A).obj ℱ)
        (((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ))
        ((S.colimitStageSheafPullbackCompIso (Type u) A.unop.hom).hom.app ℱ) := by
  have hwB : overLeftHom u ≫ A.unop.hom = B.unop.hom := by simpa using Over.w u.unop
  have h'u : (stageSheafPullbackAlong S (overLeftHom u ≫ A.unop.hom)).obj ℱ =
      (overStageSheafPullback S B).obj ℱ := by
    simpa [overStageSheafPullback] using
      congrArg (fun f : B.unop.left ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ) hwB
  have hformu : colimitSiteStagePullbackSectionTransition S ℱ u =
      (((S.stageFunctor (overLeftHom u)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv
        ((overStageSheafPullback S A).obj ℱ) ((overStageSheafPullback S B).obj ℱ))
        ((S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ ≫
          eqToHom h'u) := rfl
  rw [hformu]
  set ep := ((S.stageFunctor (overLeftHom u)).sheafAdjunctionContinuous (Type u)
    (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)) with hep
  set ecB := ((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
    (S.stageTopology B.unop.left) S.colimitTopology) with hecB
  set ecA := ((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
    (S.stageTopology A.unop.left) S.colimitTopology) with hecA
  set K := (Functor.sheafPushforwardContinuousComp'
    (eqToIso (S.stageCoconeFunctor_comp_eq (overLeftHom u)))
    (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
    S.colimitTopology) with hK
  set Gi := (((S.stageCoconeFunctor i).sheafPullback (Type u)
    (S.stageTopology i) S.colimitTopology).obj ℱ) with hGi
  set αu := ((S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ ≫
    eqToHom h'u) with hαu
  set βB := ((S.colimitStageSheafPullbackCompIso (Type u) B.unop.hom).hom.app ℱ) with hβB
  set βA := ((S.colimitStageSheafPullbackCompIso (Type u) A.unop.hom).hom.app ℱ) with hβA
  -- transpose-composition normalizations
  have h1 : (ep.homEquiv ((overStageSheafPullback S A).obj ℱ)
        ((overStageSheafPullback S B).obj ℱ)) αu ≫
      ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).map
        ((ecB.homEquiv ((overStageSheafPullback S B).obj ℱ) Gi) βB) =
      (ep.homEquiv _ _) (αu ≫ (ecB.homEquiv _ _) βB) :=
    (Adjunction.homEquiv_naturality_right _ _ _).symm
  have h2 : αu ≫ (ecB.homEquiv ((overStageSheafPullback S B).obj ℱ) Gi) βB =
      (ecB.homEquiv _ _) (((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).map αu ≫ βB) :=
    (Adjunction.homEquiv_naturality_left _ _ _).symm
  have h3 : ∀ γ : ((S.stageFunctor (overLeftHom u)).sheafPullback (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left) ⋙
      (S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).obj
        ((overStageSheafPullback S A).obj ℱ) ⟶ Gi,
      ((ep.comp ecB).homEquiv ((overStageSheafPullback S A).obj ℱ) Gi) γ =
      (ep.homEquiv _ _) ((ecB.homEquiv _ _) γ) := by
    intro γ
    rw [Adjunction.comp_homEquiv]
    rfl
  -- the mixed cocycle core
  have hcore : ((S.stageCoconeFunctor B.unop.left).sheafPullback (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).map αu ≫ βB =
      (S.colimitStageSheafPullbackCompIso (Type u) (overLeftHom u)).hom.app
        ((overStageSheafPullback S A).obj ℱ) ≫ βA := by
    have hcongr := colimitStageSheafPullbackCompIso_congr S hwB ℱ h'u
    have hassoc := colimitStageSheafPullbackCompIso_assoc_app S
      A.unop.hom (overLeftHom u) ℱ
    rw [hαu, Functor.map_comp, Category.assoc, hβB]
    refine Eq.trans (congrArg (fun t => ((S.stageCoconeFunctor B.unop.left).sheafPullback
      (Type u) (S.stageTopology B.unop.left) S.colimitTopology).map
      ((S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ) ≫ t)
      hcongr.symm) ?_
    exact hassoc.symm
  have hex := homEquiv_conjugateEquiv_exchange ecA (ep.comp ecB)
    ((S.colimitStageSheafPullbackCompIso (Type u) (overLeftHom u)).hom) βA
  rw [hecA, hep, hecB, colimit_stage_pullback_comp_conjugate_hom] at hex
  -- assemble
  have hA' : ((ep.homEquiv _ _) αu ≫
      ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).map
        ((ecB.homEquiv _ _) βB)) ≫ K.hom.app Gi =
      (((ep.comp ecB).homEquiv _ _) (((S.stageCoconeFunctor B.unop.left).sheafPullback
        (Type u) (S.stageTopology B.unop.left) S.colimitTopology).map αu ≫ βB)) ≫
        K.hom.app Gi := by
    refine congrArg (fun t => t ≫ K.hom.app Gi) ?_
    exact h1.trans ((congrArg (fun t => (ep.homEquiv _ _) t) h2).trans (h3 _).symm)
  refine Eq.trans (Category.assoc _ _ _).symm (hA'.trans ?_)
  have hB' : (((ep.comp ecB).homEquiv _ _) (((S.stageCoconeFunctor B.unop.left).sheafPullback
        (Type u) (S.stageTopology B.unop.left) S.colimitTopology).map αu ≫ βB)) ≫
        K.hom.app Gi =
      (((ep.comp ecB).homEquiv _ _)
        ((S.colimitStageSheafPullbackCompIso (Type u) (overLeftHom u)).hom.app
          ((overStageSheafPullback S A).obj ℱ) ≫ βA)) ≫ K.hom.app Gi := by
    refine congrArg (fun t => ((ep.comp ecB).homEquiv _ _) t ≫ K.hom.app Gi) ?_
    exact hcore
  refine hB'.trans ?_
  have hD := congrArg (fun t => t ≫ K.hom.app Gi) hex
  refine hD.trans ?_
  rw [hK]
  simp only [Category.assoc]
  refine Eq.trans (congrArg (fun t => (ecA.homEquiv _ Gi) βA ≫ t)
    (Iso.inv_hom_id_app _ _)) ?_
  simp only [Category.comp_id]
  rfl

/-- Helper for Lemma 7.18.3: the explicit legs defining the comparison cocone are natural in the
over-category variable. -/
theorem colimitSiteStagePullbackSectionsComparisonCocone_naturality
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    (colimitSiteStagePullbackSectionDiagram S ℱ X).map u ≫
        ((((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
              (S.stageTopology B.unop.left) S.colimitTopology).unit.app
              ((overStageSheafPullback S B).obj ℱ)).1.app
            (op (S.overImage X B)) ≫
          eqToHom (by rfl) ≫
          ((((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous
                (Type u) (S.stageTopology B.unop.left)
                  S.colimitTopology).map
              ((S.colimitStageSheafPullbackCompIso (Type u) B.unop.hom).hom.app ℱ)).1.app
              (op (S.overImage X B))) ≫
          eqToHom (colimitSiteStagePullbackSectionsComparisonTarget_eq S ℱ X B)) =
      ((((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
            (S.stageTopology A.unop.left) S.colimitTopology).unit.app
            ((overStageSheafPullback S A).obj ℱ)).1.app
          (op (S.overImage X A)) ≫
        eqToHom (by rfl) ≫
        ((((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous
              (Type u) (S.stageTopology A.unop.left)
                S.colimitTopology).map
            ((S.colimitStageSheafPullbackCompIso (Type u) A.unop.hom).hom.app ℱ)).1.app
            (op (S.overImage X A))) ≫
        eqToHom (colimitSiteStagePullbackSectionsComparisonTarget_eq S ℱ X A)) := by
  have hnat := colimitSiteStagePullbackSectionLeg_natural S ℱ u
  have hobj : (S.stageFunctor (overLeftHom u)).obj (S.overImage X A) = S.overImage X B := by
    have hcomp :
        S.stageFunctor A.unop.hom ⋙ S.stageFunctor (overLeftHom u) =
          S.stageFunctor (overLeftHom u ≫ A.unop.hom) :=
      congrArg Cat.Hom.toFunctor
        (S.diagram.map_comp A.unop.hom.op (overLeftHom u).op).symm
    have h₁ : (S.stageFunctor (overLeftHom u)).obj (S.overImage X A) =
        (S.stageFunctor (overLeftHom u ≫ A.unop.hom)).obj X := by
      simpa [CofilteredSiteDiagram.overImage] using
        congrArg (fun F : S.stage i ⥤ S.stage B.unop.left ↦ F.obj X) hcomp
    have hw : overLeftHom u ≫ A.unop.hom = B.unop.hom := by simpa using Over.w u.unop
    have h₂ : (S.stageFunctor (overLeftHom u ≫ A.unop.hom)).obj X = S.overImage X B := by
      simpa [CofilteredSiteDiagram.overImage] using
        congrArg (fun a : B.unop.left ⟶ i ↦ (S.stageFunctor a).obj X) hw
    exact h₁.trans h₂
  have htB : ((((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) S.colimitTopology).obj
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj (op (S.overImage X B))) =
      ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.obj
        (op ((S.stageCoconeFunctor i).obj X))) := by
    simpa using colimitSiteStagePullbackSectionsComparisonTarget_eq S ℱ X B
  have htA : ((((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology A.unop.left) S.colimitTopology).obj
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj (op (S.overImage X A))) =
      ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.obj
        (op ((S.stageCoconeFunctor i).obj X))) := by
    simpa using colimitSiteStagePullbackSectionsComparisonTarget_eq S ℱ X A
  funext s
  change eqToHom htB
    (((((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology B.unop.left) S.colimitTopology).homEquiv
        ((overStageSheafPullback S B).obj ℱ)
        (((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ))
        ((S.colimitStageSheafPullbackCompIso (Type u) B.unop.hom).hom.app ℱ)).1.app
      (op (S.overImage X B))
      (eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u)
        ((colimitSiteStagePullbackSectionTransition S ℱ u).1.app
          (op (S.overImage X A)) s))) =
    eqToHom htA
    (((((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
        (S.stageTopology A.unop.left) S.colimitTopology).homEquiv
        ((overStageSheafPullback S A).obj ℱ)
        (((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ))
        ((S.colimitStageSheafPullbackCompIso (Type u) A.unop.hom).hom.app ℱ)).1.app
      (op (S.overImage X A)) s)
  have hA_el := congrArg (fun t => eqToHom htA (t.1.app (op (S.overImage X A)) s)) hnat
  refine Eq.trans ?_ hA_el
  -- cast bookkeeping data
  have h₁ : (((overStageSheafPullback S B).obj ℱ).obj.obj
      (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) =
      (((overStageSheafPullback S B).obj ℱ).obj.obj (op (S.overImage X B))) :=
    congrArg (fun Z => ((overStageSheafPullback S B).obj ℱ).obj.obj (op Z)) hobj
  have h₂ : ((((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) S.colimitTopology).obj
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj (op (S.overImage X B))) =
      ((((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) S.colimitTopology).obj
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj
      (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) :=
    congrArg (fun Z => (((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous
      (Type u) (S.stageTopology B.unop.left) S.colimitTopology).obj
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj (op Z)) hobj.symm
  have hKty : ((((S.stageCoconeFunctor B.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology B.unop.left) S.colimitTopology).obj
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj
      (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) =
      ((((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous (Type u)
      (S.stageTopology A.unop.left) S.colimitTopology).obj
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj (op (S.overImage X A))) := by
    simpa using congrArg
      (fun G : S.stage A.unop.left ⥤ S.ColimitCategory =>
        ((((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj
          (op (G.obj (S.overImage X A))))
      (S.stageCoconeFunctor_comp_eq (overLeftHom u))
  set legB := ((((S.stageCoconeFunctor B.unop.left).sheafAdjunctionContinuous (Type u)
    (S.stageTopology B.unop.left) S.colimitTopology).homEquiv
    ((overStageSheafPullback S B).obj ℱ)
    (((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ))
    ((S.colimitStageSheafPullbackCompIso (Type u) B.unop.hom).hom.app ℱ)) with hlegB
  set y := ((colimitSiteStagePullbackSectionTransition S ℱ u).1.app
    (op (S.overImage X A)) s) with hy
  have hcongr : legB.1.app (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A))) =
      eqToHom h₁ ≫ legB.1.app (op (S.overImage X B)) ≫ eqToHom h₂ := by
    have := NatTrans.congr legB.1 (congrArg op hobj)
    simpa [eqToHom_map] using this
  have hKcast : ∀ z, (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq (overLeftHom u)))
      (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)
      S.colimitTopology).hom.app
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).1.app (op (S.overImage X A))) z =
      eqToHom hKty z := by
    intro z
    simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
      CategoryTheory.eqToHom_map, eqToHom_app]
  -- assemble the five steps
  refine ((eqToHom_apply_collapse₃₁ h₂ hKty htA htB
      (legB.1.app (op (S.overImage X B))
        (eqToHom (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u) y))).symm).trans
    ((congrArg (fun t => eqToHom htA (eqToHom hKty (eqToHom h₂
      (legB.1.app (op (S.overImage X B)) t))))
      (eqToHom_apply_irrel (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u)
        h₁ y)).trans ?_)
  refine (congrArg (fun t => eqToHom htA (eqToHom hKty t))
    (congrFun hcongr y).symm).trans ?_
  exact congrArg (fun t => eqToHom htA t) (hKcast _).symm

noncomputable def colimitSiteStagePullbackSectionsComparisonCocone
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Cocone (colimitSiteStagePullbackSectionDiagram S ℱ X) where
  pt :=
    ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.obj
      (op ((S.stageCoconeFunctor i).obj X)))
  ι :=
    { app := fun A ↦
        (((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous (Type u)
            (S.stageTopology A.unop.left) S.colimitTopology).unit.app
            ((overStageSheafPullback S A).obj ℱ)).1.app
            (op (S.overImage X A)) ≫
          eqToHom (by rfl) ≫
          ((((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous
                (Type u) (S.stageTopology A.unop.left)
                  S.colimitTopology).map
              ((S.colimitStageSheafPullbackCompIso (Type u) A.unop.hom).hom.app ℱ)).1.app
              (op (S.overImage X A))) ≫
          eqToHom (colimitSiteStagePullbackSectionsComparisonTarget_eq S ℱ X A)
      naturality := by
        intro A B u
        simpa using
          colimitSiteStagePullbackSectionsComparisonCocone_naturality S ℱ X u }

/-- Lemma 7.18.3, equation `(7.18.3.1)`: for a sheaf `ℱ` on the stage site `i` and an object
`X` of `\mathcal C_i`, the canonical map from the filtered colimit over arrows `a : j ⟶ i` of
the section sets `f_a⁻¹ ℱ (u_a(X))` to the section set `f_i⁻¹ ℱ (u_i(X))` is bijective. In Lean
the indexing category is `(Over i)ᵒᵖ`. -/
noncomputable def colimitSiteStagePullbackSectionsComparison
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    colimit (colimitSiteStagePullbackSectionDiagram S ℱ X) ⟶
      ((((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ).obj.obj
        (op ((S.stageCoconeFunctor i).obj X))) :=
  colimit.desc _ (colimitSiteStagePullbackSectionsComparisonCocone S ℱ X) ≫
    eqToHom (by simp [colimitSiteStagePullbackSectionsComparisonCocone])

section AuxiliaryIso

/-- The colimit-site restriction transpose: the stage-to-colimit analogue of
`stageRestriction`, sending a stage pullback sheaf to the pushforward of the colimit-site
pullback along the corresponding cocone functor. -/
noncomputable def colimitRestriction
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {j : S.I} (a : j ⟶ i) :
    ((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).obj ℱ ⟶
    ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
      (S.stageTopology j) S.colimitTopology).obj
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ) :=
  (((S.stageCoconeFunctor j).sheafAdjunctionContinuous (Type u)
    (S.stageTopology j) S.colimitTopology).homEquiv _ _)
    ((S.colimitStageSheafPullbackCompIso (Type u) a).hom.app ℱ)

/-- The representative-level comparison map into the colimit-site pullback sections. -/
noncomputable def auxiliaryToPullback₀
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {V : S.ColimitCategory}
    (r : GRep S ℱ V) :
    (((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.obj (op V) :=
  ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map (eqToHom r.hW.symm).op)
    (((colimitRestriction S ℱ r.a).1.app (op r.W)) r.s)

/-- The representative-level comparison map is invariant under componentwise transport. -/
theorem auxiliaryToPullback₀_congr
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {V : S.ColimitCategory}
    {j : S.I} {a a' : j ⟶ i} (ha : a = a') {W W' : S.stage j} (hw : W = W')
    {h₁ : S.ιObj j W = V} {h₂ : S.ιObj j W' = V}
    {s : (((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).obj ℱ).obj.obj (op W)}
    {s' : (((S.stageFunctor a').sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).obj ℱ).obj.obj (op W')}
    (hs : eqToHom (gsec_type_congr ℱ ha hw) s = s') :
    auxiliaryToPullback₀ S ℱ (⟨j, a, W, h₁, s⟩ : GRep S ℱ V) =
      auxiliaryToPullback₀ S ℱ (⟨j, a', W', h₂, s'⟩ : GRep S ℱ V) := by
  subst ha
  subst hw
  rw [Subsingleton.elim (gsec_type_congr ℱ rfl rfl)
    (rfl : (((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).obj ℱ).obj.obj (op W) = _)] at hs
  subst hs
  rfl

/-- The mixed pushforward composition comparison acts on sections as a pure cast. -/
theorem mixedPushComp_app_eval_cast
    (S : CofilteredSiteDiagram.{u, u, u}) {j k : S.I} (b : k ⟶ j)
    (G : Sheaf S.colimitTopology (Type u)) (W : (S.stage j)ᵒᵖ)
    (hsec : ((((S.stageFunctor b).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)).obj
        (((S.stageCoconeFunctor k).sheafPushforwardContinuous (Type u)
          (S.stageTopology k) S.colimitTopology).obj G)).obj.obj W) =
      ((((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).obj G).obj.obj W))
    (z : (((S.stageFunctor b).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)).obj
        (((S.stageCoconeFunctor k).sheafPushforwardContinuous (Type u)
          (S.stageTopology k) S.colimitTopology).obj G)).obj.obj W) :
    (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq b))
      (Type u) (S.stageTopology j) (S.stageTopology k) S.colimitTopology).hom.app
      G).1.app W) z = eqToHom hsec z := by
  simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
    CategoryTheory.eqToHom_map, eqToHom_app]

/-- Lowering invariance of the representative-level comparison map: the comparison value of a
lowered representative is the comparison value of the original. This is the sheaf-level mixed
cocycle `colimitSiteStagePullbackSectionLeg_natural` instantiated at the over-category dressing
of the lowering arrow. -/
theorem auxiliaryToPullback₀_lower
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {V : S.ColimitCategory}
    (r : GRep S ℱ V) {k : S.I} (b : k ⟶ r.j) :
    auxiliaryToPullback₀ S ℱ (r.lower ℱ b) = auxiliaryToPullback₀ S ℱ r := by
  -- the over-category dressing of the lowering arrow
  have hnat := colimitSiteStagePullbackSectionLeg_natural S ℱ
    ((Over.homMk b (rfl : b ≫ r.a = b ≫ r.a) :
      Over.mk (b ≫ r.a) ⟶ Over.mk r.a).op :
      (op (Over.mk r.a) : (Over i)ᵒᵖ) ⟶ op (Over.mk (b ≫ r.a)))
  have hnat_el := congrFun (congrArg (fun t => t.1.app (op r.W)) hnat) r.s
  -- the transition evaluates to the lowered section
  have h'u : (stageSheafPullbackAlong S (b ≫ r.a)).obj ℱ =
      (stageSheafPullbackAlong S (b ≫ r.a)).obj ℱ := rfl
  have htrans_el : ((colimitSiteStagePullbackSectionTransition S ℱ
      ((Over.homMk b (rfl : b ≫ r.a = b ≫ r.a) :
        Over.mk (b ≫ r.a) ⟶ Over.mk r.a).op :
        (op (Over.mk r.a) : (Over i)ᵒᵖ) ⟶ op (Over.mk (b ≫ r.a)))).1.app (op r.W)) r.s =
      (r.lower ℱ b).s := by
    have hform := congrFun (congrArg (fun t => t.1.app (op r.W))
      (Adjunction.homEquiv_naturality_right
        ((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
          (S.stageTopology r.j) (S.stageTopology k))
        ((S.stageSheafPullbackCompIso (Type u) r.a b).hom.app ℱ)
        (eqToHom h'u))) r.s
    refine hform.trans ?_
    exact sheaf_functor_map_eqToHom_eval
      ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
        (S.stageTopology r.j) (S.stageTopology k)) h'u (op r.W) rfl _
  -- the mixed pushforward collapse cast
  have hsec : ((((S.stageFunctor b).sheafPushforwardContinuous (Type u)
      (S.stageTopology r.j) (S.stageTopology k)).obj
      (((S.stageCoconeFunctor k).sheafPushforwardContinuous (Type u)
        (S.stageTopology k) S.colimitTopology).obj
        (((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ))).obj.obj (op r.W)) =
      ((((S.stageCoconeFunctor r.j).sheafPushforwardContinuous (Type u)
        (S.stageTopology r.j) S.colimitTopology).obj
        (((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj (op r.W)) := by
    simpa using congrArg
      (fun G : S.stage r.j ⥤ S.ColimitCategory =>
        ((((S.stageCoconeFunctor i).sheafPullback (Type u)
          (S.stageTopology i) S.colimitTopology).obj ℱ)).obj.obj (op (G.obj r.W)))
      (S.stageCoconeFunctor_comp_eq b)
  -- evaluate the sheaf-level cocycle on the section
  have key : (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq b))
      (Type u) (S.stageTopology r.j) (S.stageTopology k) S.colimitTopology).hom.app
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).1.app (op r.W))
      (((colimitRestriction S ℱ (b ≫ r.a)).1.app
        (op ((S.stageFunctor b).obj r.W))) ((r.lower ℱ b).s)) =
      ((colimitRestriction S ℱ r.a).1.app (op r.W)) r.s := by
    refine Eq.trans ?_ hnat_el
    exact congrArg (fun z => (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq b))
      (Type u) (S.stageTopology r.j) (S.stageTopology k) S.colimitTopology).hom.app
      (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ)).1.app (op r.W))
      (((colimitRestriction S ℱ (b ≫ r.a)).1.app
        (op ((S.stageFunctor b).obj r.W))) z)) htrans_el.symm
  have key₂ : eqToHom hsec
      (((colimitRestriction S ℱ (b ≫ r.a)).1.app
        (op ((S.stageFunctor b).obj r.W))) ((r.lower ℱ b).s)) =
      ((colimitRestriction S ℱ r.a).1.app (op r.W)) r.s :=
    (mixedPushComp_app_eval_cast S b _ (op r.W) hsec _).symm.trans key
  -- exchange the collapse cast for the presheaf transport along the presentation identity
  have hmap := presheaf_map_eqToHom_op_eval
    ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj)
    (S.ιObj_lower b r.W).symm hsec
    (((colimitRestriction S ℱ (b ≫ r.a)).1.app
      (op ((S.stageFunctor b).obj r.W))) ((r.lower ℱ b).s))
  have hcomb : ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
      (eqToHom (S.ιObj_lower b r.W).symm).op)
      (((colimitRestriction S ℱ (b ≫ r.a)).1.app
        (op ((S.stageFunctor b).obj r.W))) ((r.lower ℱ b).s)) =
      ((colimitRestriction S ℱ r.a).1.app (op r.W)) r.s := hmap.trans key₂
  show ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
      (eqToHom ((r.lower ℱ b).hW).symm).op)
      (((colimitRestriction S ℱ (b ≫ r.a)).1.app
        (op ((S.stageFunctor b).obj r.W))) ((r.lower ℱ b).s)) =
    ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map (eqToHom r.hW.symm).op)
      (((colimitRestriction S ℱ r.a).1.app (op r.W)) r.s)
  rw [← hcomb, ← FunctorToTypes.map_comp_apply, ← op_comp, eqToHom_trans]
  rfl

/-- The representative-level comparison map is invariant under the lowering relation. -/
theorem auxiliaryToPullback₀_grel
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {V : S.ColimitCategory}
    {r₁ r₂ : GRep S ℱ V} (h : grel r₁ r₂) :
    auxiliaryToPullback₀ S ℱ r₁ = auxiliaryToPullback₀ S ℱ r₂ := by
  obtain ⟨k, b₁, b₂, ha, hw, hs⟩ := h
  exact (auxiliaryToPullback₀_lower S ℱ r₁ b₁).symm.trans
    ((auxiliaryToPullback₀_congr S ℱ ha hw hs).trans
      (auxiliaryToPullback₀_lower S ℱ r₂ b₂))

/-- The comparison map from the auxiliary sections to the colimit-site pullback sections. -/
noncomputable def auxiliaryToPullbackApp
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (V : S.ColimitCategory) :
    GSec ℱ V → (((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.obj (op V) :=
  _root_.Quotient.lift (auxiliaryToPullback₀ S ℱ)
    (fun _ _ h => auxiliaryToPullback₀_grel S ℱ h)

/-- Two transport-conjugated composites with a common middle agree up to proof irrelevance. -/
theorem eqToHom_pentagon_irrel {D : Type*} [Category D]
    {V' X₁ X₂ X₃ V R T : D}
    (p₁ : V' = X₁) (m : X₁ ⟶ X₂) (q₁ : X₂ = X₃) (q₂ : X₃ = V)
    (p₂ : V' = R) (p₃ : R = X₁) (q₃ : X₂ = T) (q₄ : T = V) :
    eqToHom p₁ ≫ (m ≫ eqToHom q₁) ≫ eqToHom q₂ =
      eqToHom p₂ ≫ (eqToHom p₃ ≫ m ≫ eqToHom q₃) ≫ eqToHom q₄ := by
  subst_vars
  simp

/-- Cancel a transport pair `h` then `h.symm` at the head of a composite. -/
theorem eqToHom_comp_symm_cancel'
    {D : Type*} [Category D] {P Q R : D} (h : P = Q) (m : P ⟶ R) :
    eqToHom h ≫ eqToHom h.symm ≫ m = m := by
  subst h
  simp

/-- The representative-level comparison map intertwines restriction data actions with the
colimit-site presheaf restriction. -/
theorem auxiliaryToPullback₀_res
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {V' V : S.ColimitCategory}
    {gr : HomRep V' V} {r : GRep S ℱ V} (d : ResData ℱ gr r) :
    auxiliaryToPullback₀ S ℱ (d.res) =
      ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
        (Quiver.Hom.op (_root_.Quotient.mk _ gr : V' ⟶ V)))
        (auxiliaryToPullback₀ S ℱ r) := by
  -- naturality of the colimit restriction against the lowered stage morphism
  have hnatψ := congrFun ((colimitRestriction S ℱ (d.toRep ≫ r.a)).1.naturality
    ((S.stageFunctor d.toHom).map gr.hom ≫ eqToHom d.glue).op) ((r.lower ℱ d.toRep).s)
  -- invert the lowering identification of the comparison values
  have hKL := auxiliaryToPullback₀_lower S ℱ r d.toRep
  have hinv : ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
      (eqToHom ((S.ιObj_lower d.toRep r.W).trans r.hW)).op)
      (auxiliaryToPullback₀ S ℱ r) =
      ((colimitRestriction S ℱ (d.toRep ≫ r.a)).1.app
        (op ((S.stageFunctor d.toRep).obj r.W))) ((r.lower ℱ d.toRep).s) := by
    rw [← hKL]
    show ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
      (eqToHom ((S.ιObj_lower d.toRep r.W).trans r.hW)).op)
      (((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
        (eqToHom ((S.ιObj_lower d.toRep r.W).trans r.hW).symm).op)
        (((colimitRestriction S ℱ (d.toRep ≫ r.a)).1.app
          (op ((S.stageFunctor d.toRep).obj r.W))) ((r.lower ℱ d.toRep).s))) = _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, eqToHom_trans]
    exact presheaf_map_eqToHom_op_eval
      ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj) _ rfl _
  -- the colimit arrow class in transported cocone form
  have hψarrow : eqToHom ((S.ιObj_lower d.toHom gr.src).trans gr.hsrc).symm ≫
      (S.stageCoconeFunctor d.idx).map
        ((S.stageFunctor d.toHom).map gr.hom ≫ eqToHom d.glue) ≫
      eqToHom ((S.ιObj_lower d.toRep r.W).trans r.hW) =
      (_root_.Quotient.mk _ gr : V' ⟶ V) := by
    have hmapF := S.stageCoconeFunctor_map_lower d.toHom gr.hom
    refine Eq.trans ?_ (mk_eq_eqToHom_comp gr.hom gr.hsrc gr.htgt).symm
    rw [Functor.map_comp, eqToHom_map, hmapF]
    exact eqToHom_pentagon_irrel _ _ _ _ _ _ _ _
  -- assemble
  have main : ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
      (Quiver.Hom.op (eqToHom ((S.ιObj_lower d.toHom gr.src).trans gr.hsrc).symm ≫
        (S.stageCoconeFunctor d.idx).map
          ((S.stageFunctor d.toHom).map gr.hom ≫ eqToHom d.glue) ≫
        eqToHom ((S.ιObj_lower d.toRep r.W).trans r.hW))))
      (auxiliaryToPullback₀ S ℱ r) = auxiliaryToPullback₀ S ℱ (d.res) := by
    have S1 : ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
        (Quiver.Hom.op (eqToHom ((S.ιObj_lower d.toHom gr.src).trans gr.hsrc).symm ≫
          (S.stageCoconeFunctor d.idx).map
            ((S.stageFunctor d.toHom).map gr.hom ≫ eqToHom d.glue) ≫
          eqToHom ((S.ιObj_lower d.toRep r.W).trans r.hW))))
        (auxiliaryToPullback₀ S ℱ r) =
        ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
        (eqToHom ((S.ιObj_lower d.toHom gr.src).trans gr.hsrc).symm).op)
        (((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
        ((S.stageCoconeFunctor d.idx).map
          ((S.stageFunctor d.toHom).map gr.hom ≫ eqToHom d.glue)).op)
        (((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
        (eqToHom ((S.ιObj_lower d.toRep r.W).trans r.hW)).op)
        (auxiliaryToPullback₀ S ℱ r))) := by
      rw [op_comp, op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply]
      rfl
    refine S1.trans ?_
    refine (congrArg (fun z => ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
      (eqToHom ((S.ιObj_lower d.toHom gr.src).trans gr.hsrc).symm).op)
      (((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
      ((S.stageCoconeFunctor d.idx).map
        ((S.stageFunctor d.toHom).map gr.hom ≫ eqToHom d.glue)).op) z)) hinv).trans ?_
    have hnat' : ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
        ((S.stageCoconeFunctor d.idx).map
          ((S.stageFunctor d.toHom).map gr.hom ≫ eqToHom d.glue)).op)
        (((colimitRestriction S ℱ (d.toRep ≫ r.a)).1.app
          (op ((S.stageFunctor d.toRep).obj r.W))) ((r.lower ℱ d.toRep).s)) =
        ((colimitRestriction S ℱ (d.toRep ≫ r.a)).1.app
          (op ((S.stageFunctor d.toHom).obj gr.src)))
        (((((S.stageFunctor (d.toRep ≫ r.a)).sheafPullback (Type u)
          (S.stageTopology i) (S.stageTopology d.idx)).obj ℱ).obj.map
          ((S.stageFunctor d.toHom).map gr.hom ≫ eqToHom d.glue).op)
          ((r.lower ℱ d.toRep).s)) := hnatψ.symm
    exact congrArg (fun z => ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map
      (eqToHom ((S.ιObj_lower d.toHom gr.src).trans gr.hsrc).symm).op) z) hnat'
  exact main.symm.trans (congrArg (fun ar => ((((S.stageCoconeFunctor i).sheafPullback (Type u)
    (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map (Quiver.Hom.op ar))
    (auxiliaryToPullback₀ S ℱ r)) hψarrow)

/-- Pointwise naturality of the comparison map over the colimit category. -/
theorem auxiliaryToPullbackApp_natural
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {V' V : S.ColimitCategory}
    (g : V' ⟶ V) (x : GSec ℱ V) :
    auxiliaryToPullbackApp S ℱ V' (gres ℱ g x) =
      ((((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ).obj.map (Quiver.Hom.op g))
        (auxiliaryToPullbackApp S ℱ V x) := by
  induction g using _root_.Quotient.inductionOn with | _ gr =>
  induction x using _root_.Quotient.inductionOn with | _ r =>
  exact auxiliaryToPullback₀_res S ℱ (ResData.some ℱ gr r)

/-- The comparison morphism from the auxiliary sheaf to the colimit-site pullback sheaf. -/
noncomputable def auxiliaryToPullback
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    auxiliarySheaf ℱ ⟶ ((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ where
  hom :=
    { app := fun V => auxiliaryToPullbackApp S ℱ V.unop
      naturality := fun V V' f => funext fun x =>
        auxiliaryToPullbackApp_natural S ℱ f.unop x }

/-- The unital coherence of the mixed pushforward comparison at the identity stage arrow. -/
theorem mixedPushComp_id_coherence
    (S : CofilteredSiteDiagram.{u, u, u}) (i : S.I) :
    Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq (𝟙 i)))
      (Type u) (S.stageTopology i) (S.stageTopology i) S.colimitTopology =
    Functor.isoWhiskerLeft
      ((S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) S.colimitTopology)
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (CofilteredSiteDiagram.stageFunctor_id_eq S i))
        (Type u) (S.stageTopology i)) ≪≫
    Functor.rightUnitor
      ((S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) S.colimitTopology) := by
  apply Iso.ext
  ext G Y y
  simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousId,
    CategoryTheory.eqToHom_map, eqToHom_app]

/-- The identity-arrow degeneration of the mixed pullback composition comparison. -/
theorem colimitCompIso_id_app
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    (S.colimitStageSheafPullbackCompIso (Type u) (𝟙 i)).hom.app ℱ =
      ((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).map
        ((stagePullbackIdIso i).hom.app ℱ) := by
  have hdeg := Adjunction.leftAdjointCompIso_id_comp
    ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology i))
    ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology)
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq (𝟙 i)))
      (Type u) (S.stageTopology i) (S.stageTopology i) S.colimitTopology)
    (Functor.sheafPushforwardContinuousId'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_id_eq S i))
      (Type u) (S.stageTopology i))
    (mixedPushComp_id_coherence S i)
  have happ := congrArg (fun I => I.hom.app ℱ) hdeg
  simpa [stagePullbackIdIso, colimitStageSheafPullbackCompIso] using happ

/-- The unit-side triangle: the identity-stage structure map composed with the colimit
restriction transpose is the adjunction unit. -/
theorem auxiliaryUnit_triangle
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    (stagePullbackIdIso i).inv.app ℱ ≫ colimitRestriction S ℱ (𝟙 i) =
      ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) S.colimitTopology).unit.app ℱ := by
  show (stagePullbackIdIso i).inv.app ℱ ≫
    (((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology).homEquiv _ _)
      ((S.colimitStageSheafPullbackCompIso (Type u) (𝟙 i)).hom.app ℱ) = _
  rw [colimitCompIso_id_app S ℱ, ← Adjunction.homEquiv_naturality_left]
  have hid : ((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).map ((stagePullbackIdIso i).inv.app ℱ) ≫
      ((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).map ((stagePullbackIdIso i).hom.app ℱ) =
      𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  refine Eq.trans (congrArg (fun z => (((S.stageCoconeFunctor i).sheafAdjunctionContinuous
    (Type u) (S.stageTopology i) S.colimitTopology).homEquiv _ _) z) hid) ?_
  exact Adjunction.homEquiv_id _ ℱ

/-- The transposed unit: the comparison morphism from the colimit-site pullback sheaf into the
auxiliary sheaf. -/
noncomputable def auxiliaryFromPullback
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    ((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ ⟶ auxiliarySheaf ℱ :=
  (((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
    (S.stageTopology i) S.colimitTopology).homEquiv ℱ (auxiliarySheaf ℱ)).symm
    (auxiliaryUnit ℱ)

/-- Pointwise unit-side triangle for the comparison morphisms. -/
theorem auxiliaryUnit_comp_toPullback
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    auxiliaryUnit ℱ ≫ ((S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
      (S.stageTopology i) S.colimitTopology).map (auxiliaryToPullback S ℱ) =
    ((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) S.colimitTopology).unit.app ℱ := by
  apply Sheaf.hom_ext
  ext W s
  -- the composite evaluates the representative-level comparison at the identity representative
  have hstrip := presheaf_map_eqToHom_op_eval
    ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj)
    ((rfl : S.ιObj i W.unop = S.ιObj i W.unop).symm)
    rfl
    (((colimitRestriction S ℱ (𝟙 i)).1.app (op W.unop))
      ((((stagePullbackIdIso i).inv.app ℱ).1.app W) s))
  refine hstrip.trans ?_
  exact congrFun (congrArg (fun t => t.1.app W) (auxiliaryUnit_triangle S ℱ)) s

/-- The first triangle: the transposed unit splits the comparison morphism. -/
theorem auxiliaryFromPullback_comp_toPullback
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    auxiliaryFromPullback S ℱ ≫ auxiliaryToPullback S ℱ =
      𝟙 (((S.stageCoconeFunctor i).sheafPullback (Type u)
        (S.stageTopology i) S.colimitTopology).obj ℱ) := by
  apply Equiv.injective (((S.stageCoconeFunctor i).sheafAdjunctionContinuous (Type u)
    (S.stageTopology i) S.colimitTopology).homEquiv ℱ _)
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_id]
  refine Eq.trans (congrArg (fun t => t ≫
    ((S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
      (S.stageTopology i) S.colimitTopology).map (auxiliaryToPullback S ℱ))
    (Equiv.apply_symm_apply _ _)) ?_
  exact auxiliaryUnit_comp_toPullback S ℱ

/-- Mirror helper: precomposing a stage functor with the identity-stage functor changes
nothing. -/
theorem stageFunctor_id_comp_eq
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    S.stageFunctor (𝟙 i) ⋙ S.stageFunctor a = S.stageFunctor a := by
  calc
    S.stageFunctor (𝟙 i) ⋙ S.stageFunctor a = S.stageFunctor (a ≫ 𝟙 i) := by
      symm
      exact congrArg Cat.Hom.toFunctor (S.diagram.map_comp (𝟙 i).op a.op)
    _ = S.stageFunctor a := by simp

/-- Mirror helper: the left-unital pushforward comparison for the identity-first composite. -/
theorem stageSheafPushforwardComp_id_comp
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    Functor.sheafPushforwardContinuousComp'
        (eqToIso (stageFunctor_id_comp_eq S a))
        (Type u) (S.stageTopology i) (S.stageTopology i) (S.stageTopology j) =
      Functor.isoWhiskerLeft
          ((S.stageFunctor a).sheafPushforwardContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          (Functor.sheafPushforwardContinuousId'
            (eqToIso (CofilteredSiteDiagram.stageFunctor_id_eq S i))
            (Type u) (S.stageTopology i)) ≪≫
        Functor.rightUnitor
          ((S.stageFunctor a).sheafPushforwardContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j)) := by
  ext ℱ Y y
  simp [CategoryTheory.eqToHom_map, eqToHom_op]

/-- Mirror helper: the owner pushforward comparison after normalizing `a ≫ 𝟙 i = a`. -/
theorem stageSheafPushforwardComp_id_comp_owner_normalize
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor (𝟙 i) ⋙ S.stageFunctor a =
              S.stageFunctor (a ≫ 𝟙 i) from
            (congrArg Cat.Hom.toFunctor (S.diagram.map_comp (𝟙 i).op a.op)).symm))
        (Type u) (S.stageTopology i) (S.stageTopology i) (S.stageTopology j) ≪≫
      Functor.sheafPushforwardContinuousIso
        (eqToIso
          (show S.stageFunctor (a ≫ 𝟙 i) = S.stageFunctor a from by
            simpa [CofilteredSiteDiagram.stageFunctor] using
              congrArg Cat.Hom.toFunctor (Category.comp_id a)))
        (Type u) (S.stageTopology i) (S.stageTopology j) =
      Functor.sheafPushforwardContinuousComp'
        (eqToIso (stageFunctor_id_comp_eq S a))
        (Type u) (S.stageTopology i) (S.stageTopology i) (S.stageTopology j) := by
  ext ℱ Y y
  simp

/-- Mirror helper: the pullback target equality induced by `a ≫ 𝟙 i = a`. -/
theorem stageSheafPullbackComp_id_comp_target_eq
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    stageSheafPullbackAlong S (a ≫ 𝟙 i) = stageSheafPullbackAlong S a := by
  simpa [stageSheafPullbackAlong] using
    congrArg (fun f : j ⟶ i ↦ stageSheafPullbackAlong S f) (Category.comp_id a)

/-- Mirror helper: the section-type form of the left-unital target equality. -/
theorem stageSheafPullbackComp_id_comp_target_eq_app
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y : (S.stage j)ᵒᵖ) :
    (((stageSheafPullbackAlong S (a ≫ 𝟙 i)).obj ℱ).obj.obj Y) =
      (((stageSheafPullbackAlong S a).obj ℱ).obj.obj Y) := by
  simpa [stageSheafPullbackAlong] using
    congrArg (fun f : j ⟶ i ↦ ((stageSheafPullbackAlong S f).obj ℱ).obj.obj Y)
      (Category.comp_id a)

/-- Mirror helper: the pushforward-level transport induced by `a ≫ 𝟙 i = a`. -/
theorem stageSheafPushforward_id_comp_push_eq
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (S.stageFunctor (a ≫ 𝟙 i)).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j) =
      (S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j) := by
  exact congrArg
    (fun f : j ⟶ i => (S.stageFunctor f).sheafPushforwardContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j))
    (Category.comp_id a)

/-- Mirror helper: the left-unital pushforward comparison. -/
noncomputable abbrev stageSheafPushforwardIdCompIso
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (S.stageFunctor a).sheafPushforwardContinuous
        (Type u) (S.stageTopology i) (S.stageTopology j) ⋙
      (S.stageFunctor (𝟙 i)).sheafPushforwardContinuous
        (Type u) (S.stageTopology i) (S.stageTopology i) ≅
    (S.stageFunctor a).sheafPushforwardContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j) :=
  Functor.isoWhiskerLeft
      ((S.stageFunctor a).sheafPushforwardContinuous
        (Type u) (S.stageTopology i) (S.stageTopology j))
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (CofilteredSiteDiagram.stageFunctor_id_eq S i))
        (Type u) (S.stageTopology i)) ≪≫
    Functor.rightUnitor
      ((S.stageFunctor a).sheafPushforwardContinuous
        (Type u) (S.stageTopology i) (S.stageTopology j))

/-- Mirror helper: the left-unital comparison is the owner comparison followed by the
pushforward transport. -/
theorem stageSheafPushforwardIdCompIso_eq_comp
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (stageSheafPushforwardIdCompIso S a) =
      Functor.sheafPushforwardContinuousComp'
          (eqToIso
            (show S.stageFunctor (𝟙 i) ⋙ S.stageFunctor a =
                S.stageFunctor (a ≫ 𝟙 i) from
              (congrArg Cat.Hom.toFunctor (S.diagram.map_comp (𝟙 i).op a.op)).symm))
          (Type u) (S.stageTopology i) (S.stageTopology i) (S.stageTopology j) ≪≫
        eqToIso (stageSheafPushforward_id_comp_push_eq S a) := by
  refine ((stageSheafPushforwardComp_id_comp S a).symm.trans
    (stageSheafPushforwardComp_id_comp_owner_normalize S a).symm).trans ?_
  exact congrArg
    (fun e => Functor.sheafPushforwardContinuousComp'
        (eqToIso
          (show S.stageFunctor (𝟙 i) ⋙ S.stageFunctor a =
              S.stageFunctor (a ≫ 𝟙 i) from
            (congrArg Cat.Hom.toFunctor (S.diagram.map_comp (𝟙 i).op a.op)).symm))
        (Type u) (S.stageTopology i) (S.stageTopology i) (S.stageTopology j) ≪≫ e)
    (sheafPushforwardContinuousIso_eqToIso
      (show S.stageFunctor (a ≫ 𝟙 i) = S.stageFunctor a from by
        simpa [CofilteredSiteDiagram.stageFunctor] using
          congrArg Cat.Hom.toFunctor (Category.comp_id a))
      (stageSheafPushforward_id_comp_push_eq S a))

/-- Mirror helper: the left-unital target transport evaluates as the explicit section cast. -/
theorem stageSheafPullbackComp_id_comp_section_cast
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y : (S.stage j)ᵒᵖ)
    (z : (((stageSheafPullbackAlong S (a ≫ 𝟙 i)).obj ℱ).obj.obj Y)) :
    (let e : (stageSheafPullbackAlong S (a ≫ 𝟙 i)).obj ℱ ⟶
          (stageSheafPullbackAlong S a).obj ℱ :=
        eqToHom (by
          simpa [stageSheafPullbackAlong] using
            congrArg
              (fun f : j ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
              (Category.comp_id a))
      ; ((e.1.app Y) z)) =
      eqToHom (stageSheafPullbackComp_id_comp_target_eq_app S a ℱ Y) z := by
  let p : (stageSheafPullbackAlong S (a ≫ 𝟙 i)).obj ℱ =
      (stageSheafPullbackAlong S a).obj ℱ := by
    simpa [stageSheafPullbackAlong] using
      congrArg
        (fun f : j ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
        (Category.comp_id a)
  have hp :
      congrArg
          (fun G : Sheaf (S.stageTopology j) (Type u) ↦ G.obj.obj Y) p =
        stageSheafPullbackComp_id_comp_target_eq_app S a ℱ Y := by
    apply Subsingleton.elim
  change (((eqToHom p).1.app Y) z) =
    eqToHom (stageSheafPullbackComp_id_comp_target_eq_app S a ℱ Y) z
  simpa [hp]

/-- Mirror normalization: composing the identity-first pullback comparison with the target
transport gives the left-unital comparison. -/
theorem stageSheafPullbackComp_id_comp_hom_normalize
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (S.stageSheafPullbackCompIso (Type u) (𝟙 i) a).hom ≫
        eqToHom (stageSheafPullbackComp_id_comp_target_eq S a) =
      (Adjunction.leftAdjointCompIso
        ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology i))
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        (stageSheafPushforwardIdCompIso S a)).hom := by
  set adj :=
    ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous
      (Type u) (S.stageTopology i) (S.stageTopology i)).comp
      ((S.stageFunctor a).sheafAdjunctionContinuous
        (Type u) (S.stageTopology i) (S.stageTopology j)) with hadj
  set adj_a :=
    (S.stageFunctor a).sheafAdjunctionContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j) with hadja
  set adj_c :=
    (S.stageFunctor (a ≫ 𝟙 i)).sheafAdjunctionContinuous
      (Type u) (S.stageTopology i) (S.stageTopology j) with hadjc
  apply (conjugateEquiv adj_a adj).injective
  have hsplit := (CategoryTheory.conjugateEquiv_comp adj_a adj_c adj
    (eqToHom (stageSheafPullbackComp_id_comp_target_eq S a))
    ((S.stageSheafPullbackCompIso (Type u) (𝟙 i) a).hom)).symm
  refine hsplit.trans ?_
  rw [stage_pullback_comp_conjugate_hom_aux (𝟙 i) a,
    conjugateEquiv_sheafPullback_eqToHom
      (show S.stageFunctor (a ≫ 𝟙 i) = S.stageFunctor a from by
        simpa [CofilteredSiteDiagram.stageFunctor] using
          congrArg Cat.Hom.toFunctor (Category.comp_id a))
      (stageSheafPullbackComp_id_comp_target_eq S a)
      (stageSheafPushforward_id_comp_push_eq S a).symm]
  have hrhs : conjugateEquiv adj_a adj
      (Adjunction.leftAdjointCompIso
        ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology i)) adj_a adj_a
        (stageSheafPushforwardIdCompIso S a)).hom =
      (stageSheafPushforwardIdCompIso S a).inv :=
    (conjugateEquiv adj_a adj).apply_symm_apply _
  refine Eq.trans ?_ hrhs.symm
  rw [stageSheafPushforwardIdCompIso_eq_comp S a]
  simp
  rfl

/-- Mirror evaluation: the identity-first pullback comparison evaluates as the cast of the
left-unital comparison. -/
theorem stageSheafPullbackComp_id_comp_cast_mate_eval
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y : (S.stage j)ᵒᵖ)
    (y :
      (((S.stageFunctor (𝟙 i)).sheafPullback (Type u)
          (S.stageTopology i) (S.stageTopology i) ⋙
            (S.stageFunctor a).sheafPullback (Type u)
              (S.stageTopology i) (S.stageTopology j)).obj
          ℱ).obj.obj
        Y) :
    eqToHom (stageSheafPullbackComp_id_comp_target_eq_app S a ℱ Y)
      ((((S.stageSheafPullbackCompIso (Type u) (𝟙 i) a).hom.app ℱ).1.app Y) y) =
      (((Adjunction.leftAdjointCompIso
          ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology i))
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          ((S.stageFunctor a).sheafAdjunctionContinuous
            (Type u) (S.stageTopology i) (S.stageTopology j))
          (stageSheafPushforwardIdCompIso S a)).hom.app ℱ).1.app Y) y := by
  have happ := congrArg (fun t => ((t.app ℱ).1.app Y) y)
    (stageSheafPullbackComp_id_comp_hom_normalize S a)
  refine Eq.trans ?_ happ
  have he : ((eqToHom (stageSheafPullbackComp_id_comp_target_eq S a) :
      stageSheafPullbackAlong S (a ≫ 𝟙 i) ⟶ stageSheafPullbackAlong S a).app ℱ) =
      eqToHom (Functor.congr_obj (stageSheafPullbackComp_id_comp_target_eq S a) ℱ) :=
    eqToHom_app _ ℱ
  have hz :
      ((((eqToHom (stageSheafPullbackComp_id_comp_target_eq S a) :
          stageSheafPullbackAlong S (a ≫ 𝟙 i) ⟶ stageSheafPullbackAlong S a).app ℱ).1.app Y)
        ((((S.stageSheafPullbackCompIso (Type u) (𝟙 i) a).hom.app ℱ).1.app Y) y)) =
      eqToHom (stageSheafPullbackComp_id_comp_target_eq_app S a ℱ Y)
        ((((S.stageSheafPullbackCompIso (Type u) (𝟙 i) a).hom.app ℱ).1.app Y) y) := by
    rw [he]
    exact stageSheafPullbackComp_id_comp_section_cast S a ℱ Y _
  exact hz.symm

/-- The right-unital degeneration of the stage pullback comparison. -/
theorem stageLACI_comp_id_degen
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (Adjunction.leftAdjointCompIso
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology j) (S.stageTopology j))
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        (stageSheafPushforwardCompIdIso S a)) =
      Functor.isoWhiskerLeft
          ((S.stageFunctor a).sheafPullback (Type u)
            (S.stageTopology i) (S.stageTopology j))
          (Adjunction.leftAdjointIdIso
            ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
              (Type u) (S.stageTopology j) (S.stageTopology j))
            (Functor.sheafPushforwardContinuousId'
              (eqToIso (stageFunctor_id_eq_local S j))
              (Type u) (S.stageTopology j))) ≪≫
        Functor.rightUnitor _ :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ rfl

/-- The left-unital degeneration of the stage pullback comparison. -/
theorem stageLACI_id_comp_degen
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i) :
    (Adjunction.leftAdjointCompIso
        ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology i))
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        ((S.stageFunctor a).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology j))
        (stageSheafPushforwardIdCompIso S a)) =
      Functor.isoWhiskerRight
          (Adjunction.leftAdjointIdIso
            ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous
              (Type u) (S.stageTopology i) (S.stageTopology i))
            (Functor.sheafPushforwardContinuousId'
              (eqToIso (CofilteredSiteDiagram.stageFunctor_id_eq S i))
              (Type u) (S.stageTopology i)))
          ((S.stageFunctor a).sheafPullback (Type u)
            (S.stageTopology i) (S.stageTopology j)) ≪≫
        Functor.leftUnitor _ :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ rfl

/-- The transpose of the identity-pullback comparison is the inverse identity-pushforward
comparison. -/
theorem homEquiv_pullbackIdIso_hom_app
    (S : CofilteredSiteDiagram.{u, u, u}) (j : S.I)
    (G : Sheaf (S.stageTopology j) (Type u)) :
    (((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
      (Type u) (S.stageTopology j) (S.stageTopology j)).homEquiv G G)
      ((Adjunction.leftAdjointIdIso
        ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology j) (S.stageTopology j))
        (Functor.sheafPushforwardContinuousId'
          (eqToIso (stageFunctor_id_eq_local S j))
          (Type u) (S.stageTopology j))).hom.app G) =
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (stageFunctor_id_eq_local S j))
        (Type u) (S.stageTopology j)).inv.app G := by
  have hexch := homEquiv_conjugateEquiv_exchange_aux Adjunction.id
    ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
      (Type u) (S.stageTopology j) (S.stageTopology j))
    ((Adjunction.leftAdjointIdIso
      ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
        (Type u) (S.stageTopology j) (S.stageTopology j))
      (Functor.sheafPushforwardContinuousId'
        (eqToIso (stageFunctor_id_eq_local S j))
        (Type u) (S.stageTopology j))).hom) (𝟙 G)
  refine Eq.trans (congrArg (fun f => (((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
    (Type u) (S.stageTopology j) (S.stageTopology j)).homEquiv G G) f)
    (Category.comp_id _).symm) (hexch.trans ?_)
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  refine Eq.trans (congrArg (fun t => t ≫
    (Functor.sheafPushforwardContinuousId' (eqToIso (stageFunctor_id_eq_local S j))
      (Type u) (S.stageTopology j)).inv.app G) (Adjunction.homEquiv_id Adjunction.id G)) ?_
  simp [Adjunction.id]

/-- The inverse identity-pushforward comparison evaluates as a section cast. -/
theorem pushforwardIdPrime_inv_app_eval
    (S : CofilteredSiteDiagram.{u, u, u}) (j : S.I)
    (G : Sheaf (S.stageTopology j) (Type u)) (Y : (S.stage j)ᵒᵖ)
    (hsec : (G.obj.obj Y) =
      ((((S.stageFunctor (𝟙 j)).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology j)).obj G).obj.obj Y))
    (z : G.obj.obj Y) :
    (((Functor.sheafPushforwardContinuousId'
      (eqToIso (stageFunctor_id_eq_local S j))
      (Type u) (S.stageTopology j)).inv.app G).1.app Y) z = eqToHom hsec z := by
  simp [Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousId,
    CategoryTheory.eqToHom_map, eqToHom_app]

/-- Lowering a stage pullback section along the identity arrow is a pure section cast. -/
theorem stageRestriction_comp_id_eval
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (Y₀ : S.stage j)
    (hsec : ((((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj ℱ).obj.obj (op Y₀)) =
      ((((S.stageFunctor (𝟙 j)).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology j)).obj
        (((S.stageFunctor (𝟙 j ≫ a)).sheafPullback (Type u)
          (S.stageTopology i) (S.stageTopology j)).obj ℱ)).obj.obj (op Y₀)))
    (z : (((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj ℱ).obj.obj (op Y₀)) :
    ((stageRestriction ℱ a (𝟙 j)).1.app (op Y₀)) z = eqToHom hsec z := by
  have c2 := stageSheafPullbackComp_comp_id_cast_mate_eval S a ℱ
    (op ((S.stageFunctor (𝟙 j)).obj Y₀))
    ((((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology j)).unit.app
      (((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj ℱ)).1.app (op Y₀) z)
  have c3 := congrFun (congrArg (fun t => (t.hom.app ℱ).1.app
      (op ((S.stageFunctor (𝟙 j)).obj Y₀)))
    (stageLACI_comp_id_degen S a))
    ((((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology j)).unit.app
      (((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj ℱ)).1.app (op Y₀) z)
  have c3' : (((Functor.isoWhiskerLeft
      ((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j))
      (Adjunction.leftAdjointIdIso
        ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology j) (S.stageTopology j))
        (Functor.sheafPushforwardContinuousId'
          (eqToIso (stageFunctor_id_eq_local S j))
          (Type u) (S.stageTopology j))) ≪≫
      Functor.rightUnitor _).hom.app ℱ).1.app
      (op ((S.stageFunctor (𝟙 j)).obj Y₀)))
      ((((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) (S.stageTopology j)).unit.app
        (((S.stageFunctor a).sheafPullback (Type u)
          (S.stageTopology i) (S.stageTopology j)).obj ℱ)).1.app (op Y₀) z) =
      (((Adjunction.leftAdjointIdIso
        ((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology j) (S.stageTopology j))
        (Functor.sheafPushforwardContinuousId'
          (eqToIso (stageFunctor_id_eq_local S j))
          (Type u) (S.stageTopology j))).hom.app
        (((S.stageFunctor a).sheafPullback (Type u)
          (S.stageTopology i) (S.stageTopology j)).obj ℱ)).1.app
        (op ((S.stageFunctor (𝟙 j)).obj Y₀)))
      ((((S.stageFunctor (𝟙 j)).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) (S.stageTopology j)).unit.app
        (((S.stageFunctor a).sheafPullback (Type u)
          (S.stageTopology i) (S.stageTopology j)).obj ℱ)).1.app (op Y₀) z) := by
    simp
  have c4 := congrFun (congrArg (fun t => t.1.app (op Y₀))
    (homEquiv_pullbackIdIso_hom_app S j
      (((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj ℱ))) z
  have c5 := pushforwardIdPrime_inv_app_eval S j
    (((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).obj ℱ) (op Y₀)
    (by
      simpa using congrArg
        (fun G : S.stage j ⥤ S.stage j =>
          ((((S.stageFunctor a).sheafPullback (Type u)
            (S.stageTopology i) (S.stageTopology j)).obj ℱ)).obj.obj (op (G.obj Y₀)))
        (CofilteredSiteDiagram.stageFunctor_id_eq S j).symm) z
  refine Eq.trans (cast_step_symm c2).symm ?_
  refine (congrArg (fun w => eqToHom
    (stageSheafPullbackComp_comp_id_target_eq_app S a ℱ
      (op ((S.stageFunctor (𝟙 j)).obj Y₀))).symm w)
    ((c3.trans c3').trans (c4.trans c5))).trans ?_
  exact eqToHom_apply_collapse₂₁_aux _ _ hsec z

/-- Lowering the identity-stage structure section along `a` is the unit section up to cast. -/
theorem stageRestriction_id_comp_eval
    (S : CofilteredSiteDiagram.{u, u, u}) {i j : S.I} (a : j ⟶ i)
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (W₀ : S.stage i)
    (hsec : ((((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj ℱ).obj.obj
        (op ((S.stageFunctor a).obj W₀))) =
      ((((S.stageFunctor (a ≫ 𝟙 i)).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).obj ℱ).obj.obj
        (op ((S.stageFunctor a).obj W₀))))
    (s : ℱ.obj.obj (op W₀)) :
    ((stageRestriction ℱ (𝟙 i) a).1.app (op W₀))
      ((((stagePullbackIdIso i).inv.app ℱ).1.app (op W₀)) s) =
    eqToHom hsec
      ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).unit.app ℱ).1.app (op W₀) s) := by
  have k2 := congrFun (congrArg (fun t => t.1.app (op W₀))
    (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).unit.naturality
      ((stagePullbackIdIso i).inv.app ℱ))) s
  simp only [Functor.id_map] at k2
  have k3 := stageSheafPullbackComp_id_comp_cast_mate_eval S a ℱ
    (op ((S.stageFunctor a).obj W₀))
    ((((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).map
      ((stagePullbackIdIso i).inv.app ℱ)).1.app (op ((S.stageFunctor a).obj W₀))
      ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).unit.app ℱ).1.app (op W₀) s))
  have k4 := congrFun (congrArg (fun t => (t.hom.app ℱ).1.app
      (op ((S.stageFunctor a).obj W₀)))
    (stageLACI_id_comp_degen S a))
    ((((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).map
      ((stagePullbackIdIso i).inv.app ℱ)).1.app (op ((S.stageFunctor a).obj W₀))
      ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).unit.app ℱ).1.app (op W₀) s))
  have k4' : (((Functor.isoWhiskerRight
      (Adjunction.leftAdjointIdIso
        ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous
          (Type u) (S.stageTopology i) (S.stageTopology i))
        (Functor.sheafPushforwardContinuousId'
          (eqToIso (CofilteredSiteDiagram.stageFunctor_id_eq S i))
          (Type u) (S.stageTopology i)))
      ((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)) ≪≫
      Functor.leftUnitor _).hom.app ℱ).1.app (op ((S.stageFunctor a).obj W₀)))
      ((((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).map
        ((stagePullbackIdIso i).inv.app ℱ)).1.app (op ((S.stageFunctor a).obj W₀))
        ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology j)).unit.app ℱ).1.app (op W₀) s)) =
      ((((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).map
        ((stagePullbackIdIso i).hom.app ℱ)).1.app (op ((S.stageFunctor a).obj W₀)))
      ((((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i) (S.stageTopology j)).map
        ((stagePullbackIdIso i).inv.app ℱ)).1.app (op ((S.stageFunctor a).obj W₀))
        ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology j)).unit.app ℱ).1.app (op W₀) s)) := by
    simp [stagePullbackIdIso]
  have hm : ((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).map ((stagePullbackIdIso i).inv.app ℱ) ≫
      ((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i) (S.stageTopology j)).map ((stagePullbackIdIso i).hom.app ℱ) =
      𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  have k5 := congrFun (congrArg (fun m => m.1.app (op ((S.stageFunctor a).obj W₀))) hm)
    ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).unit.app ℱ).1.app (op W₀) s)
  refine Eq.trans (congrArg (fun w => ((S.stageSheafPullbackCompIso (Type u) (𝟙 i) a).hom.app
    ℱ).1.app (op ((S.stageFunctor a).obj W₀)) w) k2) ?_
  refine Eq.trans (cast_step_symm k3).symm ?_
  refine (congrArg (fun w => eqToHom
    (stageSheafPullbackComp_id_comp_target_eq_app S a ℱ
      (op ((S.stageFunctor a).obj W₀))).symm w)
    ((k4.trans k4').trans k5)).trans ?_
  rfl

/-- The inverse mixed pushforward comparison acts on sections as a pure cast. -/
theorem mixedPushComp_inv_app_eval_cast
    (S : CofilteredSiteDiagram.{u, u, u}) {j k : S.I} (b : k ⟶ j)
    (G : Sheaf S.colimitTopology (Type u)) (W : (S.stage j)ᵒᵖ)
    (hsec : ((((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).obj G).obj.obj W) =
      ((((S.stageFunctor b).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)).obj
        (((S.stageCoconeFunctor k).sheafPushforwardContinuous (Type u)
          (S.stageTopology k) S.colimitTopology).obj G)).obj.obj W))
    (z : (((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).obj G).obj.obj W) :
    (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq b))
      (Type u) (S.stageTopology j) (S.stageTopology k) S.colimitTopology).inv.app
      G).1.app W) z = eqToHom hsec z := by
  simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
    CategoryTheory.eqToHom_map, eqToHom_app]

/-- The unit representative and the identity representative are related. -/
theorem auxiliaryUnit_rep_rel
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {j : S.I} (a : j ⟶ i)
    (W₀ : S.stage i) (s : ℱ.obj.obj (op W₀))
    (h₂ : S.ιObj i W₀ = S.ιObj j ((S.stageFunctor a).obj W₀)) :
    grel
      (⟨j, a, (S.stageFunctor a).obj W₀, rfl,
        (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
          (S.stageTopology i) (S.stageTopology j)).unit.app ℱ).1.app (op W₀) s⟩ :
        GRep S ℱ (S.ιObj j ((S.stageFunctor a).obj W₀)))
      ⟨i, 𝟙 i, W₀, h₂,
        (((stagePullbackIdIso i).inv.app ℱ).1.app (op W₀)) s⟩ := by
  refine ⟨j, 𝟙 j, a, by simp, ?_, ?_⟩
  · exact S.stageFunctor_obj_id ((S.stageFunctor a).obj W₀)
  · have hL := stageRestriction_comp_id_eval S a ℱ ((S.stageFunctor a).obj W₀)
      (gsec_type_congr ℱ (show a = 𝟙 j ≫ a by simp)
        (S.stageFunctor_obj_id ((S.stageFunctor a).obj W₀)).symm)
      ((((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).unit.app ℱ).1.app (op W₀) s)
    have hR := stageRestriction_id_comp_eval S a ℱ W₀
      (gsec_type_congr ℱ (Category.comp_id a).symm rfl) s
    refine (congrArg (fun w => eqToHom (gsec_type_congr ℱ
      (show 𝟙 j ≫ a = a ≫ 𝟙 i by simp)
      (S.stageFunctor_obj_id ((S.stageFunctor a).obj W₀))) w) hL).trans ?_
    refine Eq.trans (eqToHom_apply_collapse₂₁_aux _ _
      (gsec_type_congr ℱ (Category.comp_id a).symm rfl) _) ?_
    exact hR.symm

/-- The stage triangle: the unit composed with the pushforward of the stage structure map is
the auxiliary unit conjugated through the pushforward composition comparison. -/
theorem auxiliaryStage_triangle
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {j : S.I} (a : j ⟶ i) :
    ((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).unit.app ℱ ≫
      ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).map (auxiliaryStageMap ℱ a) =
    auxiliaryUnit ℱ ≫
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq a))
        (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology).inv.app
        (auxiliarySheaf ℱ) := by
  apply Sheaf.hom_ext
  ext W s
  refine Eq.trans (_root_.Quotient.sound (auxiliaryUnit_rep_rel S ℱ a W.unop s
    ((S.ιObj_lower a W.unop).symm))) ?_
  refine Eq.trans (GSec.cast_mk ((S.ιObj_lower a W.unop).symm)
    (⟨i, 𝟙 i, W.unop, rfl,
      (((stagePullbackIdIso i).inv.app ℱ).1.app (op W.unop)) s⟩ :
      GRep S ℱ (S.ιObj i W.unop))
    (congrArg (fun V : S.ColimitCategory => GSec ℱ V)
      (S.ιObj_lower a W.unop).symm)).symm ?_
  exact (mixedPushComp_inv_app_eval_cast S a (auxiliarySheaf ℱ) W
    (congrArg (fun V : S.ColimitCategory => GSec ℱ V)
      (S.ιObj_lower a W.unop).symm)
    ((auxiliaryUnit ℱ).1.app W s)).symm

/-- Morphisms out of the auxiliary sheaf are determined by their unit-side transposes. -/
theorem auxiliary_hom_ext
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) {H : Sheaf S.colimitTopology (Type u)}
    {φ₁ φ₂ : auxiliarySheaf ℱ ⟶ H}
    (h : auxiliaryUnit ℱ ≫ ((S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) S.colimitTopology).map φ₁ =
      auxiliaryUnit ℱ ≫ ((S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) S.colimitTopology).map φ₂) :
    φ₁ = φ₂ := by
  have hdet : ∀ (φ : auxiliarySheaf ℱ ⟶ H) {j : S.I} (a : j ⟶ i),
      (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).homEquiv ℱ _)
        (auxiliaryStageMap ℱ a ≫
          ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
            (S.stageTopology j) S.colimitTopology).map φ) =
      (auxiliaryUnit ℱ ≫ ((S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) S.colimitTopology).map φ) ≫
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (S.stageCoconeFunctor_comp_eq a))
          (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology).inv.app H := by
    intro φ j a
    rw [Adjunction.homEquiv_naturality_right]
    refine Eq.trans (congrArg (fun t => t ≫
      ((S.stageFunctor a).sheafPushforwardContinuous (Type u)
        (S.stageTopology i) (S.stageTopology j)).map
        (((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
          (S.stageTopology j) S.colimitTopology).map φ))
      ((Adjunction.homEquiv_unit _ _ _ _).trans (auxiliaryStage_triangle S ℱ a))) ?_
    simp only [Category.assoc]
    exact congrArg (fun t => auxiliaryUnit ℱ ≫ t)
      ((Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq a))
        (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology).inv.naturality
        φ).symm
  have hσ : ∀ {j : S.I} (a : j ⟶ i),
      auxiliaryStageMap ℱ a ≫
        ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
          (S.stageTopology j) S.colimitTopology).map φ₁ =
      auxiliaryStageMap ℱ a ≫
        ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
          (S.stageTopology j) S.colimitTopology).map φ₂ := by
    intro j a
    apply Equiv.injective (((S.stageFunctor a).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i) (S.stageTopology j)).homEquiv ℱ _)
    exact (hdet φ₁ a).trans ((congrArg (fun t => t ≫
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (S.stageCoconeFunctor_comp_eq a))
        (Type u) (S.stageTopology i) (S.stageTopology j) S.colimitTopology).inv.app H) h).trans
      (hdet φ₂ a).symm)
  apply Sheaf.hom_ext
  ext V x
  induction x using _root_.Quotient.inductionOn with | _ r =>
  have hcast := (GSec.cast_mk r.hW
    (⟨r.j, r.a, r.W, rfl, r.s⟩ : GRep S ℱ (S.ιObj r.j r.W))
    (congrArg (fun v : S.ColimitCategory => GSec ℱ v) r.hW)).symm
  have hmap := presheaf_map_eqToHom_op_eval (auxiliaryPresheaf ℱ) r.hW.symm
    (congrArg (fun v : S.ColimitCategory => GSec ℱ v) r.hW)
    (GSec.mk (⟨r.j, r.a, r.W, rfl, r.s⟩ : GRep S ℱ (S.ιObj r.j r.W)))
  have hkey := congrFun (congrArg (fun t => t.1.app (op r.W)) (hσ r.a)) r.s
  have hn₁ := congrFun (φ₁.1.naturality ((eqToHom r.hW.symm).op))
    (GSec.mk (⟨r.j, r.a, r.W, rfl, r.s⟩ : GRep S ℱ (S.ιObj r.j r.W)))
  have hn₂ := congrFun (φ₂.1.naturality ((eqToHom r.hW.symm).op))
    (GSec.mk (⟨r.j, r.a, r.W, rfl, r.s⟩ : GRep S ℱ (S.ιObj r.j r.W)))
  have hx : (GSec.mk r : GSec ℱ V.unop) =
      (auxiliaryPresheaf ℱ).map ((eqToHom r.hW.symm).op)
        (GSec.mk (⟨r.j, r.a, r.W, rfl, r.s⟩ : GRep S ℱ (S.ιObj r.j r.W))) :=
    (hcast.trans hmap.symm)
  show φ₁.1.app V (GSec.mk r) = φ₂.1.app V (GSec.mk r)
  rw [hx]
  refine hn₁.trans (Eq.trans ?_ hn₂.symm)
  exact congrArg (fun z => H.obj.map ((eqToHom r.hW.symm).op) z) hkey

/-- The second triangle: the comparison morphism splits the transposed unit. -/
theorem auxiliaryToPullback_comp_fromPullback
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    auxiliaryToPullback S ℱ ≫ auxiliaryFromPullback S ℱ = 𝟙 (auxiliarySheaf ℱ) := by
  apply auxiliary_hom_ext S ℱ
  rw [Functor.map_comp, Functor.map_id, Category.comp_id, ← Category.assoc,
    auxiliaryUnit_comp_toPullback]
  exact ((Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _))

/-- The auxiliary sheaf is isomorphic to the colimit-site pullback sheaf. -/
noncomputable def auxiliaryIso
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) :
    auxiliarySheaf ℱ ≅ ((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ where
  hom := auxiliaryToPullback S ℱ
  inv := auxiliaryFromPullback S ℱ
  hom_inv_id := auxiliaryToPullback_comp_fromPullback S ℱ
  inv_hom_id := auxiliaryFromPullback_comp_toPullback S ℱ

/-- The comparison map is bijective on sections over every colimit object. -/
theorem auxiliaryToPullbackApp_bijective
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (V : S.ColimitCategory) :
    Function.Bijective (auxiliaryToPullbackApp S ℱ V) := by
  have h₁ := congrFun (congrArg (fun t => t.1.app (op V))
    (auxiliaryToPullback_comp_fromPullback S ℱ))
  have h₂ := congrFun (congrArg (fun t => t.1.app (op V))
    (auxiliaryFromPullback_comp_toPullback S ℱ))
  exact Function.bijective_iff_has_inverse.2
    ⟨((auxiliaryFromPullback S ℱ).1.app (op V)), fun x => h₁ x, fun y => h₂ y⟩

/-- The class cocone: every stage section over a lowering of `X` defines an auxiliary class. -/
noncomputable def auxiliaryClassCocone
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Cocone (colimitSiteStagePullbackSectionDiagram S ℱ X) where
  pt := GSec ℱ (S.ιObj i X)
  ι :=
    { app := fun A ω => GSec.mk (⟨A.unop.left, A.unop.hom, S.overImage X A,
        S.ιObj_lower A.unop.hom X, ω⟩ : GRep S ℱ (S.ιObj i X))
      naturality := by
        intro A B u
        funext ω
        -- identify the transition value with the lowered representative section
        have h'u : (stageSheafPullbackAlong S (overLeftHom u ≫ A.unop.hom)).obj ℱ =
            (overStageSheafPullback S B).obj ℱ := by
          simpa [overStageSheafPullback] using
            congrArg (fun f : B.unop.left ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
            (show overLeftHom u ≫ A.unop.hom = B.unop.hom by simpa using Over.w u.unop)
        have htrans_el : ((colimitSiteStagePullbackSectionTransition S ℱ u).1.app
            (op (S.overImage X A))) ω =
            eqToHom (congrArg (fun G : Sheaf (S.stageTopology B.unop.left) (Type u) =>
              G.obj.obj (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) h'u)
            (((⟨A.unop.left, A.unop.hom, S.overImage X A,
              S.ιObj_lower A.unop.hom X, ω⟩ : GRep S ℱ (S.ιObj i X)).lower ℱ
              (overLeftHom u)).s) := by
          have hform := congrFun (congrArg (fun t => t.1.app (op (S.overImage X A)))
            (Adjunction.homEquiv_naturality_right
              ((S.stageFunctor (overLeftHom u)).sheafAdjunctionContinuous (Type u)
                (S.stageTopology A.unop.left) (S.stageTopology B.unop.left))
              ((S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ)
              (eqToHom h'u))) ω
          refine hform.trans ?_
          exact sheaf_functor_map_eqToHom_eval
            ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous (Type u)
              (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)) h'u
            (op (S.overImage X A))
            (congrArg (fun G : Sheaf (S.stageTopology B.unop.left) (Type u) =>
              G.obj.obj (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) h'u)
            _
        have hov : B.unop.hom = overLeftHom u ≫ A.unop.hom :=
          (show overLeftHom u ≫ A.unop.hom = B.unop.hom by simpa using Over.w u.unop).symm
        have hwBA : S.overImage X B =
            (S.stageFunctor (overLeftHom u)).obj (S.overImage X A) := by
          calc S.overImage X B
              = (S.stageFunctor (overLeftHom u ≫ A.unop.hom)).obj X := by
                simpa [CofilteredSiteDiagram.overImage] using
                  congrArg (fun f : B.unop.left ⟶ i => (S.stageFunctor f).obj X) hov
            _ = (S.stageFunctor (overLeftHom u)).obj (S.overImage X A) :=
                (S.stageFunctor_obj_comp A.unop.hom (overLeftHom u) X).symm
        refine Eq.trans (congrArg (fun z => GSec.mk (⟨B.unop.left, B.unop.hom,
          S.overImage X B, S.ιObj_lower B.unop.hom X, z⟩ : GRep S ℱ (S.ιObj i X)))
          (congrArg (fun w => eqToHom
            (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u) w) htrans_el)) ?_
        refine _root_.Quotient.sound (grel_trans
          (grel_of_components hov hwBA ?_)
          (grel_symm (grel_lower (⟨A.unop.left, A.unop.hom, S.overImage X A,
            S.ιObj_lower A.unop.hom X, ω⟩ : GRep S ℱ (S.ιObj i X)) (overLeftHom u))))
        refine Eq.trans (congrArg (fun w => eqToHom (gsec_type_congr ℱ hov hwBA) w)
          (eqToHom_apply_collapse₂₁_aux
            (congrArg (fun G : Sheaf (S.stageTopology B.unop.left) (Type u) =>
              G.obj.obj (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) h'u)
            (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u)
            ((congrArg (fun G : Sheaf (S.stageTopology B.unop.left) (Type u) =>
              G.obj.obj (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) h'u).trans
              (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u)) _)) ?_
        exact eqToHom_apply_collapse₂₁_aux _ _ rfl _ }

/-- The diagram transition evaluates as the lowered representative section. -/
theorem sectionMap_eval_lower
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (u : A ⟶ B)
    (ω : colimitSiteStagePullbackSectionValue S ℱ X A)
    (hcast : (((stageSheafPullbackAlong S (overLeftHom u ≫ A.unop.hom)).obj ℱ).obj.obj
        (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) =
      colimitSiteStagePullbackSectionValue S ℱ X B) :
    colimitSiteStagePullbackSectionMap S ℱ X u ω =
      eqToHom hcast
        (((⟨A.unop.left, A.unop.hom, S.overImage X A,
          S.ιObj_lower A.unop.hom X, ω⟩ : GRep S ℱ (S.ιObj i X)).lower ℱ
          (overLeftHom u)).s) := by
  have h'u : (stageSheafPullbackAlong S (overLeftHom u ≫ A.unop.hom)).obj ℱ =
      (overStageSheafPullback S B).obj ℱ := by
    simpa [overStageSheafPullback] using
      congrArg (fun f : B.unop.left ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ)
      (show overLeftHom u ≫ A.unop.hom = B.unop.hom by simpa using Over.w u.unop)
  have htrans_el : ((colimitSiteStagePullbackSectionTransition S ℱ u).1.app
      (op (S.overImage X A))) ω =
      eqToHom (congrArg (fun G : Sheaf (S.stageTopology B.unop.left) (Type u) =>
        G.obj.obj (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) h'u)
      (((⟨A.unop.left, A.unop.hom, S.overImage X A,
        S.ιObj_lower A.unop.hom X, ω⟩ : GRep S ℱ (S.ιObj i X)).lower ℱ
        (overLeftHom u)).s) := by
    have hform := congrFun (congrArg (fun t => t.1.app (op (S.overImage X A)))
      (Adjunction.homEquiv_naturality_right
        ((S.stageFunctor (overLeftHom u)).sheafAdjunctionContinuous (Type u)
          (S.stageTopology A.unop.left) (S.stageTopology B.unop.left))
        ((S.stageSheafPullbackCompIso (Type u) A.unop.hom (overLeftHom u)).hom.app ℱ)
        (eqToHom h'u))) ω
    refine hform.trans ?_
    exact sheaf_functor_map_eqToHom_eval
      ((S.stageFunctor (overLeftHom u)).sheafPushforwardContinuous (Type u)
        (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)) h'u
      (op (S.overImage X A))
      (congrArg (fun G : Sheaf (S.stageTopology B.unop.left) (Type u) =>
        G.obj.obj (op ((S.stageFunctor (overLeftHom u)).obj (S.overImage X A)))) h'u)
      _
  refine Eq.trans (congrArg (fun w => eqToHom
    (colimitSiteStagePullbackSectionMap_target_eq S ℱ X u) w) htrans_el) ?_
  exact eqToHom_apply_collapse₂₁_aux _ _ hcast _

/-- The class comparison map from the section colimit. -/
noncomputable def auxiliaryClassMap
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    colimit (colimitSiteStagePullbackSectionDiagram S ℱ X) ⟶ GSec ℱ (S.ιObj i X) :=
  colimit.desc _ (auxiliaryClassCocone S ℱ X)

/-- The class comparison map computes on colimit injections as the tautological class. -/
theorem auxiliaryClassMap_ι
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) (ω : colimitSiteStagePullbackSectionValue S ℱ X A) :
    auxiliaryClassMap S ℱ X
      (colimit.ι (colimitSiteStagePullbackSectionDiagram S ℱ X) A ω) =
      GSec.mk (⟨A.unop.left, A.unop.hom, S.overImage X A,
        S.ιObj_lower A.unop.hom X, ω⟩ : GRep S ℱ (S.ιObj i X)) :=
  congrFun (colimit.ι_desc (auxiliaryClassCocone S ℱ X) A) ω

/-- The class comparison map is surjective. -/
theorem auxiliaryClassMap_surjective
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Function.Surjective (auxiliaryClassMap S ℱ X) := by
  intro x
  obtain ⟨k, e, a', σ, hσ⟩ := GSec.exists_lowered_rep x
  obtain ⟨n, w, hwa⟩ : ∃ (n : S.I) (w : n ⟶ k), w ≫ a' = w ≫ e :=
    ⟨_, IsCofiltered.eqHom _ _, IsCofiltered.eq_condition _ _⟩
  -- the diagonal representative at the merged stage
  have hWdiag : (S.stageFunctor w).obj ((S.stageFunctor e).obj X) =
      (S.stageFunctor (w ≫ a')).obj X :=
    (S.stageFunctor_obj_comp e w X).trans
      (congrArg (fun c : n ⟶ i => (S.stageFunctor c).obj X) hwa.symm)
  refine ⟨colimit.ι (colimitSiteStagePullbackSectionDiagram S ℱ X)
    (op (Over.mk (w ≫ a')))
    (eqToHom (gsec_type_congr ℱ rfl hWdiag)
      (((⟨k, a', (S.stageFunctor e).obj X, S.ιObj_lower e X, σ⟩ :
        GRep S ℱ (S.ιObj i X)).lower ℱ w).s)), ?_⟩
  rw [auxiliaryClassMap_ι]
  refine Eq.trans (_root_.Quotient.sound (grel_trans
    (grel_of_components rfl hWdiag.symm
      (eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ rfl hWdiag)
        (gsec_type_congr ℱ rfl hWdiag.symm) rfl _))
    (grel_symm (grel_lower (⟨k, a', (S.stageFunctor e).obj X,
      S.ιObj_lower e X, σ⟩ : GRep S ℱ (S.ιObj i X)) w)))) hσ

/-- The class comparison map is injective. -/
theorem auxiliaryClassMap_injective
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Function.Injective (auxiliaryClassMap S ℱ X) := by
  intro z₁ z₂ h
  obtain ⟨A₁, x₁, rfl⟩ := Types.jointly_surjective'
    (F := colimitSiteStagePullbackSectionDiagram S ℱ X) z₁
  obtain ⟨A₂, x₂, rfl⟩ := Types.jointly_surjective'
    (F := colimitSiteStagePullbackSectionDiagram S ℱ X) z₂
  rw [auxiliaryClassMap_ι, auxiliaryClassMap_ι] at h
  obtain ⟨k, b₁, b₂, ha, hw, hs⟩ := GSec.mk_eq_mk.1 h
  -- the merged over-object receiving both representatives
  have hw₂ : b₂ ≫ A₂.unop.hom = b₁ ≫ A₁.unop.hom := ha.symm
  have e₁ := congrFun (colimit.w (colimitSiteStagePullbackSectionDiagram S ℱ X)
    ((Over.homMk b₁ (rfl : b₁ ≫ A₁.unop.hom = b₁ ≫ A₁.unop.hom) :
      Over.mk (b₁ ≫ A₁.unop.hom) ⟶ A₁.unop).op : A₁ ⟶ op (Over.mk (b₁ ≫ A₁.unop.hom)))) x₁
  have e₂ := congrFun (colimit.w (colimitSiteStagePullbackSectionDiagram S ℱ X)
    ((Over.homMk b₂ hw₂ :
      Over.mk (b₁ ≫ A₁.unop.hom) ⟶ A₂.unop).op : A₂ ⟶ op (Over.mk (b₁ ≫ A₁.unop.hom)))) x₂
  -- the casts of the evaluation lemma
  have h'u₁ : (stageSheafPullbackAlong S (b₁ ≫ A₁.unop.hom)).obj ℱ =
      (overStageSheafPullback S (op (Over.mk (b₁ ≫ A₁.unop.hom)))).obj ℱ := rfl
  have h'u₂ : (stageSheafPullbackAlong S (b₂ ≫ A₂.unop.hom)).obj ℱ =
      (overStageSheafPullback S (op (Over.mk (b₁ ≫ A₁.unop.hom)))).obj ℱ := by
    simpa [overStageSheafPullback] using
      congrArg (fun f : k ⟶ i ↦ (stageSheafPullbackAlong S f).obj ℱ) hw₂
  have T₁ : (((stageSheafPullbackAlong S (b₁ ≫ A₁.unop.hom)).obj ℱ).obj.obj
      (op ((S.stageFunctor b₁).obj (S.overImage X A₁)))) =
      colimitSiteStagePullbackSectionValue S ℱ X (op (Over.mk (b₁ ≫ A₁.unop.hom))) :=
    (congrArg (fun G : Sheaf (S.stageTopology k) (Type u) =>
      G.obj.obj (op ((S.stageFunctor b₁).obj (S.overImage X A₁)))) h'u₁).trans
    (colimitSiteStagePullbackSectionMap_target_eq S ℱ X
      ((Over.homMk b₁ (rfl : b₁ ≫ A₁.unop.hom = b₁ ≫ A₁.unop.hom) :
        Over.mk (b₁ ≫ A₁.unop.hom) ⟶ A₁.unop).op))
  have T₂ : (((stageSheafPullbackAlong S (b₂ ≫ A₂.unop.hom)).obj ℱ).obj.obj
      (op ((S.stageFunctor b₂).obj (S.overImage X A₂)))) =
      colimitSiteStagePullbackSectionValue S ℱ X (op (Over.mk (b₁ ≫ A₁.unop.hom))) :=
    (congrArg (fun G : Sheaf (S.stageTopology k) (Type u) =>
      G.obj.obj (op ((S.stageFunctor b₂).obj (S.overImage X A₂)))) h'u₂).trans
    (colimitSiteStagePullbackSectionMap_target_eq S ℱ X
      ((Over.homMk b₂ hw₂ :
        Over.mk (b₁ ≫ A₁.unop.hom) ⟶ A₂.unop).op))
  have hl₁ := sectionMap_eval_lower S ℱ X
    ((Over.homMk b₁ (rfl : b₁ ≫ A₁.unop.hom = b₁ ≫ A₁.unop.hom) :
      Over.mk (b₁ ≫ A₁.unop.hom) ⟶ A₁.unop).op) x₁ T₁
  have hl₂ := sectionMap_eval_lower S ℱ X
    ((Over.homMk b₂ hw₂ :
      Over.mk (b₁ ≫ A₁.unop.hom) ⟶ A₂.unop).op) x₂ T₂
  have hmap : colimitSiteStagePullbackSectionMap S ℱ X
      ((Over.homMk b₁ (rfl : b₁ ≫ A₁.unop.hom = b₁ ≫ A₁.unop.hom) :
        Over.mk (b₁ ≫ A₁.unop.hom) ⟶ A₁.unop).op) x₁ =
      colimitSiteStagePullbackSectionMap S ℱ X
      ((Over.homMk b₂ hw₂ :
        Over.mk (b₁ ≫ A₁.unop.hom) ⟶ A₂.unop).op) x₂ := by
    refine hl₁.trans (Eq.trans ?_ hl₂.symm)
    refine Eq.trans ((eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ ha hw) T₂ T₁ _).symm) ?_
    exact congrArg (fun w => eqToHom T₂ w) hs
  exact e₁.symm.trans ((congrArg (colimit.ι
    (colimitSiteStagePullbackSectionDiagram S ℱ X)
    (op (Over.mk (b₁ ≫ A₁.unop.hom)))) hmap).trans e₂)

/-- The class comparison map is bijective. -/
theorem auxiliaryClassMap_bijective
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Function.Bijective (auxiliaryClassMap S ℱ X) :=
  ⟨auxiliaryClassMap_injective S ℱ X, auxiliaryClassMap_surjective S ℱ X⟩

/-- The comparison cocone leg is the representative-level comparison of the tautological
class. -/
theorem comparisonLeg_eq_auxiliary
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) (ω : colimitSiteStagePullbackSectionValue S ℱ X A) :
    ((colimitSiteStagePullbackSectionsComparisonCocone S ℱ X).ι.app A) ω =
      auxiliaryToPullback₀ S ℱ
        (⟨A.unop.left, A.unop.hom, S.overImage X A,
          S.ιObj_lower A.unop.hom X, ω⟩ : GRep S ℱ (S.ιObj i X)) := by
  refine Eq.trans ?_ (presheaf_map_eqToHom_op_eval
    ((((S.stageCoconeFunctor i).sheafPullback (Type u)
      (S.stageTopology i) S.colimitTopology).obj ℱ).obj)
    (S.ιObj_lower A.unop.hom X).symm
    (by simpa using colimitSiteStagePullbackSectionsComparisonTarget_eq S ℱ X A)
    (((colimitRestriction S ℱ A.unop.hom).1.app (op (S.overImage X A))) ω)).symm
  rfl

end AuxiliaryIso

/-- Lemma 7.18.3, equation `(7.18.3.1)`, as an isomorphism in `Type`. -/
theorem colimitSiteStagePullbackSectionsComparison_isIso
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    IsIso (colimitSiteStagePullbackSectionsComparison S ℱ X) := by
  -- ARCHITECTURE (settled 2026-06-12, see memory for full analysis). Choice-free G-route:
  -- let `P_A := Lan_{(u_{A.left}).op} (pull_{A.hom}ℱ).val` be the presheaf pullbacks and
  -- `Q := colim_A P_A` the PRESHEAF colimit over `(Over i)ᵒᵖ` (no presentation category needed).
  -- Then:
  -- (ii)  `Q(u_iX) = colim_A [P_A(u_iX)]` is formal (presheaf colimits are pointwise);
  -- (iii) `colim_A [(pull_{A.hom}ℱ)(im_A)] ≅ colim_A [P_A(u_iX)]`: the Lan sections are comma
  --       colimits, and in the outer filtered colimit every comma object merges with the
  --       canonical pair `(im_A, identity)` by `exists_hom_rep`/`exists_hom_rep_pair` descent —
  --       a filtered-colimit element calculus exactly like the bind-axiom proof;
  -- (i)   `Q` is a sheaf: coverings of the colimit site are finite stage images
  --       (`Precoverage.exists_mem_generate_le_of_mem_toGrothendieck` + `stageCov_finite`), H⁰
  --       commutes with the filtered A-colimit (finite limits vs filtered colimits), and after
  --       (iii) the stage H⁰ reduces to the stage sheaf condition for `pull_{A.hom}ℱ`;
  -- (iv)  sheafification is a left adjoint, so `colim D ≅ sheafify Q` where
  --       `D_A := pull-cocone-A.left (pull_{A.hom}ℱ)`, and `D ≅ const (f_i⁻¹ℱ)` via
  --       `colimitStageSheafPullbackCompIso` (naturality = the PROVEN
  --       `colimitStageSheafPullbackCompIso_assoc_app`), with `(Over i)ᵒᵖ` connected (initial
  --       object), hence `colim D ≅ f_i⁻¹ℱ`;
  -- conclude: `f_i⁻¹ℱ(u_iX) = (sheafify Q)(u_iX) = Q(u_iX)` (by (i) `toSheafify` is an iso)
  -- `= colim_A [P_A(u_iX)] = colim_A [(pull_{A.hom}ℱ)(im_A)]`, compatibly with the legs.
  -- EXECUTED via the auxiliary sheaf: the comparison factors as the class comparison map
  -- (bijective by the quotient description) followed by the auxiliary-to-pullback comparison
  -- (bijective by the universal property isomorphism).
  rw [isIso_iff_bijective]
  have hφ : ∀ z, colimitSiteStagePullbackSectionsComparison S ℱ X z =
      auxiliaryToPullbackApp S ℱ (S.ιObj i X) (auxiliaryClassMap S ℱ X z) := by
    intro z
    obtain ⟨A, ω, rfl⟩ := Types.jointly_surjective'
      (F := colimitSiteStagePullbackSectionDiagram S ℱ X) z
    have h₁ : colimitSiteStagePullbackSectionsComparison S ℱ X
        (colimit.ι (colimitSiteStagePullbackSectionDiagram S ℱ X) A ω) =
        ((colimitSiteStagePullbackSectionsComparisonCocone S ℱ X).ι.app A) ω :=
      congrFun (colimit.ι_desc
        (colimitSiteStagePullbackSectionsComparisonCocone S ℱ X) A) ω
    rw [auxiliaryClassMap_ι]
    exact h₁.trans (comparisonLeg_eq_auxiliary S ℱ X A ω)
  have hφeq : colimitSiteStagePullbackSectionsComparison S ℱ X =
      fun z => auxiliaryToPullbackApp S ℱ (S.ιObj i X) (auxiliaryClassMap S ℱ X z) :=
    funext hφ
  rw [hφeq]
  exact Function.Bijective.comp (auxiliaryToPullbackApp_bijective S ℱ _)
    (auxiliaryClassMap_bijective S ℱ X)

/-- Lemma 7.18.3, equation `(7.18.3.1)`, in the source-text bijectivity form. -/
theorem colimitSiteStagePullbackSectionsComparison_bijective
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (ℱ : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Function.Bijective (colimitSiteStagePullbackSectionsComparison S ℱ X) := by
  simpa [isIso_iff_bijective] using
    (colimitSiteStagePullbackSectionsComparison_isIso S ℱ X)

/-- Merge two transports at the head of a composite. -/
theorem eqToHom_head_merge {D : Type*} [Category D] {A B C R : D}
    (p : A = B) (q : B = C) (r : A = C) (m : C ⟶ R) :
    eqToHom p ≫ eqToHom q ≫ m = eqToHom r ≫ m := by
  subst_vars
  simp

/-- Inserting a cancelling transport pair between two composite factors changes nothing. -/
theorem eqToHom_insert_cancel {D : Type*} [Category D] {A B C D' E T : D}
    (α : A = B) (M₁ : B ⟶ C) (γ : C = D') (M₂ : C ⟶ E) (β : E = T) :
    eqToHom α ≫ (M₁ ≫ M₂) ≫ eqToHom β =
      eqToHom α ≫ (M₁ ≫ eqToHom γ) ≫ eqToHom γ.symm ≫ M₂ ≫ eqToHom β := by
  subst_vars
  simp

/-- Two transport-conjugated composites of a common middle along different object paths agree. -/
theorem eqToHom_conj_paths {D : Type*} [Category D] {A B B' X Y C C' T : D}
    (p₁ : A = B) (p₂ : B = X) (q₁ : Y = C) (q₂ : C = T)
    (r₁ : A = B') (r₂ : B' = X) (s₁ : Y = C') (s₂ : C' = T) (m : X ⟶ Y) :
    eqToHom p₁ ≫ (eqToHom p₂ ≫ m ≫ eqToHom q₁) ≫ eqToHom q₂ =
      eqToHom r₁ ≫ (eqToHom r₂ ≫ m ≫ eqToHom s₁) ≫ eqToHom s₂ := by
  subst_vars
  simp

/-- Push a stage comma object up to the colimit comma category. -/
noncomputable def structuredArrowPush
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k : S.I} {W : S.stage j}
    {V : S.ColimitCategory} (hW : S.ιObj j W = V) (a : k ⟶ j) (b : k ⟶ i)
    (Q : StructuredArrow ((S.stageFunctor a).obj W) (S.stageFunctor b)) :
    StructuredArrow V (S.stageCoconeFunctor i) :=
  StructuredArrow.mk (Y := Q.right)
    (eqToHom ((S.ιObj_lower a W).trans hW).symm ≫
      (S.stageCoconeFunctor k).map Q.hom ≫ eqToHom (S.ιObj_lower b Q.right))

/-- The pushed comma object maps to any colimit comma object whose structure arrow descends to
a stage arrow with a stage triangle from the pushed datum. -/
theorem structuredArrowPush_w
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k : S.I} {W : S.stage j}
    {V : S.ColimitCategory} (hW : S.ιObj j W = V) (a : k ⟶ j) (b : k ⟶ i)
    (Q : StructuredArrow ((S.stageFunctor a).obj W) (S.stageFunctor b))
    (P : StructuredArrow V (S.stageCoconeFunctor i))
    (gP : (S.stageFunctor a).obj W ⟶ (S.stageFunctor b).obj P.right)
    (hP : eqToHom hW ≫ P.hom = eqToHom (S.ιObj_lower a W).symm ≫
      (S.stageCoconeFunctor k).map gP ≫ eqToHom (S.ιObj_lower b P.right))
    (t : Q.right ⟶ P.right) (ht : Q.hom ≫ (S.stageFunctor b).map t = gP) :
    (structuredArrowPush S hW a b Q).hom ≫ (S.stageCoconeFunctor i).map t = P.hom := by
  have hPsolved : P.hom = eqToHom ((S.ιObj_lower a W).trans hW).symm ≫
      (S.stageCoconeFunctor k).map gP ≫ eqToHom (S.ιObj_lower b P.right) := by
    refine Eq.trans (eqToHom_symm_comp_cancel hW P.hom).symm ?_
    refine Eq.trans (congrArg (fun m => eqToHom hW.symm ≫ m) hP) ?_
    refine Eq.trans (eqToHom_head_merge hW.symm (S.ιObj_lower a W).symm
      ((S.ιObj_lower a W).trans hW).symm _) rfl
  show (eqToHom ((S.ιObj_lower a W).trans hW).symm ≫
    (S.stageCoconeFunctor k).map Q.hom ≫ eqToHom (S.ιObj_lower b Q.right)) ≫
    (S.stageCoconeFunctor i).map t = P.hom
  rw [S.stageCoconeFunctor_map_lower b t]
  simp only [Category.assoc]
  refine Eq.trans (congrArg (fun z => eqToHom ((S.ιObj_lower a W).trans hW).symm ≫
    (S.stageCoconeFunctor k).map Q.hom ≫ z)
    (eqToHom_comp_symm_cancel' (S.ιObj_lower b Q.right)
      ((S.stageCoconeFunctor k).map ((S.stageFunctor b).map t) ≫
        eqToHom (S.ιObj_lower b P.right)))) ?_
  have hmaps : (S.stageCoconeFunctor k).map Q.hom ≫
      (S.stageCoconeFunctor k).map ((S.stageFunctor b).map t) =
      (S.stageCoconeFunctor k).map gP := by
    rw [← Functor.map_comp, ht]
    rfl
  refine Eq.trans (congrArg (fun z => eqToHom ((S.ιObj_lower a W).trans hW).symm ≫ z)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ eqToHom (S.ιObj_lower b P.right)) hmaps))) ?_
  exact hPsolved.symm

/-- Any two objects of the comma category over the cocone functor admit a common refinement:
descend both structure arrows to a common stage and merge there by the stage flatness. -/
theorem structuredArrow_cocone_cone_objs
    (S : CofilteredSiteDiagram.{u, u, u}) (i : S.I) (V : S.ColimitCategory)
    (P₁ P₂ : StructuredArrow V (S.stageCoconeFunctor i)) :
    ∃ (R : StructuredArrow V (S.stageCoconeFunctor i))
      (_ : R ⟶ P₁) (_ : R ⟶ P₂), True := by
  obtain ⟨j, W, hW⟩ := S.ιObj_surjective V
  obtain ⟨k, a, b, g₁, g₂, h₁, h₂⟩ := exists_hom_rep_pair
    (eqToHom hW ≫ P₁.hom) (eqToHom hW ≫ P₂.hom)
  haveI := (S.stageFunctor_representablyFlat b).cofiltered ((S.stageFunctor a).obj W)
  obtain ⟨R₀, r₁, r₂, -⟩ := IsCofilteredOrEmpty.cone_objs
    (StructuredArrow.mk (T := S.stageFunctor b) g₁)
    (StructuredArrow.mk (T := S.stageFunctor b) g₂)
  exact ⟨structuredArrowPush S hW a b R₀,
    StructuredArrow.homMk r₁.right
      (structuredArrowPush_w S hW a b R₀ P₁ g₁ h₁ r₁.right (StructuredArrow.w r₁)),
    StructuredArrow.homMk r₂.right
      (structuredArrowPush_w S hW a b R₀ P₂ g₂ h₂ r₂.right (StructuredArrow.w r₂)),
    trivial⟩

/-- Descend the structure-arrow presentation of a comma object along a further stage arrow. -/
theorem structuredArrow_descent_lower
    (S : CofilteredSiteDiagram.{u, u, u}) {i j k m : S.I} {W : S.stage j}
    {V : S.ColimitCategory} (hW : S.ιObj j W = V) (a : k ⟶ j) (b : k ⟶ i) (e : m ⟶ k)
    (P : StructuredArrow V (S.stageCoconeFunctor i))
    (gP : (S.stageFunctor a).obj W ⟶ (S.stageFunctor b).obj P.right)
    (hP : eqToHom hW ≫ P.hom = eqToHom (S.ιObj_lower a W).symm ≫
      (S.stageCoconeFunctor k).map gP ≫ eqToHom (S.ιObj_lower b P.right)) :
    eqToHom hW ≫ P.hom = eqToHom (S.ιObj_lower (e ≫ a) W).symm ≫
      (S.stageCoconeFunctor m).map
        (eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
          (S.stageFunctor e).map gP ≫
          eqToHom (S.stageFunctor_obj_comp b e P.right)) ≫
      eqToHom (S.ιObj_lower (e ≫ b) P.right) := by
  rw [hP, S.stageCoconeFunctor_map_lower e gP]
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  try simp only [Category.assoc]
  exact eqToHom_conj_paths _ _ _ _ _ _ _ _
    ((S.stageCoconeFunctor m).map ((S.stageFunctor e).map gP))

/-- Parallel pairs in the comma category over the cocone functor are equalized: push the
triangle equations down to a common stage, separate them there, and equalize by the stage
flatness. -/
theorem structuredArrow_cocone_cone_maps
    (S : CofilteredSiteDiagram.{u, u, u}) (i : S.I) (V : S.ColimitCategory)
    {P₁ P₂ : StructuredArrow V (S.stageCoconeFunctor i)} (φ ψ : P₁ ⟶ P₂) :
    ∃ (R : StructuredArrow V (S.stageCoconeFunctor i)) (r : R ⟶ P₁),
      r ≫ φ = r ≫ ψ := by
  obtain ⟨j, W, hW⟩ := S.ιObj_surjective V
  obtain ⟨k, a, b, g₁, hg₁⟩ := exists_hom_rep (eqToHom hW ≫ P₁.hom)
  rw [mk_eq_eqToHom_comp] at hg₁
  -- the pushed-down triangle equations
  have hpush : ∀ (t : P₁.right ⟶ P₂.right),
      P₁.hom ≫ (S.stageCoconeFunctor i).map t = P₂.hom →
      eqToHom (S.ιObj_lower a W).symm ≫
        (S.stageCoconeFunctor k).map (g₁ ≫ (S.stageFunctor b).map t) ≫
        eqToHom (S.ιObj_lower b P₂.right) = eqToHom hW ≫ P₂.hom := by
    intro t hw
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ (S.stageCoconeFunctor i).map t) hg₁.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (fun m => eqToHom hW ≫ m) hw))))
    -- goal: LHS = (e⁻ ≫ map g₁ ≫ e⁺) ≫ map-i-t
    rw [S.stageCoconeFunctor_map_lower b t, Functor.map_comp]
    exact eqToHom_insert_cancel _ _ _ _ _
  have heq0 : (S.stageCoconeFunctor k).map (g₁ ≫ (S.stageFunctor b).map φ.right) =
      (S.stageCoconeFunctor k).map (g₁ ≫ (S.stageFunctor b).map ψ.right) := by
    have h5 := (hpush φ.right (StructuredArrow.w φ)).trans
      (hpush ψ.right (StructuredArrow.w ψ)).symm
    have h6 := (cancel_epi (eqToHom (S.ιObj_lower a W).symm)).1 h5
    exact (cancel_mono (eqToHom (S.ιObj_lower b P₂.right))).1 h6
  obtain ⟨m, e, heq⟩ := exists_stageFunctor_map_eq heq0
  -- the mate of the transition against the merged-stage maps
  have hmate : ∀ (t : P₁.right ⟶ P₂.right),
      eqToHom (S.stageFunctor_obj_comp b e P₁.right) ≫
        (S.stageFunctor (e ≫ b)).map t =
      (S.stageFunctor e).map ((S.stageFunctor b).map t) ≫
        eqToHom (S.stageFunctor_obj_comp b e P₂.right) := by
    intro t
    rw [S.stageFunctor_map_map b e t]
    simp only [Category.assoc]
    exact congrArg (fun z => eqToHom (S.stageFunctor_obj_comp b e P₁.right) ≫ z)
      (comp_eqToHom_symm_cancel (S.stageFunctor_obj_comp b e P₂.right)
        ((S.stageFunctor (e ≫ b)).map t)).symm
  -- the transported parallel equation at the merged stage
  have hcomp : (eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
      (S.stageFunctor e).map g₁ ≫ eqToHom (S.stageFunctor_obj_comp b e P₁.right)) ≫
      (S.stageFunctor (e ≫ b)).map φ.right =
      (eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
      (S.stageFunctor e).map g₁ ≫ eqToHom (S.stageFunctor_obj_comp b e P₁.right)) ≫
      (S.stageFunctor (e ≫ b)).map ψ.right := by
    have hside : ∀ (t : P₁.right ⟶ P₂.right),
        (eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
          (S.stageFunctor e).map g₁ ≫ eqToHom (S.stageFunctor_obj_comp b e P₁.right)) ≫
          (S.stageFunctor (e ≫ b)).map t =
        eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
          (S.stageFunctor e).map (g₁ ≫ (S.stageFunctor b).map t) ≫
          eqToHom (S.stageFunctor_obj_comp b e P₂.right) := by
      intro t
      rw [Functor.map_comp]
      simp only [Category.assoc]
      exact congrArg (fun z => eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
        (S.stageFunctor e).map g₁ ≫ z) (hmate t)
    refine (hside φ.right).trans (Eq.trans ?_ (hside ψ.right).symm)
    exact congrArg (fun z => eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
      z ≫ eqToHom (S.stageFunctor_obj_comp b e P₂.right)) heq
  -- equalize at the stage comma category
  haveI := (S.stageFunctor_representablyFlat (e ≫ b)).cofiltered
    ((S.stageFunctor (e ≫ a)).obj W)
  obtain ⟨R₀, r₀, hr₀⟩ := IsCofilteredOrEmpty.cone_maps
    (StructuredArrow.homMk φ.right rfl :
      StructuredArrow.mk (T := S.stageFunctor (e ≫ b))
        (eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
          (S.stageFunctor e).map g₁ ≫ eqToHom (S.stageFunctor_obj_comp b e P₁.right)) ⟶
      StructuredArrow.mk (T := S.stageFunctor (e ≫ b))
        ((eqToHom (S.stageFunctor_obj_comp a e W).symm ≫
          (S.stageFunctor e).map g₁ ≫ eqToHom (S.stageFunctor_obj_comp b e P₁.right)) ≫
          (S.stageFunctor (e ≫ b)).map φ.right))
    (StructuredArrow.homMk ψ.right hcomp.symm)
  have hright : r₀.right ≫ φ.right = r₀.right ≫ ψ.right := by
    have := congrArg CommaMorphism.right hr₀
    simpa using this
  -- the descended presentation of `P₁` at the merged stage
  have hP₁m := structuredArrow_descent_lower S hW a b e P₁ g₁ hg₁
  refine ⟨structuredArrowPush S hW (e ≫ a) (e ≫ b) R₀,
    StructuredArrow.homMk r₀.right
      (structuredArrowPush_w S hW (e ≫ a) (e ≫ b) R₀ P₁ _ hP₁m r₀.right
        (StructuredArrow.w r₀)), ?_⟩
  apply StructuredArrow.hom_ext
  simpa using hright

/-- The comma category of a colimit object over the cocone functor is nonempty: present the
object at a common refinement of its stage and `i`, and use the stage flatness there. -/
theorem structuredArrow_cocone_nonempty
    (S : CofilteredSiteDiagram.{u, u, u}) (i : S.I) (V : S.ColimitCategory) :
    Nonempty (StructuredArrow V (S.stageCoconeFunctor i)) := by
  obtain ⟨j, W, hW⟩ := S.ιObj_surjective V
  haveI := (S.stageFunctor_representablyFlat (IsCofiltered.minToRight j i)).cofiltered
    ((S.stageFunctor (IsCofiltered.minToLeft j i)).obj W)
  obtain ⟨P⟩ := IsCofiltered.nonempty
    (C := StructuredArrow ((S.stageFunctor (IsCofiltered.minToLeft j i)).obj W)
      (S.stageFunctor (IsCofiltered.minToRight j i)))
  exact ⟨StructuredArrow.mk (Y := P.right)
    (eqToHom ((S.ιObj_lower (IsCofiltered.minToLeft j i) W).trans hW).symm ≫
      (S.stageCoconeFunctor (IsCofiltered.min j i)).map P.hom ≫
      eqToHom (S.ιObj_lower (IsCofiltered.minToRight j i) P.right))⟩

/-- Lemma 7.18.3: in Situation 7.18.1, the cocone functor
`u_i : \mathcal C_i \to \mathop{\mathrm{colim}} \mathcal C_j`
defines a morphism of sites
`(\mathop{\mathrm{colim}} \mathcal C_j, J_{\mathrm{colim}}) \to (\mathcal C_i, J_i)`. -/
instance colimit_site_cocone_isMorphismOfSites
    (S : CofilteredSiteDiagram.{u, u, u}) (i : S.I) :
    IsMorphismOfSites (S.stageTopology i) S.colimitTopology
      (S.stageCoconeFunctor i) := by
  refine
    { toIsContinuous := by
        infer_instance
      toRepresentablyFlat :=
        representablyFlat_of_structuredArrow_op_isFiltered _ (fun V => ?_) }
  -- The comma category is cofiltered: nonemptiness, pair merging, and parallel-pair
  -- equalization were established by descending to common stages and using the stage
  -- flatness there.
  haveI : IsCofilteredOrEmpty (StructuredArrow V (S.stageCoconeFunctor i)) :=
    ⟨fun P₁ P₂ => structuredArrow_cocone_cone_objs S i V P₁ P₂,
     fun _ _ φ ψ => structuredArrow_cocone_cone_maps S i V φ ψ⟩
  haveI : IsCofiltered (StructuredArrow V (S.stageCoconeFunctor i)) :=
    { nonempty := structuredArrow_cocone_nonempty S i V }
  infer_instance

end CategoryTheory
