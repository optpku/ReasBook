module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_18_2
public import stacks_project.Chap07.Situation_7_18_1

@[expose] public section

/-!
Auxiliary sheaf for Lemma 7.18.3 (Stacks 0A35, equation (7.18.3.1)).

This file constructs, for a sheaf `ℱ` on the stage site `i₀`, the source text's auxiliary
presheaf `G` on the colimit site: its value at `V` is the filtered colimit of the sections
`(f_a⁻¹ℱ)(W)` over stage presentations `u_j(W) = V` with `a : j ⟶ i₀`, taken as a quotient of
stage representatives by common lowering — the same pattern as the explicit colimit category in
`Lemma_7_18_2/ColimitCategory.lean`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CofilteredSiteDiagram

variable (S : CofilteredSiteDiagram.{u, u, u})

section AuxiliarySections

variable {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))

/-- A stage representative of an auxiliary section over the colimit-site object `V`: a stage `j`
over `i₀`, a presentation `u_j(W) = V`, and a section of the stage pullback `f_a⁻¹ℱ` at `W`. -/
structure GRep (V : S.ColimitCategory) where
  /-- The presenting stage. -/
  j : S.I
  /-- The structure arrow over `i₀`. -/
  a : j ⟶ i₀
  /-- The presenting stage object. -/
  W : S.stage j
  /-- The presentation identity. -/
  hW : S.ιObj j W = V
  /-- The stage section of the pulled-back sheaf. -/
  s : (((S.stageFunctor a).sheafPullback (Type u)
    (S.stageTopology i₀) (S.stageTopology j)).obj ℱ).obj.obj (op W)

variable {S} in
/-- Restrict a representative along a lowering `b : k ⟶ j`: the new section is the unit
co-restriction transported through the pullback composition comparison. -/
noncomputable def GRep.lower {V : S.ColimitCategory} (r : GRep S ℱ V)
    {k : S.I} (b : k ⟶ r.j) : GRep S ℱ V where
  j := k
  a := b ≫ r.a
  W := (S.stageFunctor b).obj r.W
  hW := (S.ιObj_lower b r.W).trans r.hW
  s :=
    (((S.stageSheafPullbackCompIso (Type u) r.a b).hom.app ℱ).1.app
      (op ((S.stageFunctor b).obj r.W)))
      (((((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
        (S.stageTopology r.j) (S.stageTopology k)).unit.app
        (((S.stageFunctor r.a).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology r.j)).obj ℱ)).1.app (op r.W)) r.s)

/-- A returning double chain of section casts is the identity. -/
private theorem eqToHom_apply_collapse₂₀ {A B : Type u} (p₁ : A = B) (p₂ : B = A) (x : A) :
    eqToHom p₂ (eqToHom p₁ x) = x := by
  subst p₁
  rfl

section MateToolkit

/-- Transposing after precomposition with a left-adjoint comparison is postcomposition with its
conjugate. -/
theorem homEquiv_conjugateEquiv_exchange_aux
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

variable {S} in
/-- The conjugate of the stage pullback composition comparison is the inverse owner pushforward
comparison. -/
theorem stage_pullback_comp_conjugate_hom_aux
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
        (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S a b)).symm
        (Type u) (S.stageTopology i) (S.stageTopology j) (S.stageTopology k)).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

end MateToolkit

/-- The stage pullback functor along an arrow between stages. -/
noncomputable abbrev stageSheafPullbackAlong
    (S : CofilteredSiteDiagram.{u, u, u})
    {i j : S.I} (a : j ⟶ i) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf (S.stageTopology j) (Type u) :=
  let _ : Functor.IsContinuous (S.stageFunctor a)
      (S.stageTopology i) (S.stageTopology j) :=
    S.stageFunctor_isContinuous a
  (S.stageFunctor a).sheafPullback (Type u) (S.stageTopology i) (S.stageTopology j)

/-- G-toolkit: the conjugate of an `eqToHom` between sheaf pullbacks along equal
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


/-- G-toolkit: chains of section casts between equal types collapse. -/
theorem eqToHom_apply_collapse₃₂_aux {A B C D E : Type u}
    (p₁ : A = B) (p₂ : B = C) (p₃ : C = D) (q₁ : A = E) (q₂ : E = D) (y : A) :
    eqToHom p₃ (eqToHom p₂ (eqToHom p₁ y)) = eqToHom q₂ (eqToHom q₁ y) := by
  subst p₁; subst p₂; subst p₃; subst q₁
  rfl

/-- G-toolkit: the pushforward comparison isomorphisms satisfy the associativity
coherence required by `Adjunction.leftAdjointCompIso_assoc`. -/
theorem stageSheafPushforward_comp_coherence_aux
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
  exact eqToHom_apply_collapse₃₂_aux _ _ _ _ _ y

/-- G-toolkit: the assoc-normalized composite comparison is the canonical one
followed by the transport along associativity of the arrows. -/
theorem stageSheafPullbackCompIso_assoc_norm_aux
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
  rw [stage_pullback_comp_conjugate_hom_aux,
    conjugateEquiv_sheafPullback_eqToHom
      (show S.stageFunctor (c ≫ b ≫ a) = S.stageFunctor ((c ≫ b) ≫ a) from
        congrArg (fun f : l ⟶ i => S.stageFunctor f) (Category.assoc c b a).symm)
      hpull hpush.symm]
  simp

/-- G-toolkit: the cocycle identity for the stage pullback composition
comparisons, evaluated on a sheaf. -/
theorem stageSheafPullbackCompIso_assoc_app_aux
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
    (stageSheafPushforward_comp_coherence_aux S a b c hpush)
  have happ := congrArg (fun t => t.hom.app ℱ) hassoc
  have hnorm := congrArg (fun t => t.app ℱ)
    (stageSheafPullbackCompIso_assoc_norm_aux S a b c hpush hpull)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.associator_inv_app,
    Category.id_comp] at happ hnorm
  dsimp only [Functor.whiskerLeft, Functor.whiskerRight] at happ
  refine happ.trans ?_
  rw [hnorm]
  simp [CofilteredSiteDiagram.stageSheafPullbackCompIso]


/-- G-toolkit: a transport along a reflexive object equality is the identity. -/
theorem eqToHom_self_id_aux {C : Type*} [Category C] {X : C} (h : X = X) :
    eqToHom h = 𝟙 X := by
  rw [Subsingleton.elim h (rfl : X = X), eqToHom_refl]

/-- G-toolkit: the cocycle identity for the transition comparisons, with the
`Over.w` target normalizations attached. -/
theorem stage_restriction_cocycle_core_aux
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
  have hassoc := stageSheafPullbackCompIso_assoc_app_aux S a p q ℱ hpull
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
        exact eqToHom_self_id_aux _
    _ = ((S.stageFunctor q).sheafPullback (Type u)
          (S.stageTopology k) (S.stageTopology l)).map
          ((S.stageSheafPullbackCompIso (Type u) a p).hom.app ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) (p ≫ a) q).hom.app ℱ := by
        rw [Category.comp_id]


variable {S} in
/-- The canonical stage restriction map: the transpose of the pullback composition comparison. -/
noncomputable def stageRestriction {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {j k : S.I} (a : j ⟶ i₀) (b : k ⟶ j) :
    ((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology j)).obj ℱ ⟶
    ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)).obj
      (((S.stageFunctor (b ≫ a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology k)).obj ℱ) :=
  (((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
    (S.stageTopology j) (S.stageTopology k)).homEquiv _ _)
    ((S.stageSheafPullbackCompIso (Type u) a b).hom.app ℱ)

variable {S} in
/-- The cocycle identity for the stage restriction maps: restricting along a composite lowering
is the composite of the restrictions, up to the canonical pushforward comparison and the
associativity transport. -/
theorem stageRestriction_comp {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {j k m : S.I} (a : j ⟶ i₀) (b : k ⟶ j) (d : m ⟶ k)
    (hassoc : (((S.stageFunctor (d ≫ b ≫ a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ) =
      (((S.stageFunctor ((d ≫ b) ≫ a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)) :
    stageRestriction ℱ a (d ≫ b) =
      stageRestriction ℱ a b ≫
      ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)).map
        ((((S.stageFunctor d).sheafAdjunctionContinuous (Type u)
          (S.stageTopology k) (S.stageTopology m)).homEquiv _ _)
          ((S.stageSheafPullbackCompIso (Type u) (b ≫ a) d).hom.app ℱ ≫ eqToHom hassoc)) ≫
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S b d)).symm
        (Type u) (S.stageTopology j) (S.stageTopology k) (S.stageTopology m)).hom.app
        (((S.stageFunctor ((d ≫ b) ≫ a)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m)).obj ℱ) := by
  -- transpose the left side through the composite adjunction
  have hex := homEquiv_conjugateEquiv_exchange_aux
    ((S.stageFunctor (d ≫ b)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology m))
    (((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)).comp
      ((S.stageFunctor d).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) (S.stageTopology m)))
    ((S.stageSheafPullbackCompIso (Type u) b d).hom)
    ((S.stageSheafPullbackCompIso (Type u) a (d ≫ b)).hom.app ℱ)
  rw [stage_pullback_comp_conjugate_hom_aux] at hex
  have hcancel := congrArg (fun t => t ≫
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S b d)).symm
      (Type u) (S.stageTopology j) (S.stageTopology k) (S.stageTopology m)).hom.app
      (((S.stageFunctor ((d ≫ b) ≫ a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)) hex
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hcancel
  refine Eq.trans hcancel.symm ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (fun t => t ≫
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S b d)).symm
      (Type u) (S.stageTopology j) (S.stageTopology k) (S.stageTopology m)).hom.app
      (((S.stageFunctor ((d ≫ b) ≫ a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)) ?_
  -- rewrite the transposed argument through the cocycle core
  have hcore := stage_restriction_cocycle_core_aux S ℱ a b d
    (rfl : b ≫ a = b ≫ a) (rfl : d ≫ b ≫ a = d ≫ b ≫ a)
    (rfl : _ = _) (rfl : _ = _) hassoc.symm
  have harg : (S.stageSheafPullbackCompIso (Type u) b d).hom.app
      ((stageSheafPullbackAlong S a).obj ℱ) ≫
      (S.stageSheafPullbackCompIso (Type u) a (d ≫ b)).hom.app ℱ =
      ((S.stageFunctor d).sheafPullback (Type u)
        (S.stageTopology k) (S.stageTopology m)).map
        ((S.stageSheafPullbackCompIso (Type u) a b).hom.app ℱ) ≫
      ((S.stageSheafPullbackCompIso (Type u) (b ≫ a) d).hom.app ℱ ≫ eqToHom hassoc) := by
    have h := congrArg (fun t => t ≫ eqToHom hassoc) hcore
    simp only [Category.assoc] at h
    have hLcollapse : (S.stageSheafPullbackCompIso (Type u) b d).hom.app
        ((stageSheafPullbackAlong S a).obj ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) a (d ≫ b)).hom.app ℱ ≫
        eqToHom hassoc.symm ≫ eqToHom hassoc =
        (S.stageSheafPullbackCompIso (Type u) b d).hom.app
          ((stageSheafPullbackAlong S a).obj ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) a (d ≫ b)).hom.app ℱ := by
      refine Eq.trans (congrArg (fun t => (S.stageSheafPullbackCompIso (Type u) b d).hom.app
        ((stageSheafPullbackAlong S a).obj ℱ) ≫
        (S.stageSheafPullbackCompIso (Type u) a (d ≫ b)).hom.app ℱ ≫ t)
        ((eqToHom_trans hassoc.symm hassoc).trans (eqToHom_self_id_aux _))) ?_
      simp only [Category.comp_id]
    have h2 := (hLcollapse.symm.trans (by simpa using h))
    refine h2.trans ?_
    -- normalize the right side casts
    refine congrArg₂ (fun t₁ t₂ => ((S.stageFunctor d).sheafPullback (Type u)
      (S.stageTopology k) (S.stageTopology m)).map t₁ ≫ t₂) ?_ ?_
    · rfl
    · rfl
  -- transpose calculus: split the composite adjunction and absorb the factors
  refine Eq.trans (congrArg (fun t =>
    ((((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k)).comp
      ((S.stageFunctor d).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) (S.stageTopology m))).homEquiv _ _) t) harg) ?_
  have hsplit : ∀ γ : ((S.stageFunctor b).sheafPullback (Type u)
      (S.stageTopology j) (S.stageTopology k) ⋙
      (S.stageFunctor d).sheafPullback (Type u)
        (S.stageTopology k) (S.stageTopology m)).obj
      (((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology j)).obj ℱ) ⟶
      (((S.stageFunctor ((d ≫ b) ≫ a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ),
      ((((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)).comp
        ((S.stageFunctor d).sheafAdjunctionContinuous (Type u)
          (S.stageTopology k) (S.stageTopology m))).homEquiv _ _) γ =
      ((((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k))).homEquiv _ _)
        (((((S.stageFunctor d).sheafAdjunctionContinuous (Type u)
          (S.stageTopology k) (S.stageTopology m))).homEquiv _ _) γ) := by
    intro γ
    rw [Adjunction.comp_homEquiv]
    rfl
  refine Eq.trans (hsplit _) ?_
  refine Eq.trans (congrArg (fun t =>
    ((((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
      (S.stageTopology j) (S.stageTopology k))).homEquiv _ _) t)
    (Adjunction.homEquiv_naturality_left _ _ _)) ?_
  exact Adjunction.homEquiv_naturality_right _ _ _

/-- G-toolkit: a double chain of section casts collapses to a single cast. -/
theorem eqToHom_apply_collapse₂₁_aux {A B C : Type u}
    (p₁ : A = B) (p₂ : B = C) (q : A = C) (x : A) :
    eqToHom p₂ (eqToHom p₁ x) = eqToHom q x := by
  subst p₁
  subst p₂
  rfl

/-- G-toolkit: a functor applied to a transport evaluates to a section cast. -/
theorem sheaf_functor_map_eqToHom_eval
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) {A B : Sheaf J (Type u)} (h : A = B)
    (Z : Dᵒᵖ)
    (hsec : (F.obj A).obj.obj Z = (F.obj B).obj.obj Z)
    (z : (F.obj A).obj.obj Z) :
    ((F.map (eqToHom h)).1.app Z) z = eqToHom hsec z := by
  subst h
  rw [Subsingleton.elim hsec (rfl : _ = _), eqToHom_refl, F.map_id]
  rfl

variable {S} in
/-- G-toolkit: the pushforward composition comparison acts on sections as a pure cast. -/
theorem pushComp_app_eval_cast
    {j k m : S.I} (b : k ⟶ j) (d : m ⟶ k)
    (G : Sheaf (S.stageTopology m) (Type u)) (Z : (S.stage j)ᵒᵖ)
    (hsec : ((((S.stageFunctor d).sheafPushforwardContinuous (Type u)
        (S.stageTopology k) (S.stageTopology m)).obj G).obj.obj
        (op ((S.stageFunctor b).obj Z.unop))) =
      ((((S.stageFunctor (d ≫ b)).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology m)).obj G).obj.obj Z))
    (z : (((S.stageFunctor d).sheafPushforwardContinuous (Type u)
        (S.stageTopology k) (S.stageTopology m)).obj G).obj.obj
        (op ((S.stageFunctor b).obj Z.unop))) :
    (((Functor.sheafPushforwardContinuousComp'
        (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S b d)).symm
        (Type u) (S.stageTopology j) (S.stageTopology k) (S.stageTopology m)).hom.app
        G).1.app Z) z = eqToHom hsec z := by
  simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
    CategoryTheory.eqToHom_map, eqToHom_app]

variable {S} in
/-- The lowered section of a representative is the evaluated stage restriction. -/
theorem GRep.lower_s_eq {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} (r : GRep S ℱ V) {k : S.I} (b : k ⟶ r.j) :
    (r.lower ℱ b).s = ((stageRestriction ℱ r.a b).1.app (op r.W)) r.s := by
  rfl

variable {S} in
/-- The section types of two representatives agree once the structure arrows and the stage
objects agree. -/
theorem gsec_type_congr {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {k : S.I} {a a' : k ⟶ i₀} (ha : a = a') {W W' : S.stage k} (hw : W = W') :
    ((((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology k)).obj ℱ).obj.obj (op W)) =
    ((((S.stageFunctor a').sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology k)).obj ℱ).obj.obj (op W')) := by
  subst ha
  subst hw
  rfl

variable {S} in
/-- Lowering twice is lowering along the composite, up to the canonical section cast. -/
theorem GRep.lower_lower {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} (r : GRep S ℱ V) {k m : S.I} (b : k ⟶ r.j) (d : m ⟶ k)
    (ha : d ≫ b ≫ r.a = (d ≫ b) ≫ r.a)
    (hw : (S.stageFunctor d).obj ((S.stageFunctor b).obj r.W) =
      (S.stageFunctor (d ≫ b)).obj r.W) :
    eqToHom (gsec_type_congr ℱ ha hw)
      (((r.lower ℱ b).lower ℱ d).s) = (r.lower ℱ (d ≫ b)).s := by
  have hassoc : (((S.stageFunctor (d ≫ b ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ) =
      (((S.stageFunctor ((d ≫ b) ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ) :=
    congrArg (fun f : m ⟶ i₀ => (((S.stageFunctor f).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)) (Category.assoc d b r.a).symm
  have heval := congrArg (fun t => (t.1.app (op r.W)) r.s)
    (stageRestriction_comp ℱ r.a b d hassoc)
  refine Eq.trans ?_ heval.symm
  -- evaluate the right side of the cocycle pointwise
  have hnat : (((S.stageFunctor d).sheafAdjunctionContinuous (Type u)
      (S.stageTopology k) (S.stageTopology m)).homEquiv _ _)
      ((S.stageSheafPullbackCompIso (Type u) (b ≫ r.a) d).hom.app ℱ ≫ eqToHom hassoc) =
      (((S.stageFunctor d).sheafAdjunctionContinuous (Type u)
        (S.stageTopology k) (S.stageTopology m)).homEquiv _ _)
        ((S.stageSheafPullbackCompIso (Type u) (b ≫ r.a) d).hom.app ℱ) ≫
      ((S.stageFunctor d).sheafPushforwardContinuous (Type u)
        (S.stageTopology k) (S.stageTopology m)).map (eqToHom hassoc) :=
    Adjunction.homEquiv_naturality_right _ _ _
  have hnat_el := congrFun (congrArg (fun t => t.1.app
    (op ((S.stageFunctor b).obj r.W))) hnat) ((r.lower ℱ b).s)
  -- the pushforward of the associativity cast acts as a section cast
  have hsec₁ : ((((S.stageFunctor d).sheafPushforwardContinuous (Type u)
      (S.stageTopology k) (S.stageTopology m)).obj
      (((S.stageFunctor (d ≫ b ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).obj.obj
      (op ((S.stageFunctor b).obj r.W))) =
      ((((S.stageFunctor d).sheafPushforwardContinuous (Type u)
      (S.stageTopology k) (S.stageTopology m)).obj
      (((S.stageFunctor ((d ≫ b) ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).obj.obj
      (op ((S.stageFunctor b).obj r.W))) :=
    congrArg (fun A : Sheaf (S.stageTopology m) (Type u) =>
      (((S.stageFunctor d).sheafPushforwardContinuous (Type u)
        (S.stageTopology k) (S.stageTopology m)).obj A).obj.obj
        (op ((S.stageFunctor b).obj r.W))) hassoc
  have hcast₁ := sheaf_functor_map_eqToHom_eval
    ((S.stageFunctor d).sheafPushforwardContinuous (Type u)
      (S.stageTopology k) (S.stageTopology m)) hassoc
    (op ((S.stageFunctor b).obj r.W)) hsec₁
    (((r.lower ℱ b).lower ℱ d).s)
  -- the pushforward composition comparison acts as a section cast
  have hsec₂ : ((((S.stageFunctor d).sheafPushforwardContinuous (Type u)
      (S.stageTopology k) (S.stageTopology m)).obj
      (((S.stageFunctor ((d ≫ b) ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).obj.obj
      (op ((S.stageFunctor b).obj r.W))) =
      ((((S.stageFunctor (d ≫ b)).sheafPushforwardContinuous (Type u)
      (S.stageTopology r.j) (S.stageTopology m)).obj
      (((S.stageFunctor ((d ≫ b) ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).obj.obj (op r.W)) :=
    congrArg (fun Z => (((S.stageFunctor ((d ≫ b) ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj (op Z)) hw
  have hcast₂ := pushComp_app_eval_cast (S := S) b d
    (((S.stageFunctor ((d ≫ b) ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ) (op r.W) hsec₂
    (eqToHom hsec₁ (((r.lower ℱ b).lower ℱ d).s))
  -- assemble the linear chain of identifications
  have E1 := congrArg (fun z =>
    (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S b d)).symm
      (Type u) (S.stageTopology r.j) (S.stageTopology k) (S.stageTopology m)).hom.app
      (((S.stageFunctor ((d ≫ b) ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).1.app (op r.W)) z) hnat_el
  have E2 := congrArg (fun z =>
    (((Functor.sheafPushforwardContinuousComp'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_comp_eq S b d)).symm
      (Type u) (S.stageTopology r.j) (S.stageTopology k) (S.stageTopology m)).hom.app
      (((S.stageFunctor ((d ≫ b) ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).1.app (op r.W)) z) hcast₁
  have E4 := eqToHom_apply_collapse₂₁_aux hsec₁ hsec₂
    (gsec_type_congr ℱ ha hw)
    (((r.lower ℱ b).lower ℱ d).s)
  exact ((E1.trans (E2.trans (hcast₂.trans E4))).symm)

/-- G-toolkit: fold two cast steps into one. -/
theorem cast_step_fold {A B C : Type u} {p : A = B} {q : B = C} (r : A = C)
    {x : A} {y : B} {z : C} (h₁ : eqToHom p x = y) (h₂ : eqToHom q y = z) :
    eqToHom r x = z := by
  subst h₁
  subst h₂
  exact (eqToHom_apply_collapse₂₁_aux p q r x).symm

/-- G-toolkit: fold two cast steps, accumulating the transport proofs. -/
theorem cast_step_fold' {A B C : Type u} {p : A = B} {q : B = C}
    {x : A} {y : B} {z : C} (h₁ : eqToHom p x = y) (h₂ : eqToHom q y = z) :
    eqToHom (p.trans q) x = z := by
  subst h₁
  subst h₂
  exact (eqToHom_apply_collapse₂₁_aux p q (p.trans q) x).symm

/-- G-toolkit: a pushforward-sections type congruence. -/
theorem gsec_push_congr {S : CofilteredSiteDiagram.{u, u, u}}
    {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {j m : S.I} {a a' : j ⟶ i₀} (ha : a = a') {W W' : S.stage j} (hw : W = W')
    (e : m ⟶ j) :
    ((((S.stageFunctor e).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology m)).obj
        (((S.stageFunctor (e ≫ a)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).obj.obj (op W)) =
      ((((S.stageFunctor e).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology m)).obj
        (((S.stageFunctor (e ≫ a')).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).obj.obj (op W')) := by
  subst ha
  subst hw
  rfl

/-- G-toolkit: reverse a cast step. -/
theorem cast_step_symm {A B : Type u} {p : A = B} {x : A} {y : B}
    (h : eqToHom p x = y) : eqToHom p.symm y = x := by
  subst p
  subst h
  rfl

variable {S} in
/-- Restriction evaluation commutes with the canonical section casts. -/
theorem stageRestriction_eval_congr {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {j m : S.I} {a a' : j ⟶ i₀} (ha : a = a') {W W' : S.stage j} (hw : W = W')
    (e : m ⟶ j)
    (hres : ((((S.stageFunctor e).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology m)).obj
        (((S.stageFunctor (e ≫ a)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).obj.obj (op W)) =
      ((((S.stageFunctor e).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology m)).obj
        (((S.stageFunctor (e ≫ a')).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m)).obj ℱ)).obj.obj (op W')))
    (s : (((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology j)).obj ℱ).obj.obj (op W)) :
    eqToHom hres (((stageRestriction ℱ a e).1.app (op W)) s) =
      ((stageRestriction ℱ a' e).1.app (op W')) (eqToHom (gsec_type_congr ℱ ha hw) s) := by
  subst ha
  subst hw
  rfl

variable {S} in
/-- Lowering along equal arrows gives equal sections, up to the canonical cast. -/
theorem GRep.lower_arrow_congr {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} (r : GRep S ℱ V) {m : S.I} {e e' : m ⟶ r.j} (hee : e = e')
    (hsec : (((S.stageFunctor (e ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj
        (op ((S.stageFunctor e).obj r.W)) =
      (((S.stageFunctor (e' ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj
        (op ((S.stageFunctor e').obj r.W))) :
    eqToHom hsec ((r.lower ℱ e).s) = (r.lower ℱ e').s := by
  subst hee
  rw [Subsingleton.elim hsec (rfl : _ = _), eqToHom_refl]
  rfl

variable {S} in
/-- Two representatives are related when they admit a common lowering on which the structure
arrows agree, the stage objects agree, and the lowered sections agree. -/
def grel {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)} {V : S.ColimitCategory}
    (r₁ r₂ : GRep S ℱ V) : Prop :=
  ∃ (k : S.I) (b₁ : k ⟶ r₁.j) (b₂ : k ⟶ r₂.j) (ha : b₁ ≫ r₁.a = b₂ ≫ r₂.a)
    (hw : (S.stageFunctor b₁).obj r₁.W = (S.stageFunctor b₂).obj r₂.W),
    eqToHom (gsec_type_congr ℱ ha hw) (r₁.lower ℱ b₁).s = (r₂.lower ℱ b₂).s

variable {S} in
/-- Reflexivity of the lowering relation. -/
theorem grel_refl {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} (r : GRep S ℱ V) : grel r r :=
  ⟨r.j, 𝟙 r.j, 𝟙 r.j, rfl, rfl, rfl⟩

variable {S} in
/-- Symmetry of the lowering relation. -/
theorem grel_symm {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} {r₁ r₂ : GRep S ℱ V} (h : grel r₁ r₂) : grel r₂ r₁ := by
  obtain ⟨k, b₁, b₂, ha, hw, hs⟩ := h
  refine ⟨k, b₂, b₁, ha.symm, hw.symm, ?_⟩
  rw [← hs]
  exact eqToHom_apply_collapse₂₀ _ _ _

variable {S} in
/-- Transitivity of the lowering relation: merge the two common lowerings over a cofiltered span
that equalizes the middle legs, and fold the section identifications. -/
theorem grel_trans {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} {r₁ r₂ r₃ : GRep S ℱ V}
    (h₁₂ : grel r₁ r₂) (h₂₃ : grel r₂ r₃) : grel r₁ r₃ := by
  obtain ⟨k, b₁, b₂, ha, hw, hs⟩ := h₁₂
  obtain ⟨l, c₂, c₃, ha', hw', hs'⟩ := h₂₃
  obtain ⟨m, e, f, he⟩ := S.exists_span b₂ c₂
  -- the composite witnesses
  refine ⟨m, e ≫ b₁, f ≫ c₃, ?_, ?_, ?_⟩
  · -- structure arrows agree
    calc (e ≫ b₁) ≫ r₁.a = e ≫ b₁ ≫ r₁.a := Category.assoc _ _ _
      _ = e ≫ b₂ ≫ r₂.a := congrArg (fun t => e ≫ t) ha
      _ = (e ≫ b₂) ≫ r₂.a := (Category.assoc _ _ _).symm
      _ = (f ≫ c₂) ≫ r₂.a := congrArg (fun t => t ≫ r₂.a) he
      _ = f ≫ c₂ ≫ r₂.a := Category.assoc _ _ _
      _ = f ≫ c₃ ≫ r₃.a := congrArg (fun t => f ≫ t) ha'
      _ = (f ≫ c₃) ≫ r₃.a := (Category.assoc _ _ _).symm
  · -- stage objects agree
    calc (S.stageFunctor (e ≫ b₁)).obj r₁.W
        = (S.stageFunctor e).obj ((S.stageFunctor b₁).obj r₁.W) :=
          congrArg (fun F : S.stage r₁.j ⥤ S.stage m => F.obj r₁.W)
            (CofilteredSiteDiagram.stageFunctor_comp_eq S b₁ e)
      _ = (S.stageFunctor e).obj ((S.stageFunctor b₂).obj r₂.W) :=
          congrArg (fun Z => (S.stageFunctor e).obj Z) hw
      _ = (S.stageFunctor (e ≫ b₂)).obj r₂.W :=
          (congrArg (fun F : S.stage r₂.j ⥤ S.stage m => F.obj r₂.W)
            (CofilteredSiteDiagram.stageFunctor_comp_eq S b₂ e)).symm
      _ = (S.stageFunctor (f ≫ c₂)).obj r₂.W :=
          congrArg (fun t : m ⟶ r₂.j => (S.stageFunctor t).obj r₂.W) he
      _ = (S.stageFunctor f).obj ((S.stageFunctor c₂).obj r₂.W) :=
          congrArg (fun F : S.stage r₂.j ⥤ S.stage m => F.obj r₂.W)
            (CofilteredSiteDiagram.stageFunctor_comp_eq S c₂ f)
      _ = (S.stageFunctor f).obj ((S.stageFunctor c₃).obj r₃.W) :=
          congrArg (fun Z => (S.stageFunctor f).obj Z) hw'
      _ = (S.stageFunctor (f ≫ c₃)).obj r₃.W :=
          (congrArg (fun F : S.stage r₃.j ⥤ S.stage m => F.obj r₃.W)
            (CofilteredSiteDiagram.stageFunctor_comp_eq S c₃ f)).symm
  · -- lowered sections agree: fold the seven cast steps
    have hwc₂ : (S.stageFunctor e).obj ((S.stageFunctor b₂).obj r₂.W) =
        (S.stageFunctor (e ≫ b₂)).obj r₂.W :=
      (congrArg (fun F : S.stage r₂.j ⥤ S.stage m => F.obj r₂.W)
        (CofilteredSiteDiagram.stageFunctor_comp_eq S b₂ e)).symm
    have hwc₁ : (S.stageFunctor e).obj ((S.stageFunctor b₁).obj r₁.W) =
        (S.stageFunctor (e ≫ b₁)).obj r₁.W :=
      (congrArg (fun F : S.stage r₁.j ⥤ S.stage m => F.obj r₁.W)
        (CofilteredSiteDiagram.stageFunctor_comp_eq S b₁ e)).symm
    have hwc₃ : (S.stageFunctor f).obj ((S.stageFunctor c₂).obj r₂.W) =
        (S.stageFunctor (f ≫ c₂)).obj r₂.W :=
      (congrArg (fun F : S.stage r₂.j ⥤ S.stage m => F.obj r₂.W)
        (CofilteredSiteDiagram.stageFunctor_comp_eq S c₂ f)).symm
    have hwc₄ : (S.stageFunctor f).obj ((S.stageFunctor c₃).obj r₃.W) =
        (S.stageFunctor (f ≫ c₃)).obj r₃.W :=
      (congrArg (fun F : S.stage r₃.j ⥤ S.stage m => F.obj r₃.W)
        (CofilteredSiteDiagram.stageFunctor_comp_eq S c₃ f)).symm
    have A := cast_step_symm
      (r₁.lower_lower b₁ e (Category.assoc e b₁ r₁.a).symm hwc₁)
    have B := (stageRestriction_eval_congr ℱ ha hw e
        (gsec_push_congr ℱ ha hw e) ((r₁.lower ℱ b₁).s)).trans
      (congrArg (fun t => ((stageRestriction ℱ (b₂ ≫ r₂.a) e).1.app
        (op ((S.stageFunctor b₂).obj r₂.W))) t) hs)
    have C := r₂.lower_lower b₂ e (Category.assoc e b₂ r₂.a).symm hwc₂
    have D := r₂.lower_arrow_congr he
      (congrArg (fun t : m ⟶ r₂.j => (((S.stageFunctor (t ≫ r₂.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj
        (op ((S.stageFunctor t).obj r₂.W))) he)
    have E := cast_step_symm
      (r₂.lower_lower c₂ f (Category.assoc f c₂ r₂.a).symm hwc₃)
    have F := (stageRestriction_eval_congr ℱ ha' hw' f
        (gsec_push_congr ℱ ha' hw' f) ((r₂.lower ℱ c₂).s)).trans
      (congrArg (fun t => ((stageRestriction ℱ (c₃ ≫ r₃.a) f).1.app
        (op ((S.stageFunctor c₃).obj r₃.W))) t) hs')
    have G := r₃.lower_lower c₃ f (Category.assoc f c₃ r₃.a).symm hwc₄
    exact cast_step_fold' A (cast_step_fold' B (cast_step_fold' C
      (cast_step_fold' D (cast_step_fold' E (cast_step_fold' F G)))))

variable {S} in
/-- The lowering relation is an equivalence. -/
def gsetoid {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u)) (V : S.ColimitCategory) :
    Setoid (GRep S ℱ V) where
  r := grel
  iseqv := ⟨grel_refl, fun h => grel_symm h, fun h h' => grel_trans h h'⟩

variable {S} in
/-- The auxiliary section set over `V`: stage sections of the pulled-back sheaves modulo common
lowering. This is the value of the source text's presheaf `G` at `V`. -/
def GSec {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u)) (V : S.ColimitCategory) :
    Type u :=
  _root_.Quotient (gsetoid ℱ V)

variable {S} in
/-- The class of a stage representative. -/
def GSec.mk {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)} {V : S.ColimitCategory}
    (r : GRep S ℱ V) : GSec ℱ V :=
  _root_.Quotient.mk (gsetoid ℱ V) r

variable {S} in
/-- Every auxiliary section is the class of a stage representative. -/
theorem GSec.mk_surjective {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} (x : GSec ℱ V) : ∃ r : GRep S ℱ V, GSec.mk r = x :=
  ⟨x.out, _root_.Quotient.out_eq x⟩

variable {S} in
/-- Two representatives give the same class exactly when they are related. -/
theorem GSec.mk_eq_mk {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} {r₁ r₂ : GRep S ℱ V} :
    GSec.mk r₁ = GSec.mk r₂ ↔ grel r₁ r₂ :=
  ⟨fun h => _root_.Quotient.exact h, fun h => _root_.Quotient.sound h⟩

variable {S} in
/-- A representative is related to each of its lowerings. -/
theorem grel_lower {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} (r : GRep S ℱ V) {k : S.I} (b : k ⟶ r.j) :
    grel r (r.lower ℱ b) := by
  have hwid : (S.stageFunctor (𝟙 k)).obj ((S.stageFunctor b).obj r.W) =
      (S.stageFunctor (𝟙 k ≫ b)).obj r.W :=
    (congrArg (fun F : S.stage r.j ⥤ S.stage k => F.obj r.W)
      (CofilteredSiteDiagram.stageFunctor_comp_eq S b (𝟙 k))).symm
  refine ⟨k, 𝟙 k ≫ b, 𝟙 k, ?_, ?_, ?_⟩
  · calc (𝟙 k ≫ b) ≫ r.a = 𝟙 k ≫ b ≫ r.a := Category.assoc _ _ _
      _ = 𝟙 k ≫ (r.lower ℱ b).a := rfl
  · exact hwid.symm
  · exact cast_step_symm (r.lower_lower b (𝟙 k) (Category.assoc (𝟙 k) b r.a).symm hwid)

section Restriction

variable {S} in
/-- Restriction data for a morphism representative acting on a section representative: a common
stage over which the morphism's target object and the section's presenting object become
equal. This mirrors `CompData` for composition in the colimit category. -/
structure ResData {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {x y : S.ColimitCategory} (g : HomRep x y) (r : GRep S ℱ y) where
  /-- the common stage -/
  idx : S.I
  /-- the lowering of the morphism representative's stage -/
  toHom : idx ⟶ g.idx
  /-- the lowering of the section representative's stage -/
  toRep : idx ⟶ r.j
  /-- the gluing identification -/
  glue : (S.stageFunctor toHom).obj g.tgt = (S.stageFunctor toRep).obj r.W

variable {S} in
/-- Some restriction data always exists, because the morphism's target and the section's
presenting object represent the same colimit object. -/
noncomputable def ResData.some {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {x y : S.ColimitCategory} (g : HomRep x y) (r : GRep S ℱ y) : ResData ℱ g r := by
  have h := S.ιObj_exact (g.htgt.trans r.hW.symm)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

variable {S} in
/-- The restricted representative attached to a choice of restriction data: lower the section
representative to the common stage and pull back along the lowered stage morphism. -/
noncomputable def ResData.res {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y : S.ColimitCategory} {g : HomRep x y} {r : GRep S ℱ y}
    (d : ResData ℱ g r) : GRep S ℱ x where
  j := d.idx
  a := d.toRep ≫ r.a
  W := (S.stageFunctor d.toHom).obj g.src
  hW := (S.ιObj_lower d.toHom g.src).trans g.hsrc
  s := ((((S.stageFunctor (d.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology d.idx)).obj ℱ).obj.map
      ((S.stageFunctor d.toHom).map g.hom ≫ eqToHom d.glue).op)
      ((r.lower ℱ d.toRep).s)

variable {S} in
/-- Lower restriction data along a further index arrow. -/
def ResData.lower {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y : S.ColimitCategory} {g : HomRep x y} {r : GRep S ℱ y}
    (d : ResData ℱ g r) {n : S.I} (w : n ⟶ d.idx) : ResData ℱ g r where
  idx := n
  toHom := w ≫ d.toHom
  toRep := w ≫ d.toRep
  glue := (S.stageFunctor_obj_comp d.toHom w g.tgt).symm.trans
    ((congrArg (S.stageFunctor w).obj d.glue).trans (S.stageFunctor_obj_comp d.toRep w r.W))

/-- G-toolkit: a presheaf map along an `eqToHom` of objects evaluates to a section cast. -/
theorem presheaf_map_eqToHom_op_eval {D : Type u} [Category.{u} D] (G : Dᵒᵖ ⥤ Type u)
    {X Y : D} (h : X = Y) (hsec : G.obj (op Y) = G.obj (op X)) (z : G.obj (op Y)) :
    G.map (eqToHom h).op z = eqToHom hsec z := by
  subst h
  rw [Subsingleton.elim hsec (rfl : G.obj (op X) = G.obj (op X))]
  simp

variable {S} in
/-- G-toolkit: a stage pullback presheaf map exchanges with the structure-arrow cast. -/
theorem pull_map_index_congr {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {n : S.I} {f f' : n ⟶ i₀} (hf : f = f') {Z Z' : S.stage n} (ψ : Z' ⟶ Z)
    (hsZ : ((((S.stageFunctor f).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.obj (op Z)) =
      ((((S.stageFunctor f').sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.obj (op Z)))
    (hsZ' : ((((S.stageFunctor f).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.obj (op Z')) =
      ((((S.stageFunctor f').sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.obj (op Z')))
    (z : (((S.stageFunctor f).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.obj (op Z)) :
    eqToHom hsZ' ((((S.stageFunctor f).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.map ψ.op z) =
      ((((S.stageFunctor f').sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.map ψ.op) (eqToHom hsZ z) := by
  subst hf
  rw [Subsingleton.elim hsZ (rfl : _ = _), Subsingleton.elim hsZ' (rfl : _ = _)]
  rfl

/-- G-toolkit: a presheaf map along an `eqToHom`-conjugated arrow evaluates as the cast-conjugated
map. -/
theorem presheaf_map_conj_eval {D : Type u} [Category.{u} D] (G : Dᵒᵖ ⥤ Type u)
    {X Y Z W : D} (p : X = Y) (m : Y ⟶ Z) (q : Z = W) (z : G.obj (op W))
    (hZ : G.obj (op W) = G.obj (op Z)) (hX : G.obj (op Y) = G.obj (op X)) :
    G.map ((eqToHom p ≫ m ≫ eqToHom q).op) z = eqToHom hX (G.map m.op (eqToHom hZ z)) := by
  subst p
  subst q
  rw [Subsingleton.elim hZ (rfl : _ = _), Subsingleton.elim hX (rfl : _ = _)]
  simp

variable {S} in
/-- Lowering the restricted representative is the restricted representative of the lowered
data, up to the canonical section cast. This is the single transport lemma for restrictions. -/
theorem ResData.res_lower {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y : S.ColimitCategory} {g : HomRep x y} {r : GRep S ℱ y}
    (d : ResData ℱ g r) {n : S.I} (w : n ⟶ d.idx)
    (ha : (w ≫ d.toRep) ≫ r.a = w ≫ d.toRep ≫ r.a)
    (hw : (S.stageFunctor (w ≫ d.toHom)).obj g.src =
      (S.stageFunctor w).obj ((S.stageFunctor d.toHom).obj g.src)) :
    eqToHom (gsec_type_congr ℱ ha hw) (((d.lower w).res).s) = ((d.res).lower ℱ w).s := by
  -- the lowered stage morphism decomposes through the lowered data's morphism
  have hψ : (S.stageFunctor w).map ((S.stageFunctor d.toHom).map g.hom ≫ eqToHom d.glue) =
      eqToHom (S.stageFunctor_obj_comp d.toHom w g.src) ≫
      ((S.stageFunctor (w ≫ d.toHom)).map g.hom ≫ eqToHom ((d.lower w).glue)) ≫
      eqToHom (S.stageFunctor_obj_comp d.toRep w r.W).symm := by
    rw [Functor.map_comp, S.stageFunctor_map_map d.toHom w g.hom, eqToHom_map]
    simp only [Category.assoc, eqToHom_trans]
  -- naturality of the stage restriction against the stage morphism
  have hnat := congrFun ((stageRestriction ℱ (d.toRep ≫ r.a) w).1.naturality
    ((S.stageFunctor d.toHom).map g.hom ≫ eqToHom d.glue).op) ((r.lower ℱ d.toRep).s)
  -- the conjugated composite evaluates as the cast-conjugated map
  have hconj := presheaf_map_conj_eval
    ((((S.stageFunctor (w ≫ d.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj)
    (S.stageFunctor_obj_comp d.toHom w g.src)
    ((S.stageFunctor (w ≫ d.toHom)).map g.hom ≫ eqToHom ((d.lower w).glue))
    (S.stageFunctor_obj_comp d.toRep w r.W).symm
    (((r.lower ℱ d.toRep).lower ℱ w).s)
    (congrArg (fun Z => ((((S.stageFunctor (w ≫ d.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj).obj (op Z))
      (S.stageFunctor_obj_comp d.toRep w r.W))
    (congrArg (fun Z => ((((S.stageFunctor (w ≫ d.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj).obj (op Z))
      (S.stageFunctor_obj_comp d.toHom w g.src).symm)
  -- fold the inner cast with the double-lowering identification
  have e_low := r.lower_lower d.toRep w (Category.assoc w d.toRep r.a).symm
    (S.stageFunctor_obj_comp d.toRep w r.W)
  have hin₁ := (eqToHom_apply_collapse₂₁_aux
    (gsec_type_congr ℱ (Category.assoc w d.toRep r.a).symm
      (S.stageFunctor_obj_comp d.toRep w r.W))
    (gsec_type_congr ℱ ha rfl)
    (congrArg (fun Z => ((((S.stageFunctor (w ≫ d.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj).obj (op Z))
      (S.stageFunctor_obj_comp d.toRep w r.W))
    (((r.lower ℱ d.toRep).lower ℱ w).s)).symm
  have hin₂ := congrArg (fun z => eqToHom (gsec_type_congr ℱ ha
    (rfl : (S.stageFunctor (w ≫ d.toRep)).obj r.W = (S.stageFunctor (w ≫ d.toRep)).obj r.W)) z)
    e_low
  -- the structure-arrow cast exchanges with the lowered stage morphism
  have e_mid := (pull_map_index_congr ℱ ha
    ((S.stageFunctor (w ≫ d.toHom)).map g.hom ≫ eqToHom ((d.lower w).glue))
    (gsec_type_congr ℱ ha rfl) (gsec_type_congr ℱ ha rfl)
    ((r.lower ℱ (w ≫ d.toRep)).s)).symm
  -- final fold of the outer cast into the target cast
  have hfin := eqToHom_apply_collapse₂₁_aux
    (gsec_type_congr ℱ ha rfl)
    (congrArg (fun Z => ((((S.stageFunctor (w ≫ d.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj).obj (op Z))
      (S.stageFunctor_obj_comp d.toHom w g.src).symm)
    (gsec_type_congr ℱ ha hw)
    (((d.lower w).res).s)
  -- assemble
  have c₂ := congrArg (fun m => (((S.stageFunctor (w ≫ d.toRep ≫ r.a)).sheafPullback (Type u)
    (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.map m.op
    (((r.lower ℱ d.toRep).lower ℱ w).s)) hψ
  have c₇ := congrArg (fun z => eqToHom (congrArg
    (fun Z => ((((S.stageFunctor (w ≫ d.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj).obj (op Z))
      (S.stageFunctor_obj_comp d.toHom w g.src).symm) z)
    (((congrArg (fun z => (((S.stageFunctor (w ≫ d.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n)).obj ℱ).obj.map
      ((S.stageFunctor (w ≫ d.toHom)).map g.hom ≫ eqToHom ((d.lower w).glue)).op z)
      (hin₁.trans hin₂)).trans e_mid))
  exact (hnat.trans (c₂.trans (hconj.trans (c₇.trans hfin)))).symm

variable {S} in
/-- Component congruence for restricted representatives: equal lowering paths give equal
restricted sections up to the canonical cast. -/
theorem ResData.res_congr {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y : S.ColimitCategory} {g : HomRep x y} {r : GRep S ℱ y}
    {nn : S.I} {t t' : nn ⟶ g.idx} (ht : t = t') {sR sR' : nn ⟶ r.j} (hsR : sR = sR')
    (glue : (S.stageFunctor t).obj g.tgt = (S.stageFunctor sR).obj r.W)
    (glue' : (S.stageFunctor t').obj g.tgt = (S.stageFunctor sR').obj r.W)
    (hcast : ((((S.stageFunctor (sR ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology nn)).obj ℱ).obj.obj
        (op ((S.stageFunctor t).obj g.src))) =
      ((((S.stageFunctor (sR' ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology nn)).obj ℱ).obj.obj
        (op ((S.stageFunctor t').obj g.src)))) :
    eqToHom hcast (((⟨nn, t, sR, glue⟩ : ResData ℱ g r).res).s) =
      ((⟨nn, t', sR', glue'⟩ : ResData ℱ g r).res).s := by
  subst ht
  subst hsR
  rw [Subsingleton.elim hcast (rfl : _ = _)]
  rfl

variable {S} in
/-- The class of the restricted representative does not depend on the chosen restriction data. -/
theorem ResData.res_rel {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y : S.ColimitCategory} {g : HomRep x y} {r : GRep S ℱ y}
    (d d' : ResData ℱ g r) : grel (d.res) (d'.res) := by
  obtain ⟨m, u, v, huv⟩ := S.exists_span d.toHom d'.toHom
  obtain ⟨nn, e, he⟩ : ∃ (nn : S.I) (e : nn ⟶ m), e ≫ (u ≫ d.toRep) = e ≫ (v ≫ d'.toRep) :=
    ⟨_, IsCofiltered.eqHom _ _, IsCofiltered.eq_condition _ _⟩
  have hT : (e ≫ u) ≫ d.toHom = (e ≫ v) ≫ d'.toHom := by
    simp only [Category.assoc]; rw [huv]
  have hR : (e ≫ u) ≫ d.toRep = (e ≫ v) ≫ d'.toRep := by
    simpa [Category.assoc] using he
  refine ⟨nn, e ≫ u, e ≫ v, ?_, ?_, ?_⟩
  · calc (e ≫ u) ≫ d.toRep ≫ r.a
        = ((e ≫ u) ≫ d.toRep) ≫ r.a := (Category.assoc _ _ _).symm
      _ = ((e ≫ v) ≫ d'.toRep) ≫ r.a := congrArg (fun c : nn ⟶ r.j => c ≫ r.a) hR
      _ = (e ≫ v) ≫ d'.toRep ≫ r.a := Category.assoc _ _ _
  · calc (S.stageFunctor (e ≫ u)).obj ((S.stageFunctor d.toHom).obj g.src)
        = (S.stageFunctor ((e ≫ u) ≫ d.toHom)).obj g.src := S.stageFunctor_obj_comp _ _ _
      _ = (S.stageFunctor ((e ≫ v) ≫ d'.toHom)).obj g.src :=
          congrArg (fun c : nn ⟶ g.idx => (S.stageFunctor c).obj g.src) hT
      _ = (S.stageFunctor (e ≫ v)).obj ((S.stageFunctor d'.toHom).obj g.src) :=
          (S.stageFunctor_obj_comp _ _ _).symm
  · have A := cast_step_symm (d.res_lower (e ≫ u) (Category.assoc _ _ _)
      (S.stageFunctor_obj_comp d.toHom (e ≫ u) g.src).symm)
    have B := ResData.res_congr (g := g) (r := r) hT hR
      ((d.lower (e ≫ u)).glue) ((d'.lower (e ≫ v)).glue)
      (gsec_type_congr ℱ (congrArg (fun c : nn ⟶ r.j => c ≫ r.a) hR)
        (congrArg (fun c : nn ⟶ g.idx => (S.stageFunctor c).obj g.src) hT))
    have C := d'.res_lower (e ≫ v) (Category.assoc _ _ _)
      (S.stageFunctor_obj_comp d'.toHom (e ≫ v) g.src).symm
    exact cast_step_fold' A (cast_step_fold' B C)

/-- G-toolkit: presheaf map congruence along an `Arrow.mk` identification of the mapped
morphisms, an equality of presheaves, and a cast identification of the inputs. -/
theorem presheaf_map_arrowMk_congr {D : Type u} [Category.{u} D] {G₁ G₂ : Dᵒᵖ ⥤ Type u}
    (hG : G₁ = G₂) {W₁ Z₁ W₂ Z₂ : D} {ψ₁ : W₁ ⟶ Z₁} {ψ₂ : W₂ ⟶ Z₂}
    (h : Arrow.mk ψ₁ = Arrow.mk ψ₂)
    {z₁ : G₁.obj (op Z₁)} {z₂ : G₂.obj (op Z₂)}
    (hZ : G₁.obj (op Z₁) = G₂.obj (op Z₂)) (hz : eqToHom hZ z₁ = z₂)
    (hW : G₁.obj (op W₁) = G₂.obj (op W₂)) :
    eqToHom hW (G₁.map ψ₁.op z₁) = G₂.map ψ₂.op z₂ := by
  subst hG
  obtain ⟨h₁, h₂, hcomm⟩ := (arrowMk_eq_iff _ _).1 h
  subst h₁
  subst h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hcomm
  subst hcomm
  rw [Subsingleton.elim hZ (rfl : _ = _)] at hz
  rw [Subsingleton.elim hW (rfl : _ = _)]
  exact congrArg (fun z => G₁.map ψ₁.op z) hz

variable {S} in
/-- Replacing the morphism representative by a related one does not change the class of the
restricted representative. -/
theorem ResData.res_rel_hom {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y : S.ColimitCategory} {g₁ g₂ : HomRep x y} {r : GRep S ℱ y}
    (hg : homRel g₁ g₂) (d₂ : ResData ℱ g₂ r) :
    ∃ d₁ : ResData ℱ g₁ r, grel (d₁.res) (d₂.res) := by
  obtain ⟨l, c₁, c₂, harr⟩ := hg
  obtain ⟨hsrcZ, htgtZ, -⟩ := (arrowMk_eq_iff _ _).1 harr
  obtain ⟨m, u, v, huv⟩ := S.exists_span c₂ d₂.toHom
  have glue₁ : (S.stageFunctor (u ≫ c₁)).obj g₁.tgt =
      (S.stageFunctor (v ≫ d₂.toRep)).obj r.W := by
    calc (S.stageFunctor (u ≫ c₁)).obj g₁.tgt
        = (S.stageFunctor u).obj ((S.stageFunctor c₁).obj g₁.tgt) :=
          (S.stageFunctor_obj_comp c₁ u g₁.tgt).symm
      _ = (S.stageFunctor u).obj ((S.stageFunctor c₂).obj g₂.tgt) := by rw [htgtZ]
      _ = (S.stageFunctor (u ≫ c₂)).obj g₂.tgt := S.stageFunctor_obj_comp c₂ u g₂.tgt
      _ = (S.stageFunctor (v ≫ d₂.toHom)).obj g₂.tgt := by rw [huv]
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂.toHom).obj g₂.tgt) :=
          (S.stageFunctor_obj_comp d₂.toHom v g₂.tgt).symm
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂.toRep).obj r.W) := by rw [d₂.glue]
      _ = (S.stageFunctor (v ≫ d₂.toRep)).obj r.W := S.stageFunctor_obj_comp d₂.toRep v r.W
  -- the source objects of the lowered morphism representatives agree
  have hsrcm : (S.stageFunctor (𝟙 m ≫ u ≫ c₁)).obj g₁.src =
      (S.stageFunctor (v ≫ d₂.toHom)).obj g₂.src := by
    calc (S.stageFunctor (𝟙 m ≫ u ≫ c₁)).obj g₁.src
        = (S.stageFunctor (u ≫ c₁)).obj g₁.src :=
          congrArg (fun c : m ⟶ g₁.idx => (S.stageFunctor c).obj g₁.src)
            (Category.id_comp (u ≫ c₁))
      _ = (S.stageFunctor u).obj ((S.stageFunctor c₁).obj g₁.src) :=
          (S.stageFunctor_obj_comp c₁ u g₁.src).symm
      _ = (S.stageFunctor u).obj ((S.stageFunctor c₂).obj g₂.src) := by rw [hsrcZ]
      _ = (S.stageFunctor (u ≫ c₂)).obj g₂.src := S.stageFunctor_obj_comp c₂ u g₂.src
      _ = (S.stageFunctor (v ≫ d₂.toHom)).obj g₂.src := by rw [huv]
  -- the lowered morphism representatives have equal arrow images
  have hfst : Arrow.mk ((S.stageFunctor (𝟙 m ≫ u ≫ c₁)).map g₁.hom) =
      Arrow.mk ((S.stageFunctor (v ≫ d₂.toHom)).map g₂.hom) := by
    calc Arrow.mk ((S.stageFunctor (𝟙 m ≫ u ≫ c₁)).map g₁.hom)
        = Arrow.mk ((S.stageFunctor (u ≫ c₁)).map g₁.hom) :=
          congrArg (fun c : m ⟶ g₁.idx => Arrow.mk ((S.stageFunctor c).map g₁.hom))
            (Category.id_comp (u ≫ c₁))
      _ = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor c₁).map g₁.hom)) :=
          (S.arrowMk_map_map c₁ u g₁.hom).symm
      _ = Arrow.mk ((S.stageFunctor u).map ((S.stageFunctor c₂).map g₂.hom)) :=
          congrArg ((S.stageFunctor u).mapArrow.obj) harr
      _ = Arrow.mk ((S.stageFunctor (u ≫ c₂)).map g₂.hom) := S.arrowMk_map_map c₂ u g₂.hom
      _ = Arrow.mk ((S.stageFunctor (v ≫ d₂.toHom)).map g₂.hom) :=
          congrArg (fun c : m ⟶ g₂.idx => Arrow.mk ((S.stageFunctor c).map g₂.hom)) huv
  refine ⟨⟨m, u ≫ c₁, v ≫ d₂.toRep, glue₁⟩, m, 𝟙 m, v, ?_, ?_, ?_⟩
  · calc 𝟙 m ≫ (v ≫ d₂.toRep) ≫ r.a
        = (v ≫ d₂.toRep) ≫ r.a := Category.id_comp _
      _ = v ≫ d₂.toRep ≫ r.a := Category.assoc _ _ _
  · calc (S.stageFunctor (𝟙 m)).obj ((S.stageFunctor (u ≫ c₁)).obj g₁.src)
        = (S.stageFunctor (𝟙 m ≫ u ≫ c₁)).obj g₁.src :=
          S.stageFunctor_obj_comp (u ≫ c₁) (𝟙 m) g₁.src
      _ = (S.stageFunctor (v ≫ d₂.toHom)).obj g₂.src := hsrcm
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂.toHom).obj g₂.src) :=
          (S.stageFunctor_obj_comp d₂.toHom v g₂.src).symm
  · have A := cast_step_symm
      ((⟨m, u ≫ c₁, v ≫ d₂.toRep, glue₁⟩ : ResData ℱ g₁ r).res_lower (𝟙 m)
        (Category.assoc _ _ _) (S.stageFunctor_obj_comp (u ≫ c₁) (𝟙 m) g₁.src).symm)
    have B := presheaf_map_arrowMk_congr
      (congrArg (fun c : m ⟶ i₀ => (((S.stageFunctor c).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj)
        (congrArg (fun c : m ⟶ r.j => c ≫ r.a) (Category.id_comp (v ≫ d₂.toRep))))
      ((arrowMk_comp_eqToHom _ ((((⟨m, u ≫ c₁, v ≫ d₂.toRep, glue₁⟩ :
          ResData ℱ g₁ r).lower (𝟙 m))).glue)).trans
        (hfst.trans (arrowMk_comp_eqToHom _ ((d₂.lower v).glue)).symm))
      (gsec_type_congr ℱ (congrArg (fun c : m ⟶ r.j => c ≫ r.a)
        (Category.id_comp (v ≫ d₂.toRep)))
        (congrArg (fun c : m ⟶ r.j => (S.stageFunctor c).obj r.W)
          (Category.id_comp (v ≫ d₂.toRep))))
      (r.lower_arrow_congr (Category.id_comp (v ≫ d₂.toRep)) _)
      (gsec_type_congr ℱ (congrArg (fun c : m ⟶ r.j => c ≫ r.a)
        (Category.id_comp (v ≫ d₂.toRep))) hsrcm)
    have C := d₂.res_lower v (Category.assoc _ _ _)
      (S.stageFunctor_obj_comp d₂.toHom v g₂.src).symm
    exact cast_step_fold' A (cast_step_fold' B C)

variable {S} in
/-- Replacing the section representative by a related one does not change the class of the
restricted representative. -/
theorem ResData.res_rel_rep {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y : S.ColimitCategory} {g : HomRep x y} {r₁ r₂ : GRep S ℱ y}
    (hr : grel r₁ r₂) (d₂ : ResData ℱ g r₂) :
    ∃ d₁ : ResData ℱ g r₁, grel (d₁.res) (d₂.res) := by
  obtain ⟨k, b₁, b₂, hab, hwb, hsb⟩ := hr
  obtain ⟨m, u, v, huv⟩ := S.exists_span b₂ d₂.toRep
  have glue₁ : (S.stageFunctor (v ≫ d₂.toHom)).obj g.tgt =
      (S.stageFunctor (u ≫ b₁)).obj r₁.W := by
    calc (S.stageFunctor (v ≫ d₂.toHom)).obj g.tgt
        = (S.stageFunctor v).obj ((S.stageFunctor d₂.toHom).obj g.tgt) :=
          (S.stageFunctor_obj_comp d₂.toHom v g.tgt).symm
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂.toRep).obj r₂.W) := by rw [d₂.glue]
      _ = (S.stageFunctor (v ≫ d₂.toRep)).obj r₂.W := S.stageFunctor_obj_comp d₂.toRep v r₂.W
      _ = (S.stageFunctor (u ≫ b₂)).obj r₂.W :=
          (congrArg (fun c : m ⟶ r₂.j => (S.stageFunctor c).obj r₂.W) huv).symm
      _ = (S.stageFunctor u).obj ((S.stageFunctor b₂).obj r₂.W) :=
          (S.stageFunctor_obj_comp b₂ u r₂.W).symm
      _ = (S.stageFunctor u).obj ((S.stageFunctor b₁).obj r₁.W) := by rw [hwb]
      _ = (S.stageFunctor (u ≫ b₁)).obj r₁.W := S.stageFunctor_obj_comp b₁ u r₁.W
  have hpath : (𝟙 m ≫ u ≫ b₁) ≫ r₁.a = (v ≫ d₂.toRep) ≫ r₂.a := by
    calc (𝟙 m ≫ u ≫ b₁) ≫ r₁.a
        = (u ≫ b₁) ≫ r₁.a :=
          congrArg (fun c : m ⟶ r₁.j => c ≫ r₁.a) (Category.id_comp (u ≫ b₁))
      _ = u ≫ b₁ ≫ r₁.a := Category.assoc _ _ _
      _ = u ≫ b₂ ≫ r₂.a := congrArg (fun t => u ≫ t) hab
      _ = (u ≫ b₂) ≫ r₂.a := (Category.assoc _ _ _).symm
      _ = (v ≫ d₂.toRep) ≫ r₂.a := congrArg (fun c : m ⟶ r₂.j => c ≫ r₂.a) huv
  refine ⟨⟨m, v ≫ d₂.toHom, u ≫ b₁, glue₁⟩, m, 𝟙 m, v, ?_, ?_, ?_⟩
  · calc 𝟙 m ≫ (u ≫ b₁) ≫ r₁.a
        = (u ≫ b₁) ≫ r₁.a := Category.id_comp _
      _ = u ≫ b₁ ≫ r₁.a := Category.assoc _ _ _
      _ = u ≫ b₂ ≫ r₂.a := congrArg (fun t => u ≫ t) hab
      _ = (u ≫ b₂) ≫ r₂.a := (Category.assoc _ _ _).symm
      _ = (v ≫ d₂.toRep) ≫ r₂.a := congrArg (fun c : m ⟶ r₂.j => c ≫ r₂.a) huv
      _ = v ≫ d₂.toRep ≫ r₂.a := Category.assoc _ _ _
  · calc (S.stageFunctor (𝟙 m)).obj ((S.stageFunctor (v ≫ d₂.toHom)).obj g.src)
        = (S.stageFunctor (𝟙 m ≫ v ≫ d₂.toHom)).obj g.src :=
          S.stageFunctor_obj_comp (v ≫ d₂.toHom) (𝟙 m) g.src
      _ = (S.stageFunctor (v ≫ d₂.toHom)).obj g.src :=
          congrArg (fun c : m ⟶ g.idx => (S.stageFunctor c).obj g.src)
            (Category.id_comp (v ≫ d₂.toHom))
      _ = (S.stageFunctor v).obj ((S.stageFunctor d₂.toHom).obj g.src) :=
          (S.stageFunctor_obj_comp d₂.toHom v g.src).symm
  · -- bridge the lowered base sections through the relation witness
    have zA := r₁.lower_arrow_congr (Category.id_comp (u ≫ b₁))
      (congrArg (fun c : m ⟶ r₁.j => ((((S.stageFunctor (c ≫ r₁.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj
        (op ((S.stageFunctor c).obj r₁.W)))) (Category.id_comp (u ≫ b₁)))
    have zB := cast_step_symm (r₁.lower_lower b₁ u (Category.assoc u b₁ r₁.a).symm
      (S.stageFunctor_obj_comp b₁ u r₁.W))
    have zC := (stageRestriction_eval_congr ℱ hab hwb u (gsec_push_congr ℱ hab hwb u)
      ((r₁.lower ℱ b₁).s)).trans
      (congrArg (fun t => ((stageRestriction ℱ (b₂ ≫ r₂.a) u).1.app
        (op ((S.stageFunctor b₂).obj r₂.W))) t) hsb)
    have zD := r₂.lower_lower b₂ u (Category.assoc u b₂ r₂.a).symm
      (S.stageFunctor_obj_comp b₂ u r₂.W)
    have zE := r₂.lower_arrow_congr huv
      (congrArg (fun c : m ⟶ r₂.j => ((((S.stageFunctor (c ≫ r₂.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj
        (op ((S.stageFunctor c).obj r₂.W)))) huv)
    have hzfold := cast_step_fold' zA (cast_step_fold' zB (cast_step_fold' zC
      (cast_step_fold' zD zE)))
    have A := cast_step_symm
      ((⟨m, v ≫ d₂.toHom, u ≫ b₁, glue₁⟩ : ResData ℱ g r₁).res_lower (𝟙 m)
        (Category.assoc _ _ _) (S.stageFunctor_obj_comp (v ≫ d₂.toHom) (𝟙 m) g.src).symm)
    have B := presheaf_map_arrowMk_congr
      (congrArg (fun c : m ⟶ i₀ => (((S.stageFunctor c).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj) hpath)
      ((arrowMk_comp_eqToHom _ ((((⟨m, v ≫ d₂.toHom, u ≫ b₁, glue₁⟩ :
          ResData ℱ g r₁).lower (𝟙 m))).glue)).trans
        ((congrArg (fun c : m ⟶ g.idx => Arrow.mk ((S.stageFunctor c).map g.hom))
          (Category.id_comp (v ≫ d₂.toHom))).trans
        (arrowMk_comp_eqToHom _ ((d₂.lower v).glue)).symm))
      _ hzfold
      (gsec_type_congr ℱ hpath ((congrArg (fun c : m ⟶ g.idx =>
        (S.stageFunctor c).obj g.src) (Category.id_comp (v ≫ d₂.toHom)))))
    have C := d₂.res_lower v (Category.assoc _ _ _)
      (S.stageFunctor_obj_comp d₂.toHom v g.src).symm
    exact cast_step_fold' A (cast_step_fold' B C)

variable {S} in
/-- Restriction of representatives is well defined on both common-lowering classes and does not
depend on the restriction data. -/
theorem ResData.res_sound {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y : S.ColimitCategory} {g₁ g₂ : HomRep x y} {r₁ r₂ : GRep S ℱ y}
    (hg : homRel g₁ g₂) (hr : grel r₁ r₂)
    (d₁ : ResData ℱ g₁ r₁) (d₂ : ResData ℱ g₂ r₂) : grel (d₁.res) (d₂.res) := by
  obtain ⟨dmid, hmid⟩ := ResData.res_rel_rep hr d₂
  obtain ⟨d₁', h₁'⟩ := ResData.res_rel_hom hg dmid
  exact grel_trans (ResData.res_rel d₁ d₁') (grel_trans h₁' hmid)

variable {S} in
/-- The restriction map of the auxiliary sections along a morphism of the colimit category. -/
noncomputable def gres {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {x y : S.ColimitCategory} (f : x ⟶ y) (s : GSec ℱ y) : GSec ℱ x :=
  _root_.Quotient.lift₂
    (fun (g : HomRep x y) (r : GRep S ℱ y) => GSec.mk ((ResData.some ℱ g r).res))
    (fun _ _ _ _ hg hr => _root_.Quotient.sound
      (ResData.res_sound hg hr (ResData.some ℱ _ _) (ResData.some ℱ _ _)))
    f s

variable {S} in
/-- Computation rule for the restriction map: on classes it is the class of the restricted
representative, for any choice of restriction data. -/
theorem gres_mk_mk {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {x y : S.ColimitCategory} (g : HomRep x y) (r : GRep S ℱ y) (d : ResData ℱ g r) :
    gres ℱ (_root_.Quotient.mk _ g : x ⟶ y) (GSec.mk r) = GSec.mk (d.res) :=
  _root_.Quotient.sound (ResData.res_rel (ResData.some ℱ g r) d)

variable {S} in
/-- Restricting along an identity-shaped morphism representative does not change the class. -/
theorem ResData.res_id_rel {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {y : S.ColimitCategory} {q : S.ObjRep} {hq : S.ιObj q.idx q.obj = y} {r : GRep S ℱ y}
    (d : ResData ℱ (⟨q.idx, q.obj, q.obj, 𝟙 q.obj, hq, hq⟩ : HomRep y y) r) :
    grel (d.res) r := by
  have hobj : (S.stageFunctor (𝟙 d.idx ≫ d.toHom)).obj q.obj =
      (S.stageFunctor d.toRep).obj r.W :=
    (congrArg (fun c : d.idx ⟶ q.idx => (S.stageFunctor c).obj q.obj)
      (Category.id_comp d.toHom)).trans d.glue
  refine ⟨d.idx, 𝟙 d.idx, d.toRep, ?_, ?_, ?_⟩
  · exact Category.id_comp _
  · calc (S.stageFunctor (𝟙 d.idx)).obj ((S.stageFunctor d.toHom).obj q.obj)
        = (S.stageFunctor (𝟙 d.idx ≫ d.toHom)).obj q.obj :=
          S.stageFunctor_obj_comp d.toHom (𝟙 d.idx) q.obj
      _ = (S.stageFunctor d.toRep).obj r.W := hobj
  · have A := cast_step_symm (d.res_lower (𝟙 d.idx) (Category.assoc _ _ _)
      (S.stageFunctor_obj_comp d.toHom (𝟙 d.idx) q.obj).symm)
    have B := presheaf_map_arrowMk_congr
      (congrArg (fun c : d.idx ⟶ i₀ => (((S.stageFunctor c).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology d.idx)).obj ℱ).obj)
        (congrArg (fun c : d.idx ⟶ r.j => c ≫ r.a) (Category.id_comp d.toRep)))
      ((arrowMk_comp_eqToHom _ ((d.lower (𝟙 d.idx)).glue)).trans
        ((congrArg Arrow.mk ((S.stageFunctor (𝟙 d.idx ≫ d.toHom)).map_id q.obj)).trans
          (congrArg (fun Z : S.stage d.idx => Arrow.mk (𝟙 Z)) hobj)))
      (gsec_type_congr ℱ (congrArg (fun c : d.idx ⟶ r.j => c ≫ r.a)
        (Category.id_comp d.toRep))
        (congrArg (fun c : d.idx ⟶ r.j => (S.stageFunctor c).obj r.W)
          (Category.id_comp d.toRep)))
      (r.lower_arrow_congr (Category.id_comp d.toRep) _)
      (gsec_type_congr ℱ (congrArg (fun c : d.idx ⟶ r.j => c ≫ r.a)
        (Category.id_comp d.toRep)) hobj)
    have C : ((((S.stageFunctor (d.toRep ≫ r.a)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology d.idx)).obj ℱ).obj.map
        (𝟙 ((S.stageFunctor d.toRep).obj r.W)).op) ((r.lower ℱ d.toRep).s) =
        (r.lower ℱ d.toRep).s := by
      simp
    exact (cast_step_fold' A B).trans C

variable {S} in
/-- The restriction map along an identity is the identity. -/
theorem gres_id {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {y : S.ColimitCategory} (s : GSec ℱ y) : gres ℱ (𝟙 y) s = s := by
  induction s using _root_.Quotient.inductionOn with | _ r =>
  exact _root_.Quotient.sound (ResData.res_id_rel (ResData.some ℱ _ r))

variable {S} in
/-- Two representatives on the same stage with cast-equal components are related. -/
theorem grel_of_components {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} {j : S.I} {a a' : j ⟶ i₀} (ha : a = a')
    {W W' : S.stage j} (hW : W = W')
    {h₁ : S.ιObj j W = V} {h₂ : S.ιObj j W' = V}
    {s₁ : (((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology j)).obj ℱ).obj.obj (op W)}
    {s₂ : (((S.stageFunctor a').sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology j)).obj ℱ).obj.obj (op W')}
    (hs : eqToHom (gsec_type_congr ℱ ha hW) s₁ = s₂) :
    grel (⟨j, a, W, h₁, s₁⟩ : GRep S ℱ V) ⟨j, a', W', h₂, s₂⟩ := by
  subst ha
  subst hW
  rw [Subsingleton.elim (gsec_type_congr ℱ rfl rfl)
    (rfl : (((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology j)).obj ℱ).obj.obj (op W) = _)] at hs
  subst hs
  exact grel_refl _

variable {S} in
/-- The composition transport: restricting along a composite representative is restricting in two
steps, for aligned restriction data on a common stage. -/
theorem ResData.res_comp_core {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {x y z : S.ColimitCategory} {gf : HomRep x y} {gg : HomRep y z} {r : GRep S ℱ z}
    (dc : CompData gf gg) (dgg : ResData ℱ gg r)
    {m : S.I} (p : m ⟶ dc.idx) (q : m ⟶ dgg.idx)
    (hpq : p ≫ dc.toSnd = q ≫ dgg.toHom)
    (glue_c : (S.stageFunctor p).obj (dc.comp.tgt) =
      (S.stageFunctor (q ≫ dgg.toRep)).obj r.W)
    (glue_f : (S.stageFunctor (p ≫ dc.toFst)).obj gf.tgt =
      (S.stageFunctor q).obj ((dgg.res).W)) :
    grel ((⟨m, p, q ≫ dgg.toRep, glue_c⟩ : ResData ℱ dc.comp r).res)
      ((⟨m, p ≫ dc.toFst, q, glue_f⟩ : ResData ℱ gf (dgg.res)).res) := by
  -- the bridging object identification between the two stage morphisms
  have glue_f' : (S.stageFunctor (p ≫ dc.toFst)).obj gf.tgt =
      (S.stageFunctor (q ≫ dgg.toHom)).obj gg.src := by
    calc (S.stageFunctor (p ≫ dc.toFst)).obj gf.tgt
        = (S.stageFunctor p).obj ((S.stageFunctor dc.toFst).obj gf.tgt) :=
          (S.stageFunctor_obj_comp dc.toFst p gf.tgt).symm
      _ = (S.stageFunctor p).obj ((S.stageFunctor dc.toSnd).obj gg.src) := by rw [dc.glue]
      _ = (S.stageFunctor (p ≫ dc.toSnd)).obj gg.src :=
          S.stageFunctor_obj_comp dc.toSnd p gg.src
      _ = (S.stageFunctor (q ≫ dgg.toHom)).obj gg.src :=
          congrArg (fun c : m ⟶ gg.idx => (S.stageFunctor c).obj gg.src) hpq
  -- expansion of the mapped composite morphism
  have hexp : (S.stageFunctor p).map (dc.comp.hom) =
      (S.stageFunctor p).map ((S.stageFunctor dc.toFst).map gf.hom) ≫
      eqToHom (congrArg (S.stageFunctor p).obj dc.glue) ≫
      (S.stageFunctor p).map ((S.stageFunctor dc.toSnd).map gg.hom) := by
    change (S.stageFunctor p).map ((S.stageFunctor dc.toFst).map gf.hom ≫ eqToHom dc.glue ≫
      (S.stageFunctor dc.toSnd).map gg.hom) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, eqToHom_map]
  -- the second factors agree as arrows
  have hg_arr : Arrow.mk ((S.stageFunctor p).map ((S.stageFunctor dc.toSnd).map gg.hom) ≫
      eqToHom glue_c) =
      Arrow.mk ((S.stageFunctor (q ≫ dgg.toHom)).map gg.hom ≫
        eqToHom ((dgg.lower q).glue)) := by
    calc Arrow.mk ((S.stageFunctor p).map ((S.stageFunctor dc.toSnd).map gg.hom) ≫
          eqToHom glue_c)
        = Arrow.mk ((S.stageFunctor p).map ((S.stageFunctor dc.toSnd).map gg.hom)) :=
          arrowMk_comp_eqToHom _ glue_c
      _ = Arrow.mk ((S.stageFunctor (p ≫ dc.toSnd)).map gg.hom) :=
          S.arrowMk_map_map dc.toSnd p gg.hom
      _ = Arrow.mk ((S.stageFunctor (q ≫ dgg.toHom)).map gg.hom) :=
          congrArg (fun c : m ⟶ gg.idx => Arrow.mk ((S.stageFunctor c).map gg.hom)) hpq
      _ = Arrow.mk ((S.stageFunctor (q ≫ dgg.toHom)).map gg.hom ≫
          eqToHom ((dgg.lower q).glue)) :=
          (arrowMk_comp_eqToHom _ ((dgg.lower q).glue)).symm
  -- the full composite arrows agree
  have harr : Arrow.mk ((S.stageFunctor p).map (dc.comp.hom) ≫ eqToHom glue_c) =
      Arrow.mk (((S.stageFunctor (p ≫ dc.toFst)).map gf.hom ≫ eqToHom glue_f') ≫
        ((S.stageFunctor (q ≫ dgg.toHom)).map gg.hom ≫ eqToHom ((dgg.lower q).glue))) := by
    calc Arrow.mk ((S.stageFunctor p).map (dc.comp.hom) ≫ eqToHom glue_c)
        = Arrow.mk (((S.stageFunctor p).map ((S.stageFunctor dc.toFst).map gf.hom) ≫
            eqToHom (congrArg (S.stageFunctor p).obj dc.glue) ≫
            (S.stageFunctor p).map ((S.stageFunctor dc.toSnd).map gg.hom)) ≫
            eqToHom glue_c) :=
          congrArg (fun k => Arrow.mk (k ≫ eqToHom glue_c)) hexp
      _ = Arrow.mk ((S.stageFunctor p).map ((S.stageFunctor dc.toFst).map gf.hom) ≫
            eqToHom (congrArg (S.stageFunctor p).obj dc.glue) ≫
            ((S.stageFunctor p).map ((S.stageFunctor dc.toSnd).map gg.hom) ≫
            eqToHom glue_c)) := by
          congr 1
          simp only [Category.assoc]
      _ = Arrow.mk ((S.stageFunctor (p ≫ dc.toFst)).map gf.hom ≫
            eqToHom glue_f' ≫
            ((S.stageFunctor (q ≫ dgg.toHom)).map gg.hom ≫
            eqToHom ((dgg.lower q).glue))) :=
          arrowMk_glue_comp_congr (S.arrowMk_map_map dc.toFst p gf.hom) hg_arr _ _
      _ = Arrow.mk (((S.stageFunctor (p ≫ dc.toFst)).map gf.hom ≫ eqToHom glue_f') ≫
            ((S.stageFunctor (q ≫ dgg.toHom)).map gg.hom ≫
            eqToHom ((dgg.lower q).glue))) := by
          congr 1
          simp only [Category.assoc]
  refine grel_of_components (Category.assoc q dgg.toRep r.a)
    (S.stageFunctor_obj_comp dc.toFst p gf.src) ?_
  -- F1: collapse the composite to the two-step mapped form on the common-stage presheaf
  have F1 := presheaf_map_arrowMk_congr
    (rfl : (((S.stageFunctor ((q ≫ dgg.toRep) ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj = _)
    harr
    (z₁ := (r.lower ℱ (q ≫ dgg.toRep)).s)
    (z₂ := (r.lower ℱ (q ≫ dgg.toRep)).s)
    (rfl : (((S.stageFunctor ((q ≫ dgg.toRep) ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj
      (op ((S.stageFunctor (q ≫ dgg.toRep)).obj r.W)) = _)
    rfl
    (congrArg (fun Z => ((((S.stageFunctor ((q ≫ dgg.toRep) ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj).obj (op Z))
      (S.stageFunctor_obj_comp dc.toFst p gf.src))
  -- F2: split the two-step map
  have F2 : (((S.stageFunctor ((q ≫ dgg.toRep) ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.map
      ((((S.stageFunctor (p ≫ dc.toFst)).map gf.hom ≫ eqToHom glue_f') ≫
        ((S.stageFunctor (q ≫ dgg.toHom)).map gg.hom ≫
        eqToHom ((dgg.lower q).glue))).op) ((r.lower ℱ (q ≫ dgg.toRep)).s) =
      (((S.stageFunctor ((q ≫ dgg.toRep) ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.map
      (((S.stageFunctor (p ≫ dc.toFst)).map gf.hom ≫ eqToHom glue_f').op)
      ((((S.stageFunctor ((q ≫ dgg.toRep) ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.map
      (((S.stageFunctor (q ≫ dgg.toHom)).map gg.hom ≫
        eqToHom ((dgg.lower q).glue)).op) ((r.lower ℱ (q ≫ dgg.toRep)).s)) := by
    simp only [op_comp, FunctorToTypes.map_comp_apply]
  -- F4: exchange the index cast with the first-factor map
  have F4 := presheaf_map_arrowMk_congr
    (congrArg (fun c : m ⟶ i₀ => (((S.stageFunctor c).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj)
      ((Category.assoc q dgg.toRep r.a)))
    ((arrowMk_comp_eqToHom ((S.stageFunctor (p ≫ dc.toFst)).map gf.hom) glue_f').trans
      (arrowMk_comp_eqToHom ((S.stageFunctor (p ≫ dc.toFst)).map gf.hom) glue_f).symm)
    (z₁ := ((dgg.lower q).res).s)
    (z₂ := eqToHom (gsec_type_congr ℱ (Category.assoc q dgg.toRep r.a)
      (S.stageFunctor_obj_comp dgg.toHom q gg.src).symm) (((dgg.lower q).res).s))
    (gsec_type_congr ℱ (Category.assoc q dgg.toRep r.a)
      (S.stageFunctor_obj_comp dgg.toHom q gg.src).symm)
    rfl
    (gsec_type_congr ℱ (Category.assoc q dgg.toRep r.a) rfl)
  -- F5: rewrite the cast inner section through the restriction transport
  have F5 := congrArg (fun zz => (((S.stageFunctor (q ≫ dgg.toRep ≫ r.a)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.map
      (((S.stageFunctor (p ≫ dc.toFst)).map gf.hom ≫ eqToHom glue_f).op) zz)
    (dgg.res_lower q (Category.assoc q dgg.toRep r.a)
      (S.stageFunctor_obj_comp dgg.toHom q gg.src).symm)
  exact cast_step_fold' (F1.trans F2) (F4.trans F5)

variable {S} in
/-- Functoriality of the restriction maps: restricting along a composite is restricting in two
steps. -/
theorem gres_comp {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {x y z : S.ColimitCategory} (f : x ⟶ y) (g : y ⟶ z) (s : GSec ℱ z) :
    gres ℱ (f ≫ g) s = gres ℱ f (gres ℱ g s) := by
  induction f using _root_.Quotient.inductionOn with | _ gf =>
  induction g using _root_.Quotient.inductionOn with | _ gg =>
  induction s using _root_.Quotient.inductionOn with | _ r =>
  obtain ⟨m, p, q, hpq⟩ := S.exists_span (CompData.some gf gg).toSnd
    (ResData.some ℱ gg r).toHom
  have glue_c : (S.stageFunctor p).obj ((CompData.some gf gg).comp.tgt) =
      (S.stageFunctor (q ≫ (ResData.some ℱ gg r).toRep)).obj r.W := by
    calc (S.stageFunctor p).obj ((S.stageFunctor (CompData.some gf gg).toSnd).obj gg.tgt)
        = (S.stageFunctor (p ≫ (CompData.some gf gg).toSnd)).obj gg.tgt :=
          S.stageFunctor_obj_comp _ p gg.tgt
      _ = (S.stageFunctor (q ≫ (ResData.some ℱ gg r).toHom)).obj gg.tgt :=
          congrArg (fun c : m ⟶ gg.idx => (S.stageFunctor c).obj gg.tgt) hpq
      _ = (S.stageFunctor q).obj ((S.stageFunctor (ResData.some ℱ gg r).toHom).obj gg.tgt) :=
          (S.stageFunctor_obj_comp _ q gg.tgt).symm
      _ = (S.stageFunctor q).obj ((S.stageFunctor (ResData.some ℱ gg r).toRep).obj r.W) := by
          rw [(ResData.some ℱ gg r).glue]
      _ = (S.stageFunctor (q ≫ (ResData.some ℱ gg r).toRep)).obj r.W :=
          S.stageFunctor_obj_comp _ q r.W
  have glue_f : (S.stageFunctor (p ≫ (CompData.some gf gg).toFst)).obj gf.tgt =
      (S.stageFunctor q).obj (((ResData.some ℱ gg r).res).W) := by
    calc (S.stageFunctor (p ≫ (CompData.some gf gg).toFst)).obj gf.tgt
        = (S.stageFunctor p).obj ((S.stageFunctor (CompData.some gf gg).toFst).obj gf.tgt) :=
          (S.stageFunctor_obj_comp _ p gf.tgt).symm
      _ = (S.stageFunctor p).obj ((S.stageFunctor (CompData.some gf gg).toSnd).obj gg.src) := by
          rw [(CompData.some gf gg).glue]
      _ = (S.stageFunctor (p ≫ (CompData.some gf gg).toSnd)).obj gg.src :=
          S.stageFunctor_obj_comp _ p gg.src
      _ = (S.stageFunctor (q ≫ (ResData.some ℱ gg r).toHom)).obj gg.src :=
          congrArg (fun c : m ⟶ gg.idx => (S.stageFunctor c).obj gg.src) hpq
      _ = (S.stageFunctor q).obj ((S.stageFunctor (ResData.some ℱ gg r).toHom).obj gg.src) :=
          (S.stageFunctor_obj_comp _ q gg.src).symm
  calc gres ℱ ((_root_.Quotient.mk _ gf ≫ _root_.Quotient.mk _ gg : x ⟶ z)) (GSec.mk r)
      = gres ℱ (_root_.Quotient.mk _ ((CompData.some gf gg).comp) : x ⟶ z) (GSec.mk r) := by
        rw [mk_comp_mk gf gg (CompData.some gf gg)]
    _ = GSec.mk ((⟨m, p, q ≫ (ResData.some ℱ gg r).toRep, glue_c⟩ :
        ResData ℱ (CompData.some gf gg).comp r).res) :=
        gres_mk_mk ℱ _ r _
    _ = GSec.mk ((⟨m, p ≫ (CompData.some gf gg).toFst, q, glue_f⟩ :
        ResData ℱ gf ((ResData.some ℱ gg r).res)).res) :=
        _root_.Quotient.sound
          (ResData.res_comp_core (CompData.some gf gg) (ResData.some ℱ gg r) p q hpq
            glue_c glue_f)
    _ = gres ℱ (_root_.Quotient.mk _ gf : x ⟶ y) (GSec.mk ((ResData.some ℱ gg r).res)) :=
        (gres_mk_mk ℱ gf ((ResData.some ℱ gg r).res) _).symm
    _ = gres ℱ (_root_.Quotient.mk _ gf : x ⟶ y)
        (gres ℱ (_root_.Quotient.mk _ gg : y ⟶ z) (GSec.mk r)) := rfl

variable {S} in
/-- The auxiliary presheaf `G` on the colimit category (the source's equation (7.18.3.1)
machine): sections over `V` are stage sections of the pulled-back sheaves modulo common
lowering, and restriction maps descend from the stages. -/
noncomputable def auxiliaryPresheaf {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u)) :
    (S.ColimitCategory)ᵒᵖ ⥤ Type u where
  obj V := GSec ℱ V.unop
  map {V V'} f s := gres ℱ f.unop s
  map_id V := by
    funext s
    exact gres_id ℱ s
  map_comp {V V' V''} f g := by
    funext s
    exact gres_comp ℱ g.unop f.unop s

end Restriction

section SheafProperty

variable {S} in
/-- Stage-level computation of the restriction map: restricting the class of a stage
representative along the image of a stage morphism with the same presenting object is the class
of the mapped section. -/
theorem gres_stage_mk {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {i : S.I} {Y X : S.stage i} (g : Y ⟶ X) (a : i ⟶ i₀)
    (s : (((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology i)).obj ℱ).obj.obj (op X)) :
    gres ℱ ((S.stageCoconeFunctor i).map g)
      (GSec.mk (⟨i, a, X, rfl, s⟩ : GRep S ℱ (S.ιObj i X))) =
      GSec.mk (⟨i, a, Y, rfl,
        ((((S.stageFunctor a).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology i)).obj ℱ).obj.map g.op) s⟩ :
        GRep S ℱ (S.ιObj i Y)) := by
  refine (gres_mk_mk ℱ (⟨i, Y, X, g, rfl, rfl⟩ : HomRep (S.ιObj i Y) (S.ιObj i X))
    (⟨i, a, X, rfl, s⟩ : GRep S ℱ (S.ιObj i X)) ⟨i, 𝟙 i, 𝟙 i, rfl⟩).trans
    (_root_.Quotient.sound ?_)
  -- relate the data-restricted representative to the clean mapped representative
  have hnat := congrFun ((stageRestriction ℱ a (𝟙 i)).1.naturality g.op) s
  refine ⟨i, 𝟙 i, 𝟙 i, ?_, ?_, ?_⟩
  · exact Category.id_comp _
  · calc (S.stageFunctor (𝟙 i)).obj ((S.stageFunctor (𝟙 i)).obj Y)
        = (S.stageFunctor (𝟙 i ≫ 𝟙 i)).obj Y := S.stageFunctor_obj_comp (𝟙 i) (𝟙 i) Y
      _ = (S.stageFunctor (𝟙 i)).obj Y :=
          congrArg (fun c : i ⟶ i => (S.stageFunctor c).obj Y) (Category.id_comp (𝟙 i))
  · have A := cast_step_symm
      ((⟨i, 𝟙 i, 𝟙 i, rfl⟩ : ResData ℱ
        (⟨i, Y, X, g, rfl, rfl⟩ : HomRep (S.ιObj i Y) (S.ιObj i X))
        (⟨i, a, X, rfl, s⟩ : GRep S ℱ (S.ιObj i X))).res_lower (𝟙 i)
        (Category.assoc _ _ _) (S.stageFunctor_obj_comp (𝟙 i) (𝟙 i) Y).symm)
    have C := presheaf_map_arrowMk_congr
      (congrArg (fun c : i ⟶ i₀ => (((S.stageFunctor c).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology i)).obj ℱ).obj)
        (congrArg (fun c : i ⟶ i => c ≫ a) (Category.id_comp (𝟙 i))))
      ((arrowMk_comp_eqToHom ((S.stageFunctor (𝟙 i ≫ 𝟙 i)).map g)
        ((⟨i, 𝟙 i, 𝟙 i, rfl⟩ : ResData ℱ
          (⟨i, Y, X, g, rfl, rfl⟩ : HomRep (S.ιObj i Y) (S.ιObj i X))
          (⟨i, a, X, rfl, s⟩ : GRep S ℱ (S.ιObj i X))).lower (𝟙 i)).glue).trans
        (congrArg (fun c : i ⟶ i => Arrow.mk ((S.stageFunctor c).map g))
          (Category.id_comp (𝟙 i))))
      (gsec_type_congr ℱ (congrArg (fun c : i ⟶ i => c ≫ a) (Category.id_comp (𝟙 i)))
        (congrArg (fun c : i ⟶ i => (S.stageFunctor c).obj X) (Category.id_comp (𝟙 i))))
      ((⟨i, a, X, rfl, s⟩ : GRep S ℱ (S.ιObj i X)).lower_arrow_congr
        (Category.id_comp (𝟙 i))
        (gsec_type_congr ℱ (congrArg (fun c : i ⟶ i => c ≫ a) (Category.id_comp (𝟙 i)))
          (congrArg (fun c : i ⟶ i => (S.stageFunctor c).obj X) (Category.id_comp (𝟙 i)))))
      (gsec_type_congr ℱ (congrArg (fun c : i ⟶ i => c ≫ a) (Category.id_comp (𝟙 i)))
        (congrArg (fun c : i ⟶ i => (S.stageFunctor c).obj Y) (Category.id_comp (𝟙 i))))
    exact cast_step_fold' A (C.trans hnat.symm)

variable {S} in
/-- Restriction along a transport morphism is the section transport. -/
theorem gres_eqToHom {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {x y : S.ColimitCategory} (h : x = y) (hsec : GSec ℱ y = GSec ℱ x) (s : GSec ℱ y) :
    gres ℱ (eqToHom h) s = eqToHom hsec s := by
  subst h
  rw [Subsingleton.elim hsec (rfl : GSec ℱ x = GSec ℱ x)]
  exact gres_id ℱ s

variable {S} in
/-- Every auxiliary section over a stage image is the class of a representative presenting
through a lowering of the given stage object. -/
theorem GSec.exists_lowered_rep {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {i : S.I} {X : S.stage i} (x : GSec ℱ (S.ιObj i X)) :
    ∃ (k : S.I) (e : k ⟶ i) (a : k ⟶ i₀)
      (σ : (((S.stageFunctor a).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology k)).obj ℱ).obj.obj
        (op ((S.stageFunctor e).obj X))),
      GSec.mk (⟨k, a, (S.stageFunctor e).obj X, S.ιObj_lower e X, σ⟩ :
        GRep S ℱ (S.ιObj i X)) = x := by
  obtain ⟨r, rfl⟩ := GSec.mk_surjective x
  obtain ⟨k, c, e, hce⟩ := S.ιObj_exact r.hW
  refine ⟨k, e, c ≫ r.a, eqToHom (gsec_type_congr ℱ rfl hce) ((r.lower ℱ c).s), ?_⟩
  refine _root_.Quotient.sound (grel_trans (grel_of_components rfl hce.symm ?_)
    (grel_symm (grel_lower r c)))
  exact eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ rfl hce)
    (gsec_type_congr ℱ rfl hce.symm) rfl ((r.lower ℱ c).s)

/-- G-toolkit: the functor image of an `ofArrows` presieve is the `ofArrows` of the images. -/
theorem presieve_map_ofArrows {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X : C} {ι : Type*} (Y : ι → C) (π : ∀ t, Y t ⟶ X) :
    (Presieve.ofArrows Y π).map F =
      Presieve.ofArrows (fun t => F.obj (Y t)) (fun t => F.map (π t)) := by
  refine le_antisymm ?_ ?_
  · rintro Z g ⟨hp⟩
    rcases hp with ⟨t⟩
    exact Presieve.ofArrows.mk t
  · rintro Z g ⟨t⟩
    exact Presieve.map.of (Presieve.ofArrows.mk t)

/-- G-toolkit: every presieve is the `ofArrows` family of its own member data. -/
theorem presieve_eq_ofArrows_uncurry {C : Type*} [Category C] {X : C} (R : Presieve X) :
    R = Presieve.ofArrows (fun ω : R.uncurry => ω.1.1) (fun ω => ω.1.2) :=
  le_antisymm (fun _Z g hg => Presieve.ofArrows.mk (⟨⟨_, g⟩, hg⟩ : R.uncurry))
    (fun _Z _g ⟨ω⟩ => ω.2)

variable {S} in
/-- G-toolkit: a class transported along an equality of base objects is the class of the
representative with the transported presentation. -/
theorem GSec.cast_mk {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V V' : S.ColimitCategory} (h : V = V') (r : GRep S ℱ V)
    (hsec : GSec ℱ V = GSec ℱ V') :
    eqToHom hsec (GSec.mk r) = GSec.mk ⟨r.j, r.a, r.W, r.hW.trans h, r.s⟩ := by
  subst h
  rw [Subsingleton.elim hsec (rfl : GSec ℱ V = GSec ℱ V)]
  rfl

variable {S} in
/-- G-toolkit: finitely many parallel index arrows are simultaneously equalized at a common
lower stage. -/
theorem exists_equalize_finite {ι : Type*} [Finite ι] {m i₀ : S.I} (q : ι → (m ⟶ i₀)) :
    ∃ (m' : S.I) (e : m' ⟶ m), ∀ ω₁ ω₂, e ≫ q ω₁ = e ≫ q ω₂ := by
  classical
  cases nonempty_fintype ι
  suffices h : ∀ s : Finset (ι × ι), ∃ (m' : S.I) (e : m' ⟶ m),
      ∀ p ∈ s, e ≫ q p.1 = e ≫ q p.2 by
    obtain ⟨m', e, he⟩ := h Finset.univ
    exact ⟨m', e, fun ω₁ ω₂ => he (ω₁, ω₂) (Finset.mem_univ _)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨m, 𝟙 m, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨m', e, he⟩ := ih
    obtain ⟨m'', e', he'⟩ : ∃ (m'' : S.I) (e' : m'' ⟶ m'),
        e' ≫ (e ≫ q p.1) = e' ≫ (e ≫ q p.2) :=
      ⟨IsCofiltered.eq _ _, IsCofiltered.eqHom _ _, IsCofiltered.eq_condition _ _⟩
    refine ⟨m'', e' ≫ e, ?_⟩
    intro p' hp'
    rcases Finset.mem_insert.1 hp' with rfl | hps
    · simpa [Category.assoc] using he'
    · simp only [Category.assoc]
      exact congrArg (fun t => e' ≫ t) (he p' hps)

variable {S} in
/-- Stage-level computation of the restriction map for lowered presentations: restricting the
class of a representative presenting through a lowering of `X` along the image of a stage
morphism into `X` is the class of the mapped section. -/
theorem gres_stage_lowered_mk {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {i m : S.I} (w : m ⟶ i) {Y X : S.stage i} (g : Y ⟶ X) (b : m ⟶ i₀)
    (σ : (((S.stageFunctor b).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj
      (op ((S.stageFunctor w).obj X))) :
    gres ℱ ((S.stageCoconeFunctor i).map g)
      (GSec.mk (⟨m, b, (S.stageFunctor w).obj X, S.ιObj_lower w X, σ⟩ :
        GRep S ℱ (S.ιObj i X))) =
      GSec.mk (⟨m, b, (S.stageFunctor w).obj Y, S.ιObj_lower w Y,
        ((((S.stageFunctor b).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.map
          ((S.stageFunctor w).map g).op) σ⟩ : GRep S ℱ (S.ιObj i Y)) := by
  have glue_w : (S.stageFunctor w).obj X = (S.stageFunctor (𝟙 m)).obj
      ((S.stageFunctor w).obj X) :=
    ((S.stageFunctor_obj_comp w (𝟙 m) X).trans
      (congrArg (fun c : m ⟶ i => (S.stageFunctor c).obj X) (Category.id_comp w))).symm
  refine (gres_mk_mk ℱ (⟨i, Y, X, g, rfl, rfl⟩ : HomRep (S.ιObj i Y) (S.ιObj i X))
    (⟨m, b, (S.stageFunctor w).obj X, S.ιObj_lower w X, σ⟩ : GRep S ℱ (S.ιObj i X))
    ⟨m, w, 𝟙 m, glue_w⟩).trans
    (_root_.Quotient.sound ?_)
  have hnat := congrFun ((stageRestriction ℱ b (𝟙 m)).1.naturality
    ((S.stageFunctor w).map g).op) σ
  refine ⟨m, 𝟙 m, 𝟙 m, Category.id_comp _, rfl, ?_⟩
  have A := cast_step_symm
    ((⟨m, w, 𝟙 m, glue_w⟩ : ResData ℱ
      (⟨i, Y, X, g, rfl, rfl⟩ : HomRep (S.ιObj i Y) (S.ιObj i X))
      (⟨m, b, (S.stageFunctor w).obj X, S.ιObj_lower w X, σ⟩ :
        GRep S ℱ (S.ιObj i X))).res_lower (𝟙 m)
      (Category.assoc _ _ _) (S.stageFunctor_obj_comp w (𝟙 m) Y).symm)
  have C := presheaf_map_arrowMk_congr
    (congrArg (fun c : m ⟶ i₀ => (((S.stageFunctor c).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj)
      (congrArg (fun c : m ⟶ m => c ≫ b) (Category.id_comp (𝟙 m))))
    ((arrowMk_comp_eqToHom ((S.stageFunctor (𝟙 m ≫ w)).map g)
      ((⟨m, w, 𝟙 m, glue_w⟩ : ResData ℱ
        (⟨i, Y, X, g, rfl, rfl⟩ : HomRep (S.ιObj i Y) (S.ιObj i X))
        (⟨m, b, (S.stageFunctor w).obj X, S.ιObj_lower w X, σ⟩ :
          GRep S ℱ (S.ιObj i X))).lower (𝟙 m)).glue).trans
      (S.arrowMk_map_map w (𝟙 m) g).symm)
    (gsec_type_congr ℱ (congrArg (fun c : m ⟶ m => c ≫ b) (Category.id_comp (𝟙 m)))
      (congrArg (fun c : m ⟶ m => (S.stageFunctor c).obj ((S.stageFunctor w).obj X))
        (Category.id_comp (𝟙 m))))
    ((⟨m, b, (S.stageFunctor w).obj X, S.ιObj_lower w X, σ⟩ :
      GRep S ℱ (S.ιObj i X)).lower_arrow_congr (Category.id_comp (𝟙 m))
      (gsec_type_congr ℱ (congrArg (fun c : m ⟶ m => c ≫ b) (Category.id_comp (𝟙 m)))
        (congrArg (fun c : m ⟶ m => (S.stageFunctor c).obj ((S.stageFunctor w).obj X))
          (Category.id_comp (𝟙 m)))))
    (gsec_type_congr ℱ (congrArg (fun c : m ⟶ m => c ≫ b) (Category.id_comp (𝟙 m)))
      (S.stageFunctor_obj_comp w (𝟙 m) Y).symm)
  exact cast_step_fold' A (C.trans hnat.symm)

/-- G-toolkit: cancel a transport conjugation at the head of a three-factor composite. -/
theorem eqToHom_cancel_conj₂ {D : Type*} [Category D] {P Q R T : D}
    (h : P = Q) (m : P ⟶ R) (g : R ⟶ T) :
    eqToHom h ≫ eqToHom h.symm ≫ m ≫ g = m ≫ g := by
  subst h
  simp

variable {S} in
/-- A commuting square of stage morphisms at a lowered stage induces a commuting square of the
corresponding colimit-category morphisms into the cover members. -/
theorem cocone_lowered_square {i m : S.I} (w : m ⟶ i) {Y₁ Y₂ X : S.stage i} {Z : S.stage m}
    (π₁ : Y₁ ⟶ X) (π₂ : Y₂ ⟶ X) (h₁ : Z ⟶ (S.stageFunctor w).obj Y₁)
    (h₂ : Z ⟶ (S.stageFunctor w).obj Y₂)
    (hsq : h₁ ≫ (S.stageFunctor w).map π₁ = h₂ ≫ (S.stageFunctor w).map π₂) :
    ((S.stageCoconeFunctor m).map h₁ ≫ eqToHom (S.ιObj_lower w Y₁)) ≫
      (S.stageCoconeFunctor i).map π₁ =
    ((S.stageCoconeFunctor m).map h₂ ≫ eqToHom (S.ιObj_lower w Y₂)) ≫
      (S.stageCoconeFunctor i).map π₂ := by
  have key : ∀ {Y : S.stage i} (π : Y ⟶ X) (hh : Z ⟶ (S.stageFunctor w).obj Y),
      ((S.stageCoconeFunctor m).map hh ≫ eqToHom (S.ιObj_lower w Y)) ≫
        (S.stageCoconeFunctor i).map π =
      (S.stageCoconeFunctor m).map (hh ≫ (S.stageFunctor w).map π) ≫
        eqToHom (S.ιObj_lower w X) := by
    intro Y π hh
    rw [S.stageCoconeFunctor_map_lower w π, Functor.map_comp]
    simp only [Category.assoc]
    congr 1
    exact eqToHom_cancel_conj₂ (S.ιObj_lower w Y)
      ((S.stageCoconeFunctor m).map ((S.stageFunctor w).map π))
      (eqToHom (S.ιObj_lower w X))
  rw [key π₁ h₁, key π₂ h₂, hsq]

variable {S} in
/-- Extract from a relation between two representatives with identical structure data a single
common lowering where the underlying stage sections agree on the nose. -/
theorem grel_extract_lowering {i₀ : S.I} {ℱ : Sheaf (S.stageTopology i₀) (Type u)}
    {V : S.ColimitCategory} {m : S.I} {b : m ⟶ i₀} {Z : S.stage m}
    {h₁ h₂ : S.ιObj m Z = V}
    {s₁ s₂ : (((S.stageFunctor b).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj (op Z)}
    (hrel : grel (⟨m, b, Z, h₁, s₁⟩ : GRep S ℱ V) ⟨m, b, Z, h₂, s₂⟩) :
    ∃ (n : S.I) (e : n ⟶ m),
      ((stageRestriction ℱ b e).1.app (op Z)) s₁ =
        ((stageRestriction ℱ b e).1.app (op Z)) s₂ := by
  obtain ⟨k, c₁, c₂, hac, hwc, hsc⟩ := hrel
  obtain ⟨n, e', he'⟩ : ∃ (n : S.I) (e' : n ⟶ k), e' ≫ c₁ = e' ≫ c₂ :=
    ⟨_, IsCofiltered.eqHom _ _, IsCofiltered.eq_condition _ _⟩
  refine ⟨n, e' ≫ c₁, ?_⟩
  have A := cast_step_symm
    ((⟨m, b, Z, h₁, s₁⟩ : GRep S ℱ V).lower_lower c₁ e'
      (Category.assoc e' c₁ b).symm (S.stageFunctor_obj_comp c₁ e' Z))
  have B := (stageRestriction_eval_congr ℱ hac hwc e' (gsec_push_congr ℱ hac hwc e')
    (((⟨m, b, Z, h₁, s₁⟩ : GRep S ℱ V).lower ℱ c₁).s)).trans
    (congrArg (fun t => ((stageRestriction ℱ (c₂ ≫ b) e').1.app
      (op ((S.stageFunctor c₂).obj Z))) t) hsc)
  have C := (⟨m, b, Z, h₂, s₂⟩ : GRep S ℱ V).lower_lower c₂ e'
    (Category.assoc e' c₂ b).symm (S.stageFunctor_obj_comp c₂ e' Z)
  have D := (⟨m, b, Z, h₂, s₂⟩ : GRep S ℱ V).lower_arrow_congr he'.symm
    (gsec_type_congr ℱ (congrArg (fun c : n ⟶ m => c ≫ b) he'.symm)
      (congrArg (fun c : n ⟶ m => (S.stageFunctor c).obj Z) he'.symm))
  exact cast_step_fold' A (cast_step_fold' B (cast_step_fold' C D))

variable {S} in
/-- Computation of the restriction along a lowered-stage morphism composed with the presentation
transport: it is the mapped section at the lower stage. -/
theorem gres_lowered_cocone_mk {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {i m : S.I} (w : m ⟶ i) {Y : S.stage i} {Z : S.stage m}
    (h : Z ⟶ (S.stageFunctor w).obj Y) (b : m ⟶ i₀)
    (τ : (((S.stageFunctor b).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.obj
      (op ((S.stageFunctor w).obj Y))) :
    gres ℱ ((S.stageCoconeFunctor m).map h ≫ eqToHom (S.ιObj_lower w Y))
      (GSec.mk (⟨m, b, (S.stageFunctor w).obj Y, S.ιObj_lower w Y, τ⟩ :
        GRep S ℱ (S.ιObj i Y))) =
      GSec.mk (⟨m, b, Z, rfl,
        ((((S.stageFunctor b).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m)).obj ℱ).obj.map h.op) τ⟩ :
        GRep S ℱ (S.ιObj m Z)) := by
  refine (gres_comp ℱ _ _ _).trans ?_
  refine (congrArg (fun z => gres ℱ ((S.stageCoconeFunctor m).map h) z)
    ((gres_eqToHom ℱ (S.ιObj_lower w Y)
      (congrArg (fun v => GSec ℱ v) (S.ιObj_lower w Y).symm) _).trans
      (GSec.cast_mk (S.ιObj_lower w Y).symm _ _))).trans ?_
  exact gres_stage_mk ℱ h b τ

/-- G-toolkit: cancel an inverse transport pair at the head of a composite. -/
theorem eqToHom_symm_comp_cancel {D : Type*} [Category D] {P Q R : D}
    (h : P = Q) (m : Q ⟶ R) :
    eqToHom h.symm ≫ eqToHom h ≫ m = m := by
  subst h
  simp

/-- G-toolkit: cancel an inverse transport pair at the tail of a composite. -/
theorem comp_eqToHom_symm_cancel {D : Type*} [Category D] {P Q R : D}
    (h : P = Q) (m : R ⟶ Q) :
    m ≫ eqToHom h.symm ≫ eqToHom h = m := by
  subst h
  simp

variable {S} in
/-- G-toolkit: a finite family of stages over `i` admits a common refinement that also maps to
`i₀`. -/
theorem exists_bicone_finite {ι : Type*} [Finite ι] (i i₀ : S.I) (k : ι → S.I)
    (e : ∀ ω, k ω ⟶ i) :
    ∃ (m : S.I) (w : m ⟶ i) (b₀ : m ⟶ i₀) (u : ∀ ω, m ⟶ k ω),
      ∀ ω, u ω ≫ e ω = w := by
  obtain ⟨m₀, w₀, u₀, hu₀⟩ := IsCofiltered.wideCospan e
  exact ⟨IsCofiltered.min m₀ i₀, IsCofiltered.minToLeft m₀ i₀ ≫ w₀,
    IsCofiltered.minToRight m₀ i₀,
    fun ω => IsCofiltered.minToLeft m₀ i₀ ≫ u₀ ω,
    fun ω => by rw [Category.assoc, hu₀]⟩

variable {S} in
/-- THE SHEAF CORE (source 0A35, "G is a sheaf"): the auxiliary presheaf satisfies the sheaf
condition at every stage covering image. Source proof: the covering is finite, all section
classes and the finitely many pullback-compatibility conditions merge at a common stage by
cofilteredness, and the stage sheaf condition for the pulled-back sheaf glues. -/
theorem auxiliaryPresheaf_isSheafFor_stageCover {i₀ : S.I}
    (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {i : S.I} (X : S.stage i) {V : S.ColimitCategory} (hX : S.ιObj i X = V)
    {R : Presieve X} (hR : R ∈ S.stageCov i X) :
    Presieve.IsSheafFor (auxiliaryPresheaf ℱ) (S.stageCover i X hX R) := by
  subst hX
  rw [S.stageCover_rfl_eq_map]
  haveI hfin : Finite R.uncurry :=
    ((Precoverage.mem_finite_iff).1 (S.stageCov_finite hR)).to_subtype
  rw [presieve_eq_ofArrows_uncurry R, presieve_map_ofArrows]
  refine (Presieve.isSheafFor_arrows_iff (auxiliaryPresheaf ℱ)
    (fun ω : R.uncurry => (S.stageCoconeFunctor i).map ω.1.2)).2 ?_
  intro x hx
  -- choose lowered representatives of the section classes
  choose k e a σ hσ using fun ω : R.uncurry => GSec.exists_lowered_rep (x ω)
  -- merge the presenting stages over `i` and `i₀`
  obtain ⟨m₀, w₀, b₀, u, hu⟩ := exists_bicone_finite i i₀ k e
  obtain ⟨m₁, e₁, he₁⟩ := exists_equalize_finite
    (fun o : Option R.uncurry => Option.elim o b₀ (fun ω => u ω ≫ a ω))
  have hv : ∀ ω : R.uncurry, (e₁ ≫ u ω) ≫ e ω = e₁ ≫ w₀ := by
    intro ω
    rw [Category.assoc, hu ω]
  have hb : ∀ ω : R.uncurry, (e₁ ≫ u ω) ≫ a ω = e₁ ≫ b₀ := by
    intro ω
    rw [Category.assoc]
    exact he₁ (some ω) none
  have hWeq : ∀ ω : R.uncurry,
      (S.stageFunctor (e₁ ≫ u ω)).obj ((S.stageFunctor (e ω)).obj ω.1.1) =
        (S.stageFunctor (e₁ ≫ w₀)).obj ω.1.1 := fun ω =>
    (S.stageFunctor_obj_comp (e ω) (e₁ ≫ u ω) ω.1.1).trans
      (congrArg (fun c : m₁ ⟶ i => (S.stageFunctor c).obj ω.1.1) (hv ω))
  -- the merged stage sections
  obtain ⟨τ, hτ⟩ : ∃ τ : ∀ ω : R.uncurry,
      (((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.obj
        (op ((S.stageFunctor (e₁ ≫ w₀)).obj ω.1.1)),
      ∀ ω, τ ω = eqToHom (gsec_type_congr ℱ (hb ω) (hWeq ω))
        (((⟨k ω, a ω, (S.stageFunctor (e ω)).obj ω.1.1,
          S.ιObj_lower (e ω) ω.1.1, σ ω⟩ : GRep S ℱ (S.ιObj i ω.1.1)).lower ℱ
          (e₁ ≫ u ω)).s) :=
    ⟨_, fun ω => rfl⟩
  -- every class is presented by its merged section
  have hx' : ∀ ω : R.uncurry, GSec.mk (⟨m₁, e₁ ≫ b₀, (S.stageFunctor (e₁ ≫ w₀)).obj ω.1.1,
      S.ιObj_lower (e₁ ≫ w₀) ω.1.1, τ ω⟩ : GRep S ℱ (S.ιObj i ω.1.1)) = x ω := by
    intro ω
    rw [hτ ω]
    refine Eq.trans (_root_.Quotient.sound (grel_trans
      (grel_of_components (hb ω).symm (hWeq ω).symm
        (eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ (hb ω) (hWeq ω))
          (gsec_type_congr ℱ (hb ω).symm (hWeq ω).symm) rfl _))
      (grel_symm (grel_lower (⟨k ω, a ω, (S.stageFunctor (e ω)).obj ω.1.1,
        S.ιObj_lower (e ω) ω.1.1, σ ω⟩ : GRep S ℱ (S.ιObj i ω.1.1)) (e₁ ≫ u ω))))) (hσ ω)
  -- class-level compatibility at arbitrary lowered squares
  have hclass : ∀ (ω₁ ω₂ : R.uncurry) {Z : S.stage m₁}
      (h₁ : Z ⟶ (S.stageFunctor (e₁ ≫ w₀)).obj ω₁.1.1)
      (h₂ : Z ⟶ (S.stageFunctor (e₁ ≫ w₀)).obj ω₂.1.1),
      h₁ ≫ (S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2 =
        h₂ ≫ (S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2 →
      GSec.mk (⟨m₁, e₁ ≫ b₀, Z, rfl,
        ((((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.map h₁.op) (τ ω₁)⟩ :
        GRep S ℱ (S.ιObj m₁ Z)) =
      GSec.mk (⟨m₁, e₁ ≫ b₀, Z, rfl,
        ((((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.map h₂.op) (τ ω₂)⟩ :
        GRep S ℱ (S.ιObj m₁ Z)) := by
    intro ω₁ ω₂ Z h₁ h₂ hsq
    have hcomp := hx ω₁ ω₂ (S.ιObj m₁ Z)
      ((S.stageCoconeFunctor m₁).map h₁ ≫ eqToHom (S.ιObj_lower (e₁ ≫ w₀) ω₁.1.1))
      ((S.stageCoconeFunctor m₁).map h₂ ≫ eqToHom (S.ιObj_lower (e₁ ≫ w₀) ω₂.1.1))
      (cocone_lowered_square (e₁ ≫ w₀) ω₁.1.2 ω₂.1.2 h₁ h₂ hsq)
    rw [← hx' ω₁, ← hx' ω₂] at hcomp
    exact (gres_lowered_cocone_mk ℱ (e₁ ≫ w₀) h₁ (e₁ ≫ b₀) (τ ω₁)).symm.trans
      (hcomp.trans (gres_lowered_cocone_mk ℱ (e₁ ≫ w₀) h₂ (e₁ ≫ b₀) (τ ω₂)))
  -- the merged covering family at the common stage
  have hRm : (R.map (S.stageFunctor (e₁ ≫ w₀))) ∈ S.stageCov m₁
      ((S.stageFunctor (e₁ ≫ w₀)).obj X) :=
    (S.stageFunctor_isContinuousSiteFunctor (e₁ ≫ w₀)).toLeComap _ hR
  have hPB : ∀ ω₁ ω₂ : R.uncurry, HasPullback
      ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2)
      ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2) := by
    intro ω₁ ω₂
    haveI := Precoverage.hasPullbacks_of_mem
      ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2) hRm
    exact Presieve.hasPullback _ (Presieve.map.of ω₁.2)
  -- per-pair single-arrow agreement at the chosen pullbacks
  have hpair : ∀ pq : R.uncurry × R.uncurry, ∃ (n : S.I) (epr : n ⟶ m₁),
      haveI := hPB pq.1 pq.2
      ((stageRestriction ℱ (e₁ ≫ b₀) epr).1.app
        (op (pullback ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2))))
        (((((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.map
          (pullback.fst _ _).op) (τ pq.1)) =
      ((stageRestriction ℱ (e₁ ≫ b₀) epr).1.app
        (op (pullback ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2))))
        (((((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.map
          (pullback.snd _ _).op) (τ pq.2)) := by
    intro pq
    haveI := hPB pq.1 pq.2
    exact grel_extract_lowering (GSec.mk_eq_mk.1
      (hclass pq.1 pq.2 (pullback.fst _ _) (pullback.snd _ _) pullback.condition))
  choose npr epr hepr using hpair
  -- merge the pair stages
  obtain ⟨m₂, ε, vp, hvp⟩ := IsCofiltered.wideCospan (i := m₁) (j := npr) epr
  -- the final-stage sections
  have hWε : ∀ ω : R.uncurry,
      (S.stageFunctor ε).obj ((S.stageFunctor (e₁ ≫ w₀)).obj ω.1.1) =
        (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj ω.1.1 := fun ω =>
    S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω.1.1
  obtain ⟨τ', hτ'⟩ : ∃ τ' : ∀ ω : R.uncurry,
      (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.obj
        (op ((S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj ω.1.1)),
      ∀ ω, τ' ω = eqToHom (gsec_type_congr ℱ rfl (hWε ω))
        (((⟨m₁, e₁ ≫ b₀, (S.stageFunctor (e₁ ≫ w₀)).obj ω.1.1,
          S.ιObj_lower (e₁ ≫ w₀) ω.1.1, τ ω⟩ : GRep S ℱ (S.ιObj i ω.1.1)).lower ℱ ε).s) :=
    ⟨_, fun ω => rfl⟩
  have hx'' : ∀ ω : R.uncurry, GSec.mk (⟨m₂, ε ≫ e₁ ≫ b₀,
      (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj ω.1.1,
      S.ιObj_lower (ε ≫ e₁ ≫ w₀) ω.1.1, τ' ω⟩ : GRep S ℱ (S.ιObj i ω.1.1)) = x ω := by
    intro ω
    rw [hτ' ω]
    refine Eq.trans (_root_.Quotient.sound (grel_trans
      (grel_of_components rfl (hWε ω).symm
        (eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ rfl (hWε ω))
          (gsec_type_congr ℱ rfl (hWε ω).symm) rfl _))
      (grel_symm (grel_lower (⟨m₁, e₁ ≫ b₀, (S.stageFunctor (e₁ ≫ w₀)).obj ω.1.1,
        S.ιObj_lower (e₁ ≫ w₀) ω.1.1, τ ω⟩ : GRep S ℱ (S.ιObj i ω.1.1)) ε)))) (hx' ω)
  -- class-level compatibility at the final stage
  have hclass₂ : ∀ (ω₁ ω₂ : R.uncurry) {Z : S.stage m₂}
      (h₁ : Z ⟶ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj ω₁.1.1)
      (h₂ : Z ⟶ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj ω₂.1.1),
      h₁ ≫ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).map ω₁.1.2 =
        h₂ ≫ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).map ω₂.1.2 →
      GSec.mk (⟨m₂, ε ≫ e₁ ≫ b₀, Z, rfl,
        ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map h₁.op) (τ' ω₁)⟩ :
        GRep S ℱ (S.ιObj m₂ Z)) =
      GSec.mk (⟨m₂, ε ≫ e₁ ≫ b₀, Z, rfl,
        ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map h₂.op) (τ' ω₂)⟩ :
        GRep S ℱ (S.ιObj m₂ Z)) := by
    intro ω₁ ω₂ Z h₁ h₂ hsq
    have hcomp := hx ω₁ ω₂ (S.ιObj m₂ Z)
      ((S.stageCoconeFunctor m₂).map h₁ ≫ eqToHom (S.ιObj_lower (ε ≫ e₁ ≫ w₀) ω₁.1.1))
      ((S.stageCoconeFunctor m₂).map h₂ ≫ eqToHom (S.ιObj_lower (ε ≫ e₁ ≫ w₀) ω₂.1.1))
      (cocone_lowered_square (ε ≫ e₁ ≫ w₀) ω₁.1.2 ω₂.1.2 h₁ h₂ hsq)
    rw [← hx'' ω₁, ← hx'' ω₂] at hcomp
    exact (gres_lowered_cocone_mk ℱ (ε ≫ e₁ ≫ w₀) h₁ (ε ≫ e₁ ≫ b₀) (τ' ω₁)).symm.trans
      (hcomp.trans (gres_lowered_cocone_mk ℱ (ε ≫ e₁ ≫ w₀) h₂ (ε ≫ e₁ ≫ b₀) (τ' ω₂)))
  -- the pair conditions transported to the final stage
  have hμ : ∀ pq : R.uncurry × R.uncurry,
      haveI := hPB pq.1 pq.2
      (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.fst ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2)) ≫ eqToHom (hWε pq.1)).op (τ' pq.1) =
      (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.snd ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2)) ≫ eqToHom (hWε pq.2)).op (τ' pq.2) := by
    intro pq
    haveI := hPB pq.1 pq.2
    -- the two hclass-shaped representatives at the chosen pullback
    -- single-arrow agreement at ε via the merged pair lowerings
    have c1 := (⟨m₁, e₁ ≫ b₀, pullback ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
        ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2), rfl,
        (((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.map
          (pullback.fst _ _).op (τ pq.1)⟩ :
        GRep S ℱ (S.ιObj m₁ _)).lower_arrow_congr (hvp pq).symm
      (gsec_type_congr ℱ (congrArg (fun c : m₂ ⟶ m₁ => c ≫ e₁ ≫ b₀) (hvp pq).symm)
        (congrArg (fun c : m₂ ⟶ m₁ => (S.stageFunctor c).obj _) (hvp pq).symm))
    have c2 := cast_step_symm
      ((⟨m₁, e₁ ≫ b₀, pullback ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
        ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2), rfl,
        (((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.map
          (pullback.fst _ _).op (τ pq.1)⟩ :
        GRep S ℱ (S.ιObj m₁ _)).lower_lower (epr pq) (vp pq)
        (Category.assoc (vp pq) (epr pq) (e₁ ≫ b₀)).symm
        (S.stageFunctor_obj_comp (epr pq) (vp pq) _))
    have c3 := congrArg (fun z => ((stageRestriction ℱ (epr pq ≫ e₁ ≫ b₀) (vp pq)).1.app
      (op ((S.stageFunctor (epr pq)).obj (pullback
        ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
        ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2))))) z) (hepr pq)
    have c4 := (⟨m₁, e₁ ≫ b₀, pullback ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
        ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2), rfl,
        (((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.map
          (pullback.snd _ _).op (τ pq.2)⟩ :
        GRep S ℱ (S.ιObj m₁ _)).lower_lower (epr pq) (vp pq)
        (Category.assoc (vp pq) (epr pq) (e₁ ≫ b₀)).symm
        (S.stageFunctor_obj_comp (epr pq) (vp pq) _)
    have c5 := (⟨m₁, e₁ ≫ b₀, pullback ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
        ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2), rfl,
        (((S.stageFunctor (e₁ ≫ b₀)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology m₁)).obj ℱ).obj.map
          (pullback.snd _ _).op (τ pq.2)⟩ :
        GRep S ℱ (S.ιObj m₁ _)).lower_arrow_congr (hvp pq)
      (gsec_type_congr ℱ (congrArg (fun c : m₂ ⟶ m₁ => c ≫ e₁ ≫ b₀) (hvp pq))
        (congrArg (fun c : m₂ ⟶ m₁ => (S.stageFunctor c).obj _) (hvp pq)))
    have hε := cast_step_fold' c1 (cast_step_fold' (c2.trans c3) (cast_step_fold' c4 c5))
    -- naturality bridges to the final-stage mapped sections
    have hnat₁ := congrFun ((stageRestriction ℱ (e₁ ≫ b₀) ε).1.naturality
      (pullback.fst ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
        ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2)).op) (τ pq.1)
    have hnat₂ := congrFun ((stageRestriction ℱ (e₁ ≫ b₀) ε).1.naturality
      (pullback.snd ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
        ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2)).op) (τ pq.2)
    -- split the conjugated maps and close
    have hsplit₁ : (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.fst ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2)) ≫ eqToHom (hWε pq.1)).op (τ' pq.1) =
        (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.fst _ _)).op
        ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        (eqToHom (hWε pq.1)).op (τ' pq.1)) := by
      rw [op_comp, FunctorToTypes.map_comp_apply]
    have hcast₁ := presheaf_map_eqToHom_op_eval
      ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj)
      (hWε pq.1) (gsec_type_congr ℱ rfl (hWε pq.1).symm) (τ' pq.1)
    have hsplit₂ : (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.snd ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2)) ≫ eqToHom (hWε pq.2)).op (τ' pq.2) =
        (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.snd _ _)).op
        ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        (eqToHom (hWε pq.2)).op (τ' pq.2)) := by
      rw [op_comp, FunctorToTypes.map_comp_apply]
    have hcast₂ := presheaf_map_eqToHom_op_eval
      ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj)
      (hWε pq.2) (gsec_type_congr ℱ rfl (hWε pq.2).symm) (τ' pq.2)
    have hτc₁ : eqToHom (gsec_type_congr ℱ rfl (hWε pq.1).symm) (τ' pq.1) =
        ((⟨m₁, e₁ ≫ b₀, (S.stageFunctor (e₁ ≫ w₀)).obj pq.1.1.1,
          S.ιObj_lower (e₁ ≫ w₀) pq.1.1.1, τ pq.1⟩ :
          GRep S ℱ (S.ιObj i pq.1.1.1)).lower ℱ ε).s := by
      rw [hτ' pq.1]
      exact eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ rfl (hWε pq.1))
        (gsec_type_congr ℱ rfl (hWε pq.1).symm) rfl _
    have hτc₂ : eqToHom (gsec_type_congr ℱ rfl (hWε pq.2).symm) (τ' pq.2) =
        ((⟨m₁, e₁ ≫ b₀, (S.stageFunctor (e₁ ≫ w₀)).obj pq.2.1.1,
          S.ιObj_lower (e₁ ≫ w₀) pq.2.1.1, τ pq.2⟩ :
          GRep S ℱ (S.ιObj i pq.2.1.1)).lower ℱ ε).s := by
      rw [hτ' pq.2]
      exact eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ rfl (hWε pq.2))
        (gsec_type_congr ℱ rfl (hWε pq.2).symm) rfl _
    have side₁ := hsplit₁.trans ((congrArg (fun z =>
      (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.fst ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2))).op z)
        (hcast₁.trans hτc₁)).trans hnat₁.symm)
    have side₂ := hsplit₂.trans ((congrArg (fun z =>
      (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.snd ((S.stageFunctor (e₁ ≫ w₀)).map pq.1.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map pq.2.1.2))).op z)
        (hcast₂.trans hτc₂)).trans hnat₂.symm)
    exact side₁.trans (hε.trans side₂.symm)
  -- full square-compatibility of the final-stage sections
  have hcompat₂ : ∀ (ω₁ ω₂ : R.uncurry) {Z : S.stage m₂}
      (h₁ : Z ⟶ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj ω₁.1.1)
      (h₂ : Z ⟶ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj ω₂.1.1),
      h₁ ≫ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).map ω₁.1.2 =
        h₂ ≫ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).map ω₂.1.2 →
      (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map h₁.op (τ' ω₁) =
      (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map h₂.op (τ' ω₂) := by
    intro ω₁ ω₂ Z h₁ h₂ hsq
    haveI := hPB ω₁ ω₂
    haveI : PreservesLimit (cospan ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2)
        ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) (S.stageFunctor ε) :=
      (S.stageFunctor_isContinuousSiteFunctor ε).preservesPullback hRm
        (Presieve.map.of ω₂.2) _
    have l := isLimitOfHasPullbackOfPreservesLimit (S.stageFunctor ε)
      ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2) ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)
    have key₂ : ∀ {Y : S.stage i} (π : Y ⟶ X)
        (hh : Z ⟶ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj Y),
        (hh ≫ eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε Y).symm) ≫
          (S.stageFunctor ε).map ((S.stageFunctor (e₁ ≫ w₀)).map π) =
        (hh ≫ (S.stageFunctor (ε ≫ e₁ ≫ w₀)).map π) ≫
          eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε X).symm := by
      intro Y π hh
      rw [S.stageFunctor_map_map (e₁ ≫ w₀) ε π]
      simp only [Category.assoc]
      congr 1
      exact eqToHom_symm_comp_cancel (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε Y) _
    have hcomm : (h₁ ≫ eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω₁.1.1).symm) ≫
        (S.stageFunctor ε).map ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2) =
        (h₂ ≫ eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω₂.1.1).symm) ≫
        (S.stageFunctor ε).map ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2) := by
      exact (key₂ ω₁.1.2 h₁).trans ((congrArg (fun t => t ≫
        eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε X).symm) hsq).trans
        (key₂ ω₂.1.2 h₂).symm)
    obtain ⟨lam, hlam₁, hlam₂⟩ := PullbackCone.IsLimit.lift' l
      (h₁ ≫ eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω₁.1.1).symm)
      (h₂ ≫ eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω₂.1.1).symm) hcomm
    have hlam₁' : lam ≫ (S.stageFunctor ε).map (pullback.fst
        ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2) ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) =
        h₁ ≫ eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω₁.1.1).symm := hlam₁
    have hlam₂' : lam ≫ (S.stageFunctor ε).map (pullback.snd
        ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2) ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) =
        h₂ ≫ eqToHom (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω₂.1.1).symm := hlam₂
    have hfac₁ : lam ≫ ((S.stageFunctor ε).map (pullback.fst
        ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2) ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) ≫
        eqToHom (hWε ω₁)) = h₁ :=
      (Category.assoc lam _ _).symm.trans
        ((congrArg (fun t => t ≫ eqToHom (hWε ω₁)) hlam₁').trans
          ((Category.assoc h₁ _ _).trans
            (comp_eqToHom_symm_cancel (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω₁.1.1) h₁)))
    have hfac₂ : lam ≫ ((S.stageFunctor ε).map (pullback.snd
        ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2) ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) ≫
        eqToHom (hWε ω₂)) = h₂ :=
      (Category.assoc lam _ _).symm.trans
        ((congrArg (fun t => t ≫ eqToHom (hWε ω₂)) hlam₂').trans
          ((Category.assoc h₂ _ _).trans
            (comp_eqToHom_symm_cancel (S.stageFunctor_obj_comp (e₁ ≫ w₀) ε ω₂.1.1) h₂)))
    have hsplit₁' : (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((lam ≫ ((S.stageFunctor ε).map (pullback.fst
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) ≫ eqToHom (hWε ω₁)))).op (τ' ω₁) =
        (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map lam.op
        ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.fst
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) ≫ eqToHom (hWε ω₁)).op (τ' ω₁)) :=
      (congrArg (fun ar => (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map ar (τ' ω₁))
        (op_comp (f := lam) (g := (S.stageFunctor ε).map (pullback.fst
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) ≫ eqToHom (hWε ω₁)))).trans
      (FunctorToTypes.map_comp_apply _ _ _ _)
    have hsplit₂' : (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((lam ≫ ((S.stageFunctor ε).map (pullback.snd
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) ≫ eqToHom (hWε ω₂)))).op (τ' ω₂) =
        (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map lam.op
        ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map
        ((S.stageFunctor ε).map (pullback.snd
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) ≫ eqToHom (hWε ω₂)).op (τ' ω₂)) :=
      (congrArg (fun ar => (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map ar (τ' ω₂))
        (op_comp (f := lam) (g := (S.stageFunctor ε).map (pullback.snd
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₁.1.2)
          ((S.stageFunctor (e₁ ≫ w₀)).map ω₂.1.2)) ≫ eqToHom (hWε ω₂)))).trans
      (FunctorToTypes.map_comp_apply _ _ _ _)
    refine (congrArg (fun μ => (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map μ.op (τ' ω₁)) hfac₁.symm).trans
      ((hsplit₁'.trans ?_).trans ((congrArg (fun μ =>
        (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map μ.op (τ' ω₂))
        hfac₂.symm).trans hsplit₂').symm)
    exact congrArg (fun z => (((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ).obj.map lam.op z) (hμ (ω₁, ω₂))
  -- the stage sheaf condition at the final cover
  have hRm₂ : (R.map (S.stageFunctor (ε ≫ e₁ ≫ w₀))) ∈ S.stageCov m₂
      ((S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj X) :=
    (S.stageFunctor_isContinuousSiteFunctor (ε ≫ e₁ ≫ w₀)).toLeComap _ hR
  have hstage := (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderPullbackArrows
    (S.stageCov m₂) _).1 ((isSheaf_iff_isSheaf_of_type _ _).1
    ((((S.stageFunctor (ε ≫ e₁ ≫ b₀)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology m₂)).obj ℱ)).cond) _ hRm₂
  rw [presieve_eq_ofArrows_uncurry R, presieve_map_ofArrows] at hstage
  obtain ⟨σglue, hglue, huniq⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hstage τ'
    (fun ω₁ ω₂ Z h₁ h₂ hsq => hcompat₂ ω₁ ω₂ h₁ h₂ hsq)
  have ham : ∀ ω : R.uncurry, (auxiliaryPresheaf ℱ).map
      ((S.stageCoconeFunctor i).map ω.1.2).op
      (GSec.mk (⟨m₂, ε ≫ e₁ ≫ b₀, (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj X,
        S.ιObj_lower (ε ≫ e₁ ≫ w₀) X, σglue⟩ : GRep S ℱ (S.ιObj i X))) = x ω := by
    intro ω
    exact (gres_stage_lowered_mk ℱ (ε ≫ e₁ ≫ w₀) ω.1.2 (ε ≫ e₁ ≫ b₀) σglue).trans
      ((congrArg (fun z => GSec.mk (⟨m₂, ε ≫ e₁ ≫ b₀,
        (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj ω.1.1,
        S.ιObj_lower (ε ≫ e₁ ≫ w₀) ω.1.1, z⟩ : GRep S ℱ (S.ιObj i ω.1.1)))
        (hglue ω)).trans (hx'' ω))
  refine ⟨GSec.mk (⟨m₂, ε ≫ e₁ ≫ b₀, (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj X,
    S.ιObj_lower (ε ≫ e₁ ≫ w₀) X, σglue⟩ : GRep S ℱ (S.ιObj i X)), ham, ?_⟩
  intro y hy
  -- present the competitor at a lowering of `X` and merge with the glue stage
  obtain ⟨ky, ey, ay, ζ, hζ⟩ := GSec.exists_lowered_rep y
  obtain ⟨n₀, py, pt, hpt⟩ := S.exists_span ey (ε ≫ e₁ ≫ w₀)
  obtain ⟨n₁, eq₁, heq₁⟩ : ∃ (n₁ : S.I) (eq₁ : n₁ ⟶ n₀),
      eq₁ ≫ (py ≫ ay) = eq₁ ≫ (pt ≫ (ε ≫ e₁ ≫ b₀)) :=
    ⟨_, IsCofiltered.eqHom _ _, IsCofiltered.eq_condition _ _⟩
  have hCt : (eq₁ ≫ pt) ≫ (ε ≫ e₁ ≫ b₀) = (eq₁ ≫ py) ≫ ay :=
    (Category.assoc _ _ _).trans (heq₁.symm.trans (Category.assoc _ _ _).symm)
  have hDt : (eq₁ ≫ pt) ≫ (ε ≫ e₁ ≫ w₀) = (eq₁ ≫ py) ≫ ey :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => eq₁ ≫ t) hpt.symm).trans
      (Category.assoc _ _ _).symm)
  have hwY : (S.stageFunctor (eq₁ ≫ py)).obj ((S.stageFunctor ey).obj X) =
      (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X :=
    S.stageFunctor_obj_comp ey (eq₁ ≫ py) X
  have hwT : (S.stageFunctor (eq₁ ≫ pt)).obj
      ((S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj X) =
      (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X :=
    (S.stageFunctor_obj_comp (ε ≫ e₁ ≫ w₀) (eq₁ ≫ pt) X).trans
      (congrArg (fun c : n₁ ⟶ i => (S.stageFunctor c).obj X) hDt)
  -- the two competitor sections at the common stage
  obtain ⟨ζ', hζ'⟩ : ∃ ζ' : (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.obj
      (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X)),
      ζ' = eqToHom (gsec_type_congr ℱ rfl hwY)
        (((⟨ky, ay, (S.stageFunctor ey).obj X, S.ιObj_lower ey X, ζ⟩ :
          GRep S ℱ (S.ιObj i X)).lower ℱ (eq₁ ≫ py)).s) := ⟨_, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.obj
      (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X)),
      σ' = eqToHom (gsec_type_congr ℱ hCt hwT)
        (((⟨m₂, ε ≫ e₁ ≫ b₀, (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj X,
          S.ιObj_lower (ε ≫ e₁ ≫ w₀) X, σglue⟩ :
          GRep S ℱ (S.ιObj i X)).lower ℱ (eq₁ ≫ pt)).s) := ⟨_, rfl⟩
  have hy' : GSec.mk (⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X,
      S.ιObj_lower ((eq₁ ≫ py) ≫ ey) X, ζ'⟩ : GRep S ℱ (S.ιObj i X)) = y := by
    rw [hζ']
    refine Eq.trans (_root_.Quotient.sound (grel_trans
      (grel_of_components rfl hwY.symm
        (eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ rfl hwY)
          (gsec_type_congr ℱ rfl hwY.symm) rfl _))
      (grel_symm (grel_lower (⟨ky, ay, (S.stageFunctor ey).obj X,
        S.ιObj_lower ey X, ζ⟩ : GRep S ℱ (S.ιObj i X)) (eq₁ ≫ py))))) hζ
  have ht' : GSec.mk (⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X,
      S.ιObj_lower ((eq₁ ≫ py) ≫ ey) X, σ'⟩ : GRep S ℱ (S.ιObj i X)) =
      GSec.mk (⟨m₂, ε ≫ e₁ ≫ b₀, (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj X,
        S.ιObj_lower (ε ≫ e₁ ≫ w₀) X, σglue⟩ : GRep S ℱ (S.ιObj i X)) := by
    rw [hσ']
    exact _root_.Quotient.sound (grel_trans
      (grel_of_components hCt.symm hwT.symm
        (eqToHom_apply_collapse₂₁_aux (gsec_type_congr ℱ hCt hwT)
          (gsec_type_congr ℱ hCt.symm hwT.symm) rfl _))
      (grel_symm (grel_lower (⟨m₂, ε ≫ e₁ ≫ b₀,
        (S.stageFunctor (ε ≫ e₁ ≫ w₀)).obj X,
        S.ιObj_lower (ε ≫ e₁ ≫ w₀) X, σglue⟩ : GRep S ℱ (S.ιObj i X)) (eq₁ ≫ pt))))
  -- the restrictions of the two sections agree on the cover after a single common lowering
  have hsep : ∀ ω : R.uncurry, ∃ (n' : S.I) (e' : n' ⟶ n₁),
      ((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) e').1.app
        (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1)))
        ((((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op ζ') =
      ((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) e').1.app
        (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1)))
        ((((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op σ') := by
    intro ω
    refine grel_extract_lowering (V := S.ιObj i ω.1.1)
      (h₁ := S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1)
      (h₂ := S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1) (GSec.mk_eq_mk.1 ?_)
    exact (gres_stage_lowered_mk ℱ ((eq₁ ≫ py) ≫ ey) ω.1.2 ((eq₁ ≫ py) ≫ ay) ζ').symm.trans
      (((congrArg (fun z => (auxiliaryPresheaf ℱ).map
        ((S.stageCoconeFunctor i).map ω.1.2).op z) hy').trans
        ((hy ω).trans ((ham ω).symm.trans (congrArg (fun z => (auxiliaryPresheaf ℱ).map
          ((S.stageCoconeFunctor i).map ω.1.2).op z) ht'.symm)))).trans
      (gres_stage_lowered_mk ℱ ((eq₁ ≫ py) ≫ ey) ω.1.2 ((eq₁ ≫ py) ≫ ay) σ'))
  choose nδ eδ heδ using hsep
  obtain ⟨n₂, δ, vδ, hvδ⟩ := IsCofiltered.wideCospan (i := n₁) (j := nδ) eδ
  -- transport the per-member agreements to the common lowering
  have hδeq : ∀ ω : R.uncurry,
      ((⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1,
        S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1,
        (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op ζ'⟩ :
        GRep S ℱ (S.ιObj i ω.1.1)).lower ℱ δ).s =
      ((⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1,
        S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1,
        (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op σ'⟩ :
        GRep S ℱ (S.ιObj i ω.1.1)).lower ℱ δ).s := by
    intro ω
    have c1 := (⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1,
        S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1,
        (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op ζ'⟩ :
        GRep S ℱ (S.ιObj i ω.1.1)).lower_arrow_congr (hvδ ω).symm
      (gsec_type_congr ℱ (congrArg (fun c : n₂ ⟶ n₁ => c ≫ (eq₁ ≫ py) ≫ ay) (hvδ ω).symm)
        (congrArg (fun c : n₂ ⟶ n₁ => (S.stageFunctor c).obj
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1)) (hvδ ω).symm))
    have c2 := cast_step_symm
      ((⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1,
        S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1,
        (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op ζ'⟩ :
        GRep S ℱ (S.ιObj i ω.1.1)).lower_lower (eδ ω) (vδ ω)
        (Category.assoc (vδ ω) (eδ ω) ((eq₁ ≫ py) ≫ ay)).symm
        (S.stageFunctor_obj_comp (eδ ω) (vδ ω) _))
    have c3 := congrArg (fun z => ((stageRestriction ℱ (eδ ω ≫ (eq₁ ≫ py) ≫ ay)
      (vδ ω)).1.app (op ((S.stageFunctor (eδ ω)).obj
        ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1)))) z) (heδ ω)
    have c4 := (⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1,
        S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1,
        (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op σ'⟩ :
        GRep S ℱ (S.ιObj i ω.1.1)).lower_lower (eδ ω) (vδ ω)
        (Category.assoc (vδ ω) (eδ ω) ((eq₁ ≫ py) ≫ ay)).symm
        (S.stageFunctor_obj_comp (eδ ω) (vδ ω) _)
    have c5 := (⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1,
        S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1,
        (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
          (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op σ'⟩ :
        GRep S ℱ (S.ιObj i ω.1.1)).lower_arrow_congr (hvδ ω)
      (gsec_type_congr ℱ (congrArg (fun c : n₂ ⟶ n₁ => c ≫ (eq₁ ≫ py) ≫ ay) (hvδ ω))
        (congrArg (fun c : n₂ ⟶ n₁ => (S.stageFunctor c).obj
          ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1)) (hvδ ω)))
    exact cast_step_fold' c1 (cast_step_fold' (c2.trans c3) (cast_step_fold' c4 c5))
  -- separatedness at the common lowering: the two sections agree
  have hRn₂ : ((R.map (S.stageFunctor ((eq₁ ≫ py) ≫ ey))).map (S.stageFunctor δ)) ∈
      S.stageCov n₂ ((S.stageFunctor δ).obj
        ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X)) :=
    (S.stageFunctor_isContinuousSiteFunctor δ).toLeComap _
      ((S.stageFunctor_isContinuousSiteFunctor ((eq₁ ≫ py) ≫ ey)).toLeComap _ hR)
  have hstage₂ := (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderPullbackArrows
    (S.stageCov n₂) _).1 ((isSheaf_iff_isSheaf_of_type _ _).1
    ((((S.stageFunctor (δ ≫ (eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n₂)).obj ℱ)).cond) _ hRn₂
  rw [presieve_eq_ofArrows_uncurry R, presieve_map_ofArrows, presieve_map_ofArrows]
    at hstage₂
  have hnatζ : ∀ ω : R.uncurry, ((⟨n₁, (eq₁ ≫ py) ≫ ay,
      (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1,
      S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1,
      (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
        ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op ζ'⟩ :
      GRep S ℱ (S.ιObj i ω.1.1)).lower ℱ δ).s =
      (((S.stageFunctor (δ ≫ (eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n₂)).obj ℱ).obj.map
        ((S.stageFunctor δ).map ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2)).op
        (((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) δ).1.app
          (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X))) ζ') := fun ω =>
    congrFun ((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) δ).1.naturality
      ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op) ζ'
  have hnatσ : ∀ ω : R.uncurry, ((⟨n₁, (eq₁ ≫ py) ≫ ay,
      (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj ω.1.1,
      S.ιObj_lower ((eq₁ ≫ py) ≫ ey) ω.1.1,
      (((S.stageFunctor ((eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n₁)).obj ℱ).obj.map
        ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op σ'⟩ :
      GRep S ℱ (S.ιObj i ω.1.1)).lower ℱ δ).s =
      (((S.stageFunctor (δ ≫ (eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
        (S.stageTopology i₀) (S.stageTopology n₂)).obj ℱ).obj.map
        ((S.stageFunctor δ).map ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2)).op
        (((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) δ).1.app
          (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X))) σ') := fun ω =>
    congrFun ((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) δ).1.naturality
      ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2).op) σ'
  obtain ⟨g₀, -, hu₀⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hstage₂
    (fun ω => (((S.stageFunctor (δ ≫ (eq₁ ≫ py) ≫ ay)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology n₂)).obj ℱ).obj.map
      ((S.stageFunctor δ).map ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2)).op
      (((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) δ).1.app
        (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X))) ζ'))
    (Presieve.Arrows.toCompatible (((S.stageFunctor (δ ≫ (eq₁ ≫ py) ≫ ay)).sheafPullback
      (Type u) (S.stageTopology i₀) (S.stageTopology n₂)).obj ℱ).obj
      (fun ω : R.uncurry => (S.stageFunctor δ).map
        ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).map ω.1.2))
      (((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) δ).1.app
        (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X))) ζ')).property
  have hfin : ((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) δ).1.app
      (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X))) ζ' =
      ((stageRestriction ℱ ((eq₁ ≫ py) ≫ ay) δ).1.app
      (op ((S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X))) σ' :=
    (hu₀ _ (fun ω => rfl)).trans
      (hu₀ _ (fun ω => ((hnatζ ω).symm.trans ((hδeq ω).trans (hnatσ ω))).symm)).symm
  exact hy'.symm.trans ((_root_.Quotient.sound
    (⟨n₂, δ, δ, rfl, rfl, hfin⟩ :
      grel (⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X,
        S.ιObj_lower ((eq₁ ≫ py) ≫ ey) X, ζ'⟩ : GRep S ℱ (S.ιObj i X))
        ⟨n₁, (eq₁ ≫ py) ≫ ay, (S.stageFunctor ((eq₁ ≫ py) ≫ ey)).obj X,
        S.ιObj_lower ((eq₁ ≫ py) ≫ ey) X, σ'⟩)).trans ht')

variable {S} in
/-- The auxiliary presheaf is a sheaf for the colimit topology. -/
theorem auxiliaryPresheaf_isSheaf {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u)) :
    Presieve.IsSheaf S.colimitTopology (auxiliaryPresheaf ℱ) := by
  rw [show S.colimitTopology = S.colimitSite.toGrothendieck from rfl,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderPullbackArrows]
  rintro V T ⟨i, X, hX, R, hR, rfl⟩
  exact auxiliaryPresheaf_isSheafFor_stageCover ℱ X hX hR

variable {S} in
/-- The auxiliary sheaf `G` on the colimit site. -/
noncomputable def auxiliarySheaf {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u)) :
    Sheaf S.colimitTopology (Type u) :=
  ⟨auxiliaryPresheaf ℱ, (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2
    (auxiliaryPresheaf_isSheaf ℱ)⟩

section UniversalProperty

variable {S} in
/-- The identity-stage sheaf pullback is isomorphic to the identity. -/
noncomputable def stagePullbackIdIso (i₀ : S.I) :
    (S.stageFunctor (𝟙 i₀)).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology i₀) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso
    ((S.stageFunctor (𝟙 i₀)).sheafAdjunctionContinuous (Type u)
      (S.stageTopology i₀) (S.stageTopology i₀))
    (Functor.sheafPushforwardContinuousId'
      (eqToIso (CofilteredSiteDiagram.stageFunctor_id_eq S i₀))
      (Type u) (S.stageTopology i₀))

variable {S} in
/-- The unit-side structure map of the auxiliary sheaf: a section of `ℱ` defines an auxiliary
section class through the identity-stage representative. -/
noncomputable def auxiliaryUnit {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u)) :
    ℱ ⟶ ((S.stageCoconeFunctor i₀).sheafPushforwardContinuous (Type u)
      (S.stageTopology i₀) S.colimitTopology).obj (auxiliarySheaf ℱ) where
  hom :=
    { app := fun W s => GSec.mk (⟨i₀, 𝟙 i₀, W.unop, rfl,
        (((stagePullbackIdIso i₀).inv.app ℱ).1.app W) s⟩ :
        GRep S ℱ (S.ιObj i₀ W.unop))
      naturality := by
        intro W W' g
        funext s
        refine Eq.trans ?_ (gres_stage_mk ℱ g.unop (𝟙 i₀)
          ((((stagePullbackIdIso i₀).inv.app ℱ).1.app W) s)).symm
        exact congrArg (fun z => GSec.mk (⟨i₀, 𝟙 i₀, W'.unop, rfl, z⟩ :
          GRep S ℱ (S.ιObj i₀ W'.unop)))
          (congrFun (((stagePullbackIdIso i₀).inv.app ℱ).1.naturality g) s) }

variable {S} in
/-- The stage family of structure maps: a stage pullback section defines an auxiliary section
class through the tautological representative. -/
noncomputable def auxiliaryStageMap {i₀ : S.I} (ℱ : Sheaf (S.stageTopology i₀) (Type u))
    {j : S.I} (a : j ⟶ i₀) :
    ((S.stageFunctor a).sheafPullback (Type u)
      (S.stageTopology i₀) (S.stageTopology j)).obj ℱ ⟶
    ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
      (S.stageTopology j) S.colimitTopology).obj (auxiliarySheaf ℱ) where
  hom :=
    { app := fun W s => GSec.mk (⟨j, a, W.unop, rfl, s⟩ : GRep S ℱ (S.ιObj j W.unop))
      naturality := by
        intro W W' g
        funext s
        exact (gres_stage_mk ℱ g.unop a s).symm }

end UniversalProperty

end SheafProperty

end AuxiliarySections

end CofilteredSiteDiagram
