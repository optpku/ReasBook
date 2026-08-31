module

public import stacks_project.Chap07.Lemma_7_26_4.HomPresheafTransport

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- The 2-cell `eqToHom` between parallel `Cat`-morphisms evaluates objectwise to the canonical
transport. -/
theorem cat_hom₂_eqToHom_app.{v₁, u₁} {A B : Cat.{v₁, u₁}} {f g : A ⟶ B}
    (h : f = g) (X : A) :
    (eqToHom h).toNatTrans.app X = eqToHom (congrArg (fun k ↦ k.toFunctor.obj X) h) := by
  cases h
  rfl

/-- Casting a morphism along Hom-type equalities induced by object equalities is conjugation by
the canonical transports. -/
theorem cast_hom_eq_conj {𝒜 : Type*} [Category 𝒜] {A B A' B' : 𝒜}
    (hA : A = A') (hB : B = B')
    (h : (A ⟶ B) = (A' ⟶ B')) (f : A ⟶ B) :
    cast h f = eqToHom hA.symm ≫ f ≫ eqToHom hB := by
  cases hA
  cases hB
  exact ((Category.id_comp _).trans (Category.comp_id f)).symm

/-- The canonical conjugation chain by identity-collapse cells and transports equals the
type-level cast; all bicategorical content enters through the hypotheses. -/
theorem conj_chain_eq_cast {𝒜 : Type*} [Category 𝒜]
    {Pm P0 Pq Qq Qm Q0 : 𝒜}
    (sInv : Pm ⟶ P0) (tHom : Q0 ⟶ Qm)
    (Aapp : P0 ⟶ Pq) (Bapp : Qq ⟶ Q0) (z : Pq ⟶ Qq)
    (a1 : P0 ⟶ Pm) (a2 : Pm ⟶ Pm) (a3 : Pm ⟶ Pq)
    (b2 : Qq ⟶ Qm) (b3 : Qm ⟶ Qm) (b4 : Qm ⟶ Q0)
    (hPa : Pm = Pq) (hQb : Qq = Qm)
    (hA : Aapp = (a1 ≫ a2 ≫ a3) ≫ 𝟙 Pq)
    (hB : Bapp = 𝟙 Qq ≫ b2 ≫ b3 ≫ b4)
    (ha2 : a2 = 𝟙 Pm) (hb3 : b3 = 𝟙 Qm)
    (ha3 : a3 = eqToHom hPa) (hb2 : b2 = eqToHom hQb)
    (hsa : sInv ≫ a1 = 𝟙 Pm) (hbt : b4 ≫ tHom = 𝟙 Qm)
    (hcast : (Pq ⟶ Qq) = (Pm ⟶ Qm)) :
    sInv ≫ ((Aapp ≫ z) ≫ Bapp) ≫ tHom = cast hcast z := by
  subst hA hB ha2 hb3 ha3 hb2
  rw [cast_hom_eq_conj hPa.symm hQb hcast z]
  subst hPa
  subst hQb
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc]
  calc
    sInv ≫ a1 ≫ z ≫ b4 ≫ tHom
        = (sInv ≫ a1) ≫ z ≫ b4 ≫ tHom := (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ z ≫ b4 ≫ tHom := congrArg (fun k ↦ k ≫ z ≫ b4 ≫ tHom) hsa
    _ = z ≫ b4 ≫ tHom := Category.id_comp _
    _ = z ≫ 𝟙 _ := congrArg (fun k ↦ z ≫ k) hbt
    _ = z := Category.comp_id z

/-- Helper for Lemma 7.26.4: after moving to the literal terminal-source fiber of
`(Over.map T.hom).op ⋙ presheafHom`, the terminal component of `overMapCompPresheafHomIso`
computes to the reverse type cast back to the original source fiber. -/
theorem localized_pseudofunctorOver_terminal_component_apply_cast_eq_raw
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    (z :
      (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T.left))))) :
    (Pseudofunctor.presheafHomObjHomEquiv (F := (J.pseudofunctorOver (Type w)))
        (S := T.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := (J.pseudofunctorOver (Type w))) (M := M) (N := N) T.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T.left)))) z) =
      cast
        (localized_pseudofunctorOver_terminal_source_type_eq_symm
          (J := J) (U := U) (T := T) M N)
        z := by
  obtain ⟨Tl, Tr, Th⟩ := T
  simp [Pseudofunctor.overMapCompPresheafHomIso, Pseudofunctor.presheafHomObjHomEquiv,
    Pseudofunctor.presheafHom, Pseudofunctor.mapComp', Pseudofunctor.mapComp_id_right,
    Iso.homCongr, Iso.homFromEquiv, Iso.homToEquiv, Cat.Hom.toNatIso]
  have h₁ : ((J.pseudofunctorOver (Type w)).map Th.op.toLoc) =
      ((J.pseudofunctorOver (Type w)).map (Th.op.toLoc ≫ 𝟙 (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ))) :=
    congrArg (fun k ↦ (J.pseudofunctorOver (Type w)).map k) (Category.comp_id Th.op.toLoc).symm
  have h₂ : ((J.pseudofunctorOver (Type w)).map (Th.op.toLoc ≫ 𝟙 (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ))) =
      ((J.pseudofunctorOver (Type w)).map Th.op.toLoc) := h₁.symm
  exact conj_chain_eq_cast
    (sInv := ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv.toNatTrans.app
      (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj M))
    (tHom := ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).hom.toNatTrans.app
      (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj N))
    (Aapp := ((Bicategory.whiskerLeft ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)
          ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).hom ≫
        (Bicategory.rightUnitor ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)).hom ≫
          eqToHom h₁) ≫
        𝟙 ((J.pseudofunctorOver (Type w)).map (Th.op.toLoc ≫ 𝟙 (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)))).toNatTrans.app M)
    (Bapp := ((𝟙 ((J.pseudofunctorOver (Type w)).map (Th.op.toLoc ≫ 𝟙 (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ))) ≫
        eqToHom h₂ ≫
          (Bicategory.rightUnitor ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)).inv ≫
            Bicategory.whiskerLeft ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)
              ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv).toNatTrans.app N))
    (z := z)
    (a1 := ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).hom.toNatTrans.app
      (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj M))
    (a2 := (Bicategory.rightUnitor ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)).hom.toNatTrans.app M)
    (a3 := (eqToHom h₁).toNatTrans.app M)
    (b2 := (eqToHom h₂).toNatTrans.app N)
    (b3 := (Bicategory.rightUnitor ((J.pseudofunctorOver (Type w)).map Th.op.toLoc)).inv.toNatTrans.app N)
    (b4 := ((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv.toNatTrans.app
      (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj N))
    (hPa := congrArg (fun k ↦ k.toFunctor.obj M) h₁)
    (hQb := congrArg (fun k ↦ k.toFunctor.obj N) h₂)
    (hA := rfl) (hB := rfl)
    (ha2 := rfl) (hb3 := rfl)
    (ha3 := cat_hom₂_eqToHom_app h₁ M) (hb2 := cat_hom₂_eqToHom_app h₂ N)
    (hsa := congrArg
      (fun α ↦ α.toNatTrans.app (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj M))
      (((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv_hom_id))
    (hbt := congrArg
      (fun α ↦ α.toNatTrans.app (((J.pseudofunctorOver (Type w)).map Th.op.toLoc).toFunctor.obj N))
      (((J.pseudofunctorOver (Type w)).mapId (⟨Opposite.op Tl⟩ : LocallyDiscrete Cᵒᵖ)).inv_hom_id))
    (hcast := localized_pseudofunctorOver_terminal_source_type_eq_symm
      (J := J) (U := U) (T := ⟨Tl, Tr, Th⟩) M N)

/-- Helper for Lemma 7.26.4: eliminating the owner-source cast at the terminal object reduces
the terminal component of `overMapCompPresheafHomIso` to the original section. -/
theorem localized_pseudofunctorOver_terminal_component_apply_cast_eq
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    (z : (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T))) :
    (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))
        (S := T.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T.left))))
        (Eq.mp
          (localized_pseudofunctorOver_terminal_source_type_eq
            (J := J) (U := U) (T := T) M N)
          z)) =
      z := by
  -- First compute the terminal component in the literal terminal-source fiber, so the only
  -- remaining cast is the inverse type cast back to the original source section.
  have hraw :=
    localized_pseudofunctorOver_terminal_component_apply_cast_eq_raw
      (J := J) (U := U) (T := T) (M := M) (N := N)
      (Eq.mp
        (localized_pseudofunctorOver_terminal_source_type_eq
          (J := J) (U := U) (T := T) M N)
        z)
  -- The forward and reverse terminal-source casts cancel definitionally after exposing `T`.
  have hcancel :
      cast
          (localized_pseudofunctorOver_terminal_source_type_eq_symm
            (J := J) (U := U) (T := T) M N)
          (Eq.mp
            (localized_pseudofunctorOver_terminal_source_type_eq
              (J := J) (U := U) (T := T) M N)
            z) =
        z := by
    cases T
    simp [Pseudofunctor.presheafHom]
  -- This leaves the original theorem as a short corollary of the raw terminal computation.
  exact hraw.trans hcancel

/-- Helper for Lemma 7.26.4: after rewriting the source-side terminal section into owner
coordinates, the terminal component of `overMapCompPresheafHomIso` is exactly the explicit
owner-side `pullHom` morphism before the final `mapComp'`-to-`mapComp` normalization. -/
theorem localized_pseudofunctorOver_source_terminal_component_eq_iterated_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w)) (S := T₁.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T₁.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T₁.left))))
        (Eq.mp
          (by
            simp [localized_cover_descent_overMap_terminal_obj]
            rfl)
          (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
            (J := J) (U := U) T₁ M N).trans
            ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
              (J := J) (U := U) T₁ M).homCongr
              (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
                (J := J) (U := U) T₁ N)))
            (((J.over U).overMapPullback (Type w) g).map x)))) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)
        g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g) := by
  -- Collapse the terminal round-trip via the proven cast computation; the remaining content is
  -- the sheaf-level comparison between the iterated-slice transport and the owner `pullHom`.
  refine (localized_pseudofunctorOver_terminal_component_apply_cast_eq
    (J := J) (U := U) (T := T₁) (M := M) (N := N)
    (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))).trans ?_
  apply (sheafToPresheaf (J.over T₁.left) (Type w)).map_injective
  have hcore :
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
        T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
            N.obj).hom =
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
            M) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x))) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
            N) :=
    localized_pseudofunctorOver_whisker_transport_core (J := J) (U := U) g M N x
  exact (localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form
      (J := J) (U := U) g M N x).trans
    (hcore.trans
      (localized_pseudofunctorOver_pullHom_underlying_normal_form
        (J := J) (U := U) g M N x).symm)

/-- Helper for Lemma 7.26.4: after expressing the source-side comparison in owner coordinates,
the terminal owner-source section of `overMapCompPresheafHomIso` is exactly the canonical
three-factor owner transport sheaf morphism. -/
theorem localized_pseudofunctorOver_overMapCompPresheafHomIso_terminal_component_eq_owner_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    localized_pseudofunctorOver_source_terminal_transport_hom
      (J := J) (U := U) g M N x =
      localized_pseudofunctorOver_owner_transport_hom
        (J := J) (U := U) g M N x := by
  let y' :
      (((Over.map T₁.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T₁.left)))) :=
    Eq.mp
      (by
        simp [localized_cover_descent_overMap_terminal_obj]
        rfl)
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))
  have hy :
      localized_pseudofunctorOver_presheafHom_obj_equiv_owner_source
          (J := J) (U := U) T₁ M N
          (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x) =
        y' := by
    -- Rewrite the terminal source coordinate using the already-normalized source map.
    exact congrArg
      (fun t =>
        Eq.mp
          (by
            simp [localized_cover_descent_overMap_terminal_obj]
            rfl)
          t)
      (localized_pseudofunctorOver_presheafHom_obj_equiv_source_map
        (J := J) (U := U) g M N x)
  rw [localized_pseudofunctorOver_source_terminal_transport_hom, hy]
  -- Route correction: isolate the source-side terminal cast mismatch first, then reuse the
  -- already-proved target-side normalization from `pullHom` to owner transport.
  exact
    (localized_pseudofunctorOver_source_terminal_component_eq_iterated_transport
      (J := J) (U := U) g M N x).trans
      (localized_pseudofunctorOver_pullHom_eq_owner_transport_hom
        (J := J) (U := U) g M N x)

/-- Helper for Lemma 7.26.4: the reduced source-side transport is obtained by restricting the
terminal owner-source morphism along `Over.homMk X.hom` and then evaluating at `X`. -/
theorem localized_pseudofunctorOver_transport_source_app_eq_terminal_restrict
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
      ((sheafToPresheaf (J.over T₁.left) (Type w)).map
        (localized_pseudofunctorOver_source_terminal_transport_hom
          (J := J) (U := U) g M N x)).app (Opposite.op X) := by
  let y :
      (((Over.map T₁.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T₁.left)))) :=
    localized_pseudofunctorOver_presheafHom_obj_equiv_owner_source
      (J := J) (U := U) T₁ M N
      (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x)
  let y' :
      (((Over.map T₁.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T₁.left)))) :=
    Eq.mp
      (by
        simp [localized_cover_descent_overMap_terminal_obj]
        rfl)
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))
  have hy :
      y = y' := by
    -- The terminal source section is the owner-coordinate form of the normalized source map.
    exact congrArg
      (fun t =>
        Eq.mp
          (by
            simp [localized_cover_descent_overMap_terminal_obj]
            rfl)
          t)
      (localized_pseudofunctorOver_presheafHom_obj_equiv_source_map
        (J := J) (U := U) g M N x)
  -- The terminal round-trip of the normalized source section recovers the chain value itself,
  -- so the terminal transport morphism is literally the iterated-slice comparison value.
  have h1165 :=
    localized_pseudofunctorOver_terminal_component_apply_cast_eq
      (J := J) (U := U) (T := T₁) (M := M) (N := N)
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))
  have hhom :
      localized_pseudofunctorOver_source_terminal_transport_hom
        (J := J) (U := U) g M N x =
      ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x) :=
    (congrArg
      (fun t ↦
        (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))
            (S := T₁.left)).symm
          (((Pseudofunctor.overMapCompPresheafHomIso
            (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T₁.hom).hom.app
              (Opposite.op (Over.mk (𝟙 T₁.left)))) t))
      hy).trans h1165
  exact congrArg
    (fun s ↦ ((sheafToPresheaf (J.over T₁.left) (Type w)).map s).app (Opposite.op X))
    hhom.symm

/-- Helper for Lemma 7.26.4: after expressing the source-side comparison in owner coordinates,
the iterated-slice transport is already the same canonical owner transport used on the target
side. This isolates the source half of the remaining transport/coercion normalization. -/
theorem localized_pseudofunctorOver_transport_source_app_eq_owner_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
      localized_pseudofunctorOver_owner_transport_app (J := J) (U := U) g M N x X := by
  -- Route correction: the main theorem is now reduced to two explicit helper lemmas: first,
  -- rewrite the source-side map as restriction of the terminal owner-source morphism; second,
  -- identify that terminal morphism with the canonical owner transport and evaluate at `X`.
  have hsource :=
    localized_pseudofunctorOver_transport_source_app_eq_terminal_restrict
      (J := J) (U := U) g M N x X
  have hterminal :=
    localized_pseudofunctorOver_overMapCompPresheafHomIso_terminal_component_eq_owner_transport
      (J := J) (U := U) g M N x
  have happ :
      ((sheafToPresheaf (J.over T₁.left) (Type w)).map
        (localized_pseudofunctorOver_source_terminal_transport_hom
          (J := J) (U := U) g M N x)).app (Opposite.op X) =
        localized_pseudofunctorOver_owner_transport_app (J := J) (U := U) g M N x X := by
    -- Evaluate the terminal-component identification at `X`; the right-hand side is the
    -- definition of `localized_pseudofunctorOver_owner_transport_app`.
    simpa [localized_pseudofunctorOver_owner_transport_app] using
      congrArg
        (fun φ =>
          ((sheafToPresheaf (J.over T₁.left) (Type w)).map φ).app (Opposite.op X))
        hterminal
  exact hsource.trans happ

/-- Helper for Lemma 7.26.4: the remaining prestack transport theorem is equivalent to the
reduced presheaf-level comparison obtained by rewriting both sides with the established normal
forms. -/
theorem localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport_app_iff
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    (((Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
          T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
            (Functor.isoWhiskerRight
              (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
              N.obj).hom).app (Opposite.op X)) =
        (((sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.pseudofunctorOver (Type w)).mapComp'
            T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
            (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
              M) ≫
        (sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.overMapPullback (Type w) g.left).map
            (localized_pseudofunctorOver_presheafHom_obj_equiv
              (J := J) (U := U) T₂ M N x))) ≫
        (sheafToPresheaf (J.over T₁.left) (Type w)).map
          (((J.pseudofunctorOver (Type w)).mapComp'
            T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
            (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
              N)).app (Opposite.op X)) ↔
      localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
        localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X := by
  constructor
  · intro h
    simpa [localized_pseudofunctorOver_transport_source_app,
      localized_pseudofunctorOver_transport_target_app] using
      ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form_app
        (J := J) (U := U) g M N x X).symm.trans
        (h.trans
          (localized_pseudofunctorOver_pullHom_underlying_normal_form_app
            (J := J) (U := U) g M N x X).symm))
  · intro h
    simpa [localized_pseudofunctorOver_transport_source_app,
      localized_pseudofunctorOver_transport_target_app] using
      ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form_app
        (J := J) (U := U) g M N x X).trans
        (h.trans
          (localized_pseudofunctorOver_pullHom_underlying_normal_form_app
            (J := J) (U := U) g M N x X)))

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
theorem localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    (((Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
      M.obj).inv ≫
        T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
            N.obj).hom).app (Opposite.op X)) =
      (((sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
            M) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x))) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
            N)).app (Opposite.op X)) := by
  -- Route correction: keep the transport blocker at a single slice object `X`, so the remaining
  -- work is a flat equality of component maps instead of a full natural-transformation identity.
  let hmap :
      (J.pseudofunctorOver (Type w)).map T₁.hom.op.toLoc =
        (J.pseudofunctorOver (Type w)).map (T₂.hom.op.toLoc ≫ g.left.op.toLoc) := by
    -- Transport the base equality `g.left ≫ T₂.hom = T₁.hom` through the owner pseudofunctor.
    simpa using congrArg ((J.pseudofunctorOver (Type w)).map)
      (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g).symm
  let owner_transport :
      ((Over.map T₁.hom).op ⋙ M.obj).obj (Opposite.op X) ⟶
        ((Over.map T₁.hom).op ⋙ N.obj).obj (Opposite.op X) :=
    ((sheafToPresheaf (J.over T₁.left) (Type w)).map
      ((eqToIso hmap ≪≫
          (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc).hom.toNatTrans.app
            M ≫
        (J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x) ≫
        (eqToIso hmap ≪≫
          (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc).inv.toNatTrans.app
            N)).app (Opposite.op X)
  -- Route correction: the surviving blocker is no longer the normal-form rewrites themselves,
  -- but the reduced presheaf-level equality produced by the iff lemma just above.
  have hreduce :
      localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
        localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X := by
    have htarget :
        localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X =
          owner_transport := by
      -- Normalize the target once so the remaining blocker is only the source-side comparison
      -- with the canonical owner transport.
      simpa [owner_transport, hmap, localized_pseudofunctorOver_owner_transport_app] using
        localized_pseudofunctorOver_transport_target_app_eq_owner_transport
          (J := J) (U := U) g M N x X
    have hsource :
        localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
          owner_transport := by
      -- The source side now matches the same canonical owner transport after the identical
      -- `mapComp'`-to-`mapComp` normalization.
      simpa [owner_transport, hmap, localized_pseudofunctorOver_owner_transport_app] using
        localized_pseudofunctorOver_transport_source_app_eq_owner_transport
          (J := J) (U := U) g M N x X
    exact hsource.trans (by simpa using htarget.symm)
  exact
    (localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport_app_iff
      (J := J) (U := U) g M N x X).2 hreduce

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
theorem localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
      M.obj).inv ≫
        T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
            N.obj).hom =
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
            M) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.overMapPullback (Type w) g.left).map
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x))) ≫
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (((J.pseudofunctorOver (Type w)).mapComp'
          T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
          (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
            N) := by
  -- The full forgotten equality is now reduced to the objectwise comparison proved once above.
  ext X a
  exact congrFun
    (localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport_app
      (J := J) (U := U) g M N x X.unop) a

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
theorem localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_naturality
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x)) =
      (sheafToPresheaf (J.over T₁.left) (Type w)).map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (localized_pseudofunctorOver_presheafHom_obj_equiv
            (J := J) (U := U) T₂ M N x)
          g.left T₁.hom T₁.hom
          (by simpa using Over.w g) (by simpa using Over.w g)) := by
  -- Route correction: the remaining blocker lives entirely after forgetting to presheaves, so
  -- isolate that forgotten equality before reusing full faithfulness of `sheafToPresheaf`.
  rw [localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form
    (J := J) (U := U) g M N x]
  rw [localized_pseudofunctorOver_pullHom_underlying_normal_form
    (J := J) (U := U) g M N x]
  -- The remaining equality is now the isolated forgotten-presheaf transport normalization.
  simpa using
    localized_pseudofunctorOver_pullHom_three_factor_eq_iteratedSlice_transport
      (J := J) (U := U) g M N x

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
theorem localized_pseudofunctorOver_presheafHom_obj_equiv_naturality_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
      (J := J) (U := U) T₁ M N).trans
      ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
        (J := J) (U := U) T₁ M).homCongr
        (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ N)))
      (((J.over U).overMapPullback (Type w) g).map x) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)
        g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g) := by
  -- Forget to presheaves so the comparison becomes an equality of explicit composites.
  apply (sheafToPresheaf (J.over T₁.left) (Type w)).map_injective
  -- The remaining transport normalization is exactly the isolated presheaf-level comparison.
  simpa using
    localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_naturality
      (J := J) (U := U) g M N x

/-- Helper for Lemma 7.26.4: the objectwise comparison between the ordinary slice-site Hom sheaf
and the owner-side Hom presheaf commutes with restriction maps in `Over U`. -/
theorem localized_pseudofunctorOver_presheafHom_obj_equiv_naturality
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) T₁ M N
      (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x) =
      (((J.pseudofunctorOver (Type w)).presheafHom M N).map g.op
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)) := by
  -- Normalize both sides to their concrete restriction maps before comparing the transports.
  rw [localized_pseudofunctorOver_presheafHom_obj_equiv_source_map (J := J) (U := U) g M N x,
    localized_pseudofunctorOver_presheafHom_target_map (J := J) (U := U) g M N]
  -- The remaining step is the isolated transport normalization recorded above.
  simpa using localized_pseudofunctorOver_presheafHom_obj_equiv_naturality_transport
    (J := J) (U := U) g M N x

/-- Helper for Lemma 7.26.4: at the terminal object of `Over U`, the ordinary Hom sheaf on
`J.over U` identifies with global morphisms `M ⟶ N`. -/
noncomputable def localized_pseudofunctorOver_presheafHom_base_equiv
    (M N : Sheaf (J.over U) (Type w)) :
    ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op (Over.mk (𝟙 U)))) ≃
      (M ⟶ N) := by
  -- Combine the owner comparison at `Over.mk (𝟙 U)` with the standard base-point equivalence
  -- for `Pseudofunctor.presheafHom`.
  exact
    (localized_pseudofunctorOver_presheafHom_obj_equiv
      (J := J) (U := U) (Over.mk (𝟙 U)) M N).trans
      (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))).symm

/-- Helper for Lemma 7.26.4: transporting a global morphism `ψ : M ⟶ N` to the terminal object
of the ordinary Hom sheaf and then back through the objectwise owner comparison recovers the
canonical base section of `Pseudofunctor.presheafHom`. -/
theorem localized_pseudofunctorOver_presheafHom_base_equiv_apply
    {M N : Sheaf (J.over U) (Type w)}
    (ψ : M ⟶ N) :
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
      (Over.mk (𝟙 U)) M N
      ((localized_pseudofunctorOver_presheafHom_base_equiv
        (J := J) (U := U) M N).symm ψ) =
      (Pseudofunctor.presheafHomObjHomEquiv
        (F := J.pseudofunctorOver (Type w)) ψ) := by
  -- Unfold the composite base equivalence and cancel the objectwise comparison with its inverse.
  change
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
      (Over.mk (𝟙 U)) M N
      ((localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
        (Over.mk (𝟙 U)) M N).symm
        (((Pseudofunctor.presheafHomObjHomEquiv
          (F := J.pseudofunctorOver (Type w))).symm).symm ψ)) =
      (((Pseudofunctor.presheafHomObjHomEquiv
        (F := J.pseudofunctorOver (Type w))).symm).symm ψ)
  exact
    (localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
      (Over.mk (𝟙 U)) M N).apply_symm_apply
      ((((Pseudofunctor.presheafHomObjHomEquiv
        (F := J.pseudofunctorOver (Type w))).symm).symm ψ))

/-- Helper for Lemma 7.26.4: the ordinary slice-site Hom sheaf and the owner-side Hom presheaf
are identified by the objectwise iterated-slice comparison, promoted to a presheaf isomorphism. -/
noncomputable def localized_pseudofunctorOver_presheafHom_iso
    (M N : Sheaf (J.over U) (Type w)) :
    (CategoryTheory.sheafHom (J := J.over U) M N).1 ≅
      ((J.pseudofunctorOver (Type w)).presheafHom M N) :=
  NatIso.ofComponents
    (fun T ↦
      Equiv.toIso
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T.unop M N))
    (by
      -- Route correction: prove the Hom-presheaf comparison once as a NatIso, so the fixed-cover
      -- prestack argument only transports the sheaf condition across that stable bridge.
      intro T₁ T₂ g
      ext x
      simpa using localized_pseudofunctorOver_presheafHom_obj_equiv_naturality
        (J := J) (U := U) g.unop M N x)


end

end GrothendieckTopology
end CategoryTheory
