module

public import stacks_project.Chap07.Lemma_7_26_4.FixedCoverDescent

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: transporting a sheaf on the iterated slice
`((Over U) / T)` across the canonical equivalence with `Over T.left` identifies the iterated
pullback of a slice sheaf with the ordinary pullback along `T.hom`. -/
noncomputable def localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
    (T : Over U)
    (M : Sheaf (J.over U) (Type w)) :
    (T.iteratedSliceEquiv.sheafCongr (((J.over U)).over T) (J.over T.left) (Type w)).functor.obj
      ((((J.over U)).overPullback (Type w) T).obj M) ≅
      ((J.overMapPullback (Type w) T.hom).obj M) := by
  -- Compare the two localized sheaves at the presheaf level using
  -- `iteratedSliceBackward ⋙ forget = Over.map T.hom`.
  refine (fullyFaithfulSheafToPresheaf (J.over T.left) (Type w)).preimageIso ?_
  simpa [GrothendieckTopology.overPullback, GrothendieckTopology.overMapPullback,
    Equivalence.sheafCongr, Equivalence.sheafCongr.functor] using
    (Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T)))
      M.obj)

/-- Helper for Lemma 7.26.4: after forgetting to presheaves, the forward map of the iterated-slice
pullback comparison is exactly the whiskered identity transport coming from
`Over.iteratedSliceBackward_forget`. -/
theorem localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_hom_map
    (T : Over U)
    (M : Sheaf (J.over U) (Type w)) :
    (sheafToPresheaf (J.over T.left) (Type w)).map
      (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
        (J := J) (U := U) T M).hom =
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T)))
        M.obj).hom := by
  -- This is the defining property of the `preimageIso` used above.
  simp [localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback]

/-- Helper for Lemma 7.26.4: after forgetting to presheaves, the inverse map of the iterated-slice
pullback comparison is the inverse whiskered identity transport coming from
`Over.iteratedSliceBackward_forget`. -/
theorem localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_inv_map
    (T : Over U)
    (M : Sheaf (J.over U) (Type w)) :
    (sheafToPresheaf (J.over T.left) (Type w)).map
      (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
        (J := J) (U := U) T M).inv =
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T)))
        M.obj).inv := by
  -- The inverse statement is the same `preimageIso` computation for the inverse component.
  simp [localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback]

/-- Helper for Lemma 7.26.4: after transporting from the iterated slice to `Over T.left`,
morphisms between the two iterated pullbacks are the same as morphisms between their transported
images. -/
noncomputable def localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w)) :
    ((((J.over U)).overPullback (Type w) T).obj M ⟶
      (((J.over U)).overPullback (Type w) T).obj N) ≃
      ((T.iteratedSliceEquiv.sheafCongr (((J.over U)).over T) (J.over T.left) (Type w)).functor.obj
          ((((J.over U)).overPullback (Type w) T).obj M) ⟶
        (T.iteratedSliceEquiv.sheafCongr (((J.over U)).over T) (J.over T.left) (Type w)).functor.obj
          ((((J.over U)).overPullback (Type w) T).obj N)) :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((T.iteratedSliceEquiv.sheafCongr (((J.over U)).over T) (J.over T.left) (Type w)).functor)).homEquiv

/-- Helper for Lemma 7.26.4: the ordinary Hom sheaf on `J.over U` evaluated at `T` matches the
owner-level presheaf of morphisms for `J.pseudofunctorOver` at the same object `T`. -/
noncomputable def localized_pseudofunctorOver_presheafHom_obj_equiv
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w)) :
    ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T)) ≃
      (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T)) := by
  -- First identify the ordinary Hom-sheaf value with morphisms on the iterated slice,
  -- then transport those morphisms to the `overMapPullback` owner used by `presheafHom`.
  exact
    (localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv (J := J) (U := U) T M N).trans
      (Iso.homCongr
        (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T M)
        (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T N))

/-- Helper for Lemma 7.26.4: evaluating the objectwise comparison at `T` already lands in the
owner-side source coordinates used by `overMapCompPresheafHomIso` at the terminal object of
`Over T.left`. This packages the source-side coordinate change needed in the naturality step. -/
noncomputable abbrev localized_pseudofunctorOver_presheafHom_obj_equiv_owner_source
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T))) :
    (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
      (Opposite.op (Over.mk (𝟙 T.left)))) :=
  Eq.mp
    (by
      simp [localized_cover_descent_overMap_terminal_obj]
      rfl)
    (localized_pseudofunctorOver_presheafHom_obj_equiv
      (J := J) (U := U) T M N x)

/-- Helper for Lemma 7.26.4: the objectwise comparison between the ordinary Hom sheaf and the
owner-side Hom presheaf is a bijection on every slice object `T`. -/
theorem localized_pseudofunctorOver_presheafHom_obj_equiv_bijective
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w)) :
    Function.Bijective
      (localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) T M N) := by
  -- This is just the bijectivity of the explicit equivalence recorded above.
  exact (localized_pseudofunctorOver_presheafHom_obj_equiv
    (J := J) (U := U) T M N).bijective

/-- Helper for Lemma 7.26.4: on the ordinary slice-site Hom sheaf, restriction along
`g : T₁ ⟶ T₂` is definitionally the localized pullback functor on sheaves over `J.over U`. -/
theorem localized_pseudofunctorOver_sheafHom_map_eq
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    ((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x =
      ((J.over U).overMapPullback (Type w) g).map x := by
  -- `sheafHom` is implemented via `sheafHom'`, whose restriction maps are exactly these
  -- localized pullback functors.
  rfl

/-- Helper for Lemma 7.26.4: after expanding the source-side comparison at `T₁`, the left side
of the Hom-presheaf naturality equation is the iterated-slice transport of the localized pullback
map on `x`. -/
theorem localized_pseudofunctorOver_presheafHom_obj_equiv_source_map
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) T₁ M N
      (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x) =
      ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x) := by
  -- Route correction: normalize the source-side restriction map before comparing it with the
  -- owner-side `pullHom`; this removes the outer `sheafHom` wrapper from the blocker.
  rw [localized_pseudofunctorOver_sheafHom_map_eq (J := J) (U := U) g M N x]
  rfl

/-- Helper for Lemma 7.26.4: on the owner-side Hom presheaf, restriction along `g : T₁ ⟶ T₂`
is already the explicit `pullHom` map along `g.left`. This isolates the target-side
normalization needed in the remaining transport comparison. -/
theorem localized_pseudofunctorOver_presheafHom_target_map
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (y : (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T₂))) :
    (((J.pseudofunctorOver (Type w)).presheafHom M N).map g.op y) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom y g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g) := by
  -- This is the defining formula for the restriction map of `Pseudofunctor.presheafHom`.
  rfl

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
theorem localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form
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
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
        T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
            N.obj).hom := by
  -- Normalize the objectwise equivalence and the outer comparison isomorphisms before touching
  -- the owner-side `pullHom`; this isolates the left-hand transport as a plain presheaf map.
  simp only [Equiv.trans_apply, Iso.homCongr_apply]
  rw [Functor.map_comp, Functor.map_comp,
    localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_inv_map,
    localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_hom_map]
  -- The remaining middle map is just the sheaf-congruence functor applied to the localized
  -- pullback morphism, so forgetting to presheaves reveals the expected whiskered natural map.
  simp only [localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv,
    Equivalence.sheafCongr, Equivalence.sheafCongr.functor,
    Functor.sheafPushforwardContinuous]
  rfl

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
theorem localized_pseudofunctorOver_mapComp'_witness
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂) :
    T₂.hom.op.toLoc ≫ g.left.op.toLoc = T₁.hom.op.toLoc := by
  -- This is exactly `Over.w g`, translated into the `LocallyDiscrete Cᵒᵖ` coordinates used by
  -- `pseudofunctorOver.mapComp'`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op (Over.w g))

/-- Helper for Lemma 7.26.4: the owner-side `mapComp'` for the pair
`(T₂.hom, g.left)` literally splits into the equality transport from
`g.left ≫ T₂.hom = T₁.hom` followed by the strict `mapComp`. This is the stable normal form
used to isolate the two outer factors of `pullHom`. -/
theorem localized_pseudofunctorOver_mapComp'_eq_map₂Iso_comp_mapComp
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂) :
    (J.pseudofunctorOver (Type w)).mapComp'
      T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
      (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g) =
      (J.pseudofunctorOver (Type w)).map₂Iso
        (eqToIso (by
          simpa using (localized_pseudofunctorOver_mapComp'_witness
            (T₁ := T₁) (T₂ := T₂) g).symm)) ≪≫
      (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc := by
  -- This is exactly the defining expansion of the flexible comparison `mapComp'`.
  simp [Pseudofunctor.mapComp']

/-- Helper for Lemma 7.26.4: after forgetting to presheaves, the source outer factor in the
owner-side `pullHom` formula is exactly the source-side component of
`J.overMapPullbackComp (Type w) g.left T₂.hom`. This records the stable owner-coordinate cast
used before comparing the middle restriction map. -/
theorem localized_pseudofunctorOver_mapComp'_hom_owner_source_cast_type
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M : Sheaf (J.over U) (Type w)) :
    (((J.overMapPullback (Type w) (g.left ≫ T₂.hom)).obj M).obj ⟶
      ((J.overMapPullback (Type w) T₂.hom ⋙ J.overMapPullback (Type w) g.left).obj M).obj) =
      ((((J.pseudofunctorOver (Type w)).map T₁.hom.op.toLoc).toFunctor.obj M).obj ⟶
        ((((J.pseudofunctorOver (Type w)).map T₂.hom.op.toLoc ≫
          (J.pseudofunctorOver (Type w)).map g.left.op.toLoc).toFunctor.obj M).obj)) := by
  -- Unfold the owner coordinates and use `Over.w g : g.left ≫ T₂.hom = T₁.hom`.
  simpa [GrothendieckTopology.pseudofunctorOver] using
    congrArg
      (fun f =>
        ((J.overMapPullback (Type w) f).obj M).obj ⟶
          ((J.overMapPullback (Type w) T₂.hom ⋙ J.overMapPullback (Type w) g.left).obj M).obj)
      (Over.w g)

/-- Helper for Lemma 7.26.4: the target-side component of `J.overMapPullbackComp` lives on
`g.left ≫ T₂.hom`, and this theorem records the exact owner-coordinate type equality needed to
view it over `T₁.hom`. -/
theorem localized_pseudofunctorOver_mapComp'_inv_owner_target_cast_type
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (N : Sheaf (J.over U) (Type w)) :
    (((J.overMapPullback (Type w) T₂.hom ⋙ J.overMapPullback (Type w) g.left).obj N).obj ⟶
      ((J.overMapPullback (Type w) (g.left ≫ T₂.hom)).obj N).obj) =
      (((((J.pseudofunctorOver (Type w)).map T₂.hom.op.toLoc ≫
          (J.pseudofunctorOver (Type w)).map g.left.op.toLoc).toFunctor.obj N).obj) ⟶
        (((J.pseudofunctorOver (Type w)).map T₁.hom.op.toLoc).toFunctor.obj N).obj) := by
  -- The same owner-coordinate cast uses the target equality `g.left ≫ T₂.hom = T₁.hom`.
  simpa [GrothendieckTopology.pseudofunctorOver] using
    congrArg
      (fun f =>
        ((J.overMapPullback (Type w) T₂.hom ⋙ J.overMapPullback (Type w) g.left).obj N).obj ⟶
          ((J.overMapPullback (Type w) f).obj N).obj)
      (Over.w g)

/-- Helper for Lemma 7.26.4: after forgetting the owner-side `pullHom` to presheaves, the map is
the explicit three-factor composite of the two `mapComp'` outer transports and the localized
pullback of the middle morphism. This removes hidden unfolding from the remaining transport
comparison. -/
theorem localized_pseudofunctorOver_pullHom_underlying_normal_form
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)
        g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g)) =
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
  -- Forget `pullHom` before any owner-coordinate transport rewrites; only the two outer
  -- `mapComp'` factors and the pulled-back middle morphism remain.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rfl

/-! ### HEq strip toolkit for the iterated-slice transport core
These helpers collapse cast-like component applications (`eqToHom`, 2-cell `eqToHom`
components, `pseudofunctorOver.mapComp` components) to their arguments up to `HEq`,
with syntactic patterns matching the goal spellings so no defeq-unfolding is needed. -/

theorem eqToHom_apply_heq {A B : Type w} (h : A = B) (a : A) :
    HEq ((eqToHom h) a) a := by subst h; rfl

theorem dep_app_heq {ι : Type*} {P Q : ι → Type w} (f : ∀ i, P i → Q i)
    {i j : ι} (h : i = j) {a : P i} {b : P j} (hab : HEq a b) :
    HEq (f i a) (f j b) := by subst h; rw [eq_of_heq hab]

theorem map_op_eqToHom_apply_heq {D : Type*} [Category D] (F : Dᵒᵖ ⥤ Type w)
    {A B : D} (φ : A ⟶ B) (h : A = B) (hφ : φ = eqToHom h) (m : F.obj (Opposite.op B)) :
    HEq (F.map φ.op m) m := by
  subst hφ; cases h; exact heq_of_eq (by simp)

theorem over_eqToHom_left {T : Type*} [Category T] {B : T} {A A' : Over B}
    (h : A = A') : (eqToHom h).left = eqToHom (congrArg Comma.left h) := by
  subst h; rfl

theorem sheaf2cell_eqToHom_component_apply_heq
    {𝒞 : Cat} {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    {F G : 𝒞 ⟶ Cat.of (Sheaf K (Type w))} (h : F = G) (Mo : 𝒞) (X : Dᵒᵖ)
    (m : ((F.toFunctor.obj Mo)).obj.obj X) :
    HEq ((((eqToHom h).toNatTrans.app Mo).hom.app X) m) m := by
  subst h; rfl


theorem pf_mapComp_inv_component_apply_heq
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g' : b ⟶ c)
    (No : Sheaf (J.over (Opposite.unop a.as)) (Type w)) (X : (Over (Opposite.unop c.as))ᵒᵖ)
    (m : No.obj.obj (Opposite.op
      ((Over.map f.as.unop).obj ((Over.map g'.as.unop).obj (Opposite.unop X))))) :
    HEq (((((J.pseudofunctorOver (Type w)).mapComp f g').inv.toNatTrans.app No).hom.app X) m) m := by
  rw [GrothendieckTopology.pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app]
  have hl : ((Over.mapComp g'.as.unop f.as.unop).hom.app (Opposite.unop X)).left
      = 𝟙 (Opposite.unop X).left := by simp [Over.mapComp]
  have hAB : ((Over.map (g'.as.unop ≫ f.as.unop)).obj (Opposite.unop X))
      = (Over.map f.as.unop).obj ((Over.map g'.as.unop).obj (Opposite.unop X)) :=
    (congrArg Over.mk (Category.assoc (Opposite.unop X).hom g'.as.unop f.as.unop)).symm
  exact map_op_eqToHom_apply_heq No.obj _ hAB
    (Over.OverMorphism.ext
      (hl.trans (((over_eqToHom_left hAB).trans
        (eqToHom_refl (Opposite.unop X).left _)).symm))) m

theorem pf_mapComp_hom_component_apply_heq
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g' : b ⟶ c)
    (Mo : Sheaf (J.over (Opposite.unop a.as)) (Type w)) (X : (Over (Opposite.unop c.as))ᵒᵖ)
    (m : Mo.obj.obj (Opposite.op
      ((Over.map (g'.as.unop ≫ f.as.unop)).obj (Opposite.unop X)))) :
    HEq (((((J.pseudofunctorOver (Type w)).mapComp f g').hom.toNatTrans.app Mo).hom.app X) m) m := by
  rw [GrothendieckTopology.pseudofunctorOver_mapComp_hom_toNatTrans_app_hom_app]
  have hl : ((Over.mapComp g'.as.unop f.as.unop).inv.app (Opposite.unop X)).left
      = 𝟙 (Opposite.unop X).left := by simp [Over.mapComp]
  have hBA : ((Over.map f.as.unop).obj ((Over.map g'.as.unop).obj (Opposite.unop X)))
      = (Over.map (g'.as.unop ≫ f.as.unop)).obj (Opposite.unop X) :=
    congrArg Over.mk (Category.assoc (Opposite.unop X).hom g'.as.unop f.as.unop)
  exact map_op_eqToHom_apply_heq Mo.obj _ hBA
    (Over.OverMorphism.ext
      (hl.trans (((over_eqToHom_left hBA).trans
        (eqToHom_refl (Opposite.unop X).left _)).symm))) m

/-- Helper for Lemma 7.26.4: the inverse component of a `mapComp'` comparison acts as the
identity on elements, up to heterogeneous equality. -/
theorem pf_mapComp'_inv_component_apply_heq
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g' : b ⟶ c) (k : a ⟶ c)
    (hk : f ≫ g' = k)
    (No : Sheaf (J.over (Opposite.unop a.as)) (Type w)) (X : (Over (Opposite.unop c.as))ᵒᵖ)
    (m : No.obj.obj (Opposite.op
      ((Over.map f.as.unop).obj ((Over.map g'.as.unop).obj (Opposite.unop X))))) :
    HEq (((((J.pseudofunctorOver (Type w)).mapComp' f g' k hk).inv.toNatTrans.app No).hom.app X) m)
      m := by
  -- Replace the explicit composite target by `f ≫ g'`; then the existing `mapComp` inverse
  -- component normalizer strips the only nontrivial component application.
  have hbase := pf_mapComp_inv_component_apply_heq (J := J) (f := f) (g' := g') No X m
  subst hk
  simpa [Pseudofunctor.mapComp'] using hbase

/-- Helper for Lemma 7.26.4: the forward component of a `mapComp'` comparison acts as the
identity on elements, up to heterogeneous equality. -/
theorem pf_mapComp'_hom_component_apply_heq
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g' : b ⟶ c) (k : a ⟶ c)
    (hk : f ≫ g' = k)
    (Mo : Sheaf (J.over (Opposite.unop a.as)) (Type w)) (X : (Over (Opposite.unop c.as))ᵒᵖ)
    (m : Mo.obj.obj (Opposite.op ((Over.map k.as.unop).obj (Opposite.unop X)))) :
    HEq (((((J.pseudofunctorOver (Type w)).mapComp' f g' k hk).hom.toNatTrans.app Mo).hom.app X) m)
      m := by
  -- Once the chosen composite `k` is identified with `f ≫ g'`, this is the existing forward
  -- `mapComp` component normalizer in the `mapComp'` spelling.
  subst hk
  simpa [Pseudofunctor.mapComp'] using
    (pf_mapComp_hom_component_apply_heq (J := J) (f := f) (g' := g') Mo X m)


theorem over_mk_hext {𝒞 : Type*} [Category 𝒞] {B : 𝒞} {Y₁ Y₂ : 𝒞}
    (hY : Y₁ = Y₂) (f₁ : Y₁ ⟶ B) (f₂ : Y₂ ⟶ B) (hf : HEq f₁ f₂) :
    Over.mk f₁ = Over.mk f₂ := by subst hY; rw [eq_of_heq hf]

theorem hom_heq_of_left_eq {T : Type*} [Category T] {B : T} {U₁ U₂ V : Over B}
    (hU : U₁ = U₂) (k₁ : U₁ ⟶ V) (k₂ : U₂ ⟶ V) (hk : HEq k₁.left k₂.left) :
    HEq k₁ k₂ := by
  subst hU; exact heq_of_eq (Over.OverMorphism.ext (eq_of_heq hk))

/-- Helper for Lemma 7.26.4: the iterated-slice whisker form of the transported section
equals the three-factor owner transport composite. This is the mathematical core of the
naturality square, proved elementwise by an `HEq` chain through `x.hom` at the two
canonically equal slice objects. -/
theorem localized_pseudofunctorOver_whisker_transport_core
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
  -- hmid: 619-mirror at T₂ with the chain spelled out syntactically (so trans_apply fires)
  have hmid : (sheafToPresheaf (J.over T₂.left) (Type w)).map
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₂ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₂ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₂ N)))
        x) =
      (Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₂)))
        M.obj).inv ≫
        T₂.iteratedSliceBackward.op.whiskerLeft x.hom ≫
          (Functor.isoWhiskerRight
            (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₂)))
            N.obj).hom := by
    simp only [Equiv.trans_apply, Iso.homCongr_apply]
    rw [Functor.map_comp, Functor.map_comp,
      localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_inv_map,
      localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback_hom_map]
    simp only [localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv,
      Equivalence.sheafCongr, Equivalence.sheafCongr.functor,
      Functor.sheafPushforwardContinuous]
    rfl
  -- defeq bridge: F2 = whiskeringLeft-image of the chain's presheaf shadow
  have hF2 : (sheafToPresheaf (J.over T₁.left) (Type w)).map
      ((J.overMapPullback (Type w) g.left).map
        (localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) T₂ M N x)) =
      ((Functor.whiskeringLeft (Over T₁.left)ᵒᵖ (Over T₂.left)ᵒᵖ (Type w)).obj
        (Over.map g.left).op).map
        ((sheafToPresheaf (J.over T₂.left) (Type w)).map
          (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
            (J := J) (U := U) T₂ M N).trans
            ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
              (J := J) (U := U) T₂ M).homCongr
              (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
                (J := J) (U := U) T₂ N)))
            x)) := rfl
  have h2 := hF2.trans (congrArg
    (((Functor.whiskeringLeft (Over T₁.left)ᵒᵖ (Over T₂.left)ᵒᵖ (Type w)).obj
      (Over.map g.left).op).map) hmid)
  refine Eq.trans ?core (congrArg (fun k ↦
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((J.pseudofunctorOver (Type w)).mapComp'
        T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
        (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).hom.toNatTrans.app
          M) ≫ k ≫
    (sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((J.pseudofunctorOver (Type w)).mapComp'
        T₂.hom.op.toLoc g.left.op.toLoc T₁.hom.op.toLoc
        (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g)).inv.toNatTrans.app
          N)) h2).symm
  -- core: pure whisker/eqToHom identity, all factors concrete
  ext X a
  simp [Pseudofunctor.mapComp',
    GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_map₂,
    eqToHom_map, eqToHom_app]
  apply eq_of_heq
  refine HEq.trans (b := x.hom.app
      (Opposite.op (Over.mk (Over.homMk
        (U := Over.mk (((Opposite.unop X).hom ≫ g.left) ≫ T₂.hom))
        ((Opposite.unop X).hom ≫ g.left) rfl)))
      (eqToHom (congrArg M.obj.obj (Functor.congr_obj
          (Eq.symm (congrArg Functor.op (Over.iteratedSliceBackward_forget T₂)))
          (Opposite.op ((Over.map g.left).obj (Opposite.unop X)))))
        ((((J.pseudofunctorOver (Type w)).mapComp
            T₂.hom.op.toLoc g.left.op.toLoc).hom.toNatTrans.app M).hom.app X
          (((eqToHom (congrArg (fun k => (J.pseudofunctorOver (Type w)).map k)
                ((localized_pseudofunctorOver_mapComp'_witness
                  (T₁ := T₁) (T₂ := T₂) g).symm))).toNatTrans.app M).hom.app X a)))) ?hl ?hr
  case hl =>
    refine HEq.trans (eqToHom_apply_heq _ _) ?_
    refine dep_app_heq x.hom.app ?ho ?ha
    case ho =>
      exact congrArg Opposite.op (over_mk_hext
        (congrArg Over.mk ((congrArg (fun k => (Opposite.unop X).hom ≫ k) (Over.w g)).symm.trans
          (Category.assoc _ _ _).symm)) _ _
        (hom_heq_of_left_eq
          (congrArg Over.mk ((congrArg (fun k => (Opposite.unop X).hom ≫ k) (Over.w g)).symm.trans
            (Category.assoc _ _ _).symm)) _ _ (by simp)))
    case ha =>
      refine HEq.trans (eqToHom_apply_heq _ _) (HEq.symm ?_)
      refine HEq.trans (eqToHom_apply_heq _ _) ?_
      refine HEq.trans (pf_mapComp_hom_component_apply_heq T₂.hom.op.toLoc g.left.op.toLoc M X _) ?_
      exact sheaf2cell_eqToHom_component_apply_heq _ _ _ _
  case hr =>
    exact ((sheaf2cell_eqToHom_component_apply_heq _ _ _ _).trans
      ((pf_mapComp_inv_component_apply_heq T₂.hom.op.toLoc g.left.op.toLoc N X _).trans
        (eqToHom_apply_heq _ _))).symm

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
theorem localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    ((sheafToPresheaf (J.over T₁.left) (Type w)).map
      (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
        (J := J) (U := U) T₁ M N).trans
        ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ M).homCongr
          (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
            (J := J) (U := U) T₁ N)))
        (((J.over U).overMapPullback (Type w) g).map x))).app (Opposite.op X) =
      (((Functor.isoWhiskerRight
        (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
        M.obj).inv ≫
          T₁.iteratedSliceBackward.op.whiskerLeft ((Over.map g).op.whiskerLeft x.hom) ≫
            (Functor.isoWhiskerRight
              (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T₁)))
              N.obj).hom).app (Opposite.op X)) := by
  -- Specialize the already-proved natural-transformation normal form at the chosen slice object.
  exact congrArg (fun α ↦ α.app (Opposite.op X))
    (localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form
      (J := J) (U := U) g M N x)

/-- Helper for Lemma 7.26.4: the forgotten owner-side `pullHom` normal form can be specialized to
one slice object `X`, yielding the three-factor owner composite used later in the transport
comparison. -/
theorem localized_pseudofunctorOver_pullHom_underlying_normal_form_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    ((sheafToPresheaf (J.over T₁.left) (Type w)).map
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (localized_pseudofunctorOver_presheafHom_obj_equiv
          (J := J) (U := U) T₂ M N x)
        g.left T₁.hom T₁.hom
        (by simpa using Over.w g) (by simpa using Over.w g))).app (Opposite.op X) =
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
  -- Specialize the forgotten `pullHom` normal form at the chosen slice object.
  exact congrArg (fun α ↦ α.app (Opposite.op X))
    (localized_pseudofunctorOver_pullHom_underlying_normal_form
      (J := J) (U := U) g M N x)

/-- Helper for Lemma 7.26.4: after both sides of the Hom-presheaf naturality statement are
written in owner coordinates, the remaining equality is the bare transport comparison between the
iterated-slice pullback map and the owner-side `pullHom` formula. -/
noncomputable abbrev localized_pseudofunctorOver_transport_source_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :=
  ((sheafToPresheaf (J.over T₁.left) (Type w)).map
    (((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv
      (J := J) (U := U) T₁ M N).trans
      ((localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
        (J := J) (U := U) T₁ M).homCongr
        (localized_pseudofunctorOver_iteratedSlicePullbackIsoOverMapPullback
          (J := J) (U := U) T₁ N)))
      (((J.over U).overMapPullback (Type w) g).map x))).app (Opposite.op X)

/-- Helper for Lemma 7.26.4: this is the reduced owner-side `pullHom` component appearing after
the normal-form rewrites for the remaining prestack transport comparison. -/
noncomputable abbrev localized_pseudofunctorOver_transport_target_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :=
  ((sheafToPresheaf (J.over T₁.left) (Type w)).map
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (localized_pseudofunctorOver_presheafHom_obj_equiv
        (J := J) (U := U) T₂ M N x)
      g.left T₁.hom T₁.hom
      (by simpa using Over.w g) (by simpa using Over.w g))).app (Opposite.op X)

/-- Helper for Lemma 7.26.4: rewriting the two outer `mapComp'` factors in the owner-side
`pullHom` formula by the strict `mapComp` comparison isolates the canonical three-factor owner
transport used in the remaining componentwise blocker. -/
noncomputable abbrev localized_pseudofunctorOver_owner_transport_hom
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :=
  let hmap :
      (J.pseudofunctorOver (Type w)).map T₁.hom.op.toLoc =
        (J.pseudofunctorOver (Type w)).map (T₂.hom.op.toLoc ≫ g.left.op.toLoc) := by
    simpa using congrArg ((J.pseudofunctorOver (Type w)).map)
      (localized_pseudofunctorOver_mapComp'_witness (T₁ := T₁) (T₂ := T₂) g).symm
  (((eqToIso hmap ≪≫
      (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc).hom.toNatTrans.app
        M) ≫
    (J.overMapPullback (Type w) g.left).map
      (localized_pseudofunctorOver_presheafHom_obj_equiv
        (J := J) (U := U) T₂ M N x) ≫
    ((eqToIso hmap ≪≫
      (J.pseudofunctorOver (Type w)).mapComp T₂.hom.op.toLoc g.left.op.toLoc).inv.toNatTrans.app
        N))

/-- Helper for Lemma 7.26.4: evaluating the canonical owner-side three-factor transport at a
chosen slice object `X` recovers the section-level map used in the reduced target comparison. -/
noncomputable abbrev localized_pseudofunctorOver_owner_transport_app
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :=
  ((sheafToPresheaf (J.over T₁.left) (Type w)).map
    (localized_pseudofunctorOver_owner_transport_hom
      (J := J) (U := U) g M N x)).app (Opposite.op X)

/-- Helper for Lemma 7.26.4: rewriting the two outer `mapComp'` factors in the owner-side
`pullHom` formula by the strict `mapComp` comparison isolates the canonical three-factor owner
transport used in the remaining componentwise blocker. -/
theorem localized_pseudofunctorOver_transport_target_app_eq_owner_transport
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left) :
    localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X =
      localized_pseudofunctorOver_owner_transport_app (J := J) (U := U) g M N x X := by
  -- Replace both flexible `mapComp'` transports by the strict `mapComp` normal form once, so
  -- the remaining blocker can target a single canonical owner-side composite.
  simpa [localized_pseudofunctorOver_transport_target_app,
    localized_pseudofunctorOver_owner_transport_app,
    localized_pseudofunctorOver_mapComp'_eq_map₂Iso_comp_mapComp] using
    localized_pseudofunctorOver_pullHom_underlying_normal_form_app
      (J := J) (U := U) g M N x X

/-- Helper for Lemma 7.26.4: after expressing the source-side comparison in owner coordinates,
the iterated-slice transport is already the same canonical owner transport used on the target
side. This isolates the source half of the remaining transport/coercion normalization. -/
theorem localized_pseudofunctorOver_overMapCompPresheafHomIso_hom_naturality_over_homMk
    (T : Over U)
    (M N : Sheaf (J.over U) (Type w))
    (y : (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
      (Opposite.op (Over.mk (𝟙 T.left)))))
    (X : Over T.left) :
    ((Pseudofunctor.overMapCompPresheafHomIso
      (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
        (Opposite.op X))
      ((((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).map
        (Opposite.op (show X ⟶ Over.mk (𝟙 T.left) from Over.homMk X.hom (by simp))) y)) =
      (((J.pseudofunctorOver (Type w)).presheafHom
        (((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj M)
        (((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj N)).map
        (Opposite.op (show X ⟶ Over.mk (𝟙 T.left) from Over.homMk X.hom (by simp)))
        (((Pseudofunctor.overMapCompPresheafHomIso
          (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
            (Opposite.op (Over.mk (𝟙 T.left)))) y)) := by
  -- This is exactly the naturality square of `overMapCompPresheafHomIso`, specialized to the
  -- terminal-arrow morphism `Over.homMk X.hom : X ⟶ Over.mk (𝟙 T.left)`.
  simpa using congrFun
    ((Pseudofunctor.overMapCompPresheafHomIso
      (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.naturality
        (Opposite.op (show X ⟶ Over.mk (𝟙 T.left) from Over.homMk X.hom (by simp)))) y

/-- Helper for Lemma 7.26.4: to prove the remaining source-versus-target component comparison at
`X`, it suffices to compare the two explicit normal forms already isolated earlier in the file.
This packages the reduction from the abbreviated transport maps to the raw component equality. -/
theorem localized_pseudofunctorOver_transport_app_eq_of_underlying_normal_forms
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂)))
    (X : Over T₁.left)
    (h :
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
              N)).app (Opposite.op X))) :
    localized_pseudofunctorOver_transport_source_app (J := J) (U := U) g M N x X =
      localized_pseudofunctorOver_transport_target_app (J := J) (U := U) g M N x X := by
  -- Rewrite both abbreviations to the earlier explicit normal forms and splice in the supplied
  -- component equality between those normal forms.
  simpa [localized_pseudofunctorOver_transport_source_app,
    localized_pseudofunctorOver_transport_target_app] using
    ((localized_pseudofunctorOver_iteratedSliceSheafCongrHomEquiv_underlying_left_normal_form_app
      (J := J) (U := U) g M N x X).symm.trans
      (h.trans
        (localized_pseudofunctorOver_pullHom_underlying_normal_form_app
          (J := J) (U := U) g M N x X).symm))

/-- Helper for Lemma 7.26.4: after expressing the source-side comparison in owner coordinates,
the iterated-slice transport is already the same canonical owner transport used on the target
side. This isolates the source half of the remaining transport/coercion normalization. -/
noncomputable abbrev localized_pseudofunctorOver_source_terminal_transport_hom
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    ((J.overMapPullback (Type w) T₁.hom).obj M) ⟶ ((J.overMapPullback (Type w) T₁.hom).obj N) :=
  (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w)) (S := T₁.left)).symm
    (((Pseudofunctor.overMapCompPresheafHomIso
      (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T₁.hom).hom.app
        (Opposite.op (Over.mk (𝟙 T₁.left))))
      (localized_pseudofunctorOver_presheafHom_obj_equiv_owner_source
        (J := J) (U := U) T₁ M N (((CategoryTheory.sheafHom (J := J.over U) M N).1).map g.op x)))

/-- Helper for Lemma 7.26.4: the owner-side `pullHom` comparison already agrees, as a sheaf
morphism, with the canonical three-factor owner transport. This packages the target-side
normalization once, so the remaining transport blocker is purely on the source side. -/
theorem localized_pseudofunctorOver_pullHom_eq_owner_transport_hom
    {T₁ T₂ : Over U}
    (g : T₁ ⟶ T₂)
    (M N : Sheaf (J.over U) (Type w))
    (x : ((CategoryTheory.sheafHom (J := J.over U) M N).1.obj (Opposite.op T₂))) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (localized_pseudofunctorOver_presheafHom_obj_equiv
        (J := J) (U := U) T₂ M N x)
      g.left T₁.hom T₁.hom
      (by simpa using Over.w g) (by simpa using Over.w g) =
      localized_pseudofunctorOver_owner_transport_hom
        (J := J) (U := U) g M N x := by
  -- Compare the two sheaf morphisms after forgetting to presheaves and evaluating componentwise;
  -- the objectwise equality is exactly `transport_target_app_eq_owner_transport`.
  apply (sheafToPresheaf (J.over T₁.left) (Type w)).map_injective
  ext X a
  exact congrFun
    (localized_pseudofunctorOver_transport_target_app_eq_owner_transport
      (J := J) (U := U) g M N x X.unop) a

/-- Helper for Lemma 7.26.4: the terminal-source cast used to regard a section over
`(Over.map T.hom).obj (Over.mk (𝟙 T.left))` as a section over `Over.mk T.hom` preserves
equalities. This isolates the cast layer that blocks the remaining terminal-component proof. -/
theorem localized_pseudofunctorOver_terminal_source_cast_congr
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    (e :
      (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T)) =
        (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
          (Opposite.op (Over.mk (𝟙 T.left)))))
    {x y :
      (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T))}
    (h : x = y) :
    cast e x = cast e y := by
  -- The owner-source terminal cast is functorial in the transported section.
  cases h
  rfl

/-- Helper for Lemma 7.26.4: once the terminal source object is fixed, applying the terminal
component of `overMapCompPresheafHomIso` and then the base-point equivalence preserves equality
of source sections. -/
theorem localized_pseudofunctorOver_terminal_component_congr
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    {x y :
      (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T.left))))}
    (h : x = y) :
    (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))
        (S := T.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T.left)))) x) =
      (Pseudofunctor.presheafHomObjHomEquiv (F := J.pseudofunctorOver (Type w))
        (S := T.left)).symm
      (((Pseudofunctor.overMapCompPresheafHomIso
        (F := J.pseudofunctorOver (Type w)) (M := M) (N := N) T.hom).hom.app
          (Opposite.op (Over.mk (𝟙 T.left)))) y) := by
  -- The remaining terminal comparison is honest function application after the cast has been
  -- normalized, so equality propagates directly.
  cases h
  rfl

/-- Helper for Lemma 7.26.4: the terminal source fiber of the restricted Hom presheaf over
`T.hom` is literally the morphism type between the two pulled-back sheaves along `T.hom`. This
packages the source-fiber cast in a transport-stable form before the raw terminal-component
computation. -/
theorem localized_pseudofunctorOver_terminal_source_fiber_eq_mapObjHom
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w)) :
    (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
      (Opposite.op (Over.mk (𝟙 T.left)))) =
      ((((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj M) ⟶
        (((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj N)) := by
  -- Expose `T`; then both sides are exactly the same pulled-back Hom type by definition of
  -- `Pseudofunctor.presheafHom` and the terminal object of the slice over `T.left`.
  cases T
  simp [Pseudofunctor.presheafHom]
  rfl

/-- Helper for Lemma 7.26.4: the source section over `T : Over U` and the terminal-source
section over `Over.mk (𝟙 T.left)` for the restricted Hom presheaf have the same underlying type.
This isolates the exact cast that appears in the remaining terminal-component normalization. -/
theorem localized_pseudofunctorOver_terminal_source_type_eq
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w)) :
    (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T)) =
      (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T.left)))) := by
  -- Route correction: identify both source fibers with the same pulled-back Hom type, rather
  -- than reopening the restricted functor every time the terminal-source cast appears.
  trans ((((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj M) ⟶
      (((J.pseudofunctorOver (Type w)).map T.hom.op.toLoc).toFunctor.obj N))
  · -- The direct source fiber is the defining value of `presheafHom` at `T`.
    cases T
    simp [Pseudofunctor.presheafHom]
  · -- The restricted terminal-source fiber is the same pulled-back Hom type by the new stable
    -- terminal-fiber identification.
    exact
      (localized_pseudofunctorOver_terminal_source_fiber_eq_mapObjHom
        (J := J) (U := U) (T := T) M N).symm

/-- Helper for Lemma 7.26.4: the terminal-source type equality can also be used in the reverse
direction when the raw terminal-component computation is converted back to the original source
fiber. -/
theorem localized_pseudofunctorOver_terminal_source_type_eq_symm
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w)) :
    (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
      (Opposite.op (Over.mk (𝟙 T.left)))) =
      (((J.pseudofunctorOver (Type w)).presheafHom M N).obj (Opposite.op T)) := by
  -- Reuse the forward identification and reverse it once, so later proofs avoid ad hoc casts.
  simpa using
    (localized_pseudofunctorOver_terminal_source_type_eq
      (J := J) (U := U) (T := T) M N).symm

/-- Helper for Lemma 7.26.4: casting a terminal restricted source section along the stable
terminal-fiber identification does not change the underlying morphism after exposing `T`; the
result is heterogeneously equal to the original section. This records the transport layer needed
before comparing the terminal component itself. -/
theorem localized_pseudofunctorOver_terminal_source_fiber_cast_heq
    {T : Over U}
    (M N : Sheaf (J.over U) (Type w))
    (z :
      (((Over.map T.hom).op ⋙ (J.pseudofunctorOver (Type w)).presheafHom M N).obj
        (Opposite.op (Over.mk (𝟙 T.left))))) :
    HEq
      (cast
      (localized_pseudofunctorOver_terminal_source_fiber_eq_mapObjHom
        (J := J) (U := U) (T := T) M N)
      z)
      z := by
  -- After exposing `T`, the cast is the identity on the literal pulled-back Hom type.
  cases T
  simp [Pseudofunctor.presheafHom]


end

end GrothendieckTopology
end CategoryTheory
