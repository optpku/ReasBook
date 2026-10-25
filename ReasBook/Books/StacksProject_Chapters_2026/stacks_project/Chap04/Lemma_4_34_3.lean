module

public import stacks_project.Chap04.«4_34_2_2»
public import stacks_project.Chap04.«4_34_2_3»

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory
namespace CategoryOver

open BasedNatIso
open BasedNatTrans
open scoped Bicategory BasedFunctor

variable {C : Type*} [Category C]
variable {X Y : CategoryOver C}

/- Domain-style sampling for Lemma 4.34.3:
- primary domain: bicategorical `2`-fibre products in `Cat/C`, specialized to the relative and
  absolute inertia constructions of a morphism in `Cat/C`;
- inspected owner declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `absoluteInertiaIdentitySection`,
  `absoluteInertiaOverMap`,
  `relativeInertiaToAbsoluteInertia`,
  `relativeInertiaMap_obj_α`;
- best owner abstraction: the source-facing square below, expressed directly as a
  `BicategoricalTwoCommutativeSquare` in `Cat/C`;
- source/core/bridge triage:
  `source-facing`: `relativeAbsoluteInertiaSquare`;
  `core/canonical`: `Bicategory.IsFinal (relativeAbsoluteInertiaSquare F)`;
  `bridge/view`: the typed `Cat/C` comparison maps
  `relativeInertiaToAbsoluteInertia`, `absoluteInertiaOverMap`, and
  `absoluteInertiaIdentitySection`;
- primitive-vs-derived split: the square uses only the canonical inertia maps and their
  comparison isomorphism; the `IsFinal` universal property is derived API. -/

abbrev relativeAbsoluteInertiaLeftMap
    (F : X ⥤ᵇ Y) :
    relativeInertiaOver F ⥤ᵇ Y :=
  relativeInertiaStructureMap F ⋙ F

abbrev relativeAbsoluteInertiaTop
    (F : X ⥤ᵇ Y) :
    relativeInertiaOver F ⥤ᵇ absoluteInertiaOver Y :=
  relativeAbsoluteInertiaLeftMap F ⋙ absoluteInertiaIdentitySection Y

noncomputable abbrev relativeAbsoluteInertiaBottom
    (F : X ⥤ᵇ Y) :
    relativeInertiaOver F ⥤ᵇ absoluteInertiaOver Y :=
  relativeInertiaToAbsoluteInertia F ⋙ absoluteInertiaOverMap F

theorem relativeAbsoluteInertiaHom_comm
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    ((relativeAbsoluteInertiaTop F).obj Z).α.hom ≫
        𝟙 ((relativeAbsoluteInertiaTop F).obj Z).x =
      𝟙 ((relativeAbsoluteInertiaTop F).obj Z).x ≫
        ((relativeAbsoluteInertiaBottom F).obj Z).α.hom := by
  simpa [relativeAbsoluteInertiaTop, relativeAbsoluteInertiaBottom,
    relativeAbsoluteInertiaLeftMap, relativeInertiaStructureMap,
    absoluteInertiaIdentitySection, relativeInertiaToAbsoluteInertia,
    absoluteInertiaOverMap, relativeInertiaIdentitySection_obj_α,
    relativeInertiaMap_obj_x] using Z.map_hom_eq_id.symm

theorem relativeAbsoluteInertiaInv_comm
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    ((relativeAbsoluteInertiaBottom F).obj Z).α.hom ≫
        𝟙 ((relativeAbsoluteInertiaBottom F).obj Z).x =
      𝟙 ((relativeAbsoluteInertiaBottom F).obj Z).x ≫
        ((relativeAbsoluteInertiaTop F).obj Z).α.hom := by
  simpa [relativeAbsoluteInertiaTop, relativeAbsoluteInertiaBottom,
    relativeAbsoluteInertiaLeftMap, relativeInertiaStructureMap,
    absoluteInertiaIdentitySection, relativeInertiaToAbsoluteInertia,
    absoluteInertiaOverMap, relativeInertiaIdentitySection_obj_α,
    relativeInertiaMap_obj_x] using Z.map_hom_eq_id

noncomputable def relativeAbsoluteInertiaHom
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    (relativeAbsoluteInertiaTop F).obj Z ⟶ (relativeAbsoluteInertiaBottom F).obj Z :=
  { φ := 𝟙 _
    comm := relativeAbsoluteInertiaHom_comm F Z }

noncomputable def relativeAbsoluteInertiaInv
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    (relativeAbsoluteInertiaBottom F).obj Z ⟶ (relativeAbsoluteInertiaTop F).obj Z :=
  { φ := 𝟙 _
    comm := relativeAbsoluteInertiaInv_comm F Z }

noncomputable def relativeAbsoluteInertiaObjIso
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    (relativeAbsoluteInertiaTop F).obj Z ≅ (relativeAbsoluteInertiaBottom F).obj Z where
  hom := relativeAbsoluteInertiaHom F Z
  inv := relativeAbsoluteInertiaInv F Z
  hom_inv_id := by
    apply RelativeInertiaHom.ext
    change (relativeAbsoluteInertiaHom F Z).φ ≫
        (relativeAbsoluteInertiaInv F Z).φ =
      𝟙 ((relativeAbsoluteInertiaTop F).obj Z).x
    change 𝟙 (F.obj Z.x) ≫ 𝟙 (F.obj Z.x) = 𝟙 (F.obj Z.x)
    simp
  inv_hom_id := by
    apply RelativeInertiaHom.ext
    change (relativeAbsoluteInertiaInv F Z).φ ≫
        (relativeAbsoluteInertiaHom F Z).φ =
      𝟙 ((relativeAbsoluteInertiaBottom F).obj Z).x
    change 𝟙 (F.obj Z.x) ≫ 𝟙 (F.obj Z.x) = 𝟙 (F.obj Z.x)
    simp

noncomputable def relativeAbsoluteInertiaComparisonNatIso
    (F : X ⥤ᵇ Y) :
    (relativeAbsoluteInertiaTop F).toFunctor ≅
      (relativeAbsoluteInertiaBottom F).toFunctor :=
  NatIso.ofComponents
    (fun Z ↦ relativeAbsoluteInertiaObjIso F Z)
    (fun {Z Z'} f ↦ by
      apply RelativeInertiaHom.ext
      change ((relativeAbsoluteInertiaTop F).map f).φ ≫
          (relativeAbsoluteInertiaHom F Z').φ =
        (relativeAbsoluteInertiaHom F Z).φ ≫
          ((relativeAbsoluteInertiaBottom F).map f).φ
      change F.map f.φ ≫ 𝟙 (F.obj Z'.x) = 𝟙 (F.obj Z.x) ≫ F.map f.φ
      simp)

theorem relativeAbsoluteInertiaComparison_over_id
    (F : X ⥤ᵇ Y) :
    eqToHom (relativeAbsoluteInertiaTop F).w.symm ≫
        Functor.whiskerRight
          (relativeAbsoluteInertiaComparisonNatIso F).hom
          (absoluteInertiaOver Y).p ≫
      eqToHom (relativeAbsoluteInertiaBottom F).w =
        𝟙 (relativeInertiaOver F).p := by
  -- Evaluate the comparison at an arbitrary relative inertia object and compute the three pieces
  -- of the composite explicitly.
  ext Z
  cases Z with
  | mk x α hα =>
    have htop :
        (eqToHom (relativeAbsoluteInertiaTop F).w.symm).app
            { x := x, α := α, map_hom_eq_id := hα } =
          eqToHom (F.w_obj x).symm := by
      simp only [BasedFunctor.comp_assoc, BasedFunctor.comp_toFunctor, Functor.comp_obj,
        eqToHom_app]
      exact congrArg eqToHom (Subsingleton.elim _ _)
    have hmid :
        (Functor.whiskerRight
            (relativeAbsoluteInertiaComparisonNatIso F).hom
            (absoluteInertiaOver Y).p).app
            { x := x, α := α, map_hom_eq_id := hα } =
          𝟙 (Y.p.obj (F.obj x)) := by
      -- The whiskered component is the base image of the identity comparison on `F.obj x`.
      change
        (absoluteInertiaOver Y).p.map
            (relativeAbsoluteInertiaObjIso F
              { x := x, α := α, map_hom_eq_id := hα }).hom =
          𝟙 (Y.p.obj (F.obj x))
      change Y.p.map (𝟙 (F.obj x)) = 𝟙 (Y.p.obj (F.obj x))
      simp
    have hbot :
        (eqToHom (relativeAbsoluteInertiaBottom F).w).app
            { x := x, α := α, map_hom_eq_id := hα } =
          eqToHom (F.w_obj x) := by
      simp only [BasedFunctor.comp_toFunctor, Functor.comp_obj, eqToHom_app]
      exact congrArg eqToHom (Subsingleton.elim _ _)
    simp only [NatTrans.comp_app]
    rw [htop, hmid, hbot]
    calc
      eqToHom (F.w_obj x).symm ≫ 𝟙 (Y.p.obj (F.obj x)) ≫ eqToHom (F.w_obj x)
          = eqToHom (F.w_obj x).symm ≫ eqToHom (F.w_obj x) := by
              simp
      _ = eqToHom ((F.w_obj x).symm.trans (F.w_obj x)) := by
            exact CategoryTheory.eqToHom_trans (F.w_obj x).symm (F.w_obj x)
      _ = 𝟙 ((relativeInertiaOver F).p.obj { x := x, α := α, map_hom_eq_id := hα }) := by
            change 𝟙 (X.p.obj x) = 𝟙 (X.p.obj x)
            rfl

noncomputable def relativeAbsoluteInertiaComparison
    (F : X ⥤ᵇ Y) :
    relativeAbsoluteInertiaTop F ≅ relativeAbsoluteInertiaBottom F :=
  let η : relativeAbsoluteInertiaTop F ⟶ relativeAbsoluteInertiaBottom F :=
    of_over_id
      (relativeAbsoluteInertiaComparisonNatIso F).hom
      (relativeAbsoluteInertiaComparison_over_id F)
  mkNatIso (relativeAbsoluteInertiaComparisonNatIso F) η.isHomLift'

/-- Helper for Lemma 4.34.3: the ambient bicategory of competing squares for the cospan
`\mathcal S' \to \mathcal I_{\mathcal S'} \leftarrow \mathcal I_{\mathcal S}`. -/
private abbrev relativeAbsoluteInertiaSquareShape
    (F : X ⥤ᵇ Y) :=
  let G : absoluteInertiaOver X ⟶ absoluteInertiaOver Y := absoluteInertiaOverMap F
  BicategoricalTwoCommutativeSquare
    (absoluteInertiaIdentitySection Y : Y ⟶ absoluteInertiaOver Y)
    G

/-- Helper for Lemma 4.34.3: the comparison with the identity section forces the image of the
chosen automorphism in `\mathcal I_{\mathcal S}` to become the identity in
`\mathcal I_{\mathcal S'}`. -/
private theorem identity_section_comparison_forces_image_id
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (T : S.obj.obj) :
    F.toFunctor.map ((S.q.obj T).α.hom) = 𝟙 (F.obj ((S.q.obj T).x)) := by
  -- The component of the square comparison says that the identity automorphism on `S.p.obj T`
  -- coincides with the image of the automorphism carried by `S.q.obj T`.
  have hcomm :
      (S.ψ.hom.app T).φ =
        (S.ψ.hom.app T).φ ≫ F.toFunctor.map ((S.q.obj T).α.hom) := by
    have hcomm' := (S.ψ.hom.app T).comm
    change 𝟙 (S.p.obj T) ≫ (S.ψ.hom.app T).φ =
        (S.ψ.hom.app T).φ ≫ F.toFunctor.map ((S.q.obj T).α.hom) at hcomm'
    simpa [Category.id_comp] using hcomm'
  let τ := (BasedNatTrans.forgetful S.obj (absoluteInertiaOver Y)).mapIso S.ψ
  haveI : IsIso (S.ψ.hom.app T).φ := by
    refine ⟨⟨(τ.app T).inv.φ, ?_, ?_⟩⟩
    · change ((τ.app T).hom ≫ (τ.app T).inv).φ =
          𝟙 ((CategoryTheory.relativeInertiaIdentitySection Y.p).obj (S.p.obj T)).x
      exact congrArg RelativeInertiaHom.φ (τ.app T).hom_inv_id
    · change (S.ψ.inv.app T ≫ S.ψ.hom.app T).φ = 𝟙 (F.obj (S.q.obj T).x)
      change ((τ.app T).inv ≫ (τ.app T).hom).φ = 𝟙 (F.obj (S.q.obj T).x)
      simpa using congrArg RelativeInertiaHom.φ (τ.app T).inv_hom_id
  -- Since the comparison component is an isomorphism, right-cancellation isolates the image
  -- automorphism.
  symm
  apply (cancel_epi (S.ψ.hom.app T).φ).1
  simpa [Category.comp_id] using hcomm

/-- Helper for Lemma 4.34.3: forgetting the extra proof field of a relative inertia object is
faithful on morphisms. -/
private theorem relativeInertiaToAbsoluteInertia_map_injective
    (F : X ⥤ᵇ Y)
    {A B : RelativeInertiaObject F.toFunctor}
    {f g : A ⟶ B}
    (h :
      (relativeInertiaToAbsoluteInertia F).toFunctor.map f =
        (relativeInertiaToAbsoluteInertia F).toFunctor.map g) :
    f = g := by
  -- Both relative-inertia morphisms are determined by the same underlying arrow in `X`.
  apply RelativeInertiaHom.ext
  simpa [relativeInertiaToAbsoluteInertia, relativeInertiaMap_map_hom] using
    congrArg RelativeInertiaHom.φ h

/-- Helper for Lemma 4.34.3: a based natural transformation is determined by its underlying
ordinary natural transformation. -/
private theorem basedNatTrans_ext_toNatTrans
    {A B : CategoryOver C}
    {F G : A ⥤ᵇ B}
    {η θ : BasedNatTrans F G}
    (h : η.toNatTrans = θ.toNatTrans) :
    η = θ := by
  cases η with
  | mk η hη =>
      cases θ with
      | mk θ hθ =>
          cases h
          rfl

/-- Helper for Lemma 4.34.3: a lift condition in the absolute inertia is equivalent to the same
lift condition on the underlying arrow in the ambient category. -/
private theorem absoluteInertia_isHomLift_iff_underlying
    {Z : CategoryOver C}
    {A B : RelativeInertiaObject Z.toBase.toFunctor}
    {R S : C}
    {f : R ⟶ S}
    {φ : A ⟶ B} :
    (absoluteInertiaOver Z).p.IsHomLift f φ ↔ Z.p.IsHomLift f φ.φ := by
  -- Unfolding the packaged absolute inertia exposes the same base projection on the underlying
  -- arrow in `Z`.
  constructor
  · intro h
    let _ : (absoluteInertiaOver Z).p.IsHomLift f φ := h
    refine IsHomLift.of_fac' Z.p f φ.φ
      (IsHomLift.domain_eq (absoluteInertiaOver Z).p f φ)
      (IsHomLift.codomain_eq (absoluteInertiaOver Z).p f φ) ?_
    simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver,
      relativeInertiaProjection] using
      (IsHomLift.fac' (absoluteInertiaOver Z).p f φ)
  · intro h
    let _ : Z.p.IsHomLift f φ.φ := h
    refine IsHomLift.of_fac' (absoluteInertiaOver Z).p f φ
      (IsHomLift.domain_eq Z.p f φ.φ)
      (IsHomLift.codomain_eq Z.p f φ.φ) ?_
    simpa [CategoryOver.absoluteInertiaOver, CategoryOver.relativeInertiaOver,
      relativeInertiaProjection] using
      (IsHomLift.fac' Z.p f φ.φ)

/-- The canonical relative/absolute inertia square attached to a morphism in `Cat/\mathcal C` is
a `2`-commutative square in the ambient bicategory `Cat/\mathcal C`. -/
noncomputable def relativeAbsoluteInertiaSquare
    (F : X ⥤ᵇ Y) :=
  let G : absoluteInertiaOver X ⟶ absoluteInertiaOver Y := absoluteInertiaOverMap F
  show BicategoricalTwoCommutativeSquare
      (absoluteInertiaIdentitySection Y : Y ⟶ absoluteInertiaOver Y)
      G from
    { obj := relativeInertiaOver F
      p := relativeAbsoluteInertiaLeftMap F
      q := relativeInertiaToAbsoluteInertia F
      ψ := relativeAbsoluteInertiaComparison F }

/-- Helper for Lemma 4.34.3: the comparison in the canonical relative/absolute inertia square is
objectwise the identity on the image object in `\mathcal S'`. -/
private theorem relativeAbsoluteInertiaSquare_comparison_hom_app_phi
    (F : X ⥤ᵇ Y)
    (Z : RelativeInertiaObject F.toFunctor) :
    ((relativeAbsoluteInertiaSquare F).ψ.hom.app Z).φ = 𝟙 (F.obj Z.x) := by
  rfl

/-- Helper for Lemma 4.34.3: the inverse comparison in the canonical relative/absolute inertia
square is also objectwise the identity on the image object in `\mathcal S'`. -/
private theorem relativeAbsoluteInertiaSquare_comparison_inv_app_phi
    (F : X ⥤ᵇ Y)
    (Z : RelativeInertiaObject F.toFunctor) :
    ((relativeAbsoluteInertiaSquare F).ψ.inv.app Z).φ = 𝟙 (F.obj Z.x) := by
  rfl

/-- Helper for Lemma 4.34.3: the right leg of a competing square canonically upgrades to a
functor landing in the relative inertia, because the square comparison forces the image
automorphism to become trivial in `\mathcal S'`. -/
private noncomputable def relativeAbsoluteInertiaTerminalLift_hom
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F) :
    S.obj ⥤ᵇ relativeInertiaOver F :=
  { toFunctor :=
      { obj := fun T ↦
          { x := (S.q.obj T).x
            α := (S.q.obj T).α
            map_hom_eq_id := identity_section_comparison_forces_image_id F S T }
        map := fun f ↦
          { φ := (S.q.map f).φ
            comm := by
              -- The promoted morphism uses the same intertwining relation as the right leg.
              simpa using (S.q.map f).comm }
        map_id := by
          intro T
          apply RelativeInertiaHom.ext
          change (S.q.map (𝟙 T)).φ = 𝟙 (S.q.obj T).x
          exact congrArg RelativeInertiaHom.φ (S.q.toFunctor.map_id T)
        map_comp := by
          intro T₁ T₂ T₃ f g
          apply RelativeInertiaHom.ext
          change (S.q.map (f ≫ g)).φ = (S.q.map f).φ ≫ (S.q.map g).φ
          exact congrArg RelativeInertiaHom.φ (S.q.toFunctor.map_comp f g) }
    w := by
      -- The promoted functor has the same underlying base projection as the original right leg.
      simpa [CategoryOver.relativeInertiaOver, CategoryOver.absoluteInertiaOver,
        relativeInertiaProjection] using S.q.w }

/-- Helper for Lemma 4.34.3: forgetting the extra relative-inertia proof field recovers the
original right leg of the competing square. -/
private theorem relativeAbsoluteInertiaTerminalLift_right_eq
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F) :
    relativeAbsoluteInertiaTerminalLift_hom F S ⋙ relativeInertiaToAbsoluteInertia F = S.q := by
  rfl

/-- Helper for Lemma 4.34.3: the left comparison of the canonical factorization is obtained by
taking the underlying arrows of the inverse square comparison. -/
private noncomputable def relativeAbsoluteInertiaTerminalLift_leftNatTrans
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F) :
    (relativeAbsoluteInertiaTerminalLift_hom F S ⋙ relativeAbsoluteInertiaLeftMap F).toFunctor ⟶
      S.p.toFunctor where
  app T := (S.ψ.inv.app T).φ
  naturality := by
    intro T T' f
    -- Project the naturality of `S.ψ.inv` to the underlying arrows in `Y`.
    simpa [relativeAbsoluteInertiaTerminalLift_hom, relativeAbsoluteInertiaLeftMap,
      relativeInertiaStructureMap, absoluteInertiaIdentitySection, absoluteInertiaOverMap,
      relativeInertiaToAbsoluteInertia, relativeInertiaMap_map_hom] using
      congrArg RelativeInertiaHom.φ (S.ψ.inv.toNatTrans.naturality f)

/-- Helper for Lemma 4.34.3: the left comparison of the canonical factorization is already a
based natural transformation, because each component of `S.ψ.inv` is vertical over the identity.
-/
private noncomputable def relativeAbsoluteInertiaTerminalLift_left
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F) :
    relativeAbsoluteInertiaTerminalLift_hom F S ⋙ relativeAbsoluteInertiaLeftMap F ⟶ S.p where
  toNatTrans := relativeAbsoluteInertiaTerminalLift_leftNatTrans F S
  isHomLift' := by
    intro T
    -- The comparison component already lifts the identity in the absolute inertia; unfolding the
    -- projection identifies this with the underlying arrow in `Y`.
    exact (absoluteInertia_isHomLift_iff_underlying.mp (S.ψ.inv.isHomLift' T))

/-- Helper for Lemma 4.34.3: the square-hom coherence into the relative/absolute inertia square
reduces objectwise to the underlying equality in `Y`. -/
private theorem square_hom_comm_underlying_phi
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (u : S ⟶ relativeAbsoluteInertiaSquare F)
    (T : S.obj.obj) :
    u.left.app T ≫ (S.ψ.hom.app T).φ = F.map (u.right.app T).φ := by
  -- Evaluate the square-morphism compatibility at `T` and forget the extra inertia proof field.
  have h := congrArg BasedNatTrans.toNatTrans u.comm
  have hT := congrArg (fun τ => τ.app T) h
  have hφ := congrArg RelativeInertiaHom.φ hT
  have hleft :
      (((u.left ▷ Y.absoluteInertiaIdentitySection ≫ S.ψ.hom).toNatTrans.app T)).φ =
        u.left.app T ≫ (S.ψ.hom.app T).φ := by
    rfl
  have hright :
      ((((α_ u.hom (relativeAbsoluteInertiaSquare F).p Y.absoluteInertiaIdentitySection).hom ≫
            u.hom ◁ (relativeAbsoluteInertiaSquare F).ψ.hom ≫
              (α_ u.hom (relativeAbsoluteInertiaSquare F).q (absoluteInertiaOverMap F)).inv ≫
                u.right ▷ absoluteInertiaOverMap F).toNatTrans.app T)).φ =
          (((u.right ▷ absoluteInertiaOverMap F).app T)).φ := by
    have htmp :
        ((u.hom ◁ (relativeAbsoluteInertiaSquare F).ψ.hom).app T).φ ≫
            ((u.right ▷ absoluteInertiaOverMap F).app T).φ =
          ((u.right ▷ absoluteInertiaOverMap F).app T).φ := by
      have hcmp :
          ((u.hom ◁ (relativeAbsoluteInertiaSquare F).ψ.hom).app T).φ =
            𝟙 (F.obj ((u.hom.obj T).x)) := by
        rfl
      rw [hcmp]
      exact Category.id_comp _
    simpa [Bicategory.Strict.associator_eqToIso] using htmp
  have hright' : (((u.right ▷ absoluteInertiaOverMap F).app T)).φ = F.map (u.right.app T).φ := by
    rfl
  have hφ' :
      (((u.left ▷ Y.absoluteInertiaIdentitySection ≫ S.ψ.hom).toNatTrans.app T)).φ =
        ((((α_ u.hom (relativeAbsoluteInertiaSquare F).p Y.absoluteInertiaIdentitySection).hom ≫
            u.hom ◁ (relativeAbsoluteInertiaSquare F).ψ.hom ≫
              (α_ u.hom (relativeAbsoluteInertiaSquare F).q (absoluteInertiaOverMap F)).inv ≫
                u.right ▷ absoluteInertiaOverMap F).toNatTrans.app T)).φ := hφ
  exact hleft.symm.trans (hφ'.trans (hright.trans hright'))

/-- Helper for Lemma 4.34.3: the forward square comparison followed by its inverse is objectwise
the identity on the left leg of a competing square. -/
private theorem square_comparison_hom_inv_app_phi
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (T : S.obj.obj) :
    (S.ψ.hom.app T).φ ≫ (S.ψ.inv.app T).φ = 𝟙 (S.p.obj T) := by
  -- Forget the inertia structure and use the objectwise inverse law of the comparison isomorphism.
  let τ := (BasedNatTrans.forgetful S.obj (absoluteInertiaOver Y)).mapIso S.ψ
  change ((τ.app T).hom ≫ (τ.app T).inv).φ = 𝟙 (S.p.obj T)
  simpa using congrArg RelativeInertiaHom.φ (τ.app T).hom_inv_id

/-- Helper for Lemma 4.34.3: the inverse square comparison followed by the forward comparison is
objectwise the identity on the image object in `\mathcal S'`. -/
private theorem square_comparison_inv_hom_app_phi
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (T : S.obj.obj) :
    (S.ψ.inv.app T).φ ≫ (S.ψ.hom.app T).φ = 𝟙 (F.obj (S.q.obj T).x) := by
  -- Forget the inertia structure and use the objectwise inverse law on the right leg.
  let τ := (BasedNatTrans.forgetful S.obj (absoluteInertiaOver Y)).mapIso S.ψ
  change ((τ.app T).inv ≫ (τ.app T).hom).φ = 𝟙 (F.obj (S.q.obj T).x)
  simpa using congrArg RelativeInertiaHom.φ (τ.app T).inv_hom_id

/-- Helper for Lemma 4.34.3: once the right comparison into the canonical square is fixed, the
left comparison is forced by the inverse of the given square comparison. -/
private theorem relativeAbsoluteInertiaSquare_left_app_from_right
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (u : S ⟶ relativeAbsoluteInertiaSquare F)
    (T : S.obj.obj) :
    u.left.app T = F.map (u.right.app T).φ ≫ (S.ψ.inv.app T).φ := by
  -- Postcompose the square equation by the inverse comparison to isolate the forced left leg.
  have hpost :=
    congrArg
      (fun k ↦ k ≫ (S.ψ.inv.app T).φ)
      (square_hom_comm_underlying_phi F S u T)
  have hleft :
      u.left.app T = u.left.app T ≫ ((S.ψ.hom.app T).φ ≫ (S.ψ.inv.app T).φ) := by
    symm
    have hcomp :=
      congrArg
        (fun k ↦ u.left.app T ≫ k)
        (square_comparison_hom_inv_app_phi F S T)
    calc
      u.left.app T ≫ ((S.ψ.hom.app T).φ ≫ (S.ψ.inv.app T).φ)
          = u.left.app T ≫ 𝟙 (S.p.obj T) := by
              exact hcomp
      _ = u.left.app T := by
        simp
  have hright :
      u.left.app T ≫ ((S.ψ.hom.app T).φ ≫ (S.ψ.inv.app T).φ) =
        F.map (u.right.app T).φ ≫ (S.ψ.inv.app T).φ := by
    simpa [Category.assoc] using hpost
  exact hleft.trans hright

/-- Helper for Lemma 4.34.3: a promoted right leg determines the induced left comparison by
applying `F` to the right component and then using the inverse square comparison of `S`. -/
private noncomputable def relativeAbsoluteInertiaSquare_hom_of_right_leftNatTrans
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (J : S.obj ⥤ᵇ relativeInertiaOver F)
    (ρ : J ⋙ relativeInertiaToAbsoluteInertia F ⟶ S.q) :
    (J ⋙ relativeAbsoluteInertiaLeftMap F).toFunctor ⟶ S.p.toFunctor where
  app T := F.map ((ρ.app T).φ) ≫ (S.ψ.inv.app T).φ
  naturality := by
    intro T T' f
    -- The promoted left leg inherits naturality from the right comparison `ρ` and the inverse of
    -- the original square comparison `S.ψ`.
    have hρ :
        (J.map f).φ ≫ (ρ.app T').φ =
          (ρ.app T).φ ≫ (S.q.map f).φ := by
      simpa [relativeInertiaToAbsoluteInertia, relativeInertiaMap_map_hom] using
        congrArg RelativeInertiaHom.φ (ρ.toNatTrans.naturality f)
    have hψ :
        F.map ((S.q.map f).φ) ≫ (S.ψ.inv.app T').φ =
          (S.ψ.inv.app T).φ ≫ S.p.map f := by
      simpa [relativeAbsoluteInertiaLeftMap, relativeInertiaStructureMap,
        absoluteInertiaIdentitySection, absoluteInertiaOverMap, relativeInertiaMap_map_hom] using
        congrArg RelativeInertiaHom.φ (S.ψ.inv.toNatTrans.naturality f)
    have hρ' :
        F.map ((J.map f).φ) ≫ F.map ((ρ.app T').φ) ≫ (S.ψ.inv.app T').φ =
          F.map ((ρ.app T).φ) ≫ F.map ((S.q.map f).φ) ≫ (S.ψ.inv.app T').φ := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (fun k ↦ F.map k ≫ (S.ψ.inv.app T').φ) hρ
    have hψ' :
        F.map ((ρ.app T).φ) ≫ F.map ((S.q.map f).φ) ≫ (S.ψ.inv.app T').φ =
          F.map ((ρ.app T).φ) ≫ ((S.ψ.inv.app T).φ ≫ S.p.map f) := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ F.map ((ρ.app T).φ) ≫ k) hψ
    change F.map ((J.map f).φ) ≫ (F.map ((ρ.app T').φ) ≫ (S.ψ.inv.app T').φ) =
      (F.map ((ρ.app T).φ) ≫ (S.ψ.inv.app T).φ) ≫ S.p.map f
    rw [hρ']
    rw [hψ']
    simp [Category.assoc]

/-- Helper for Lemma 4.34.3: the left comparison built from a promoted right leg is vertical over
the identity, so it packages to a based natural transformation in `Cat/\mathcal C`. -/
private noncomputable def relativeAbsoluteInertiaSquare_hom_of_right_left
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (J : S.obj ⥤ᵇ relativeInertiaOver F)
    (ρ : J ⋙ relativeInertiaToAbsoluteInertia F ⟶ S.q) :
    J ⋙ relativeAbsoluteInertiaLeftMap F ⟶ S.p where
  toNatTrans := relativeAbsoluteInertiaSquare_hom_of_right_leftNatTrans F S J ρ
  isHomLift' := by
    intro T
    -- The left component is a composite of two arrows over the identity: the right comparison
    -- `ρ.app T` mapped through `F`, followed by the inverse comparison `S.ψ.inv.app T`.
    have hρX :
        X.p.IsHomLift (𝟙 (S.obj.p.obj T)) ((ρ.app T).φ) := by
      exact absoluteInertia_isHomLift_iff_underlying.mp (ρ.isHomLift' T)
    have hFρ :
        Y.p.IsHomLift (𝟙 (S.obj.p.obj T)) (F.map ((ρ.app T).φ)) := by
      exact (F.isHomLift_iff (𝟙 (S.obj.p.obj T)) ((ρ.app T).φ)).2 hρX
    have hψ :
        Y.p.IsHomLift (𝟙 (S.obj.p.obj T)) ((S.ψ.inv.app T).φ) := by
      exact absoluteInertia_isHomLift_iff_underlying.mp (S.ψ.inv.isHomLift' T)
    -- Compose the two vertical lifts over the identity base morphism.
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
      (𝟙 (S.obj.p.obj T)) (F.map ((ρ.app T).φ)) hFρ
      (S.obj.p.obj T) ((S.ψ.inv.app T).φ) hψ

/-- Helper for Lemma 4.34.3: any promoted right leg into the relative inertia determines a square
morphism into the canonical relative/absolute inertia square. -/
private noncomputable def relativeAbsoluteInertiaSquare_hom_of_right
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (J : S.obj ⥤ᵇ relativeInertiaOver F)
    (ρ : J ⋙ relativeInertiaToAbsoluteInertia F ⟶ S.q) :
    S ⟶ relativeAbsoluteInertiaSquare F :=
  { hom := J
    left := relativeAbsoluteInertiaSquare_hom_of_right_left F S J ρ
    right := ρ
    comm := by
      -- The chosen left component was defined so that composing with `S.ψ.hom` collapses to the
      -- right comparison after the inverse/forward comparison cancels.
      apply basedNatTrans_ext_toNatTrans
      ext T
      apply RelativeInertiaHom.ext
      let τ := CategoryTheory.BasedCategory.whiskerRight
        (relativeAbsoluteInertiaSquare_hom_of_right_left F S J ρ)
        Y.absoluteInertiaIdentitySection
      let ρ' : J ⋙ (relativeAbsoluteInertiaSquare F).q ⟶ S.q := ρ
      let σ := CategoryTheory.BasedCategory.whiskerRight ρ' (absoluteInertiaOverMap F)
      have hσ : F.map ((ρ.app T).φ) = (σ.app T).φ := by
        rfl
      have hright :
          (((α_ J (relativeAbsoluteInertiaSquare F).p Y.absoluteInertiaIdentitySection).hom ≫
                J ◁ (relativeAbsoluteInertiaSquare F).ψ.hom ≫
                  (α_ J (relativeAbsoluteInertiaSquare F).q (absoluteInertiaOverMap F)).inv ≫ σ).app
              T).φ =
            (σ.app T).φ := by
        have htmp :
            ((J ◁ (relativeAbsoluteInertiaSquare F).ψ.hom).app T).φ ≫
                (σ.app T).φ =
              (σ.app T).φ := by
          have hcmp :
              ((J ◁ (relativeAbsoluteInertiaSquare F).ψ.hom).app T).φ =
                𝟙 (F.obj ((J.obj T).x)) := by
            rfl
          rw [hcmp]
          exact Category.id_comp _
        simpa [Bicategory.Strict.associator_eqToIso] using htmp
      have hleftside :
          ((CategoryTheory.BasedNatTrans.comp τ S.ψ.hom).app T).φ =
            F.map ((ρ.app T).φ) := by
        have hcomp :
            F.map ((ρ.app T).φ) ≫ ((S.ψ.inv.app T).φ ≫ (S.ψ.hom.app T).φ) =
              F.map ((ρ.app T).φ) ≫ 𝟙 (F.obj ((S.q.obj T).x)) := by
          exact
            congrArg
              (fun k ↦ F.map ((ρ.app T).φ) ≫ k)
              (square_comparison_inv_hom_app_phi F S T)
        have hcancel :
            (F.map ((ρ.app T).φ) ≫ (S.ψ.inv.app T).φ) ≫ (S.ψ.hom.app T).φ =
              F.map ((ρ.app T).φ) := by
          calc
            (F.map ((ρ.app T).φ) ≫ (S.ψ.inv.app T).φ) ≫ (S.ψ.hom.app T).φ
                = F.map ((ρ.app T).φ) ≫ ((S.ψ.inv.app T).φ ≫ (S.ψ.hom.app T).φ) := by
                    rw [Category.assoc]
            _ = F.map ((ρ.app T).φ) ≫ 𝟙 (F.obj ((S.q.obj T).x)) := by
              exact hcomp
            _ = F.map ((ρ.app T).φ) := by
              simp
        have hfirst :
            ((CategoryTheory.BasedNatTrans.comp τ S.ψ.hom).app T).φ =
              (F.map ((ρ.app T).φ) ≫ (S.ψ.inv.app T).φ) ≫ (S.ψ.hom.app T).φ := by
          rfl
        exact hfirst.trans hcancel
      have hfinal :
          ((CategoryTheory.BasedNatTrans.comp τ S.ψ.hom).app T).φ =
            (((α_ J (relativeAbsoluteInertiaSquare F).p Y.absoluteInertiaIdentitySection).hom ≫
                J ◁ (relativeAbsoluteInertiaSquare F).ψ.hom ≫
                  (α_ J (relativeAbsoluteInertiaSquare F).q (absoluteInertiaOverMap F)).inv ≫ σ).app
              T).φ := by
        exact hleftside.trans (hσ.trans hright.symm)
      simpa [τ, CategoryTheory.BasedCategory.whiskerRight, CategoryTheory.BasedNatTrans.comp]
        using hfinal }

/-- Helper for Lemma 4.34.3: the square comparison of a competing square factors canonically
through the relative/absolute inertia square. -/
private noncomputable def relativeAbsoluteInertiaTerminalLift
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F) :
    S ⟶ relativeAbsoluteInertiaSquare F :=
  relativeAbsoluteInertiaSquare_hom_of_right F S
    (relativeAbsoluteInertiaTerminalLift_hom F S) (𝟙 S.q)

/-- Helper for Lemma 4.34.3: the canonical factorization is the specialization of the generic
right-determined square constructor to the promoted right leg and the identity right comparison.
-/
private theorem relativeAbsoluteInertiaTerminalLift_eq_hom_of_right
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F) :
    relativeAbsoluteInertiaTerminalLift F S =
      relativeAbsoluteInertiaSquare_hom_of_right F S
        (relativeAbsoluteInertiaTerminalLift_hom F S) (𝟙 S.q) := by
  -- The terminal lift is defined as this specialization of the generic right-determined
  -- constructor.
  rfl

/-- Helper for Lemma 4.34.3: the right component of a square morphism into the relative/absolute
inertia square lifts uniquely to the apex natural transformation into the canonical factorization.
-/
private noncomputable def hom_to_relativeAbsoluteInertiaTerminalLift_hom
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (u : S ⟶ relativeAbsoluteInertiaSquare F) :
    u.hom ⟶ relativeAbsoluteInertiaTerminalLift_hom F S :=
  { toNatTrans :=
      { app := fun T ↦
          { φ := (u.right.app T).φ
            comm := by
              -- The lifted component keeps the same intertwining relation as the right comparison.
              simpa [relativeAbsoluteInertiaTerminalLift_hom, relativeAbsoluteInertiaSquare,
                relativeInertiaToAbsoluteInertia] using (u.right.app T).comm }
        naturality := by
          intro T T' f
          -- Naturality is inherited from the right comparison of `u`.
          apply RelativeInertiaHom.ext
          simpa [relativeAbsoluteInertiaTerminalLift_hom, relativeInertiaToAbsoluteInertia,
            relativeInertiaMap_map_hom] using
            congrArg RelativeInertiaHom.φ (u.right.toNatTrans.naturality f) }
    isHomLift' := by
      intro T
      -- The right comparison already lifts the identity in the absolute inertia over `X`, and the
      -- underlying arrow is the component of the promoted transformation.
      let φ' : (u.hom.obj T) ⟶ (relativeAbsoluteInertiaTerminalLift_hom F S).obj T :=
        { φ := (u.right.app T).φ
          comm := by
            simpa [relativeAbsoluteInertiaTerminalLift_hom, relativeAbsoluteInertiaSquare,
              relativeInertiaToAbsoluteInertia] using (u.right.app T).comm }
      have hmap : (relativeInertiaToAbsoluteInertia F).map φ' = u.right.app T := by
        apply RelativeInertiaHom.ext
        simp [φ', relativeInertiaToAbsoluteInertia, relativeInertiaMap_map_hom]
      have habs :
          (absoluteInertiaOver X).p.IsHomLift (𝟙 (S.obj.p.obj T))
            ((relativeInertiaToAbsoluteInertia F).map φ') := by
        simpa [hmap] using (u.right.isHomLift' T)
      exact ((relativeInertiaToAbsoluteInertia F).isHomLift_iff (𝟙 (S.obj.p.obj T)) φ').1 habs }

/-- Helper for Lemma 4.34.3: the left component of a `2`-morphism into the canonical
factorization is forced objectwise by the square equation of the original morphism. -/
private theorem hom_to_relativeAbsoluteInertiaTerminalLift_left_comm_app
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (u : S ⟶ relativeAbsoluteInertiaSquare F)
    (T : S.obj.obj) :
    ((hom_to_relativeAbsoluteInertiaTerminalLift_hom F S u ▷ (relativeAbsoluteInertiaSquare F).p ≫
          (relativeAbsoluteInertiaTerminalLift F S).left).app T) =
      u.left.app T := by
  -- Unfold the specialized terminal lift to recover the same right-determined left component.
  change
    (relativeAbsoluteInertiaLeftMap F).map
        ((hom_to_relativeAbsoluteInertiaTerminalLift_hom F S u).app T) ≫
      (relativeAbsoluteInertiaSquare_hom_of_right_left
          F S (relativeAbsoluteInertiaTerminalLift_hom F S) (𝟙 S.q)).app T =
        u.left.app T
  change
    F.map (u.right.app T).φ ≫
      (F.map ((𝟙 S.q : S.q ⟶ S.q).app T).φ ≫ (S.ψ.inv.app T).φ) =
        u.left.app T
  calc
    F.map (u.right.app T).φ ≫
        (F.map ((𝟙 S.q : S.q ⟶ S.q).app T).φ ≫ (S.ψ.inv.app T).φ)
        = F.map (u.right.app T).φ ≫ (S.ψ.inv.app T).φ := by
            have hid :
                F.map ((𝟙 S.q : S.q ⟶ S.q).app T).φ =
                  𝟙 (F.obj ((S.q.obj T).x)) := by
              change F.map (𝟙 ((S.q.obj T).x)) = 𝟙 (F.obj ((S.q.obj T).x))
              simp
            rw [hid]
            simp
    _ = u.left.app T := by
      exact (relativeAbsoluteInertiaSquare_left_app_from_right F S u T).symm

/-- Helper for Lemma 4.34.3: on the right leg, forgetting the promoted apex morphism recovers
exactly the original right comparison. -/
private theorem hom_to_relativeAbsoluteInertiaTerminalLift_right_comm_app
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (u : S ⟶ relativeAbsoluteInertiaSquare F)
    (T : S.obj.obj) :
    ((hom_to_relativeAbsoluteInertiaTerminalLift_hom F S u ▷
          (relativeAbsoluteInertiaSquare F).q ≫
        (relativeAbsoluteInertiaTerminalLift F S).right).app T) =
      u.right.app T := by
  -- The target right comparison of the terminal lift is the identity, so the composite is the
  -- original right component.
  apply RelativeInertiaHom.ext
  change (u.right.app T).φ ≫ 𝟙 ((S.q.obj T).x) = (u.right.app T).φ
  simp

/-- Helper for Lemma 4.34.3: any `2`-morphism into the canonical factorization has the same apex
comparison as the canonical one, because the right leg determines the underlying map into the
relative inertia. -/
private theorem hom_to_relativeAbsoluteInertiaTerminalLift_hom_eq
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (u : S ⟶ relativeAbsoluteInertiaSquare F)
    (η : u ⟶ relativeAbsoluteInertiaTerminalLift F S) :
    η.hom = hom_to_relativeAbsoluteInertiaTerminalLift_hom F S u := by
  -- The right compatibility determines each component after forgetting to absolute inertia, and
  -- that forgetful map is faithful on relative-inertia morphisms.
  apply basedNatTrans_ext_toNatTrans
  ext T
  apply relativeInertiaToAbsoluteInertia_map_injective F
  have hη := congrArg BasedNatTrans.toNatTrans η.right_comm
  have hηT := congrArg (fun τ ↦ τ.app T) hη
  have hηT' :
      ((η.hom ▷ (relativeAbsoluteInertiaSquare F).q).app T) = u.right.app T := by
    change ((η.hom ▷ (relativeAbsoluteInertiaSquare F).q).app T) ≫
        ((𝟙 S.q : S.q ⟶ S.q).app T) = u.right.app T at hηT
    have hid :
        ((η.hom ▷ (relativeAbsoluteInertiaSquare F).q).app T) =
          ((η.hom ▷ (relativeAbsoluteInertiaSquare F).q).app T) ≫
            ((𝟙 S.q : S.q ⟶ S.q).app T) := by
      exact (Category.comp_id _).symm
    simpa [relativeAbsoluteInertiaTerminalLift, relativeAbsoluteInertiaSquare_hom_of_right]
      using hid.trans hηT
  have hright :
      (relativeInertiaToAbsoluteInertia F).map (η.hom.app T) = u.right.app T := by
    simpa [relativeAbsoluteInertiaSquare] using hηT'
  have hcanon :
      (relativeInertiaToAbsoluteInertia F).map
          ((hom_to_relativeAbsoluteInertiaTerminalLift_hom F S u).app T) = u.right.app T := by
    apply RelativeInertiaHom.ext
    simp [hom_to_relativeAbsoluteInertiaTerminalLift_hom, relativeInertiaToAbsoluteInertia,
      relativeInertiaMap_map_hom]
  exact hright.trans hcanon.symm

/-- Helper for Lemma 4.34.3: every square morphism into the relative/absolute inertia square has a
unique `2`-morphism to the canonical factorization. -/
private noncomputable abbrev hom_to_relativeAbsoluteInertiaTerminalLift_unique
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F)
    (u : S ⟶ relativeAbsoluteInertiaSquare F) :
    Unique (u ⟶ relativeAbsoluteInertiaTerminalLift F S) := by
  let η0 : u ⟶ relativeAbsoluteInertiaTerminalLift F S :=
    { hom := hom_to_relativeAbsoluteInertiaTerminalLift_hom F S u
      left_comm := by
        -- The left leg is forced by the square equation of `u`, rewritten using `S.ψ.hom_inv_id`.
        apply basedNatTrans_ext_toNatTrans
        ext T
        -- The left compatibility is the objectwise computation packaged in the helper lemma.
        exact hom_to_relativeAbsoluteInertiaTerminalLift_left_comm_app F S u T
      right_comm := by
        -- On the right, the chosen factorization is literally the same comparison data.
        apply basedNatTrans_ext_toNatTrans
        ext T
        -- The target right leg is the identity, so the helper lemma is already the required
        -- objectwise equality.
        exact hom_to_relativeAbsoluteInertiaTerminalLift_right_comm_app F S u T }
  refine { default := η0, uniq := ?_ }
  intro η
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  exact hom_to_relativeAbsoluteInertiaTerminalLift_hom_eq F S u η

/-- Helper for Lemma 4.34.3: for any competing square, the hom-category into the canonical
relative/absolute inertia square has a terminal object given by the promoted right leg. -/
private theorem relativeAbsoluteInertiaSquare_hasTerminal
    (F : X ⥤ᵇ Y)
    (S : relativeAbsoluteInertiaSquareShape F) :
    Limits.HasTerminal (S ⟶ relativeAbsoluteInertiaSquare F) := by
  -- The promoted right leg is terminal because every competing morphism factors through it
  -- with a unique `2`-morphism.
  let _ : ∀ u : S ⟶ relativeAbsoluteInertiaSquare F,
      Unique (u ⟶ relativeAbsoluteInertiaTerminalLift F S) :=
    fun u ↦ hom_to_relativeAbsoluteInertiaTerminalLift_unique F S u
  exact Limits.hasTerminal_of_unique (relativeAbsoluteInertiaTerminalLift F S)

-- Proof sketch: unpack the relative inertia and the absolute inertias into the canonical square
-- described in the text, then verify the universal property by giving the usual factorization of
-- any competing square through the inertia condition that the induced automorphism in
-- `\mathcal{I}_{\mathcal S'}` is the identity.
/-- Lemma 4.34.3: for a `1`-morphism `F : \mathcal{S} \to \mathcal{S}'` in `Cat/\mathcal C`, the
displayed square
`\mathcal{I}_{\mathcal S / \mathcal S'} \to \mathcal{I}_{\mathcal S} \to
\mathcal{I}_{\mathcal S'} \leftarrow \mathcal S'`
is a strict `2`-fibre product in `Cat/\mathcal C`. -/
theorem relativeAbsoluteInertiaSquare_isTwoFibreProduct
    (F : X ⥤ᵇ Y) :
    Bicategory.IsFinal (relativeAbsoluteInertiaSquare F) := by
  -- Route correction: the workable proof packages the right leg first and then derives the left
  -- comparison from the existing square isomorphism, instead of hand-building both square legs.
  refine ⟨fun S ↦ ?_⟩
  -- The helper theorem packages the terminal-object argument for each competing square.
  exact relativeAbsoluteInertiaSquare_hasTerminal F S

end CategoryOver
end CategoryTheory
