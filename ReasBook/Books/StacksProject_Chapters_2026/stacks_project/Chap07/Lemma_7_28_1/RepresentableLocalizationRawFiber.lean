module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_28_1.RepresentableLocalizationSigma

@[expose] public section

open CategoryTheory
open Opposite

universe u v w

noncomputable section

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/-- Helper for Lemma 7.28.1: the raw enlarged representable presheaf `h_U` before
sheafification. -/
abbrev uliftRepresentablePresheaf (U : C) : Cᵒᵖ ⥤ Type (max w u v) :=
  (CategoryTheory.uliftYoneda.{max w u v}.obj U : Cᵒᵖ ⥤ Type (max w u v))

/-- Helper for Lemma 7.28.1: restriction along a morphism in `C/U` preserves the raw fibre
condition over the representable presheaf `h_U`. -/
theorem uliftFiberPresheafOverRepresentable_map_property
    {U : C} (P : Over (uliftRepresentablePresheaf.{u, v, w} U))
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    (s : { t : P.left.obj (op X.unop.left) //
        (P.hom.app (op X.unop.left) t).down = X.unop.hom }) :
    (P.hom.app (op Y.unop.left) (P.left.map f.unop.left.op s.1)).down = Y.unop.hom := by
  -- Naturality of the structure map moves the fibre equation through the restriction map.
  have hnat := congrFun (P.hom.naturality f.unop.left.op) s.1
  dsimp at hnat
  rw [s.2] at hnat
  exact Eq.trans (congrArg ULift.down hnat) (Over.w f.unop)

/-- Helper for Lemma 7.28.1: the restriction map on raw fibres over `h_U`. -/
def uliftFiberPresheafOverRepresentable_map
    {U : C} (P : Over (uliftRepresentablePresheaf.{u, v, w} U))
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    { t : P.left.obj (op X.unop.left) //
        (P.hom.app (op X.unop.left) t).down = X.unop.hom } →
      { t : P.left.obj (op Y.unop.left) //
        (P.hom.app (op Y.unop.left) t).down = Y.unop.hom } :=
  fun s ↦
    ⟨P.left.map f.unop.left.op s.1,
      uliftFiberPresheafOverRepresentable_map_property P f s⟩

/-- Helper for Lemma 7.28.1: raw fibre restriction is the identity on identity morphisms. -/
theorem uliftFiberPresheafOverRepresentable_map_id
    {U : C} (P : Over (uliftRepresentablePresheaf.{u, v, w} U))
    (X : (Over U)ᵒᵖ) :
    uliftFiberPresheafOverRepresentable_map P (𝟙 X) = id := by
  -- The underlying presheaf restriction is the identity, and the fibre proof is irrelevant.
  funext s
  apply Subtype.ext
  simp [uliftFiberPresheafOverRepresentable_map]

/-- Helper for Lemma 7.28.1: raw fibre restrictions compose as the underlying presheaf
restrictions do. -/
theorem uliftFiberPresheafOverRepresentable_map_comp
    {U : C} (P : Over (uliftRepresentablePresheaf.{u, v, w} U))
    {X Y Z : (Over U)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    uliftFiberPresheafOverRepresentable_map P (f ≫ g) =
      uliftFiberPresheafOverRepresentable_map P g ∘
        uliftFiberPresheafOverRepresentable_map P f := by
  -- Composition is inherited from the presheaf `P.left`.
  funext s
  apply Subtype.ext
  simp [uliftFiberPresheafOverRepresentable_map, FunctorToTypes.map_comp_apply]

/-- Helper for Lemma 7.28.1: a morphism over the raw representable preserves the fibre
condition objectwise. -/
theorem uliftFiberPresheafOverRepresentable_hom_property
    {U : C} {P Q : Over (uliftRepresentablePresheaf.{u, v, w} U)} (α : P ⟶ Q)
    (X : (Over U)ᵒᵖ)
    (s : { t : P.left.obj (op X.unop.left) //
        (P.hom.app (op X.unop.left) t).down = X.unop.hom }) :
    (Q.hom.app (op X.unop.left) (α.left.app (op X.unop.left) s.1)).down =
      X.unop.hom := by
  -- The commuting triangle in the over-category keeps the section over the same arrow.
  have hcomp := congrFun (NatTrans.congr_app (Over.w α) (op X.unop.left)) s.1
  dsimp at hcomp
  exact (congrArg ULift.down hcomp).trans s.2

/-- Helper for Lemma 7.28.1: the objectwise map on raw fibres induced by a morphism over
`h_U`. -/
def uliftFiberPresheafOverRepresentable_hom
    {U : C} {P Q : Over (uliftRepresentablePresheaf.{u, v, w} U)} (α : P ⟶ Q)
    (X : (Over U)ᵒᵖ) :
    { t : P.left.obj (op X.unop.left) //
        (P.hom.app (op X.unop.left) t).down = X.unop.hom } →
      { t : Q.left.obj (op X.unop.left) //
        (Q.hom.app (op X.unop.left) t).down = X.unop.hom } :=
  fun s ↦ ⟨α.left.app (op X.unop.left) s.1,
    uliftFiberPresheafOverRepresentable_hom_property α X s⟩

/-- Helper for Lemma 7.28.1: the raw fibre construction as a functor from objects over `h_U` to
presheaves on the localized site `C/U`. -/
def uliftFiberPresheafOverRepresentable (U : C) :
    Over (uliftRepresentablePresheaf.{u, v, w} U) ⥤ (Over U)ᵒᵖ ⥤ Type (max w u v) where
  obj P :=
    { obj := fun X =>
        { t : P.left.obj (op X.unop.left) //
          (P.hom.app (op X.unop.left) t).down = X.unop.hom }
      map := uliftFiberPresheafOverRepresentable_map P
      map_id := uliftFiberPresheafOverRepresentable_map_id P
      map_comp := uliftFiberPresheafOverRepresentable_map_comp P }
  map α :=
    { app := uliftFiberPresheafOverRepresentable_hom α
      naturality := by
        intro X Y f
        funext s
        apply Subtype.ext
        -- Naturality of the left component is the whole functoriality check on raw fibres.
        simpa [uliftFiberPresheafOverRepresentable_hom,
          uliftFiberPresheafOverRepresentable_map] using
          congrFun (α.left.naturality f.unop.left.op) s.1 }
  map_id P := by
    -- The fibre map induced by the identity over-object morphism is pointwise the identity.
    ext X s
    rfl
  map_comp α β := by
    -- Composition is inherited pointwise from the over-object left components.
    ext X s
    rfl

/-- Helper for Lemma 7.28.1: the first coordinate of the enlarged sigma model for
`j_{U!}^{PSh} G` is natural in the base object. -/
theorem uliftLocalizationOverRepresentable_hom_naturality
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {V Y : C} (f : Y ⟶ V) :
    (fun x ↦ ULift.up ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y).hom
      (((Over.forget U).op.lan.obj G).map f.op x)).1) =
    fun x ↦ (uliftRepresentablePresheaf.{u, v, w} U).map f.op
      (ULift.up ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).hom x).1) := by
  -- The sigma-model map formula identifies the first coordinate after restriction with
  -- precomposition of the original first coordinate by `f`.
  funext x
  apply ULift.ext
  simpa [uliftRepresentablePresheaf] using congrArg Sigma.fst
    (uliftLocalizationLeftKanExtensionObjIsoSigma_hom_map (U := U) G f x)

/-- Helper for Lemma 7.28.1: the raw source-side localization object over the enlarged
representable presheaf `h_U`. -/
noncomputable def uliftLocalizationOverRepresentable
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) :
    Over (uliftRepresentablePresheaf.{u, v, w} U) :=
  Over.mk (Y := ((Over.forget U).op.lan.obj G))
    { app := fun V x ↦
        ULift.up ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G (unop V)).hom x).1
      naturality := by
        -- The structure map is the first coordinate of the left-Kan sigma model.
        intro V Y f
        exact uliftLocalizationOverRepresentable_hom_naturality (U := U) G f.unop }

/-- Helper for Lemma 7.28.1: for the raw localization object over `h_U`, the fibre condition
over `X.hom` is exactly the sigma-model first-coordinate condition. -/
theorem uliftLocalizationOverRepresentable_fiber_condition
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) (X : Over U)
    (s : (((Over.forget U).op.lan.obj G).obj (op X.left))) :
    ((uliftLocalizationOverRepresentable (U := U) G).hom.app (op X.left) s).down =
        X.hom ↔
      ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
        X.hom := by
  -- The raw structure map is the first coordinate of the sigma model, wrapped in `ULift`.
  simp [uliftLocalizationOverRepresentable]

/-- Helper for Lemma 7.28.1: the first coordinate of a restricted raw fibre point is the target
slice arrow. -/
theorem uliftLocalizationFiber_firstCoordinate
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {X Y : Over U}
    (f : op X ⟶ op Y)
    (s : (((Over.forget U).op.lan.obj G).obj (op X.left)))
    (hs : ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
      X.hom) :
    ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y.left).hom
        (((Over.forget U).op.lan.obj G).map f.unop.left.op s)).1 =
      Y.hom := by
  -- The sigma-model restriction formula updates the first coordinate by `f.unop.left`.
  have hmap :=
    congrArg
      (fun z : Σ φ : Y.left ⟶ U, G.obj (op (Over.mk φ)) ↦ z.1)
      (uliftLocalizationLeftKanExtensionObjIsoSigma_hom_map (U := U) G f.unop.left s)
  dsimp at hmap
  rw [hs] at hmap
  exact hmap.trans (Over.w f.unop)

/-- Helper for Lemma 7.28.1: the sigma-fibre equivalence reads off the transported second
coordinate. -/
theorem uliftLocalizationFiberSigmaIso_hom_eq_snd
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) (X : Over U)
    (s : (((Over.forget U).op.lan.obj G).obj (op X.left)))
    (hs : ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
      X.hom) :
    HEq
      ((uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩)
      ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).2 := by
  -- Unfold the fibre equivalence over `X`; after substituting the first coordinate, it returns
  -- the second sigma coordinate.
  let e := uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left
  rcases hσ : e.hom s with ⟨a, x⟩
  have hs' : a = X.hom := by
    simpa [e, hσ] using hs
  change HEq ((uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩) x
  subst hs'
  simp [uliftLocalizationFiberSigmaIso, e, hσ]
  cases X
  rfl

/-- Helper for Lemma 7.28.1: once the first sigma coordinate is fixed, the whole sigma point is
determined by the raw fibre equivalence. -/
theorem uliftLocalizationFiberSigma_eq_pair
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) (X : Over U)
    (s : (((Over.forget U).op.lan.obj G).obj (op X.left)))
    (hs : ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
      X.hom) :
    (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s =
      ⟨X.hom, (uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩⟩ := by
  -- Pair the first-coordinate equation with the heterogeneous second-coordinate computation.
  refine (Sigma.mk.inj_iff).2 ?_
  constructor
  · exact hs
  · exact (uliftLocalizationFiberSigmaIso_hom_eq_snd (U := U) G X s hs).symm

/-- Helper for Lemma 7.28.1: after substituting a source fibre point into the sigma-model
restriction formula, the target point has the displayed raw second coordinate. -/
theorem uliftLocalizationFiber_map_sigma_raw
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {X Y : Over U}
    (f : op X ⟶ op Y)
    (s : (((Over.forget U).op.lan.obj G).obj (op X.left)))
    (hs : ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
      X.hom) :
    (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y.left).hom
        (((Over.forget U).op.lan.obj G).map f.unop.left.op s) =
      ⟨f.unop.left ≫ X.hom,
        G.map
          (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from
            Over.homMk f.unop.left).op
          ((uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩)⟩ := by
  -- Substitute the source fibre pair into the sigma-model map formula.
  have hmap :=
    uliftLocalizationLeftKanExtensionObjIsoSigma_hom_map (U := U) G f.unop.left s
  rw [uliftLocalizationFiberSigma_eq_pair (U := U) G X s hs] at hmap
  simpa using hmap

/-- Helper for Lemma 7.28.1: the inverse raw fibre point maps to the expected sigma pair. -/
theorem uliftLocalizationFiber_inv_sigma_eq_pair
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) (Y : Over U)
    (y : G.obj (op Y)) :
    (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y.left).hom
        ↑((uliftLocalizationFiberSigmaIso (U := U) G Y).inv y) =
      ⟨Y.hom, y⟩ := by
  -- The inverse fibre point is characterized by the sigma pair over `Y.hom`.
  have hpair :=
    (uliftLocalizationFiberSigma_eq_pair (U := U) G Y
      (((uliftLocalizationFiberSigmaIso (U := U) G Y).inv y).1)
      (((uliftLocalizationFiberSigmaIso (U := U) G Y).inv y).2))
  have hcancel :
      (uliftLocalizationFiberSigmaIso (U := U) G Y).hom
          ((uliftLocalizationFiberSigmaIso (U := U) G Y).inv y) = y :=
    congrFun (uliftLocalizationFiberSigmaIso (U := U) G Y).inv_hom_id y
  simpa [hcancel] using hpair

/-- Helper for Lemma 7.28.1: eliminating a displayed triangle equation removes the dependent
transport in a raw restriction map. -/
theorem uliftLocalizationFiber_displayed_map_transport_homMk
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {X : Over U}
    {Y' : C} {Yhom : Y' ⟶ U}
    (g : Y' ⟶ X.left) (hg : g ≫ X.hom = Yhom) (z : G.obj (op X)) :
    Eq.ndrec
        (motive := fun a : Y' ⟶ U => G.obj (op (Over.mk a)))
        (G.map
          (show Over.mk (g ≫ X.hom) ⟶ Over.mk X.hom from Over.homMk g).op
          z)
        hg =
      G.map (Over.homMk g hg).op z := by
  -- With the triangle equality eliminated, both displayed morphisms are definitionally equal.
  cases hg
  rfl

/-- Helper for Lemma 7.28.1: the displayed map in the sigma-model formula is the literal
presheaf restriction along the arrow in `(C/U)ᵒᵖ`. -/
theorem uliftLocalizationFiber_displayed_map_transport
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {X Y : Over U}
    (f : op X ⟶ op Y) (z : G.obj (op X)) :
    Eq.ndrec
        (motive := fun a : Y.left ⟶ U => G.obj (op (Over.mk a)))
        (G.map
          (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from
            Over.homMk f.unop.left).op
          z)
        (Over.w f.unop) =
      G.map f z := by
  -- Put the target slice object in `Over.mk` form, then use the cast-free `Over.homMk`
  -- computation.
  rcases Over.mk_surjective Y with ⟨Y', Yhom, rfl⟩
  simpa using
    uliftLocalizationFiber_displayed_map_transport_homMk (U := U) G
      (X := X) (Y' := Y') (Yhom := Yhom) f.unop.left (Over.w f.unop) z

/-- Helper for Lemma 7.28.1: after aligning first coordinates, the two raw second-coordinate
restrictions are heterogeneously equal. -/
theorem uliftLocalizationFiber_second_coordinate_heq
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {X Y : Over U}
    (f : op X ⟶ op Y)
    (x :
      (((uliftFiberPresheafOverRepresentable.{u, v, w} U).obj
          (uliftLocalizationOverRepresentable (U := U) G)).obj (op X))) :
    G.map f
        ((uliftLocalizationFiberSigmaIso (U := U) G X).hom x) ≍
      G.map
        (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from
          Over.homMk f.unop.left).op
        ((uliftLocalizationFiberSigmaIso (U := U) G X).hom x) := by
  -- Replace the fibre proof by the sigma-model first-coordinate proof and use the transport
  -- computation to remove the displayed cast.
  rcases x with ⟨s, hs⟩
  have hs' :
      ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
        X.hom := by
    simpa [uliftLocalizationOverRepresentable_fiber_condition (U := U) G X s] using hs
  have hz :
      (uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩ =
        (uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs'⟩ := by
    -- The underlying section determines the fibre point; the proof component is irrelevant.
    apply congrArg ((uliftLocalizationFiberSigmaIso (U := U) G X).hom)
    apply Subtype.ext
    rfl
  let z := (uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs'⟩
  have htransport :
      Eq.ndrec
          (motive := fun a : Y.left ⟶ U => G.obj (op (Over.mk a)))
          (G.map
            (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from
              Over.homMk f.unop.left).op z)
          (Over.w f.unop) =
        G.map f z :=
    uliftLocalizationFiber_displayed_map_transport (U := U) G f z
  have hcast :
      cast
          (congrArg
            (fun a : Y.left ⟶ U => G.obj (op (Over.mk a)))
            (Over.w f.unop))
          (G.map
            (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from
              Over.homMk f.unop.left).op z) =
        G.map f z := by
    -- Put the transport equality in cast form so it can be read as a heterogeneous equality.
    simpa [eqRec_eq_cast] using htransport
  have hheq :
      G.map f z ≍
        G.map
          (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from
            Over.homMk f.unop.left).op z := by
    exact ((cast_eq_iff_heq).1 hcast).symm
  simpa [z, hz] using hheq

/-- Helper for Lemma 7.28.1: the inverse fibre equivalence identifies a mapped section with the
canonical target fibre point. -/
theorem uliftLocalizationFiber_inv_map_eq
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {X Y : Over U}
    (f : op X ⟶ op Y)
    (s : (((Over.forget U).op.lan.obj G).obj (op X.left)))
    (hs : ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
      X.hom)
    (hfst :
      ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y.left).hom
          (((Over.forget U).op.lan.obj G).map f.unop.left.op s)).1 = Y.hom) :
    (uliftLocalizationFiberSigmaIso (U := U) G Y).inv
        (G.map f ((uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩)) =
      ⟨((Over.forget U).op.lan.obj G).map f.unop.left.op s, hfst⟩ := by
  cases X
  rename_i X_left X_right X_hom
  cases Y
  rename_i Y_left Y_right Y_hom
  dsimp at hs hfst ⊢
  -- Compare both target fibre points through the sigma model and then cancel the sigma-model
  -- isomorphism.
  have hleft :=
    uliftLocalizationFiber_inv_sigma_eq_pair (U := U) G
      { left := Y_left, right := Y_right, hom := Y_hom }
      (G.map f
        ((uliftLocalizationFiberSigmaIso (U := U) G
          { left := X_left, right := X_right, hom := X_hom }).hom ⟨s, hs⟩))
  have hright :=
    uliftLocalizationFiber_map_sigma_raw (U := U) G
      (X := { left := X_left, right := X_right, hom := X_hom })
      (Y := { left := Y_left, right := Y_right, hom := Y_hom }) f s hs
  have hright' :
      (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y_left).hom
          (((Over.forget U).op.lan.obj G).map f.unop.left.op s) =
        ⟨Y_hom,
          G.map f
            ((uliftLocalizationFiberSigmaIso (U := U) G
              { left := X_left, right := X_right, hom := X_hom }).hom ⟨s, hs⟩)⟩ := by
    -- The first coordinates agree by the over-category triangle; the second coordinates agree
    -- after removing the displayed transport.
    convert hright using 1
    ext
    · exact (Over.w f.unop).symm
    · change
        (G.map f
            ((uliftLocalizationFiberSigmaIso (U := U) G
              { left := X_left, right := X_right, hom := X_hom }).hom ⟨s, hs⟩) ≍
          G.map
            (show Over.mk (f.unop.left ≫ X_hom) ⟶ Over.mk X_hom from
              Over.homMk f.unop.left).op
            ((uliftLocalizationFiberSigmaIso (U := U) G
              { left := X_left, right := X_right, hom := X_hom }).hom ⟨s, hs⟩))
      exact uliftLocalizationFiber_second_coordinate_heq (U := U) G
        (X := { left := X_left, right := X_right, hom := X_hom })
        (Y := { left := Y_left, right := Y_right, hom := Y_hom }) f ⟨s, hs⟩
  apply Subtype.ext
  -- Inject through the sigma chart to identify the underlying left-Kan-extension sections.
  apply (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y_left).toEquiv.injective
  exact hleft.trans hright'.symm

/-- Helper for Lemma 7.28.1: the second coordinate of the mapped raw fibre point is the
presheaf restriction of the source second coordinate. -/
theorem uliftLocalizationFiber_second_coordinate_transport
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {X Y : Over U}
    (f : op X ⟶ op Y)
    (s : (((Over.forget U).op.lan.obj G).obj (op X.left)))
    (hs : ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
      X.hom)
    (hfst :
      ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y.left).hom
          (((Over.forget U).op.lan.obj G).map f.unop.left.op s)).1 = Y.hom) :
    (uliftLocalizationFiberSigmaIso (U := U) G Y).hom
        ⟨((Over.forget U).op.lan.obj G).map f.unop.left.op s, hfst⟩ =
      G.map f ((uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩) := by
  -- Apply the forward fibre equivalence to the subtype equality just proved.
  have hcancel :
      (uliftLocalizationFiberSigmaIso (U := U) G Y).hom
          ((uliftLocalizationFiberSigmaIso (U := U) G Y).inv
            (G.map f ((uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩))) =
        G.map f ((uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩) :=
    congrFun (uliftLocalizationFiberSigmaIso (U := U) G Y).inv_hom_id
      (G.map f ((uliftLocalizationFiberSigmaIso (U := U) G X).hom ⟨s, hs⟩))
  have hmap := congrArg
    (fun t ↦ (uliftLocalizationFiberSigmaIso (U := U) G Y).hom t)
    (uliftLocalizationFiber_inv_map_eq (U := U) G f s hs hfst).symm
  exact hmap.trans hcancel

/-- Helper for Lemma 7.28.1: the raw fibre identity is natural on `(C/U)ᵒᵖ`. -/
theorem uliftLocalizationFiber_map_apply
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v))
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    (s :
      (((uliftFiberPresheafOverRepresentable.{u, v, w} U).obj
          (uliftLocalizationOverRepresentable (U := U) G)).obj X)) :
    (uliftLocalizationFiberSigmaIso (U := U) G Y.unop).hom
        ((((uliftFiberPresheafOverRepresentable.{u, v, w} U).obj
            (uliftLocalizationOverRepresentable (U := U) G)).map f) s) =
      G.map f ((uliftLocalizationFiberSigmaIso (U := U) G X.unop).hom s) := by
  -- Expand the raw fibre restriction once and delegate the dependent transport to the dedicated
  -- second-coordinate lemma.
  cases X using Opposite.rec
  rename_i X
  cases Y using Opposite.rec
  rename_i Y
  cases X
  rename_i X_left X_right X_hom
  cases Y
  rename_i Y_left Y_right Y_hom
  rcases s with ⟨s, hs⟩
  dsimp [uliftFiberPresheafOverRepresentable, uliftFiberPresheafOverRepresentable_map]
  have hs' :
      ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X_left).hom s).1 =
        X_hom := by
    simpa using
      (uliftLocalizationOverRepresentable_fiber_condition (U := U) G
        { left := X_left, right := X_right, hom := X_hom } s).1 hs
  have hfst :
      ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y_left).hom
          (((Over.forget U).op.lan.obj G).map f.unop.left.op s)).1 =
        Y_hom := by
    -- The first coordinate is controlled by the sigma-model restriction formula.
    simpa using uliftLocalizationFiber_firstCoordinate (U := U) G f s hs'
  simpa using uliftLocalizationFiber_second_coordinate_transport
    (U := U) G f s hs' hfst

/-- Helper for Lemma 7.28.1: the raw fibre identity gives a natural isomorphism from the
fibre of the raw localization object back to the original presheaf. -/
theorem uliftLocalizationFiber_naturality
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v))
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    ((uliftFiberPresheafOverRepresentable.{u, v, w} U).obj
        (uliftLocalizationOverRepresentable (U := U) G)).map f ≫
      (uliftLocalizationFiberSigmaIso (U := U) G Y.unop).hom =
    (uliftLocalizationFiberSigmaIso (U := U) G X.unop).hom ≫ G.map f := by
  -- Pointwise, this is the second-coordinate computation above.
  ext s
  simpa using uliftLocalizationFiber_map_apply (U := U) G f s

/-- Helper for Lemma 7.28.1: the raw source-side fibre of `j_{U!}^{PSh} G` over the identity
section is the original presheaf `G`. -/
noncomputable def uliftLocalizationOverRepresentable_fiberIso
    {U : C} (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) :
    (uliftFiberPresheafOverRepresentable.{u, v, w} U).obj
        (uliftLocalizationOverRepresentable (U := U) G) ≅
      G :=
  NatIso.ofComponents
    (fun X ↦ uliftLocalizationFiberSigmaIso (U := U) G X.unop)
    (uliftLocalizationFiber_naturality (U := U) G)

end

end CategoryTheory
