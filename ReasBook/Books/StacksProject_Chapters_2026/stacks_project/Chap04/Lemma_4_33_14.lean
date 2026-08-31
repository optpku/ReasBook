module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import stacks_project.Chap04.Definition_4_33_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Functor.IsHomLift
open scoped Bicategory

universe u v w

namespace CategoryTheory.FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredCategoryOver.{u, v, w, w} C}

noncomputable section

/- Domain-style sampling for Lemma 4.33.14:
- primary domain: fibred categories over a fixed base together with source-facing vertical
  factorizations of a morphism in the fibres;
- sampled owner declarations:
  `FibredCategoryOver`,
  `X ⟶ Y`,
  `Bicategory.Adjunction`,
  `Comma`,
  `ObjectProperty.FullSubcategory`,
  `StructuredArrow`,
  `Functor.Fiber`;
- best owner abstraction: globally, the factorization lives as the full subcategory of the comma
  category `Comma (𝟭 Y.S) (toFunctor F)` cut out by the verticality condition over the common
  base; over a
  fixed fibre `U`, its source-facing view is the structured-arrow owner
  `StructuredArrow y (fiberFunctor F U)`;
- primitive data: a base point `U : C`, a fibre object `y : Y_U`, an object `x : X_U`, and a
  vertical comparison morphism `y ⟶ F_U(x)`;
- derived API here: the bundled fibred factorization object, its projections to `X` and `Y`, the
  canonical source map `X ⟶ X'`, and the resulting fully-faithful / adjunction / fibred
  factorization statements.

Source/core/bridge triage:
- `source-facing`: `adjointFactorization`, `adjointFactorizationFromSource`,
  `adjointFactorizationToSource`, `adjointFactorizationToTarget`, and
  `exists_adjoint_fibred_factorization`;
- `core/canonical`: `FibredCategoryOver`, the ambient owner homs `X ⟶ Y`, `Comma`,
  `Bicategory.Adjunction`, `ObjectProperty.FullSubcategory`,
  `StructuredArrow`, and the fiber functors `fiberFunctor F U`;
- `bridge/view`: the fibrewise structured-arrow description of a fixed fiber of
  `adjointFactorization`, together with any comparison to the later iso-only explicit
  `2`-fibre-product model. -/

/-- The comma-object property cutting out the source-facing factorization of `F`: the comparison
arrow `y ⟶ F(x)` must be vertical over the identity of the common base object. -/
abbrev adjointFactorizationObjectProperty
    (F : X ⟶ Y) :
    ObjectProperty (Comma (𝟭 Y.S) (toFunctor F)) :=
  fun P ↦ Y.p.IsHomLift (𝟙 (Y.p.obj P.left)) P.hom

/-- An object of the source-facing factorization of `F` is a vertical comma object
`y ⟶ F(x)`, organized as the full subcategory of `Comma (𝟭 Y.S) (toFunctor F)` cut out by the verticality
condition. -/
abbrev AdjointFactorizationObject
    (F : X ⟶ Y) :=
  (adjointFactorizationObjectProperty F).FullSubcategory

/-- The projection from the source-facing factorization to the base category `C`. -/
abbrev adjointFactorizationProjection
    (F : X ⟶ Y) :
    AdjointFactorizationObject F ⥤ C :=
  (adjointFactorizationObjectProperty F).ι ⋙ Comma.fst _ _ ⋙ Y.p

/-- The projection from the source-facing factorization to the total category of `X`. -/
abbrev adjointFactorizationToSourceFunctor
    (F : X ⟶ Y) :
    AdjointFactorizationObject F ⥤ X.S :=
  (adjointFactorizationObjectProperty F).ι ⋙ Comma.snd _ _

/-- Helper for Lemma 4.33.14: the two endpoints of a vertical comparison arrow
`y ⟶ F(x)` lie over the same base object. -/
private theorem adjointFactorizationObject_base_eq
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    X.p.obj P.obj.right = Y.p.obj P.obj.left := by
  -- Read the common base point from the verticality hypothesis on the comparison arrow.
  let _ : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
  calc
    X.p.obj P.obj.right = Y.p.obj ((toFunctor F).obj P.obj.right) := by
      symm
      exact Functor.congr_obj (comm F) P.obj.right
    _ = Y.p.obj P.obj.left := by
      exact IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom

theorem adjointFactorizationToSourceFunctor_comm
    (F : X ⟶ Y) :
    adjointFactorizationToSourceFunctor F ⋙ X.p =
      adjointFactorizationProjection F := by
  -- Both functors record the common base point of the vertical arrow `y ⟶ F(x)`.
  refine CategoryTheory.Functor.ext
    (fun P ↦ by
      change X.p.obj P.obj.right = Y.p.obj P.obj.left
      exact adjointFactorizationObject_base_eq F P) ?_
  intro P Q φ
  let _ : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
  let _ : Y.p.IsHomLift (𝟙 (Y.p.obj Q.obj.left)) Q.obj.hom := Q.property
  let hPbase : Y.p.obj ((toFunctor F).obj P.obj.right) = Y.p.obj P.obj.left :=
    IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom
  let hQbase : Y.p.obj ((toFunctor F).obj Q.obj.right) = Y.p.obj Q.obj.left :=
    IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj Q.obj.left)) Q.obj.hom
  change X.p.map φ.hom.right =
    eqToHom ((CategoryTheory.Functor.congr_obj (comm F) P.obj.right).symm.trans hPbase) ≫
      Y.p.map φ.hom.left ≫
        eqToHom (((CategoryTheory.Functor.congr_obj (comm F) Q.obj.right).symm.trans hQbase)).symm
  have hPvert : Y.p.map P.obj.hom = eqToHom hPbase.symm := by
    simpa using (IsHomLift.fac' Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom)
  have hQvert : Y.p.map Q.obj.hom = eqToHom hQbase.symm := by
    simpa using (IsHomLift.fac' Y.p (𝟙 (Y.p.obj Q.obj.left)) Q.obj.hom)
  have hleft :
      eqToHom hPbase ≫ Y.p.map φ.hom.left ≫ eqToHom hQbase.symm =
        Y.p.map ((toFunctor F).map φ.hom.right) := by
    -- Map the comma square to the base and cancel the vertical comparison arrows.
    have h := congrArg (Functor.map Y.p) φ.hom.w
    rw [Functor.map_comp, Functor.map_comp, hPvert, hQvert] at h
    have h0 :
        Y.p.map φ.hom.left ≫ eqToHom hQbase.symm =
          eqToHom hPbase.symm ≫ Y.p.map ((toFunctor F).map φ.hom.right) := by
      simpa using h
    have h' := congrArg (fun k ↦ eqToHom hPbase ≫ k) h0
    simpa [Category.assoc] using h'
  have hcomm :
      X.p.map φ.hom.right =
        eqToHom (CategoryTheory.Functor.congr_obj (comm F) P.obj.right).symm ≫
          Y.p.map ((toFunctor F).map φ.hom.right) ≫
            eqToHom (CategoryTheory.Functor.congr_obj (comm F) Q.obj.right) := by
    have h' := congrArg
      (fun k ↦
        eqToHom (CategoryTheory.Functor.congr_obj (comm F) P.obj.right).symm ≫
          k ≫
            eqToHom (CategoryTheory.Functor.congr_obj (comm F) Q.obj.right))
      (CategoryTheory.Functor.congr_hom (comm F) φ.hom.right)
    simpa [Category.assoc] using h'.symm
  -- Compare the base map of the right component with the mapped comma square.
  calc
    X.p.map φ.hom.right
        = eqToHom (CategoryTheory.Functor.congr_obj (comm F) P.obj.right).symm ≫
            Y.p.map ((toFunctor F).map φ.hom.right) ≫
              eqToHom (CategoryTheory.Functor.congr_obj (comm F) Q.obj.right) := hcomm
    _ = eqToHom (CategoryTheory.Functor.congr_obj (comm F) P.obj.right).symm ≫
          (eqToHom hPbase ≫ Y.p.map φ.hom.left ≫ eqToHom hQbase.symm) ≫
            eqToHom (CategoryTheory.Functor.congr_obj (comm F) Q.obj.right) := by
          have h' := congrArg
            (fun k ↦
              eqToHom (CategoryTheory.Functor.congr_obj (comm F) P.obj.right).symm ≫
                k ≫
                  eqToHom (CategoryTheory.Functor.congr_obj (comm F) Q.obj.right))
            hleft
          simpa [Category.assoc] using h'.symm
    _ = eqToHom ((CategoryTheory.Functor.congr_obj (comm F) P.obj.right).symm.trans hPbase) ≫
          Y.p.map φ.hom.left ≫
            eqToHom (((CategoryTheory.Functor.congr_obj (comm F) Q.obj.right).symm.trans
              hQbase)).symm := by
          simp [Category.assoc]

/-- The projection from the source-facing factorization to the total category of `Y`. -/
abbrev adjointFactorizationToTargetFunctor
    (F : X ⟶ Y) :
    AdjointFactorizationObject F ⥤ Y.S :=
  (adjointFactorizationObjectProperty F).ι ⋙ Comma.fst _ _

/-- Helper for Lemma 4.33.14: a morphism in the source-facing factorization which is vertical for
the projection to `C` remains vertical on its left component in `Y`. -/
private theorem adjointFactorization_projection_vertical_hom_left_isHomLift
    (F : X ⟶ Y) {U : C} {P Q : AdjointFactorizationObject F}
    (η : P ⟶ Q) [(adjointFactorizationProjection F).IsHomLift (𝟙 U) η] :
    Y.p.IsHomLift (𝟙 U) η.hom.left := by
  -- Repackage the left projection as a based functor over the raw projection to `C`.
  let G : BasedCategory.ofFunctor (adjointFactorizationProjection F) ⥤ᵇ Y.toBasedCategory :=
    { toFunctor := adjointFactorizationToTargetFunctor F
      w := rfl }
  -- Then verticality is preserved by the based-functor `IsHomLift` transport.
  exact (G.isHomLift_iff (𝟙 U) η).2
    (show (adjointFactorizationProjection F).IsHomLift (𝟙 U) η from inferInstance)

/-- Helper for Lemma 4.33.14: a morphism in the source-facing factorization which is vertical for
the projection to `C` remains vertical on its right component in `X`. -/
private theorem adjointFactorization_projection_vertical_hom_right_isHomLift
    (F : X ⟶ Y) {U : C} {P Q : AdjointFactorizationObject F}
    (η : P ⟶ Q) [(adjointFactorizationProjection F).IsHomLift (𝟙 U) η] :
    X.p.IsHomLift (𝟙 U) η.hom.right := by
  -- View the right projection as a based functor over `adjointFactorizationProjection`.
  let G : BasedCategory.ofFunctor (adjointFactorizationProjection F) ⥤ᵇ X.toBasedCategory :=
    { toFunctor := adjointFactorizationToSourceFunctor F
      w := adjointFactorizationToSourceFunctor_comm F }
  -- Then verticality is preserved by the based-functor `IsHomLift` transport.
  exact (G.isHomLift_iff (𝟙 U) η).2
    (show (adjointFactorizationProjection F).IsHomLift (𝟙 U) η from inferInstance)

/-- Helper for Lemma 4.33.14: forgetting a morphism in the source-facing factorization to its
source component reflects the same lifting condition over `C`. -/
private theorem adjointFactorization_toSource_hom_isHomLift_iff
    (F : X ⟶ Y) {R S : C} {P Q : AdjointFactorizationObject F}
    (f : R ⟶ S) (η : P ⟶ Q) :
    X.p.IsHomLift f η.hom.right ↔ (adjointFactorizationProjection F).IsHomLift f η := by
  -- Use the source projection as a based functor out of the raw projection category over `C`.
  let G : BasedCategory.ofFunctor (adjointFactorizationProjection F) ⥤ᵇ X.toBasedCategory :=
    { toFunctor := adjointFactorizationToSourceFunctor F
      w := adjointFactorizationToSourceFunctor_comm F }
  -- The underlying right component carries exactly the same base arrow as the full comma morphism.
  simpa [G] using G.isHomLift_iff f η

/-- Helper for Lemma 4.33.14: forgetting a morphism in the source-facing factorization to its
target component reflects the same lifting condition over `C`. -/
private theorem adjointFactorization_toTarget_hom_isHomLift_iff
    (F : X ⟶ Y) {R S : C} {P Q : AdjointFactorizationObject F}
    (f : R ⟶ S) (η : P ⟶ Q) :
    Y.p.IsHomLift f η.hom.left ↔ (adjointFactorizationProjection F).IsHomLift f η := by
  -- The left projection is already a based functor over the raw projection to `C`.
  let G : BasedCategory.ofFunctor (adjointFactorizationProjection F) ⥤ᵇ Y.toBasedCategory :=
    { toFunctor := adjointFactorizationToTargetFunctor F
      w := rfl }
  -- So the left component and the whole comma morphism encode the same lifting datum.
  simpa [G] using G.isHomLift_iff f η

/-- Helper for Lemma 4.33.14: if a morphism is already strongly cartesian, then any other lift of
the same arrow through the same morphism inherits the same strong-cartesian structure. -/
private theorem adjointFactorization_isStronglyCartesian_rebase_of_same_lift
    {𝒮 : Type u} {𝒳 : Type w} [Category.{v} 𝒮] [Category.{w} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S R' S' : 𝒮} {a b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S'} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f' φ] :
    p.IsStronglyCartesian f' φ := by
  -- Both lift witnesses describe the same morphism in the base, so the strong-cartesian
  -- structure can be transported across those lift equalities.
  subst_hom_lift p f' φ
  subst_hom_lift p f φ
  infer_instance

/-- Helper for Lemma 4.33.14: appending the canonical base-change isomorphism from `F.w_obj`
does not change whether a target morphism is a lift. -/
private theorem adjointFactorization_isHomLift_over_target_eq_iff
    (F : X ⟶ Y) {R : C} {x : X.S} {z : Y.S}
    (g : R ⟶ Y.p.obj ((toFunctor F).obj x))
    (θ : z ⟶ (toFunctor F).obj x) :
    Y.p.IsHomLift g θ ↔
      Y.p.IsHomLift
        (g ≫ eqToHom (CategoryTheory.Functor.congr_obj (comm F) x)) θ := by
  -- The extra `eqToHom` only rewrites the codomain to the source-side base coordinates.
  simpa using
    IsHomLift.lift_comp_eqToHom_iff Y.p g θ
      (CategoryTheory.Functor.congr_obj (comm F) x)

/-- Helper for Lemma 4.33.14: the comparison arrow of an object in the factorization records the
base equality between its target component and the image of its source component under `F`. -/
private theorem adjointFactorizationObject_comparison_base_eq
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    Y.p.obj ((toFunctor F).obj P.obj.right) = Y.p.obj P.obj.left := by
  -- Read the codomain equality directly from the verticality of `P.obj.hom`.
  let _ : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
  exact IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom

/-- Helper for Lemma 4.33.14: the chosen pullback of the left component of `P` in `Y` over `h`. -/
private noncomputable abbrev adjointFactorization_projection_pullback_left_obj
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    Y.S :=
  let _ : HasFibers Y.p := HasFibers.canonical Y.p
  (HasFibers.ι V).obj (HasFibers.mkPullback (p := Y.p) h rfl)

/-- Helper for Lemma 4.33.14: the chosen pullback map from the left pullback object to
`P.obj.left`. -/
private noncomputable abbrev adjointFactorization_projection_pullback_left_hom
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    adjointFactorization_projection_pullback_left_obj F P h ⟶ P.obj.left :=
  let _ : HasFibers Y.p := HasFibers.canonical Y.p
  HasFibers.pullbackMap (p := Y.p) h rfl

/-- Helper for Lemma 4.33.14: the chosen pullback map on the left component is strongly
cartesian over `h`. -/
private theorem adjointFactorization_projection_pullback_left_isStronglyCartesian
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    Y.p.IsStronglyCartesian h
      (adjointFactorization_projection_pullback_left_hom F P h) := by
  -- Use the canonical pullback chosen by `HasFibers.canonical`.
  let _ : HasFibers Y.p := HasFibers.canonical Y.p
  simpa [adjointFactorization_projection_pullback_left_obj,
    adjointFactorization_projection_pullback_left_hom] using
    (Functor.IsFibered.isStronglyCartesian_of_isCartesian Y.p h
      (HasFibers.pullbackMap (p := Y.p) h rfl))

/-- Helper for Lemma 4.33.14: the base arrow used to pull back the right component of `P` in
`X`. -/
private abbrev adjointFactorization_projection_pullback_right_base
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    V ⟶ X.p.obj P.obj.right :=
  h ≫ eqToHom (adjointFactorizationObject_base_eq F P).symm

/-- Helper for Lemma 4.33.14: the chosen pullback of the right component of `P` in `X` over the
base arrow induced by `h`. -/
private noncomputable abbrev adjointFactorization_projection_pullback_right_obj
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    X.S :=
  let _ : HasFibers X.p := HasFibers.canonical X.p
  (HasFibers.ι V).obj
    (HasFibers.mkPullback (p := X.p)
      (adjointFactorization_projection_pullback_right_base F P h) rfl)

/-- Helper for Lemma 4.33.14: the chosen pullback map from the right pullback object to
`P.obj.right`. -/
private noncomputable abbrev adjointFactorization_projection_pullback_right_hom
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    adjointFactorization_projection_pullback_right_obj F P h ⟶ P.obj.right :=
  let _ : HasFibers X.p := HasFibers.canonical X.p
  HasFibers.pullbackMap (p := X.p)
    (adjointFactorization_projection_pullback_right_base F P h) rfl

/-- Helper for Lemma 4.33.14: the chosen pullback map on the right component is strongly
cartesian over the induced base arrow in `X`. -/
private theorem adjointFactorization_projection_pullback_right_isStronglyCartesian
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    X.p.IsStronglyCartesian
      (adjointFactorization_projection_pullback_right_base F P h)
      (adjointFactorization_projection_pullback_right_hom F P h) := by
  -- Use the canonical pullback chosen by `HasFibers.canonical` on `X`.
  let _ : HasFibers X.p := HasFibers.canonical X.p
  simpa [adjointFactorization_projection_pullback_right_base,
    adjointFactorization_projection_pullback_right_obj,
    adjointFactorization_projection_pullback_right_hom] using
    (Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p
      (adjointFactorization_projection_pullback_right_base F P h)
      (HasFibers.pullbackMap (p := X.p)
        (adjointFactorization_projection_pullback_right_base F P h) rfl))

/-- Helper for Lemma 4.33.14: the mapped right pullback arrow is viewed over the target-side base
arrow induced by the comparison morphism of `P`. -/
private abbrev adjointFactorization_projection_pullback_target_base
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    V ⟶ Y.p.obj ((toFunctor F).obj P.obj.right) :=
  h ≫ eqToHom (adjointFactorizationObject_comparison_base_eq F P).symm

/-- Helper for Lemma 4.33.14: after rewriting the codomain with `comm F`, the mapped right
pullback arrow still lifts the target-side base arrow induced by `h`. -/
private theorem adjointFactorization_projection_pullback_right_map_isHomLift
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    Y.p.IsHomLift
      (adjointFactorization_projection_pullback_target_base F P h)
      ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h)) := by
  -- First transport the chosen pullback map along `F`, where it still lifts the source-side base
  -- arrow.
  have hmap :
      Y.p.IsHomLift
        (adjointFactorization_projection_pullback_right_base F P h)
        ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h)) :=
    ((toBasedFunctor F).isHomLift_iff
      (adjointFactorization_projection_pullback_right_base F P h)
      (adjointFactorization_projection_pullback_right_hom F P h)).2
      (show X.p.IsHomLift
          (adjointFactorization_projection_pullback_right_base F P h)
          (adjointFactorization_projection_pullback_right_hom F P h) from inferInstance)
  -- Then rewrite the codomain from the source-side base coordinates to the target-side ones.
  exact
    (adjointFactorization_isHomLift_over_target_eq_iff
      (F := F)
      (g := adjointFactorization_projection_pullback_target_base F P h)
      (θ := (toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h))).mpr
      (by
        simpa [adjointFactorization_projection_pullback_target_base,
          adjointFactorization_projection_pullback_right_base,
          adjointFactorizationObject_base_eq,
          adjointFactorizationObject_comparison_base_eq, Category.assoc] using hmap)

/-- Helper for Lemma 4.33.14: the mapped right pullback arrow remains strongly cartesian after
transporting its base arrow to the target-side coordinates. -/
private theorem adjointFactorization_projection_pullback_right_map_isStronglyCartesian
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    Y.p.IsStronglyCartesian
      (adjointFactorization_projection_pullback_target_base F P h)
      ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h)) := by
  let rightHom := adjointFactorization_projection_pullback_right_hom F P h
  -- First rebase the chosen pullback arrow in `X` to its literal projection map.
  have hright :
      X.p.IsStronglyCartesian (X.p.map rightHom) rightHom := by
    letI :
        X.p.IsStronglyCartesian
          (adjointFactorization_projection_pullback_right_base F P h)
          rightHom :=
      adjointFactorization_projection_pullback_right_isStronglyCartesian F P h
    exact
      adjointFactorization_isStronglyCartesian_rebase_of_same_lift
        (p := X.p)
        (f := adjointFactorization_projection_pullback_right_base F P h)
        (f' := X.p.map rightHom)
        rightHom
  -- Then transport that strong-cartesian structure across `F`.
  have hmap :
      Y.p.IsStronglyCartesian
        (Y.p.map ((toFunctor F).map rightHom))
        ((toFunctor F).map rightHom) :=
    FibredCategoryMor.map_stronglyCartesian F rightHom hright
  -- Rebase that strong-cartesian structure to the transported target-side base arrow.
  letI :
      Y.p.IsStronglyCartesian
        (Y.p.map ((toFunctor F).map rightHom))
        ((toFunctor F).map rightHom) :=
    hmap
  letI :
      Y.p.IsHomLift
        (adjointFactorization_projection_pullback_target_base F P h)
        ((toFunctor F).map rightHom) :=
    adjointFactorization_projection_pullback_right_map_isHomLift F P h
  exact
    adjointFactorization_isStronglyCartesian_rebase_of_same_lift
      (p := Y.p)
      (f := Y.p.map ((toFunctor F).map rightHom))
      (f' := adjointFactorization_projection_pullback_target_base F P h)
      ((toFunctor F).map rightHom)

/-- Helper for Lemma 4.33.14: the composite from the left pullback object to `F(P.obj.right)`
is a lift of the target-side base arrow induced by `h`. -/
private theorem adjointFactorization_projection_pullback_left_comp_isHomLift
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    Y.p.IsHomLift
      (adjointFactorization_projection_pullback_target_base F P h)
      (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom) := by
  -- Compose the chosen pullback on the left with the vertical comparison morphism of `P`.
  have hcomp :
      Y.p.IsHomLift h
        (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom) :=
    @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
      h
      (adjointFactorization_projection_pullback_left_hom F P h)
      (adjointFactorization_projection_pullback_left_isStronglyCartesian F P h).toIsHomLift
      (Y.p.obj P.obj.left)
      P.obj.hom
      P.property
  -- Finally rewrite the codomain to the target-side coordinates of `F(P.obj.right)`.
  exact
    (IsHomLift.lift_comp_eqToHom_iff
      Y.p
      h
      (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom)
      (adjointFactorizationObject_comparison_base_eq F P).symm).mpr
      (by simpa [adjointFactorization_projection_pullback_target_base, Category.assoc] using hcomp)

/-- Helper for Lemma 4.33.14: the canonical comparison arrow on the pulled-back comma object. -/
private noncomputable abbrev adjointFactorization_projection_pullback_comparison
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    adjointFactorization_projection_pullback_left_obj F P h ⟶
      (toFunctor F).obj (adjointFactorization_projection_pullback_right_obj F P h) :=
  letI :
      Y.p.IsStronglyCartesian
        (adjointFactorization_projection_pullback_target_base F P h)
        ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h)) :=
    adjointFactorization_projection_pullback_right_map_isStronglyCartesian F P h
  letI :
      Y.p.IsHomLift
        (adjointFactorization_projection_pullback_target_base F P h)
        (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom) :=
    adjointFactorization_projection_pullback_left_comp_isHomLift F P h
  -- Lift the composite `h^*y ⟶ F(x)` through the strongly cartesian mapped right pullback arrow.
  Functor.IsStronglyCartesian.map
    Y.p
    (adjointFactorization_projection_pullback_target_base F P h)
    ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h))
    (Category.id_comp _).symm
    (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom)

/-- Helper for Lemma 4.33.14: the comparison arrow on the pulled-back comma object is vertical. -/
private theorem adjointFactorization_projection_pullback_comparison_isHomLift
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    Y.p.IsHomLift (𝟙 V) (adjointFactorization_projection_pullback_comparison F P h) := by
  -- The comparison arrow is obtained from the universal property with `g = 𝟙 V`.
  letI :
      Y.p.IsStronglyCartesian
        (adjointFactorization_projection_pullback_target_base F P h)
        ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h)) :=
    adjointFactorization_projection_pullback_right_map_isStronglyCartesian F P h
  letI :
      Y.p.IsHomLift
        (adjointFactorization_projection_pullback_target_base F P h)
        (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom) :=
    adjointFactorization_projection_pullback_left_comp_isHomLift F P h
  have hcomparison :
      Y.p.IsHomLift
        (𝟙 V)
        (Functor.IsStronglyCartesian.map
          Y.p
          (adjointFactorization_projection_pullback_target_base F P h)
          ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h))
          (Category.id_comp _).symm
          (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom)) := by
    infer_instance
  simpa [adjointFactorization_projection_pullback_comparison] using hcomparison

/-- Helper for Lemma 4.33.14: the comparison arrow factors through the mapped right pullback map
to recover the original comparison morphism of `P`. -/
private theorem adjointFactorization_projection_pullback_comparison_fac
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    adjointFactorization_projection_pullback_comparison F P h ≫
        (toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h) =
      adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom := by
  -- This is the defining factorization equation of the strong-cartesian lift.
  letI :
      Y.p.IsStronglyCartesian
        (adjointFactorization_projection_pullback_target_base F P h)
        ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h)) :=
    adjointFactorization_projection_pullback_right_map_isStronglyCartesian F P h
  letI :
      Y.p.IsHomLift
        (adjointFactorization_projection_pullback_target_base F P h)
        (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom) :=
    adjointFactorization_projection_pullback_left_comp_isHomLift F P h
  simpa [adjointFactorization_projection_pullback_comparison] using
    (Functor.IsStronglyCartesian.fac
      Y.p
      (adjointFactorization_projection_pullback_target_base F P h)
      ((toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h))
      (Category.id_comp _).symm
      (adjointFactorization_projection_pullback_left_hom F P h ≫ P.obj.hom))

/-- Helper for Lemma 4.33.14: the canonical pulled-back comma object satisfies the defining
verticality condition of the factorization. -/
private theorem adjointFactorization_projection_pullback_obj_property
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    adjointFactorizationObjectProperty F
      { left := adjointFactorization_projection_pullback_left_obj F P h
        right := adjointFactorization_projection_pullback_right_obj F P h
        hom := adjointFactorization_projection_pullback_comparison F P h } := by
  -- The left pullback object lies over `V`, so the comparison arrow is vertical over `𝟙 V`.
  letI :
      Y.p.IsHomLift
        h
        (adjointFactorization_projection_pullback_left_hom F P h) :=
    (adjointFactorization_projection_pullback_left_isStronglyCartesian F P h).toIsHomLift
  let hleftbase :
      Y.p.obj (adjointFactorization_projection_pullback_left_obj F P h) = V :=
    IsHomLift.domain_eq Y.p h (adjointFactorization_projection_pullback_left_hom F P h)
  let comparison := adjointFactorization_projection_pullback_comparison F P h
  letI : Y.p.IsHomLift (𝟙 V) comparison :=
    adjointFactorization_projection_pullback_comparison_isHomLift F P h
  let hcod :
      Y.p.obj ((toFunctor F).obj (adjointFactorization_projection_pullback_right_obj F P h)) = V :=
    IsHomLift.codomain_eq Y.p (𝟙 V) comparison
  let hb :
      Y.p.obj ((toFunctor F).obj (adjointFactorization_projection_pullback_right_obj F P h)) =
        Y.p.obj (adjointFactorization_projection_pullback_left_obj F P h) :=
    hcod.trans hleftbase.symm
  refine IsHomLift.of_fac' Y.p (𝟙 (Y.p.obj (adjointFactorization_projection_pullback_left_obj F P h)))
    comparison rfl hb ?_
  simpa [comparison, hb, hleftbase, hcod, Category.assoc] using
    (IsHomLift.fac' Y.p (𝟙 V) comparison)

/-- Helper for Lemma 4.33.14: the canonical pulled-back comma object over the base arrow `h`. -/
private noncomputable abbrev adjointFactorization_projection_pullback_obj
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    AdjointFactorizationObject F :=
  ⟨{ left := adjointFactorization_projection_pullback_left_obj F P h
     right := adjointFactorization_projection_pullback_right_obj F P h
     hom := adjointFactorization_projection_pullback_comparison F P h },
    adjointFactorization_projection_pullback_obj_property F P h⟩

/-- Helper for Lemma 4.33.14: the canonical morphism from the pulled-back comma object to `P`. -/
private noncomputable abbrev adjointFactorization_projection_pullback_hom
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    adjointFactorization_projection_pullback_obj F P h ⟶ P :=
  ObjectProperty.homMk
    { left := adjointFactorization_projection_pullback_left_hom F P h
      right := adjointFactorization_projection_pullback_right_hom F P h
      w := (adjointFactorization_projection_pullback_comparison_fac F P h).symm }

/-- Helper for Lemma 4.33.14: any comma morphism into `P` lying over `g ≫ h` factors through the
canonical pulled-back comma object over `h`. -/
private theorem adjointFactorization_projection_pullback_lift_exists
    (F : X ⟶ Y) (P R : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P)
    (g : (adjointFactorizationProjection F).obj R ⟶ V)
    (τ : R ⟶ P)
    (hτ : (adjointFactorizationProjection F).IsHomLift (g ≫ h) τ) :
    ∃ χ : R ⟶ adjointFactorization_projection_pullback_obj F P h,
      (adjointFactorizationProjection F).IsHomLift g χ ∧
        χ ≫ adjointFactorization_projection_pullback_hom F P h = τ := by
  -- Read the lifting problem separately on the left and right components.
  have hτleft :
      Y.p.IsHomLift (g ≫ h) τ.hom.left :=
    (adjointFactorization_toTarget_hom_isHomLift_iff F (g ≫ h) τ).2 hτ
  have hpullbackLift :
      (adjointFactorizationProjection F).IsHomLift h
        (adjointFactorization_projection_pullback_hom F P h) := by
    exact
      (adjointFactorization_toTarget_hom_isHomLift_iff F h
        (adjointFactorization_projection_pullback_hom F P h)).1
        (show Y.p.IsHomLift h
            (adjointFactorization_projection_pullback_left_hom F P h) from
          (adjointFactorization_projection_pullback_left_isStronglyCartesian F P h).toIsHomLift)
  have hrightLift :
      X.p.IsHomLift h
        (adjointFactorization_projection_pullback_right_hom F P h) :=
    (adjointFactorization_toSource_hom_isHomLift_iff F h
      (adjointFactorization_projection_pullback_hom F P h)).2 hpullbackLift
  have hτright :
      X.p.IsHomLift (g ≫ h) τ.hom.right :=
    (adjointFactorization_toSource_hom_isHomLift_iff F (g ≫ h) τ).2 hτ
  letI : Y.p.IsHomLift (g ≫ h) τ.hom.left := hτleft
  letI :
      Y.p.IsStronglyCartesian h
        (adjointFactorization_projection_pullback_left_hom F P h) :=
    adjointFactorization_projection_pullback_left_isStronglyCartesian F P h
  letI :
      X.p.IsHomLift h
        (adjointFactorization_projection_pullback_right_hom F P h) :=
    hrightLift
  letI :
      X.p.IsStronglyCartesian h
        (adjointFactorization_projection_pullback_right_hom F P h) :=
    adjointFactorization_isStronglyCartesian_rebase_of_same_lift
      (p := X.p)
      (f := adjointFactorization_projection_pullback_right_base F P h)
      (f' := h)
      (adjointFactorization_projection_pullback_right_hom F P h)
  letI :
      X.p.IsHomLift (g ≫ h) τ.hom.right :=
    hτright
  -- Pull the left and right components back separately along the chosen pullback maps.
  obtain ⟨χleft, hχleft, _hχleft_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property
      Y.p
      h
      (adjointFactorization_projection_pullback_left_hom F P h)
      g
      (g ≫ h)
      rfl
      τ.hom.left
  obtain ⟨χright, hχright, _hχright_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property
      X.p
      h
      (adjointFactorization_projection_pullback_right_hom F P h)
      g
      (g ≫ h)
      rfl
      τ.hom.right
  let lhs :
      R.obj.left ⟶
        (toFunctor F).obj (adjointFactorization_projection_pullback_right_obj F P h) :=
    χleft ≫ adjointFactorization_projection_pullback_comparison F P h
  let rhs :
      R.obj.left ⟶
        (toFunctor F).obj (adjointFactorization_projection_pullback_right_obj F P h) :=
    R.obj.hom ≫ (toFunctor F).map χright
  have hlhs :
      Y.p.IsHomLift g lhs := by
    letI : Y.p.IsHomLift g χleft := hχleft.1
    letI :
        Y.p.IsHomLift
          (𝟙 V)
          (adjointFactorization_projection_pullback_comparison F P h) :=
      adjointFactorization_projection_pullback_comparison_isHomLift F P h
    simpa [lhs, Category.assoc] using
      (show Y.p.IsHomLift g
          (χleft ≫ adjointFactorization_projection_pullback_comparison F P h) from
        inferInstance)
  have hrhs_map :
      Y.p.IsHomLift g ((toFunctor F).map χright) :=
    ((toBasedFunctor F).isHomLift_iff g χright).2 hχright.1
  have hrhs :
      Y.p.IsHomLift g rhs := by
    letI : Y.p.IsHomLift (𝟙 ((adjointFactorizationProjection F).obj R)) R.obj.hom := R.property
    letI : Y.p.IsHomLift g ((toFunctor F).map χright) := hrhs_map
    simpa [rhs, Category.assoc] using
      (show Y.p.IsHomLift g (R.obj.hom ≫ (toFunctor F).map χright) from inferInstance)
  have hw :
      lhs = rhs := by
    let mappedRight :=
      (toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P h)
    letI :
        Y.p.IsStronglyCartesian
          (adjointFactorization_projection_pullback_target_base F P h)
          mappedRight :=
      adjointFactorization_projection_pullback_right_map_isStronglyCartesian F P h
    letI : Y.p.IsHomLift g lhs := hlhs
    letI : Y.p.IsHomLift g rhs := hrhs
    have hwpost : lhs ≫ mappedRight = rhs ≫ mappedRight := by
      change lhs ≫ mappedRight = (R.obj.hom ≫ (toFunctor F).map χright) ≫ mappedRight
      calc
        lhs ≫ mappedRight
            = χleft ≫
                adjointFactorization_projection_pullback_left_hom F P h ≫
                  P.obj.hom := by
                simp [lhs, mappedRight, Category.assoc]
        _ = τ.hom.left ≫ P.obj.hom := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ P.obj.hom) hχleft.2
        _ = R.obj.hom ≫ (toFunctor F).map τ.hom.right := by
              simpa using τ.hom.w
        _ = (R.obj.hom ≫ (toFunctor F).map χright) ≫ mappedRight := by
              simpa [mappedRight, Functor.map_comp, Category.assoc] using
                congrArg (fun k ↦ R.obj.hom ≫ (toFunctor F).map k) hχright.2.symm
    exact
      Functor.IsStronglyCartesian.ext
        (p := Y.p)
        (f := adjointFactorization_projection_pullback_target_base F P h)
        (φ := mappedRight)
        (g := g)
        (ψ := lhs)
        (ψ' := rhs)
        hwpost
  have hχw :
      χleft ≫ adjointFactorization_projection_pullback_comparison F P h =
        R.obj.hom ≫ (toFunctor F).map χright := by
    -- Compare both candidate comparison maps after postcomposing with the mapped right pullback
    -- arrow, then cancel that strongly cartesian morphism.
    simpa [lhs, rhs] using hw
  let χ : R ⟶ adjointFactorization_projection_pullback_obj F P h :=
    ObjectProperty.homMk
      { left := χleft
        right := χright
        w := hχw }
  refine ⟨χ, ?_, ?_⟩
  · -- The mediator lies over `g` because its left component does.
    exact (adjointFactorization_toTarget_hom_isHomLift_iff F g χ).1 hχleft.1
  · -- The constructed mediator composes to the original comma morphism componentwise.
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · simpa [χ, adjointFactorization_projection_pullback_hom, Category.assoc] using hχleft.2
    · simpa [χ, adjointFactorization_projection_pullback_hom, Category.assoc] using hχright.2

/-- Helper for Lemma 4.33.14: the canonical pulled-back comma morphism is strongly cartesian for
the projection `X' ⟶ C`. -/
private theorem adjointFactorization_projection_pullback_hom_isStronglyCartesian
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    (adjointFactorizationProjection F).IsStronglyCartesian h
      (adjointFactorization_projection_pullback_hom F P h) := by
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · -- The canonical morphism lies over `h` because its left component is the chosen pullback map.
      exact
        (adjointFactorization_toTarget_hom_isHomLift_iff F h
          (adjointFactorization_projection_pullback_hom F P h)).1
          (show Y.p.IsHomLift h
              (adjointFactorization_projection_pullback_left_hom F P h) from
            (adjointFactorization_projection_pullback_left_isStronglyCartesian F P h).toIsHomLift)
  · intro R g τ hτ
    -- Route correction: reuse the packaged mediator into the canonical pullback object, then
    -- discharge uniqueness by the universal properties of the left and right pullback maps.
    obtain ⟨χ, hχlift, hχfac⟩ :=
      adjointFactorization_projection_pullback_lift_exists F P R h g τ hτ
    have hτleft :
        Y.p.IsHomLift (g ≫ h) τ.hom.left :=
      (adjointFactorization_toTarget_hom_isHomLift_iff F (g ≫ h) τ).2 hτ
    have hpullbackLift :
        (adjointFactorizationProjection F).IsHomLift h
          (adjointFactorization_projection_pullback_hom F P h) := by
      exact
        (adjointFactorization_toTarget_hom_isHomLift_iff F h
          (adjointFactorization_projection_pullback_hom F P h)).1
          (show Y.p.IsHomLift h
              (adjointFactorization_projection_pullback_left_hom F P h) from
            (adjointFactorization_projection_pullback_left_isStronglyCartesian F P h).toIsHomLift)
    have hrightLift :
        X.p.IsHomLift h
          (adjointFactorization_projection_pullback_right_hom F P h) :=
      (adjointFactorization_toSource_hom_isHomLift_iff F h
        (adjointFactorization_projection_pullback_hom F P h)).2 hpullbackLift
    have hτright :
        X.p.IsHomLift (g ≫ h) τ.hom.right :=
      (adjointFactorization_toSource_hom_isHomLift_iff F (g ≫ h) τ).2 hτ
    letI : Y.p.IsHomLift (g ≫ h) τ.hom.left := hτleft
    letI :
        Y.p.IsStronglyCartesian h
          (adjointFactorization_projection_pullback_left_hom F P h) :=
      adjointFactorization_projection_pullback_left_isStronglyCartesian F P h
    letI :
        X.p.IsHomLift h
          (adjointFactorization_projection_pullback_right_hom F P h) :=
      hrightLift
    letI :
        X.p.IsStronglyCartesian h
          (adjointFactorization_projection_pullback_right_hom F P h) :=
      adjointFactorization_isStronglyCartesian_rebase_of_same_lift
        (p := X.p)
        (f := adjointFactorization_projection_pullback_right_base F P h)
        (f' := h)
        (adjointFactorization_projection_pullback_right_hom F P h)
    letI :
        X.p.IsHomLift (g ≫ h) τ.hom.right :=
      hτright
    have hχleft :
        Y.p.IsHomLift g χ.hom.left :=
      (adjointFactorization_toTarget_hom_isHomLift_iff F g χ).2 hχlift
    have hχright :
        X.p.IsHomLift g χ.hom.right :=
      (adjointFactorization_toSource_hom_isHomLift_iff F g χ).2 hχlift
    have hχleft_fac :
        χ.hom.left ≫ adjointFactorization_projection_pullback_left_hom F P h =
          τ.hom.left := by
      simpa [adjointFactorization_projection_pullback_hom, Category.assoc] using
        congrArg (fun f ↦ f.hom.left) hχfac
    have hχright_fac :
        χ.hom.right ≫ adjointFactorization_projection_pullback_right_hom F P h =
          τ.hom.right := by
      simpa [adjointFactorization_projection_pullback_hom, Category.assoc] using
        congrArg (fun f ↦ f.hom.right) hχfac
    -- Uniqueness is proved componentwise against the chosen pullback maps.
    obtain ⟨_χleft, _hχleft, hχleft_uniq⟩ :=
      Functor.IsStronglyCartesian.universal_property
        Y.p
        h
        (adjointFactorization_projection_pullback_left_hom F P h)
        g
        (g ≫ h)
        rfl
        τ.hom.left
    obtain ⟨_χright, _hχright, hχright_uniq⟩ :=
      Functor.IsStronglyCartesian.universal_property
        X.p
        h
        (adjointFactorization_projection_pullback_right_hom F P h)
        g
        (g ≫ h)
        rfl
        τ.hom.right
    refine ⟨χ, ⟨hχlift, hχfac⟩, ?_⟩
    intro ξ hξ
    -- Uniqueness reduces to the universal properties of the left and right pullback maps.
    have hξleft :
        Y.p.IsHomLift g ξ.hom.left :=
      (adjointFactorization_toTarget_hom_isHomLift_iff F g ξ).2 hξ.1
    have hξright :
        X.p.IsHomLift g ξ.hom.right :=
      (adjointFactorization_toSource_hom_isHomLift_iff F g ξ).2 hξ.1
    have hξleft_fac :
        ξ.hom.left ≫ adjointFactorization_projection_pullback_left_hom F P h =
          τ.hom.left := by
      simpa [adjointFactorization_projection_pullback_hom, Category.assoc] using
        congrArg (fun f ↦ f.hom.left) hξ.2
    have hξright_fac :
        ξ.hom.right ≫ adjointFactorization_projection_pullback_right_hom F P h =
          τ.hom.right := by
      simpa [adjointFactorization_projection_pullback_hom, Category.assoc] using
        congrArg (fun f ↦ f.hom.right) hξ.2
    have hχleft_self : χ.hom.left = _χleft :=
      hχleft_uniq _ ⟨hχleft, hχleft_fac⟩
    have hχright_self : χ.hom.right = _χright :=
      hχright_uniq _ ⟨hχright, hχright_fac⟩
    have hξleft_eq : ξ.hom.left = χ.hom.left :=
      (hχleft_uniq _ ⟨hξleft, hξleft_fac⟩).trans hχleft_self.symm
    have hξright_eq : ξ.hom.right = χ.hom.right :=
      (hχright_uniq _ ⟨hξright, hξright_fac⟩).trans hχright_self.symm
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact hξleft_eq
    · exact hξright_eq

/-- Helper for Lemma 4.33.14: the projection `X' ⟶ C` admits a canonical strongly cartesian lift
of any base arrow into a vertical comparison object. -/
private theorem adjointFactorization_projection_exists_isStronglyCartesian
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) {V : C}
    (h : V ⟶ (adjointFactorizationProjection F).obj P) :
    ∃ Q : AdjointFactorizationObject F, ∃ η : Q ⟶ P,
      (adjointFactorizationProjection F).IsStronglyCartesian h η := by
  -- Package the explicit pullback object and its canonical projection morphism.
  refine ⟨adjointFactorization_projection_pullback_obj F P h,
    adjointFactorization_projection_pullback_hom F P h, ?_⟩
  exact adjointFactorization_projection_pullback_hom_isStronglyCartesian F P h

/-- The source-facing factorization projection is fibred over `C`. -/
theorem adjointFactorizationProjection_isFibered
    (F : X ⟶ Y) :
    (adjointFactorizationProjection F).IsFibered := by
  -- Route correction: discharge fibredness only after the canonical lifted comma object has been
  -- isolated as a reusable helper, so the remaining transport arguments can target that object.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro P V h
  -- The helper produces the textbook pullback object together with its strongly cartesian map.
  exact adjointFactorization_projection_exists_isStronglyCartesian F P h

/-- The source-facing factorization owner of `F`, namely the fibred category of
vertical arrows in the comma category `Comma (𝟭 Y.S) (toFunctor F)`. Over a fixed `U : C` and
`y : Y.p.Fiber U`, its fiber is the structured-arrow category `StructuredArrow y (fiberFunctor F U)`.
-/
noncomputable abbrev adjointFactorization
    (F : X ⟶ Y) :
    FibredCategoryOver C :=
  let p := adjointFactorizationProjection F
  letI : p.IsFibered := adjointFactorizationProjection_isFibered F
  FibredCategoryOver.ofFunctor p

/-- The projection `X' ⟶ X` from the source-facing factorization. -/
noncomputable abbrev adjointFactorizationToSourceBased
    (F : X ⟶ Y) :
    (adjointFactorization F).toBasedCategory ⥤ᵇ X.toBasedCategory :=
  { toFunctor := adjointFactorizationToSourceFunctor F
    w := adjointFactorizationToSourceFunctor_comm F }

theorem adjointFactorizationToSource_preservesStronglyCartesian
    (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian (adjointFactorizationToSourceBased F) := by
  -- Route correction: compare any projection-strongly-cartesian comma morphism with the canonical
  -- pulled-back comma object, then transport strong cartesianness to the right component in `X`.
  dsimp [BasedFunctor.PreservesStronglyCartesian]
  intro P Q η hη
  letI :
      (adjointFactorizationProjection F).IsStronglyCartesian
        ((adjointFactorizationProjection F).map η) η :=
    hη
  have hηCart :
      (adjointFactorizationProjection F).IsCartesian
        ((adjointFactorizationProjection F).map η) η :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := adjointFactorizationProjection F)
      (f := (adjointFactorizationProjection F).map η)
      (φ := η)
  let κ :
      adjointFactorization_projection_pullback_obj F Q
          ((adjointFactorizationProjection F).map η) ⟶
        Q :=
    adjointFactorization_projection_pullback_hom F Q
      ((adjointFactorizationProjection F).map η)
  have hκ :
      (adjointFactorizationProjection F).IsStronglyCartesian
        ((adjointFactorizationProjection F).map η) κ := by
    -- The canonical pullback object gives the reference strongly cartesian lift.
    simpa [κ] using
      adjointFactorization_projection_pullback_hom_isStronglyCartesian F Q
        ((adjointFactorizationProjection F).map η)
  letI :
      (adjointFactorizationProjection F).IsCartesian
        ((adjointFactorizationProjection F).map η) κ :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := adjointFactorizationProjection F)
      (f := (adjointFactorizationProjection F).map η)
      (φ := κ)
  let e :=
    Functor.IsCartesian.domainUniqueUpToIso
      (adjointFactorizationProjection F)
      ((adjointFactorizationProjection F).map η)
      κ
      η
  have heHomLift :
      (adjointFactorizationProjection F).IsHomLift
        (𝟙 ((adjointFactorizationProjection F).obj P))
        e.hom := by
    -- The comparison isomorphism between the two lifts is vertical on the projection to `C`.
    change
      (adjointFactorizationProjection F).IsHomLift
        (𝟙 ((adjointFactorizationProjection F).obj P))
        ((Functor.IsCartesian.domainUniqueUpToIso
            (adjointFactorizationProjection F)
            ((adjointFactorizationProjection F).map η)
            κ
            η).hom)
    infer_instance
  have heRightLift :
      X.p.IsHomLift
        (𝟙 ((adjointFactorizationProjection F).obj P))
        e.hom.hom.right := by
    -- The right component of a projection-vertical comparison morphism is vertical in `X`.
    letI :
        (adjointFactorizationProjection F).IsHomLift
          (𝟙 ((adjointFactorizationProjection F).obj P))
          e.hom :=
      heHomLift
    exact adjointFactorization_projection_vertical_hom_right_isHomLift F e.hom
  have hκRightLift :
      X.p.IsHomLift
        ((adjointFactorizationProjection F).map η)
        (adjointFactorization_projection_pullback_right_hom F Q
          ((adjointFactorizationProjection F).map η)) := by
    -- Forget the canonical pullback comma arrow to its source component.
    exact
      (adjointFactorization_toSource_hom_isHomLift_iff F
        ((adjointFactorizationProjection F).map η)
        κ).2
        (show (adjointFactorizationProjection F).IsHomLift
            ((adjointFactorizationProjection F).map η)
            κ from
          hκ.toIsHomLift)
  letI :
      X.p.IsStronglyCartesian
        ((adjointFactorizationProjection F).map η)
        (adjointFactorization_projection_pullback_right_hom F Q
          ((adjointFactorizationProjection F).map η)) :=
    -- Rebase the chosen right pullback map to the literal projection map of the comma arrow `κ`.
    adjointFactorization_isStronglyCartesian_rebase_of_same_lift
      (p := X.p)
      (f := adjointFactorization_projection_pullback_right_base F Q
        ((adjointFactorizationProjection F).map η))
      (f' := (adjointFactorizationProjection F).map η)
      (adjointFactorization_projection_pullback_right_hom F Q
        ((adjointFactorizationProjection F).map η))
  have hfac : e.hom ≫ κ = η := by
    -- The comparison isomorphism is the unique mediator from `η` to the canonical pullback arrow.
    simpa [e, κ] using
      (Functor.IsCartesian.fac
        (adjointFactorizationProjection F)
        ((adjointFactorizationProjection F).map η)
        κ
        η)
  have hfac_right :
      e.hom.hom.right ≫
          adjointFactorization_projection_pullback_right_hom F Q
            ((adjointFactorizationProjection F).map η) =
        η.hom.right := by
    -- On the source component, the comparison isomorphism followed by the canonical pullback map
    -- recovers the original strongly cartesian arrow.
    simpa [κ, Category.assoc] using
      congrArg (fun f ↦ f.hom.right) hfac
  haveI : IsIso ((adjointFactorizationToSourceFunctor F).map e.hom) := by
    infer_instance
  haveI : IsIso e.hom.hom.right := by
    simpa [adjointFactorizationToSourceFunctor] using
      (inferInstance : IsIso ((adjointFactorizationToSourceFunctor F).map e.hom))
  letI :
      X.p.IsStronglyCartesian
        (𝟙 ((adjointFactorizationProjection F).obj P))
        e.hom.hom.right := by
    infer_instance
  have hcomp :
      X.p.IsStronglyCartesian
        (𝟙 ((adjointFactorizationProjection F).obj P) ≫
          (adjointFactorizationProjection F).map η)
        (e.hom.hom.right ≫
          adjointFactorization_projection_pullback_right_hom F Q
            ((adjointFactorizationProjection F).map η)) := by
    -- Compose the vertical comparison isomorphism with the canonical pullback map.
    infer_instance
  letI :
      X.p.IsStronglyCartesian
        (𝟙 ((adjointFactorizationProjection F).obj P) ≫
          (adjointFactorizationProjection F).map η)
        (e.hom.hom.right ≫
          adjointFactorization_projection_pullback_right_hom F Q
            ((adjointFactorizationProjection F).map η)) :=
    hcomp
  have hcompMapLift :
      X.p.IsHomLift
        (X.p.map η.hom.right)
        (e.hom.hom.right ≫
          adjointFactorization_projection_pullback_right_hom F Q
            ((adjointFactorizationProjection F).map η)) := by
    -- After identifying the composite with `η.hom.right`, its literal projection map is the base
    -- arrow for the final rebasing step.
    refine IsHomLift.of_fac' X.p (X.p.map η.hom.right)
      (e.hom.hom.right ≫
        adjointFactorization_projection_pullback_right_hom F Q
          ((adjointFactorizationProjection F).map η))
      rfl
      rfl
      ?_
    simpa [Functor.map_comp] using congrArg (Functor.map X.p) hfac_right
  -- Finally rebase the composite to its literal source-component map, which is `η.hom.right`.
  have hcomp' :
      X.p.IsStronglyCartesian
        (X.p.map η.hom.right)
        (e.hom.hom.right ≫
          adjointFactorization_projection_pullback_right_hom F Q
            ((adjointFactorizationProjection F).map η)) := by
    letI :
        X.p.IsHomLift
          (X.p.map η.hom.right)
          (e.hom.hom.right ≫
            adjointFactorization_projection_pullback_right_hom F Q
              ((adjointFactorizationProjection F).map η)) :=
      hcompMapLift
    exact
      adjointFactorization_isStronglyCartesian_rebase_of_same_lift
        (p := X.p)
        (f := 𝟙 ((adjointFactorizationProjection F).obj P) ≫
          (adjointFactorizationProjection F).map η)
        (f' := X.p.map η.hom.right)
        (e.hom.hom.right ≫
          adjointFactorization_projection_pullback_right_hom F Q
            ((adjointFactorizationProjection F).map η))
  convert hcomp' using 2
  exact hfac_right.symm

/-- The projection from the source-facing factorization back to `X`. -/
noncomputable abbrev adjointFactorizationToSource
    (F : X ⟶ Y) :
    adjointFactorization F ⟶ X :=
  ofBasedFunctor
    (adjointFactorizationToSourceBased F)
    (adjointFactorizationToSource_preservesStronglyCartesian F)

/-- The projection `X' ⟶ Y` from the source-facing factorization. -/
noncomputable abbrev adjointFactorizationToTargetBased
    (F : X ⟶ Y) :
    (adjointFactorization F).toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  { toFunctor := adjointFactorizationToTargetFunctor F
    w := rfl }

theorem adjointFactorizationToTarget_preservesStronglyCartesian
    (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian (adjointFactorizationToTargetBased F) := by
  -- Route correction: reuse the same comparison-iso package as for the source projection, but now
  -- read off the left component in `Y`.
  dsimp [BasedFunctor.PreservesStronglyCartesian]
  intro P Q η hη
  letI :
      (adjointFactorizationProjection F).IsStronglyCartesian
        ((adjointFactorizationProjection F).map η) η :=
    hη
  have hηCart :
      (adjointFactorizationProjection F).IsCartesian
        ((adjointFactorizationProjection F).map η) η :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := adjointFactorizationProjection F)
      (f := (adjointFactorizationProjection F).map η)
      (φ := η)
  let κ :
      adjointFactorization_projection_pullback_obj F Q
          ((adjointFactorizationProjection F).map η) ⟶
        Q :=
    adjointFactorization_projection_pullback_hom F Q
      ((adjointFactorizationProjection F).map η)
  have hκ :
      (adjointFactorizationProjection F).IsStronglyCartesian
        ((adjointFactorizationProjection F).map η) κ := by
    -- The canonical pullback object again provides the comparison arrow.
    simpa [κ] using
      adjointFactorization_projection_pullback_hom_isStronglyCartesian F Q
        ((adjointFactorizationProjection F).map η)
  letI :
      (adjointFactorizationProjection F).IsCartesian
        ((adjointFactorizationProjection F).map η) κ :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := adjointFactorizationProjection F)
      (f := (adjointFactorizationProjection F).map η)
      (φ := κ)
  let e :=
    Functor.IsCartesian.domainUniqueUpToIso
      (adjointFactorizationProjection F)
      ((adjointFactorizationProjection F).map η)
      κ
      η
  have heHomLift :
      (adjointFactorizationProjection F).IsHomLift
        (𝟙 ((adjointFactorizationProjection F).obj P))
        e.hom := by
    -- The domain-comparison isomorphism is vertical in the projection to `C`.
    change
      (adjointFactorizationProjection F).IsHomLift
        (𝟙 ((adjointFactorizationProjection F).obj P))
        ((Functor.IsCartesian.domainUniqueUpToIso
            (adjointFactorizationProjection F)
            ((adjointFactorizationProjection F).map η)
            κ
            η).hom)
    infer_instance
  have heLeftLift :
      Y.p.IsHomLift
        (𝟙 ((adjointFactorizationProjection F).obj P))
        e.hom.hom.left := by
    -- The left component of a projection-vertical comparison morphism is vertical in `Y`.
    letI :
        (adjointFactorizationProjection F).IsHomLift
          (𝟙 ((adjointFactorizationProjection F).obj P))
          e.hom :=
      heHomLift
    exact adjointFactorization_projection_vertical_hom_left_isHomLift F e.hom
  letI :
      Y.p.IsStronglyCartesian
        (𝟙 ((adjointFactorizationProjection F).obj P))
        e.hom.hom.left := by
    haveI : IsIso ((adjointFactorizationToTargetFunctor F).map e.hom) := by
      infer_instance
    haveI : IsIso e.hom.hom.left := by
      simpa [adjointFactorizationToTargetFunctor] using
        (inferInstance : IsIso ((adjointFactorizationToTargetFunctor F).map e.hom))
    infer_instance
  letI :
      Y.p.IsStronglyCartesian
        ((adjointFactorizationProjection F).map η)
        (adjointFactorization_projection_pullback_left_hom F Q
          ((adjointFactorizationProjection F).map η)) :=
    adjointFactorization_projection_pullback_left_isStronglyCartesian F Q
      ((adjointFactorizationProjection F).map η)
  have hfac : e.hom ≫ κ = η := by
    -- The comparison isomorphism composes with the canonical pullback arrow to recover `η`.
    simpa [e, κ] using
      (Functor.IsCartesian.fac
        (adjointFactorizationProjection F)
        ((adjointFactorizationProjection F).map η)
        κ
        η)
  have hfac_left :
      e.hom.hom.left ≫
          adjointFactorization_projection_pullback_left_hom F Q
            ((adjointFactorizationProjection F).map η) =
        η.hom.left := by
    -- Reading the previous equality on the left component gives the target-side factorization.
    simpa [κ, Category.assoc] using
      congrArg (fun f ↦ f.hom.left) hfac
  have hcomp :
      Y.p.IsStronglyCartesian
        (𝟙 ((adjointFactorizationProjection F).obj P) ≫
          (adjointFactorizationProjection F).map η)
        (e.hom.hom.left ≫
          adjointFactorization_projection_pullback_left_hom F Q
            ((adjointFactorizationProjection F).map η)) := by
    -- Compose the vertical comparison isomorphism with the canonical left pullback map.
    infer_instance
  letI :
      Y.p.IsStronglyCartesian
        (𝟙 ((adjointFactorizationProjection F).obj P) ≫
          (adjointFactorizationProjection F).map η)
        (e.hom.hom.left ≫
          adjointFactorization_projection_pullback_left_hom F Q
            ((adjointFactorizationProjection F).map η)) :=
    hcomp
  have hcompMapLift :
      Y.p.IsHomLift
        (Y.p.map η.hom.left)
        (e.hom.hom.left ≫
          adjointFactorization_projection_pullback_left_hom F Q
            ((adjointFactorizationProjection F).map η)) := by
    -- After identifying the composite with `η.hom.left`, its literal projection map is the base
    -- arrow for the final rebasing step in `Y`.
    refine IsHomLift.of_fac' Y.p (Y.p.map η.hom.left)
      (e.hom.hom.left ≫
        adjointFactorization_projection_pullback_left_hom F Q
          ((adjointFactorizationProjection F).map η))
      rfl
      rfl
      ?_
    simpa [Functor.map_comp] using congrArg (Functor.map Y.p) hfac_left
  -- Rebase to the literal target-component map of `η`.
  have hcomp' :
      Y.p.IsStronglyCartesian
        (Y.p.map η.hom.left)
        (e.hom.hom.left ≫
          adjointFactorization_projection_pullback_left_hom F Q
            ((adjointFactorizationProjection F).map η)) := by
    letI :
        Y.p.IsHomLift
          (Y.p.map η.hom.left)
          (e.hom.hom.left ≫
            adjointFactorization_projection_pullback_left_hom F Q
              ((adjointFactorizationProjection F).map η)) :=
      hcompMapLift
    exact
      adjointFactorization_isStronglyCartesian_rebase_of_same_lift
        (p := Y.p)
        (f := 𝟙 ((adjointFactorizationProjection F).obj P) ≫
          (adjointFactorizationProjection F).map η)
        (f' := Y.p.map η.hom.left)
        (e.hom.hom.left ≫
          adjointFactorization_projection_pullback_left_hom F Q
            ((adjointFactorizationProjection F).map η))
  convert hcomp' using 2
  exact hfac_left.symm

/-- The target projection in the source-facing factorization. -/
noncomputable abbrev adjointFactorizationToTarget
    (F : X ⟶ Y) :
    adjointFactorization F ⟶ Y :=
  ofBasedFunctor
    (adjointFactorizationToTargetBased F)
    (adjointFactorizationToTarget_preservesStronglyCartesian F)

/-- The canonical object `(x, F(x), id)` in the source-facing factorization. -/
abbrev adjointFactorizationFromSourceObj
    (F : X ⟶ Y) (x : X.S) :
    AdjointFactorizationObject F :=
  ⟨{ left := (toFunctor F).obj x
     right := x
     hom := 𝟙 ((toFunctor F).obj x) }, by
    change Y.p.IsHomLift (𝟙 (Y.p.obj ((toFunctor F).obj x))) (𝟙 ((toFunctor F).obj x))
    simp [IsHomLift.id]⟩

/-- The underlying comma functor `x ↦ (F(x) ⟶ F(x))` used to build the canonical source map. -/
def adjointFactorizationFromSourceComma
    (F : X ⟶ Y) :
    X.S ⥤ Comma (𝟭 Y.S) (toFunctor F) where
  obj := fun x ↦ (adjointFactorizationFromSourceObj F x).obj
  map := fun a ↦
    { left := (toFunctor F).map a
      right := a
      w := by simp }
  map_id := by
    intro x
    apply Comma.hom_ext <;> simp
  map_comp := by
    intro x y z a b
    apply Comma.hom_ext <;> simp

abbrev adjointFactorizationFromSourceFunctor
    (F : X ⟶ Y) :
    X.S ⥤ AdjointFactorizationObject F :=
  (adjointFactorizationObjectProperty F).lift
    (adjointFactorizationFromSourceComma F)
    fun x ↦ (adjointFactorizationFromSourceObj F x).property

def adjointFactorizationToSourceFunctorUnit
    (F : X ⟶ Y) :
    𝟭 (AdjointFactorizationObject F) ⟶
      adjointFactorizationToSourceFunctor F ⋙ adjointFactorizationFromSourceFunctor F where
  app P :=
    ObjectProperty.homMk
      { left := P.obj.hom
        right := 𝟙 P.obj.right
        w := by simp [adjointFactorizationFromSourceComma] }
  naturality {P Q} φ := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp [adjointFactorizationFromSourceComma]
    simpa [adjointFactorizationFromSourceComma] using φ.hom.w

def adjointFactorizationToSourceFunctorCounitIso
    (F : X ⟶ Y) :
    adjointFactorizationFromSourceFunctor F ⋙ adjointFactorizationToSourceFunctor F ≅ 𝟭 X.S where
  hom :=
    { app := fun x ↦ 𝟙 x
      naturality := by intro x x' f; simp [adjointFactorizationFromSourceComma] }
  inv :=
    { app := fun x ↦ 𝟙 x
      naturality := by intro x x' f; simp [adjointFactorizationFromSourceComma] }
  hom_inv_id := by
    ext x
    simp [adjointFactorizationFromSourceComma]
  inv_hom_id := by
    ext x
    simp [adjointFactorizationFromSourceComma]

noncomputable def adjointFactorizationToSourceFunctorAdjunction
    (F : X ⟶ Y) :
    adjointFactorizationToSourceFunctor F ⊣ adjointFactorizationFromSourceFunctor F :=
  Adjunction.mkOfUnitCounit
    { unit := adjointFactorizationToSourceFunctorUnit F
      counit := (adjointFactorizationToSourceFunctorCounitIso F).hom
      left_triangle := by
        ext P
        simp [adjointFactorizationToSourceFunctorUnit, adjointFactorizationToSourceFunctorCounitIso,
          adjointFactorizationFromSourceComma]
      right_triangle := by
        ext x <;> simp [adjointFactorizationToSourceFunctorUnit,
          adjointFactorizationToSourceFunctorCounitIso, adjointFactorizationFromSourceComma] }

/-- The canonical map `X ⟶ X'` given by `x ↦ (x, F(x), id)`. -/
noncomputable abbrev adjointFactorizationFromSourceBased
    (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ (adjointFactorization F).toBasedCategory :=
  { toFunctor := adjointFactorizationFromSourceFunctor F
    w := by
      -- The canonical object `(F(x) ⟶ F(x))` lies over the same base point as `x`.
      refine CategoryTheory.Functor.ext
        (fun x ↦ by
          change Y.p.obj ((toFunctor F).obj x) = X.p.obj x
          exact CategoryTheory.Functor.congr_obj (comm F) x) ?_
      intro x y φ
      change Y.p.map ((adjointFactorizationFromSourceComma F).map φ).left =
        eqToHom (CategoryTheory.Functor.congr_obj (comm F) x) ≫
          X.p.map φ ≫
            eqToHom (CategoryTheory.Functor.congr_obj (comm F) y).symm
      simpa [adjointFactorizationFromSourceComma, Category.assoc] using
        CategoryTheory.Functor.congr_hom (comm F) φ }

private theorem adjointFactorizationFromSourceFunctor_base_eq
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (adjointFactorization F).toBasedCategory.p.obj
        ((adjointFactorizationFromSourceFunctor F).obj P.obj.right) =
      (adjointFactorization F).toBasedCategory.p.obj P := by
  let _ : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
  change Y.p.obj ((toFunctor F).obj P.obj.right) = Y.p.obj P.obj.left
  exact IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom

def adjointFactorizationToSourceBasedUnit
    (F : X ⟶ Y) :
    BasedNatTrans (BasedFunctor.id (adjointFactorization F).toBasedCategory)
      (BasedFunctor.comp (adjointFactorizationToSourceBased F)
        (adjointFactorizationFromSourceBased F)) where
  toNatTrans := adjointFactorizationToSourceFunctorUnit F
  isHomLift' := fun P ↦ by
    let _ : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
    refine IsHomLift.of_fac'
      ((adjointFactorization F).toBasedCategory.p)
      (𝟙 (((adjointFactorization F).toBasedCategory.p).obj P))
      ((adjointFactorizationToSourceFunctorUnit F).app P) rfl ?_ ?_
    · exact adjointFactorizationFromSourceFunctor_base_eq F P
    · simpa [adjointFactorization, FibredCategoryOver.ofFunctor, adjointFactorizationProjection,
        adjointFactorizationToSourceFunctorUnit] using
        (IsHomLift.fac' Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom)

def adjointFactorizationFromSourceBasedCounit
    (F : X ⟶ Y) :
    BasedNatTrans (BasedFunctor.comp (adjointFactorizationFromSourceBased F)
        (adjointFactorizationToSourceBased F))
      (BasedFunctor.id X.toBasedCategory) where
  toNatTrans := (adjointFactorizationToSourceFunctorCounitIso F).hom
  isHomLift' := fun x ↦ by
    simpa using
      (show X.p.IsHomLift (𝟙 (X.p.obj x))
          ((adjointFactorizationToSourceFunctorCounitIso F).hom.app x) from
        IsHomLift.id (rfl : X.p.obj x = X.p.obj x))

abbrev fibredCategoryMorHomOfBasedNatTrans
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (η : FibredCategoryMor.toBasedFunctor F ⟶ FibredCategoryMor.toBasedFunctor G) :
    F ⟶ G :=
  ⟨ObjectProperty.homMk η, trivial⟩

@[simp] private theorem fibredCategoryMorHomOfBasedNatTrans_hom_hom
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (η : FibredCategoryMor.toBasedFunctor F ⟶ FibredCategoryMor.toBasedFunctor G) :
    (fibredCategoryMorHomOfBasedNatTrans η).hom.hom = η :=
  rfl

/-- Helper for Lemma 4.33.14: forgetting a right-whiskered owner `2`-morphism recovers the
right-whiskered underlying based natural transformation. -/
private theorem fibredCategoryMor_whisker_right_hom_hom
    {X Y Z : FibredCategoryOver C} {F G : X ⟶ Y}
    (η : F ⟶ G) (H : Y ⟶ Z) :
    (η ▷ H).hom.hom =
      CategoryTheory.BasedCategory.whiskerRight η.hom.hom (toBasedFunctor H) := by
  rfl

/-- Helper for Lemma 4.33.14: forgetting a left-whiskered owner `2`-morphism recovers the
left-whiskered underlying based natural transformation. -/
private theorem fibredCategoryMor_whisker_left_hom_hom
    {X Y Z : FibredCategoryOver C} (F : X ⟶ Y) {G H : Y ⟶ Z}
    (η : G ⟶ H) :
    (F ◁ η).hom.hom =
      CategoryTheory.BasedCategory.whiskerLeft (toBasedFunctor F) η.hom.hom := by
  rfl

/-- Helper for Lemma 4.33.14: a morphism into the canonical object `(x, F(x), 𝟙)` is determined
by its right component in `X`. -/
private theorem adjointFactorizationFromSource_hom_ext_right
    (F : X ⟶ Y) {P : AdjointFactorizationObject F} {x : X.S}
    {φ ψ : P ⟶ (adjointFactorizationFromSourceFunctor F).obj x}
    (h : φ.hom.right = ψ.hom.right) :
    φ = ψ := by
  -- The target comparison morphism is the identity, so the comma equation recovers the left
  -- component from the right component.
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · have hφ : φ.hom.left = P.obj.hom ≫ (toFunctor F).map φ.hom.right := by
      simpa [adjointFactorizationFromSourceComma] using φ.hom.w
    have hψ : ψ.hom.left = P.obj.hom ≫ (toFunctor F).map ψ.hom.right := by
      simpa [adjointFactorizationFromSourceComma] using ψ.hom.w
    rw [hφ, hψ, h]
  · exact h

/-- Helper for Lemma 4.33.14: the canonical source morphism associated to a strongly cartesian
arrow in `X` is strongly cartesian for the projection `X' ⟶ C`. -/
private theorem adjointFactorization_fromSource_map_isStronglyCartesian
    (F : X ⟶ Y) {x x' : X.S} (φ : x ⟶ x')
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    (adjointFactorizationProjection F).IsStronglyCartesian (X.p.map φ)
      ((adjointFactorizationFromSourceFunctor F).map φ) := by
  letI : X.p.IsStronglyCartesian (X.p.map φ) φ := hφ
  refine
    { toIsHomLift := by
        -- Read the projection lifting condition from the source component, where it is just `φ`.
        exact (adjointFactorization_toSource_hom_isHomLift_iff F (X.p.map φ)
          ((adjointFactorizationFromSourceFunctor F).map φ)).1
          (show X.p.IsHomLift (X.p.map φ) φ from inferInstance)
      universal_property' := ?_ }
  intro P g τ hτ
  -- Read the lifting problem on `τ` from the right component in `X`.
  have hτright :
      X.p.IsHomLift (g ≫ X.p.map φ) τ.hom.right :=
    (adjointFactorization_toSource_hom_isHomLift_iff F (g ≫ X.p.map φ) τ).2 hτ
  letI : X.p.IsHomLift (g ≫ X.p.map φ) τ.hom.right := hτright
  have hχexists :
      ∃! χright : P.obj.right ⟶ x,
        X.p.IsHomLift g χright ∧ χright ≫ φ = τ.hom.right :=
    @Functor.IsStronglyCartesian.universal_property _ _ _ _ X.p _ _ _ _
      (X.p.map φ) φ hφ _ _ g (g ≫ X.p.map φ) rfl τ.hom.right hτright
  obtain ⟨χright, hχright, hχright_uniq⟩ :=
    hχexists
  -- The left component is forced by the comma equation once the right component is chosen.
  let χleft : P.obj.left ⟶ (toFunctor F).obj x :=
    P.obj.hom ≫ (toFunctor F).map χright
  let χ : P ⟶ (adjointFactorizationFromSourceFunctor F).obj x :=
    ObjectProperty.homMk
      { left := χleft
        right := χright
        w := by
          -- The codomain comparison arrow is the identity, so the comma square is immediate.
          simp [χleft, adjointFactorizationFromSourceComma] }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · -- The newly built comma morphism still lies over `g` because its right component does.
    exact (adjointFactorization_toSource_hom_isHomLift_iff F g χ).1 hχright.1
  · -- Equality in the full subcategory reduces to equality of the right components.
    apply adjointFactorizationFromSource_hom_ext_right F
    simpa [χ] using hχright.2
  · intro η hη
    -- Uniqueness is inherited from the strong cartesianness of `φ` in `X`.
    have hηright_lift :
        X.p.IsHomLift g η.hom.right :=
      (adjointFactorization_toSource_hom_isHomLift_iff F g η).2 hη.1
    letI : X.p.IsHomLift g η.hom.right := hηright_lift
    have hηright_fac : η.hom.right ≫ φ = τ.hom.right := by
      simpa [adjointFactorizationFromSourceComma] using
        congrArg (fun f ↦ f.hom.right) hη.2
    have hηeq : η.hom.right = χright :=
      hχright_uniq _ ⟨hηright_lift, hηright_fac⟩
    exact adjointFactorizationFromSource_hom_ext_right F hηeq

theorem adjointFactorizationFromSource_preservesStronglyCartesian
    (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian (adjointFactorizationFromSourceBased F) := by
  intro x x' φ hφ
  -- The source map keeps the same base arrow; any difference is only the based-functor transport.
  have hχ :
      (adjointFactorizationProjection F).IsStronglyCartesian (X.p.map φ)
        ((adjointFactorizationFromSourceFunctor F).map φ) :=
    adjointFactorization_fromSource_map_isStronglyCartesian F φ hφ
  have hχ' :
      (adjointFactorizationProjection F).IsStronglyCartesian
        ((adjointFactorizationProjection F).map ((adjointFactorizationFromSourceFunctor F).map φ))
        ((adjointFactorizationFromSourceFunctor F).map φ) := by
    -- Transport the base arrow from `X.p.map φ` to the actual projection map using `comm F`.
    convert hχ using 2
    · exact CategoryTheory.Functor.congr_obj (comm F) x
    · exact CategoryTheory.Functor.congr_obj (comm F) x'
    · simpa [adjointFactorizationProjection, adjointFactorizationFromSourceFunctor,
        adjointFactorizationFromSourceComma] using
        CategoryTheory.Functor.hcongr_hom (comm F) φ
  simpa [adjointFactorization, FibredCategoryOver.ofFunctor] using hχ'

/-- The canonical source map into the source-facing factorization. -/
noncomputable abbrev adjointFactorizationFromSource
    (F : X ⟶ Y) :
    X ⟶ adjointFactorization F :=
  ofBasedFunctor
    (adjointFactorizationFromSourceBased F)
    (adjointFactorizationFromSource_preservesStronglyCartesian F)

/-- The canonical source map `X ⟶ X'` into the source-facing factorization is fully faithful. -/
noncomputable def adjointFactorizationFromSource_fullyFaithful
    (F : X ⟶ Y) :
    (toFunctor (adjointFactorizationFromSource F)).FullyFaithful := by
  let adj := adjointFactorizationToSourceFunctorAdjunction F
  letI : IsIso adj.counit := by
    change IsIso (adjointFactorizationToSourceFunctorCounitIso F).hom
    infer_instance
  change (adjointFactorizationFromSourceFunctor F).FullyFaithful
  exact adj.fullyFaithfulROfIsIsoCounit

/-- Helper for Lemma 4.33.14: forgetting the owner wrapper on the unit recovers the underlying
 based natural transformation used to build the source adjunction. -/
private theorem adjointFactorizationToSource_unit_wrapper_hom
    (F : X ⟶ Y) :
    (fibredCategoryMorHomOfBasedNatTrans
        (F := 𝟙 (adjointFactorization F))
        (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
        (adjointFactorizationToSourceBasedUnit F)).hom.hom =
      adjointFactorizationToSourceBasedUnit F := by
  rfl

/-- Helper for Lemma 4.33.14: forgetting the owner wrapper on the counit recovers the underlying
based natural transformation used to build the source adjunction. -/
private theorem adjointFactorizationToSource_counit_wrapper_hom
    (F : X ⟶ Y) :
    (fibredCategoryMorHomOfBasedNatTrans
        (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
        (G := 𝟙 X)
        (adjointFactorizationFromSourceBasedCounit F)).hom.hom =
      adjointFactorizationFromSourceBasedCounit F := by
  rfl

/-- Helper for Lemma 4.33.14: the left triangle for the lifted source adjunction reduces
pointwise to the left triangle of the underlying functor adjunction. -/
private theorem adjointFactorizationToSourceFunctorAdjunction_left_triangle_app
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    ((Functor.whiskerRight (adjointFactorizationToSourceFunctorUnit F)
        (adjointFactorizationToSourceFunctor F) ≫
      (adjointFactorizationToSourceFunctor F).whiskerLeft
        ((adjointFactorizationToSourceFunctorCounitIso F).hom)).app P =
      ((𝟙 (adjointFactorizationToSourceFunctor F) :
        adjointFactorizationToSourceFunctor F ⟶
          adjointFactorizationToSourceFunctor F).app P)) := by
  -- This is exactly the pointwise triangle identity of the ordinary functor adjunction.
  exact congrArg (fun η ↦ η.app P) (adjointFactorizationToSourceFunctorAdjunction F).left_triangle

/-- Helper for Lemma 4.33.14: the right triangle for the lifted source adjunction reduces
pointwise to the right triangle of the underlying functor adjunction. -/
private theorem adjointFactorizationToSourceFunctorAdjunction_right_triangle_app
    (F : X ⟶ Y) (x : X.S) :
    (((adjointFactorizationFromSourceFunctor F).whiskerLeft
        (adjointFactorizationToSourceFunctorUnit F) ≫
      Functor.whiskerRight
        ((adjointFactorizationToSourceFunctorCounitIso F).hom)
        (adjointFactorizationFromSourceFunctor F)).app x) =
      ((𝟙 (adjointFactorizationFromSourceFunctor F) :
        adjointFactorizationFromSourceFunctor F ⟶
          adjointFactorizationFromSourceFunctor F).app x) := by
  -- This is exactly the pointwise triangle identity of the ordinary functor adjunction.
  exact congrArg (fun η ↦ η.app x) (adjointFactorizationToSourceFunctorAdjunction F).right_triangle

/-- Helper for Lemma 4.33.14: in `BasedCategory`, the strict coherence inserted between the two
whiskers in the left zigzag contributes only the identity component. -/
private theorem adjoint_factorization_owner_left_zigzag_middle_coherence_app
    {A B : BasedCategory.{v, w} C} {L : A ⟶ B} {R : B ⟶ A}
    (eta : 𝟙 A ⟶ L ≫ R) (eps : R ≫ L ⟶ 𝟙 B) (x : A.obj) :
    ((eta ▷ L) ≫ CategoryTheory.BicategoricalCoherence.iso.hom ≫ L ◁ eps).app x =
      ((eta ▷ L) ≫ L ◁ eps).app x := by
  -- In the strict bicategory `BasedCategory`, the associator hidden inside the coherence
  -- isomorphism evaluates to the identity on each component.
  simp [CategoryTheory.BicategoricalCoherence.iso,
    CategoryTheory.Bicategory.Strict.associator_eqToIso]

/-- Helper for Lemma 4.33.14: in `BasedCategory`, the strict coherence inserted between the two
whiskers in the right zigzag contributes only the identity component. -/
private theorem adjoint_factorization_owner_right_zigzag_middle_coherence_app
    {A B : BasedCategory.{v, w} C} {L : A ⟶ B} {R : B ⟶ A}
    (eta : 𝟙 A ⟶ L ≫ R) (eps : R ≫ L ⟶ 𝟙 B) (y : B.obj) :
    ((R ◁ eta) ≫ CategoryTheory.BicategoricalCoherence.iso.hom ≫ eps ▷ R).app y =
      ((R ◁ eta) ≫ eps ▷ R).app y := by
  -- The same strictness argument removes the middle coherence factor on the right zigzag.
  simp [CategoryTheory.BicategoricalCoherence.iso,
    CategoryTheory.Bicategory.Strict.associator_eqToIso]

/-- Helper for Lemma 4.33.14: in `BasedCategory`, the coherence chosen by
`BicategoricalCoherence.assoc` is the strict associator component. -/
private theorem based_assoc_coherence_app
    {A B : BasedCategory.{v, w} C} {L : A ⟶ B} {R : B ⟶ A} (x : A.obj) :
    ((BicategoricalCoherence.assoc L R L (L ≫ R ≫ L)).1.hom.app x) =
      ((CategoryTheory.Bicategory.associator (B := BasedCategory C) L R L).hom.app x) := by
  -- In the strict bicategory `BasedCategory`, the recursive coherence reduces to the strict
  -- associator after identifying both parenthesizations by `BasedFunctor.comp_assoc`.
  simp [CategoryTheory.BicategoricalCoherence.iso,
    CategoryTheory.Bicategory.Strict.associator_eqToIso, BasedFunctor.comp_assoc]

/-- Helper for Lemma 4.33.14: in `BasedCategory`, the coherence chosen by
`BicategoricalCoherence.assoc'` is the inverse strict associator component. -/
private theorem based_assoc_inv_coherence_app
    {A B : BasedCategory.{v, w} C} {L : A ⟶ B} {R : B ⟶ A} (y : B.obj) :
    ((BicategoricalCoherence.assoc' R L R (R ≫ L ≫ R)).1.hom.app y) =
      ((CategoryTheory.Bicategory.associator (B := BasedCategory C) R L R).inv.app y) := by
  -- The right-handed recursive coherence similarly collapses to the inverse strict associator.
  simp [CategoryTheory.BicategoricalCoherence.iso,
    CategoryTheory.Bicategory.Strict.associator_eqToIso, BasedFunctor.comp_assoc]

/-- Helper for Lemma 4.33.14: specialize the generic based associator coherence to the concrete
source-factorization functors. -/
private theorem adjoint_factorization_to_source_based_assoc_coherence_app
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    ((BicategoricalCoherence.assoc
          (a := (adjointFactorization F).toBasedCategory)
          (b := X.toBasedCategory)
          (c := (adjointFactorization F).toBasedCategory)
          (d := X.toBasedCategory)
          (f := adjointFactorizationToSourceBased F)
          (g := adjointFactorizationFromSourceBased F)
          (h := adjointFactorizationToSourceBased F)
          (i := adjointFactorizationToSourceBased F ≫
            adjointFactorizationFromSourceBased F ≫
              adjointFactorizationToSourceBased F)).1.hom.app P) =
      ((CategoryTheory.Bicategory.associator (B := BasedCategory C)
          (adjointFactorizationToSourceBased F)
          (adjointFactorizationFromSourceBased F)
          (adjointFactorizationToSourceBased F)).hom.app P) := by
  -- Freeze the based-category endpoints before rewrapping the statement in owner notation.
  simp [CategoryTheory.BicategoricalCoherence.iso,
    CategoryTheory.Bicategory.Strict.associator_eqToIso, BasedFunctor.comp_assoc]

/-- Helper for Lemma 4.33.14: specialize the generic inverse based associator coherence to the
concrete source-factorization functors. -/
private theorem adjoint_factorization_to_source_based_assoc_inv_coherence_app
    (F : X ⟶ Y) (x : X.S) :
    ((BicategoricalCoherence.assoc'
          (a := X.toBasedCategory)
          (b := (adjointFactorization F).toBasedCategory)
          (c := X.toBasedCategory)
          (d := (adjointFactorization F).toBasedCategory)
          (f := adjointFactorizationFromSourceBased F)
          (g := adjointFactorizationToSourceBased F)
          (h := adjointFactorizationFromSourceBased F)
          (i := adjointFactorizationFromSourceBased F ≫
            adjointFactorizationToSourceBased F ≫
              adjointFactorizationFromSourceBased F)).1.hom.app x) =
      ((CategoryTheory.Bicategory.associator (B := BasedCategory C)
          (adjointFactorizationFromSourceBased F)
          (adjointFactorizationToSourceBased F)
          (adjointFactorizationFromSourceBased F)).inv.app x) := by
  -- Freeze the based-category endpoints in the symmetric `R-L-R` order used by the right zigzag.
  simp [CategoryTheory.BicategoricalCoherence.iso,
    CategoryTheory.Bicategory.Strict.associator_eqToIso, BasedFunctor.comp_assoc]

/-- Helper for Lemma 4.33.14: the exposed middle coherence in the owner left zigzag is exactly
the strict associator component after forgetting to `BasedCategory`. -/
private theorem adjoint_factorization_to_source_left_middle_is_associator_app
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    ((BicategoricalCoherence.assoc
          (adjointFactorizationToSource F)
          (adjointFactorizationFromSource F)
          (adjointFactorizationToSource F)
          (adjointFactorizationToSource F ≫
            adjointFactorizationFromSource F ≫
              adjointFactorizationToSource F)).1.hom.hom.hom).app P =
      ((CategoryTheory.Bicategory.associator (B := BasedCategory C)
          (adjointFactorizationToSourceBased F)
          (adjointFactorizationFromSourceBased F)
          (adjointFactorizationToSourceBased F)).hom.app P) := by
  -- Route correction: specialize the already-proved based coherence first, then forget the owner
  -- wrapper by definitional equality.
  change ((BicategoricalCoherence.assoc
        (a := (adjointFactorization F).toBasedCategory)
        (b := X.toBasedCategory)
        (c := (adjointFactorization F).toBasedCategory)
        (d := X.toBasedCategory)
        (f := adjointFactorizationToSourceBased F)
        (g := adjointFactorizationFromSourceBased F)
        (h := adjointFactorizationToSourceBased F)
        (i := adjointFactorizationToSourceBased F ≫
          adjointFactorizationFromSourceBased F ≫
            adjointFactorizationToSourceBased F)).1.hom.app P) =
    ((CategoryTheory.Bicategory.associator (B := BasedCategory C)
        (adjointFactorizationToSourceBased F)
        (adjointFactorizationFromSourceBased F)
        (adjointFactorizationToSourceBased F)).hom.app P)
  exact adjoint_factorization_to_source_based_assoc_coherence_app F P

/-- Helper for Lemma 4.33.14: the strict associator component in the owner left zigzag is the
identity on each factorization object. -/
private theorem adjoint_factorization_to_source_left_associator_app
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    ((CategoryTheory.Bicategory.associator (B := BasedCategory C)
          (adjointFactorizationToSourceBased F)
          (adjointFactorizationFromSourceBased F)
          (adjointFactorizationToSourceBased F)).hom.app P) =
      𝟙 _ := by
  -- Strictness identifies the associator with an `eqToIso`, whose component is definitionally
  -- the identity.
  rw [CategoryTheory.Bicategory.Strict.associator_eqToIso
    (B := BasedCategory C)
    (adjointFactorizationToSourceBased F)
    (adjointFactorizationFromSourceBased F)
    (adjointFactorizationToSourceBased F)]
  rfl

/-- Helper for Lemma 4.33.14: the exposed middle coherence in the owner right zigzag is exactly
the inverse strict associator component after forgetting to `BasedCategory`. -/
private theorem adjoint_factorization_to_source_right_middle_is_associator_inv_app
    (F : X ⟶ Y) (x : X.S) :
    ((BicategoricalCoherence.assoc'
          (adjointFactorizationFromSource F)
          (adjointFactorizationToSource F)
          (adjointFactorizationFromSource F)
          (adjointFactorizationFromSource F ≫
            adjointFactorizationToSource F ≫
              adjointFactorizationFromSource F)).1.hom.hom.hom).app x =
      ((CategoryTheory.Bicategory.associator (B := BasedCategory C)
          (adjointFactorizationFromSourceBased F)
          (adjointFactorizationToSourceBased F)
          (adjointFactorizationFromSourceBased F)).inv.app x) := by
  -- Route correction: reduce to the endpoint-frozen based inverse-associator statement, then
  -- forget the owner wrapper by definitional equality.
  change ((BicategoricalCoherence.assoc'
        (a := X.toBasedCategory)
        (b := (adjointFactorization F).toBasedCategory)
        (c := X.toBasedCategory)
        (d := (adjointFactorization F).toBasedCategory)
        (f := adjointFactorizationFromSourceBased F)
        (g := adjointFactorizationToSourceBased F)
        (h := adjointFactorizationFromSourceBased F)
        (i := adjointFactorizationFromSourceBased F ≫
          adjointFactorizationToSourceBased F ≫
            adjointFactorizationFromSourceBased F)).1.hom.app x) =
    ((CategoryTheory.Bicategory.associator (B := BasedCategory C)
        (adjointFactorizationFromSourceBased F)
        (adjointFactorizationToSourceBased F)
        (adjointFactorizationFromSourceBased F)).inv.app x)
  exact adjoint_factorization_to_source_based_assoc_inv_coherence_app F x

/-- Helper for Lemma 4.33.14: the inverse strict associator component in the owner right zigzag
is the identity on each source object. -/
private theorem adjoint_factorization_to_source_right_associator_inv_app
    (F : X ⟶ Y) (x : X.S) :
    ((CategoryTheory.Bicategory.associator (B := BasedCategory C)
          (adjointFactorizationFromSourceBased F)
          (adjointFactorizationToSourceBased F)
          (adjointFactorizationFromSourceBased F)).inv.app x) =
      𝟙 _ := by
  -- Strictness likewise makes the inverse associator component definitionally trivial.
  rw [CategoryTheory.Bicategory.Strict.associator_eqToIso
    (B := BasedCategory C)
    (adjointFactorizationFromSourceBased F)
    (adjointFactorizationToSourceBased F)
    (adjointFactorizationFromSourceBased F)]
  rfl

/-- Helper for Lemma 4.33.14: after removing the middle coherence, the specialized left based
whisker composite is definitionally the ordinary functor-side whisker composite. -/
private theorem adjoint_factorization_to_source_left_whisker_app
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (BasedCategory.whiskerRight (adjointFactorizationToSourceBasedUnit F)
          (toBasedFunctor (adjointFactorizationToSource F)) ≫
        BasedCategory.whiskerLeft (toBasedFunctor (adjointFactorizationToSource F))
          (adjointFactorizationFromSourceBasedCounit F)).app P =
      ((Functor.whiskerRight (adjointFactorizationToSourceFunctorUnit F)
          (adjointFactorizationToSourceFunctor F) ≫
        (adjointFactorizationToSourceFunctor F).whiskerLeft
          ((adjointFactorizationToSourceFunctorCounitIso F).hom)).app P) := by
  -- Both whiskers are defined by whiskering the same underlying natural transformations.
  rfl

/-- Helper for Lemma 4.33.14: after removing the middle coherence, the specialized right based
whisker composite is definitionally the ordinary functor-side whisker composite. -/
private theorem adjoint_factorization_to_source_right_whisker_app
    (F : X ⟶ Y) (x : X.S) :
    (BasedCategory.whiskerLeft (toBasedFunctor (adjointFactorizationFromSource F))
          (adjointFactorizationToSourceBasedUnit F) ≫
        BasedCategory.whiskerRight (adjointFactorizationFromSourceBasedCounit F)
          (toBasedFunctor (adjointFactorizationFromSource F))).app x =
      (((adjointFactorizationFromSourceFunctor F).whiskerLeft
          (adjointFactorizationToSourceFunctorUnit F) ≫
        Functor.whiskerRight
          ((adjointFactorizationToSourceFunctorCounitIso F).hom)
          (adjointFactorizationFromSourceFunctor F)).app x) := by
  -- Both whiskers are defined by whiskering the same underlying natural transformations.
  rfl

/-- Helper for Lemma 4.33.14: the left based whisker composite evaluates componentwise as the
source-unit component followed by the source-counit component. -/
private theorem adjoint_factorization_to_source_left_whisker_component
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (BasedCategory.whiskerRight (adjointFactorizationToSourceBasedUnit F)
          (adjointFactorizationToSourceBased F) ≫
        BasedCategory.whiskerLeft (adjointFactorizationToSourceBased F)
          (adjointFactorizationFromSourceBasedCounit F)).app P =
      ((adjointFactorizationToSourceBasedUnit F).app P).hom.right ≫
        (adjointFactorizationFromSourceBasedCounit F).app P.obj.right := by
  -- Unfolding the explicit based whiskers shows the pointwise composite directly.
  rfl

/-- Helper for Lemma 4.33.14: the right based whisker composite evaluates componentwise as the
source-unit component followed by the mapped source-counit component. -/
private theorem adjoint_factorization_to_source_right_whisker_component
    (F : X ⟶ Y) (x : X.S) :
    (BasedCategory.whiskerLeft (adjointFactorizationFromSourceBased F)
          (adjointFactorizationToSourceBasedUnit F) ≫
        BasedCategory.whiskerRight (adjointFactorizationFromSourceBasedCounit F)
          (adjointFactorizationFromSourceBased F)).app x =
      (adjointFactorizationToSourceBasedUnit F).app
          ((adjointFactorizationFromSourceFunctor F).obj x) ≫
        (BasedCategory.whiskerRight (adjointFactorizationFromSourceBasedCounit F)
          (adjointFactorizationFromSourceBased F)).app x := by
  -- The explicit left and right whiskers are definitionally the displayed component composite.
  rfl

/-- Helper for Lemma 4.33.14: after forgetting the owner wrapper, the left functor-side whisker
composite is the explicit unit-then-counit component on `P`. -/
private theorem adjoint_factorization_to_source_left_functor_whisker_component
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    ((Functor.whiskerRight (adjointFactorizationToSourceFunctorUnit F)
          (adjointFactorizationToSourceFunctor F) ≫
        (adjointFactorizationToSourceFunctor F).whiskerLeft
          ((adjointFactorizationToSourceFunctorCounitIso F).hom)).app P) =
      ((adjointFactorizationToSourceBasedUnit F).app P).hom.right ≫
        (adjointFactorizationFromSourceBasedCounit F).app P.obj.right := by
  -- First forget from the functor-side whiskers to the based whiskers, then expand components.
  exact (adjoint_factorization_to_source_left_whisker_app F P).symm.trans <|
    adjoint_factorization_to_source_left_whisker_component F P

/-- Helper for Lemma 4.33.14: after forgetting the owner wrapper, the right functor-side whisker
composite is the explicit unit-then-counit component on `x`. -/
private theorem adjoint_factorization_to_source_right_functor_whisker_component
    (F : X ⟶ Y) (x : X.S) :
    (((adjointFactorizationFromSourceFunctor F).whiskerLeft
          (adjointFactorizationToSourceFunctorUnit F) ≫
        Functor.whiskerRight
          ((adjointFactorizationToSourceFunctorCounitIso F).hom)
          (adjointFactorizationFromSourceFunctor F)).app x) =
      (adjointFactorizationToSourceBasedUnit F).app
          ((adjointFactorizationFromSourceFunctor F).obj x) ≫
        (BasedCategory.whiskerRight (adjointFactorizationFromSourceBasedCounit F)
          (adjointFactorizationFromSourceBased F)).app x := by
  -- First forget from the functor-side whiskers to the based whiskers, then expand components.
  exact (adjoint_factorization_to_source_right_whisker_app F x).symm.trans <|
    adjoint_factorization_to_source_right_whisker_component F x

/-- Helper for Lemma 4.33.14: once the middle owner coherence is removed, the remaining left
based whisker composite already satisfies the ordinary source adjunction triangle. -/
private theorem adjoint_factorization_to_source_left_postcoherence_triangle_app
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (BasedCategory.whiskerRight (adjointFactorizationToSourceBasedUnit F)
          (toBasedFunctor (adjointFactorizationToSource F)) ≫
        BasedCategory.whiskerLeft (toBasedFunctor (adjointFactorizationToSource F))
          (adjointFactorizationFromSourceBasedCounit F)).app P =
      ((𝟙 (adjointFactorizationToSourceFunctor F) :
        adjointFactorizationToSourceFunctor F ⟶
          adjointFactorizationToSourceFunctor F).app P) := by
  -- After forgetting the owner wrapper, the post-coherence composite is exactly the ordinary
  -- functor whisker composite, so the usual triangle identity closes it.
  exact (adjoint_factorization_to_source_left_whisker_app F P).trans <|
    adjointFactorizationToSourceFunctorAdjunction_left_triangle_app F P

/-- Helper for Lemma 4.33.14: once the middle owner coherence is removed, the remaining right
based whisker composite already satisfies the ordinary source adjunction triangle. -/
private theorem adjoint_factorization_to_source_right_postcoherence_triangle_app
    (F : X ⟶ Y) (x : X.S) :
    (BasedCategory.whiskerLeft (toBasedFunctor (adjointFactorizationFromSource F))
          (adjointFactorizationToSourceBasedUnit F) ≫
        BasedCategory.whiskerRight (adjointFactorizationFromSourceBasedCounit F)
          (toBasedFunctor (adjointFactorizationFromSource F))).app x =
      ((𝟙 (adjointFactorizationFromSourceFunctor F) :
        adjointFactorizationFromSourceFunctor F ⟶
          adjointFactorizationFromSourceFunctor F).app x) := by
  -- The right-side post-coherence composite is likewise the ordinary whisker composite.
  exact (adjoint_factorization_to_source_right_whisker_app F x).trans <|
    adjointFactorizationToSourceFunctorAdjunction_right_triangle_app F x

/-- Helper for Lemma 4.33.14: forgetting the owner wrapper on the left zigzag recovers the
ordinary left-zigzag composite for the underlying functor adjunction. -/
private theorem adjoint_factorization_to_source_owner_left_zigzag_rewrite
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (Bicategory.leftZigzag
        (fibredCategoryMorHomOfBasedNatTrans
          (F := 𝟙 (adjointFactorization F))
          (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
          (adjointFactorizationToSourceBasedUnit F))
        (fibredCategoryMorHomOfBasedNatTrans
          (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
          (G := 𝟙 X)
          (adjointFactorizationFromSourceBasedCounit F))).hom.hom.app P =
      (BasedCategory.whiskerRight (adjointFactorizationToSourceBasedUnit F)
          (toBasedFunctor (adjointFactorizationToSource F)) ≫
        (BicategoricalCoherence.assoc
            (adjointFactorizationToSource F)
            (adjointFactorizationFromSource F)
            (adjointFactorizationToSource F)
            (adjointFactorizationToSource F ≫
              adjointFactorizationFromSource F ≫
                adjointFactorizationToSource F)).1.hom.hom.hom ≫
        BasedCategory.whiskerLeft (toBasedFunctor (adjointFactorizationToSource F))
          (adjointFactorizationFromSourceBasedCounit F)).app P := by
  -- Unfold the owner left zigzag until the only nontrivial middle factor is the explicit
  -- associator-style coherence term.
  rw [CategoryTheory.Bicategory.leftZigzag, bicategoricalComp, WideSubcategory.comp_def,
    ObjectProperty.FullSubcategory.comp_hom, WideSubcategory.comp_def,
    ObjectProperty.FullSubcategory.comp_hom, fibredCategoryMor_whisker_right_hom_hom,
    fibredCategoryMor_whisker_left_hom_hom, fibredCategoryMorHomOfBasedNatTrans_hom_hom,
    adjointFactorizationToSource_counit_wrapper_hom, CategoryTheory.BicategoricalCoherence.iso]

/-- Helper for Lemma 4.33.14: forgetting the owner wrapper on the left zigzag recovers the
ordinary left-zigzag composite for the underlying functor adjunction. -/
private theorem adjoint_factorization_to_source_owner_left_zigzag_component_bridge
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (Bicategory.leftZigzag
        (fibredCategoryMorHomOfBasedNatTrans
          (F := 𝟙 (adjointFactorization F))
          (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
          (adjointFactorizationToSourceBasedUnit F))
        (fibredCategoryMorHomOfBasedNatTrans
          (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
          (G := 𝟙 X)
          (adjointFactorizationFromSourceBasedCounit F))).hom.hom.app P =
      ((Functor.whiskerRight (adjointFactorizationToSourceFunctorUnit F)
          (adjointFactorizationToSourceFunctor F) ≫
        (adjointFactorizationToSourceFunctor F).whiskerLeft
          ((adjointFactorizationToSourceFunctorCounitIso F).hom)).app P) := by
  -- Forgetting the owner wrapper exposes the ordinary whiskered unit-counit composite.
  -- Route correction: cancel the single strict-coherence factor at the based level, where the
  -- two outer whiskers are definitionally the ordinary functor whiskers.
  rw [adjoint_factorization_to_source_owner_left_zigzag_rewrite F P]
  rw [← adjoint_factorization_to_source_left_whisker_app F P]
  let leftComp :=
    (BasedCategory.whiskerRight
      (adjointFactorizationToSourceBasedUnit F)
      (toBasedFunctor (adjointFactorizationToSource F))).app P
  let rightComp :=
    (BasedCategory.whiskerLeft
      (toBasedFunctor (adjointFactorizationToSource F))
      (adjointFactorizationFromSourceBasedCounit F)).app P
  have hassoc :
      ((BicategoricalCoherence.assoc
            (adjointFactorizationToSource F)
            (adjointFactorizationFromSource F)
            (adjointFactorizationToSource F)
            (adjointFactorizationToSource F ≫
              adjointFactorizationFromSource F ≫
                adjointFactorizationToSource F)).1.hom.hom.hom).app P =
        𝟙 _ := by
    -- The middle coherence has now been reduced to the strict associator, whose component is the
    -- identity in the strict bicategory `BasedCategory`.
    exact
      (adjoint_factorization_to_source_left_middle_is_associator_app F P).trans <|
        adjoint_factorization_to_source_left_associator_app F P
  -- Rewrite the middle coherence to the identity, then reassociate once and cancel the identity.
  change leftComp ≫
      ((BicategoricalCoherence.assoc
            (adjointFactorizationToSource F)
            (adjointFactorizationFromSource F)
            (adjointFactorizationToSource F)
            (adjointFactorizationToSource F ≫
              adjointFactorizationFromSource F ≫
                adjointFactorizationToSource F)).1.hom.hom.hom.app P) ≫
        rightComp =
    leftComp ≫ rightComp
  rw [hassoc]
  calc
    leftComp ≫ 𝟙 _ ≫ rightComp = (leftComp ≫ 𝟙 _) ≫ rightComp := by
      rw [Category.assoc]
    _ = leftComp ≫ rightComp := by
      rw [Category.comp_id]

/-- Helper for Lemma 4.33.14: the right-hand unitor comparison in the owner left triangle
forgets pointwise to the identity component. -/
private theorem adjoint_factorization_to_source_owner_left_triangle_rhs_hom_app_eq_id
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (((λ_ (adjointFactorizationToSource F)).hom ≫
      (ρ_ (adjointFactorizationToSource F)).inv)).hom.hom.app P =
      ((𝟙 (adjointFactorizationToSourceFunctor F) :
        adjointFactorizationToSourceFunctor F ⟶
          adjointFactorizationToSourceFunctor F).app P) := by
  -- The unitors are strict identities after forgetting to the underlying based-natural level.
  change (CategoryTheory.BasedNatTrans.comp
      (CategoryTheory.BasedNatTrans.id (adjointFactorizationToSourceBased F))
      (CategoryTheory.BasedNatTrans.id (adjointFactorizationToSourceBased F))).app P = _
  rw [CategoryTheory.BasedNatTrans.comp]
  simp [CategoryTheory.BasedNatTrans.id]

/-- Helper for Lemma 4.33.14: the owner-level left triangle for the lifted source adjunction is
detected componentwise on the underlying functor adjunction. -/
private theorem adjoint_factorization_to_source_owner_left_triangle_app
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (Bicategory.leftZigzag
        (fibredCategoryMorHomOfBasedNatTrans
          (F := 𝟙 (adjointFactorization F))
          (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
          (adjointFactorizationToSourceBasedUnit F))
        (fibredCategoryMorHomOfBasedNatTrans
          (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
          (G := 𝟙 X)
          (adjointFactorizationFromSourceBasedCounit F))).hom.hom.app P =
      (((λ_ (adjointFactorizationToSource F)).hom ≫
        (ρ_ (adjointFactorizationToSource F)).inv)).hom.hom.app P := by
  -- Compare both owner-level sides after forgetting to the underlying functor adjunction.
  exact
    (adjoint_factorization_to_source_owner_left_zigzag_component_bridge F P).trans <|
      (adjointFactorizationToSourceFunctorAdjunction_left_triangle_app F P).trans <|
        (adjoint_factorization_to_source_owner_left_triangle_rhs_hom_app_eq_id F P).symm

/-- Helper for Lemma 4.33.14: the owner-level left triangle for the lifted source adjunction is
detected componentwise on the underlying functor adjunction. -/
theorem adjoint_factorization_to_source_owner_left_triangle
    (F : X ⟶ Y) :
    Bicategory.leftZigzag
        (fibredCategoryMorHomOfBasedNatTrans
          (F := 𝟙 (adjointFactorization F))
          (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
          (adjointFactorizationToSourceBasedUnit F))
        (fibredCategoryMorHomOfBasedNatTrans
          (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
          (G := 𝟙 X)
          (adjointFactorizationFromSourceBasedCounit F)) =
      (λ_ (adjointFactorizationToSource F)).hom ≫
        (ρ_ (adjointFactorizationToSource F)).inv := by
  -- Route correction: forget the owner wrapper first, then compare components in the underlying
  -- based natural transformations where the functor adjunction triangle is already available.
  let lhs :=
    Bicategory.leftZigzag
      (fibredCategoryMorHomOfBasedNatTrans
        (F := 𝟙 (adjointFactorization F))
        (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
        (adjointFactorizationToSourceBasedUnit F))
      (fibredCategoryMorHomOfBasedNatTrans
        (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
        (G := 𝟙 X)
        (adjointFactorizationFromSourceBasedCounit F))
  let rhs :=
    (λ_ (adjointFactorizationToSource F)).hom ≫
      (ρ_ (adjointFactorizationToSource F)).inv
  -- The hom inclusion is faithful, so it suffices to compare the underlying based
  -- natural transformations objectwise.
  apply (((fibredCategoryOverSubTwoCategory C).hom (adjointFactorization F) X).inclusion).map_injective
  change lhs.hom.hom = rhs.hom.hom
  apply BasedNatTrans.ext
  ext P
  -- After unfolding the local abbreviations, the component lemma gives the required equality.
  change (Bicategory.leftZigzag
      (fibredCategoryMorHomOfBasedNatTrans
        (F := 𝟙 (adjointFactorization F))
        (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
        (adjointFactorizationToSourceBasedUnit F))
      (fibredCategoryMorHomOfBasedNatTrans
        (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
        (G := 𝟙 X)
        (adjointFactorizationFromSourceBasedCounit F))).hom.hom.app P =
    (((λ_ (adjointFactorizationToSource F)).hom ≫
      (ρ_ (adjointFactorizationToSource F)).inv)).hom.hom.app P
  exact adjoint_factorization_to_source_owner_left_triangle_app F P

/-- Helper for Lemma 4.33.14: forgetting the owner wrapper on the right zigzag recovers the
ordinary right-zigzag composite for the underlying functor adjunction. -/
private theorem adjoint_factorization_to_source_owner_right_zigzag_rewrite
    (F : X ⟶ Y) (x : X.S) :
    (Bicategory.rightZigzag
        (fibredCategoryMorHomOfBasedNatTrans
          (F := 𝟙 (adjointFactorization F))
          (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
          (adjointFactorizationToSourceBasedUnit F))
        (fibredCategoryMorHomOfBasedNatTrans
          (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
          (G := 𝟙 X)
          (adjointFactorizationFromSourceBasedCounit F))).hom.hom.app x =
      (BasedCategory.whiskerLeft (toBasedFunctor (adjointFactorizationFromSource F))
          (adjointFactorizationToSourceBasedUnit F) ≫
        (BicategoricalCoherence.assoc'
            (adjointFactorizationFromSource F)
            (adjointFactorizationToSource F)
            (adjointFactorizationFromSource F)
            (adjointFactorizationFromSource F ≫
              adjointFactorizationToSource F ≫
                adjointFactorizationFromSource F)).1.hom.hom.hom ≫
        BasedCategory.whiskerRight (adjointFactorizationFromSourceBasedCounit F)
          (toBasedFunctor (adjointFactorizationFromSource F))).app x := by
  -- Unfold the owner right zigzag until the only nontrivial middle factor is the explicit
  -- inverse-associator coherence term.
  rw [CategoryTheory.Bicategory.rightZigzag, bicategoricalComp, WideSubcategory.comp_def,
    ObjectProperty.FullSubcategory.comp_hom, WideSubcategory.comp_def,
    ObjectProperty.FullSubcategory.comp_hom, fibredCategoryMor_whisker_left_hom_hom,
    fibredCategoryMor_whisker_right_hom_hom, fibredCategoryMorHomOfBasedNatTrans_hom_hom,
    adjointFactorizationToSource_counit_wrapper_hom, CategoryTheory.BicategoricalCoherence.iso]

/-- Helper for Lemma 4.33.14: forgetting the owner wrapper on the right zigzag recovers the
ordinary right-zigzag composite for the underlying functor adjunction. -/
private theorem adjoint_factorization_to_source_owner_right_zigzag_component_bridge
    (F : X ⟶ Y) (x : X.S) :
    (Bicategory.rightZigzag
        (fibredCategoryMorHomOfBasedNatTrans
          (F := 𝟙 (adjointFactorization F))
          (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
          (adjointFactorizationToSourceBasedUnit F))
        (fibredCategoryMorHomOfBasedNatTrans
          (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
          (G := 𝟙 X)
          (adjointFactorizationFromSourceBasedCounit F))).hom.hom.app x =
      (((adjointFactorizationFromSourceFunctor F).whiskerLeft
          (adjointFactorizationToSourceFunctorUnit F) ≫
        Functor.whiskerRight
          ((adjointFactorizationToSourceFunctorCounitIso F).hom)
          (adjointFactorizationFromSourceFunctor F)).app x) := by
  -- Forgetting the owner wrapper exposes the ordinary whiskered counit-unit composite.
  -- Route correction: cancel the single strict-coherence factor at the based level, where the
  -- two outer whiskers are definitionally the ordinary functor whiskers.
  rw [adjoint_factorization_to_source_owner_right_zigzag_rewrite F x]
  rw [← adjoint_factorization_to_source_right_whisker_app F x]
  let leftComp :=
    (BasedCategory.whiskerLeft
      (toBasedFunctor (adjointFactorizationFromSource F))
      (adjointFactorizationToSourceBasedUnit F)).app x
  let rightComp :=
    (BasedCategory.whiskerRight
      (adjointFactorizationFromSourceBasedCounit F)
      (toBasedFunctor (adjointFactorizationFromSource F))).app x
  have hassoc :
      ((BicategoricalCoherence.assoc'
            (adjointFactorizationFromSource F)
            (adjointFactorizationToSource F)
            (adjointFactorizationFromSource F)
            (adjointFactorizationFromSource F ≫
              adjointFactorizationToSource F ≫
                adjointFactorizationFromSource F)).1.hom.hom.hom).app x =
        𝟙 _ := by
    -- The inverse middle coherence is likewise reduced to the strict inverse associator, hence to
    -- the identity on the underlying source object.
    exact
      (adjoint_factorization_to_source_right_middle_is_associator_inv_app F x).trans <|
        adjoint_factorization_to_source_right_associator_inv_app F x
  -- Rewrite the middle coherence to the identity, then reassociate once and cancel the identity.
  change leftComp ≫
      ((BicategoricalCoherence.assoc'
            (adjointFactorizationFromSource F)
            (adjointFactorizationToSource F)
            (adjointFactorizationFromSource F)
            (adjointFactorizationFromSource F ≫
              adjointFactorizationToSource F ≫
                adjointFactorizationFromSource F)).1.hom.hom.hom.app x) ≫
        rightComp =
    leftComp ≫ rightComp
  rw [hassoc]
  calc
    leftComp ≫ 𝟙 _ ≫ rightComp = (leftComp ≫ 𝟙 _) ≫ rightComp := by
      rw [Category.assoc]
    _ = leftComp ≫ rightComp := by
      rw [Category.comp_id]

/-- Helper for Lemma 4.33.14: the right-hand unitor comparison in the owner right triangle
forgets pointwise to the identity component. -/
private theorem adjoint_factorization_to_source_owner_right_triangle_rhs_hom_app_eq_id
    (F : X ⟶ Y) (x : X.S) :
    (((ρ_ (adjointFactorizationFromSource F)).hom ≫
      (λ_ (adjointFactorizationFromSource F)).inv)).hom.hom.app x =
      ((𝟙 (adjointFactorizationFromSourceFunctor F) :
        adjointFactorizationFromSourceFunctor F ⟶
          adjointFactorizationFromSourceFunctor F).app x) := by
  -- The unitors are strict identities after forgetting to the underlying based-natural level.
  change (CategoryTheory.BasedNatTrans.comp
      (CategoryTheory.BasedNatTrans.id (adjointFactorizationFromSourceBased F))
      (CategoryTheory.BasedNatTrans.id (adjointFactorizationFromSourceBased F))).app x = _
  rw [CategoryTheory.BasedNatTrans.comp]
  simp [CategoryTheory.BasedNatTrans.id]
  rfl

/-- Helper for Lemma 4.33.14: the owner-level right triangle for the lifted source adjunction is
detected componentwise on the underlying functor adjunction. -/
private theorem adjoint_factorization_to_source_owner_right_triangle_app
    (F : X ⟶ Y) (x : X.S) :
    (Bicategory.rightZigzag
        (fibredCategoryMorHomOfBasedNatTrans
          (F := 𝟙 (adjointFactorization F))
          (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
          (adjointFactorizationToSourceBasedUnit F))
        (fibredCategoryMorHomOfBasedNatTrans
          (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
          (G := 𝟙 X)
          (adjointFactorizationFromSourceBasedCounit F))).hom.hom.app x =
      (((ρ_ (adjointFactorizationFromSource F)).hom ≫
        (λ_ (adjointFactorizationFromSource F)).inv)).hom.hom.app x := by
  -- Compare both owner-level sides after forgetting to the underlying functor adjunction.
  exact
    (adjoint_factorization_to_source_owner_right_zigzag_component_bridge F x).trans <|
      (adjointFactorizationToSourceFunctorAdjunction_right_triangle_app F x).trans <|
        (adjoint_factorization_to_source_owner_right_triangle_rhs_hom_app_eq_id F x).symm

/-- Helper for Lemma 4.33.14: the owner-level right triangle for the lifted source adjunction is
detected componentwise on the underlying functor adjunction. -/
theorem adjoint_factorization_to_source_owner_right_triangle
    (F : X ⟶ Y) :
    Bicategory.rightZigzag
        (fibredCategoryMorHomOfBasedNatTrans
          (F := 𝟙 (adjointFactorization F))
          (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
          (adjointFactorizationToSourceBasedUnit F))
        (fibredCategoryMorHomOfBasedNatTrans
          (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
          (G := 𝟙 X)
          (adjointFactorizationFromSourceBasedCounit F)) =
      (ρ_ (adjointFactorizationFromSource F)).hom ≫
        (λ_ (adjointFactorizationFromSource F)).inv := by
  let lhs :=
    Bicategory.rightZigzag
      (fibredCategoryMorHomOfBasedNatTrans
        (F := 𝟙 (adjointFactorization F))
        (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
        (adjointFactorizationToSourceBasedUnit F))
      (fibredCategoryMorHomOfBasedNatTrans
        (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
        (G := 𝟙 X)
        (adjointFactorizationFromSourceBasedCounit F))
  let rhs :=
    (ρ_ (adjointFactorizationFromSource F)).hom ≫
      (λ_ (adjointFactorizationFromSource F)).inv
  -- Forget to the underlying based natural transformations, where the right triangle is already
  -- the ordinary functor-adjunction triangle.
  apply (((fibredCategoryOverSubTwoCategory C).hom X (adjointFactorization F)).inclusion).map_injective
  change lhs.hom.hom = rhs.hom.hom
  apply BasedNatTrans.ext
  ext x
  -- After unfolding the local abbreviations, the component lemma gives the required equality.
  change (Bicategory.rightZigzag
      (fibredCategoryMorHomOfBasedNatTrans
        (F := 𝟙 (adjointFactorization F))
        (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
        (adjointFactorizationToSourceBasedUnit F))
      (fibredCategoryMorHomOfBasedNatTrans
        (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
        (G := 𝟙 X)
        (adjointFactorizationFromSourceBasedCounit F))).hom.hom.app x =
    (((ρ_ (adjointFactorizationFromSource F)).hom ≫
      (λ_ (adjointFactorizationFromSource F)).inv)).hom.hom.app x
  exact adjoint_factorization_to_source_owner_right_triangle_app F x

/-- The projection `X' ⟶ X` is left adjoint over `C` to the canonical source map `X ⟶ X'`. -/
noncomputable def adjointFactorizationToSource_adjunction
    (F : X ⟶ Y) :
    adjointFactorizationToSource F ⊣ adjointFactorizationFromSource F := by
  -- Package the existing based unit and counit into the owner hom-category.
  let etaMor :
      𝟙 (adjointFactorization F) ⟶
        adjointFactorizationToSource F ≫ adjointFactorizationFromSource F :=
    fibredCategoryMorHomOfBasedNatTrans
      (F := 𝟙 (adjointFactorization F))
      (G := adjointFactorizationToSource F ≫ adjointFactorizationFromSource F)
      (adjointFactorizationToSourceBasedUnit F)
  let epsMor :
      adjointFactorizationFromSource F ≫ adjointFactorizationToSource F ⟶ 𝟙 X :=
    fibredCategoryMorHomOfBasedNatTrans
      (F := adjointFactorizationFromSource F ≫ adjointFactorizationToSource F)
      (G := 𝟙 X)
      (adjointFactorizationFromSourceBasedCounit F)
  refine
    { unit := etaMor
      counit := epsMor
      left_triangle := adjoint_factorization_to_source_owner_left_triangle F
      right_triangle := adjoint_factorization_to_source_owner_right_triangle F }

/-- Helper for Lemma 4.33.14: every target arrow `c : y' ⟶ P.left` factors through the chosen
left pullback map of `P` over `Y.p.map c` by a vertical arrow. -/
private theorem adjoint_factorization_to_target_left_factor_exists
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) (y' : Y.S)
    (c : y' ⟶ P.obj.left) :
    ∃ c' : y' ⟶ adjointFactorization_projection_pullback_left_obj F P (Y.p.map c),
      Y.p.IsHomLift (𝟙 (Y.p.obj y')) c' ∧
        c' ≫ adjointFactorization_projection_pullback_left_hom F P (Y.p.map c) = c := by
  letI :
      Y.p.IsStronglyCartesian
        (Y.p.map c)
        (adjointFactorization_projection_pullback_left_hom F P (Y.p.map c)) :=
    adjointFactorization_projection_pullback_left_isStronglyCartesian F P (Y.p.map c)
  have hc :
      Y.p.IsHomLift ((𝟙 (Y.p.obj y')) ≫ Y.p.map c) c := by
    simpa using (show Y.p.IsHomLift (Y.p.map c) c from inferInstance)
  -- Factor `c` through the chosen left pullback map using its strong-cartesian universal property.
  obtain ⟨c', hc', _⟩ :=
    Functor.IsStronglyCartesian.universal_property
      Y.p
      (Y.p.map c)
      (adjointFactorization_projection_pullback_left_hom F P (Y.p.map c))
      (𝟙 (Y.p.obj y'))
      ((𝟙 (Y.p.obj y')) ≫ Y.p.map c)
      rfl
      c
  exact ⟨c', hc'.1, hc'.2⟩

/-- The target projection `X' ⟶ Y` is fibred on the underlying total categories. -/
private theorem adjointFactorization_toTarget_lift_exists_isStronglyCartesian
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) (y' : Y.S)
    (c : y' ⟶ (adjointFactorizationToTargetFunctor F).obj P) :
    ∃ Q : AdjointFactorizationObject F, ∃ η : Q ⟶ P,
      (adjointFactorizationToTargetFunctor F).IsStronglyCartesian c η := by
  obtain ⟨c', hc'lift, hc'fac⟩ :=
    adjoint_factorization_to_target_left_factor_exists F P y' c
  let Q : AdjointFactorizationObject F :=
    ⟨{ left := y'
       right := adjointFactorization_projection_pullback_right_obj F P (Y.p.map c)
       hom := c' ≫ adjointFactorization_projection_pullback_comparison F P (Y.p.map c) }, by
      -- The new comparison arrow is vertical because both factors are vertical over the identity.
      letI : Y.p.IsHomLift (𝟙 (Y.p.obj y')) c' := hc'lift
      letI :
          Y.p.IsHomLift
            (𝟙 (Y.p.obj y'))
            (adjointFactorization_projection_pullback_comparison F P (Y.p.map c)) := by
        -- The pullback comparison lives over the identity of the left pullback object's base.
        simpa [IsHomLift.domain_eq Y.p (𝟙 (Y.p.obj y')) c'] using
          adjointFactorization_projection_pullback_comparison_isHomLift F P (Y.p.map c)
      simpa [Category.assoc] using
        (show Y.p.IsHomLift (𝟙 (Y.p.obj y'))
            (c' ≫ adjointFactorization_projection_pullback_comparison F P (Y.p.map c)) from
          inferInstance)⟩
  let η : Q ⟶ P :=
    ObjectProperty.homMk
      { left := c
        right := adjointFactorization_projection_pullback_right_hom F P (Y.p.map c)
        w := by
          -- Postcompose with the mapped right pullback map and use the chosen factorization
          -- `c = c' ≫ left_hom`.
          calc
            c ≫ P.obj.hom
                = c' ≫ adjointFactorization_projection_pullback_left_hom F P (Y.p.map c) ≫
                    P.obj.hom := by
                      simpa [Category.assoc] using
                        (congrArg (fun k ↦ k ≫ P.obj.hom) hc'fac).symm
            _ = c' ≫ adjointFactorization_projection_pullback_comparison F P (Y.p.map c) ≫
                  (toFunctor F).map
                    (adjointFactorization_projection_pullback_right_hom F P (Y.p.map c)) := by
                  simpa [Q, Category.assoc] using
                    congrArg (fun k ↦ c' ≫ k)
                      (adjointFactorization_projection_pullback_comparison_fac F P (Y.p.map c))
            _ = Q.obj.hom ≫
                  (toFunctor F).map
                    (adjointFactorization_projection_pullback_right_hom F P (Y.p.map c)) := by
                  simpa [Q] }
  refine ⟨Q, η, ?_⟩
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · -- The target projection of `η` is literally the chosen arrow `c`.
    simpa [adjointFactorizationToTargetFunctor, η] using
      (show (adjointFactorizationToTargetFunctor F).IsHomLift
          ((adjointFactorizationToTargetFunctor F).map η) η from inferInstance)
  · intro R g τ hτ
    have hτleft :
        τ.hom.left = g ≫ c := by
      symm
      simpa [adjointFactorizationToTargetFunctor] using
        (IsHomLift.eq_of_isHomLift
          (p := adjointFactorizationToTargetFunctor F)
          (g ≫ c)
          τ)
    have hτleftLift :
        Y.p.IsHomLift (Y.p.map (g ≫ c)) τ.hom.left := by
      rw [hτleft]
      exact (show Y.p.IsHomLift (Y.p.map (g ≫ c)) (g ≫ c) from inferInstance)
    have hτproj :
        (adjointFactorizationProjection F).IsHomLift (Y.p.map (g ≫ c)) τ := by
      exact (adjointFactorization_toTarget_hom_isHomLift_iff F (Y.p.map (g ≫ c)) τ).1 hτleftLift
    have hτright0 :
        X.p.IsHomLift (Y.p.map (g ≫ c)) τ.hom.right := by
      exact (adjointFactorization_toSource_hom_isHomLift_iff F (Y.p.map (g ≫ c)) τ).2 hτproj
    have hτright :
        X.p.IsHomLift
          (Y.p.map g ≫ adjointFactorization_projection_pullback_right_base F P (Y.p.map c))
          τ.hom.right := by
      have hτright' :
          X.p.IsHomLift
            (Y.p.map (g ≫ c) ≫ eqToHom (adjointFactorizationObject_base_eq F P).symm)
            τ.hom.right := by
        exact
          (IsHomLift.lift_comp_eqToHom_iff
            X.p
            (Y.p.map (g ≫ c))
            τ.hom.right
            (adjointFactorizationObject_base_eq F P).symm).2
            hτright0
      simpa [adjointFactorization_projection_pullback_right_base, Functor.map_comp,
        Category.assoc] using hτright'
    letI :
        X.p.IsStronglyCartesian
          (adjointFactorization_projection_pullback_right_base F P (Y.p.map c))
          (adjointFactorization_projection_pullback_right_hom F P (Y.p.map c)) :=
      adjointFactorization_projection_pullback_right_isStronglyCartesian F P (Y.p.map c)
    letI :
        X.p.IsHomLift
          (Y.p.map g ≫ adjointFactorization_projection_pullback_right_base F P (Y.p.map c))
          τ.hom.right :=
      hτright
    obtain ⟨χright, hχright, hχright_uniq⟩ :=
      Functor.IsStronglyCartesian.universal_property
        X.p
        (adjointFactorization_projection_pullback_right_base F P (Y.p.map c))
        (adjointFactorization_projection_pullback_right_hom F P (Y.p.map c))
        (Y.p.map g)
        (Y.p.map g ≫ adjointFactorization_projection_pullback_right_base F P (Y.p.map c))
        rfl
        τ.hom.right
    let lhs : R.obj.left ⟶ (toFunctor F).obj Q.obj.right :=
      g ≫ Q.obj.hom
    let rhs : R.obj.left ⟶ (toFunctor F).obj Q.obj.right :=
      R.obj.hom ≫ (toFunctor F).map χright
    have hlhs :
        Y.p.IsHomLift (Y.p.map g) lhs := by
      letI : Y.p.IsHomLift (Y.p.map g) g := by infer_instance
      letI :
          Y.p.IsHomLift (𝟙 (Y.p.obj y'))
            (c' ≫ adjointFactorization_projection_pullback_comparison F P (Y.p.map c)) := by
        letI : Y.p.IsHomLift (𝟙 (Y.p.obj y')) c' := hc'lift
        letI :
            Y.p.IsHomLift
              (𝟙 (Y.p.obj y'))
              (adjointFactorization_projection_pullback_comparison F P (Y.p.map c)) := by
          simpa [IsHomLift.domain_eq Y.p (𝟙 (Y.p.obj y')) c'] using
            adjointFactorization_projection_pullback_comparison_isHomLift F P (Y.p.map c)
        simpa [Category.assoc] using
          (show Y.p.IsHomLift (𝟙 (Y.p.obj y'))
              (c' ≫ adjointFactorization_projection_pullback_comparison F P (Y.p.map c)) from
            inferInstance)
      simpa [lhs, Q, Category.assoc] using
        (show Y.p.IsHomLift (Y.p.map g)
            (g ≫ (c' ≫ adjointFactorization_projection_pullback_comparison F P (Y.p.map c))) from
          inferInstance)
    have hrhs :
        Y.p.IsHomLift (Y.p.map g) rhs := by
      have hχmap :
          Y.p.IsHomLift (Y.p.map g) ((toFunctor F).map χright) :=
        ((toBasedFunctor F).isHomLift_iff (Y.p.map g) χright).2 hχright.1
      letI : Y.p.IsHomLift (𝟙 (Y.p.obj R.obj.left)) R.obj.hom := R.property
      letI : Y.p.IsHomLift (Y.p.map g) ((toFunctor F).map χright) := hχmap
      have hrhs' :
          Y.p.IsHomLift (Y.p.map g) (R.obj.hom ≫ (toFunctor F).map χright) := by
        simpa using
          (IsHomLift.comp_lift_id_left'
            (p := Y.p)
            (R := Y.p.obj R.obj.left)
            (φ := R.obj.hom)
            (f := Y.p.map g)
            (ψ := (toFunctor F).map χright))
      simpa [rhs, Category.assoc] using hrhs'
    have hχw :
        g ≫ Q.obj.hom = R.obj.hom ≫ (toFunctor F).map χright := by
      -- Route correction: compare the two candidate comparison arrows only after postcomposing
      -- with the mapped right pullback arrow, then cancel that strongly cartesian map.
      let mappedRight :=
        (toFunctor F).map (adjointFactorization_projection_pullback_right_hom F P (Y.p.map c))
      letI :
          Y.p.IsStronglyCartesian
            (adjointFactorization_projection_pullback_target_base F P (Y.p.map c))
            mappedRight :=
        adjointFactorization_projection_pullback_right_map_isStronglyCartesian F P (Y.p.map c)
      letI : Y.p.IsHomLift (Y.p.map g) lhs := hlhs
      letI : Y.p.IsHomLift (Y.p.map g) rhs := hrhs
      have hτpost :
          g ≫ c ≫ P.obj.hom = R.obj.hom ≫ (toFunctor F).map τ.hom.right := by
        simpa [Category.assoc, hτleft] using τ.hom.w
      have hτrhs :
          g ≫ c ≫ P.obj.hom = rhs ≫ mappedRight := by
        refine hτpost.trans ?_
        simpa [rhs, mappedRight, Functor.map_comp, Category.assoc] using
          congrArg (fun k ↦ R.obj.hom ≫ (toFunctor F).map k) hχright.2.symm
      have hlhs_post :
          lhs ≫ mappedRight = g ≫ c ≫ P.obj.hom := by
        calc
          lhs ≫ mappedRight
              = g ≫ c' ≫
                  adjointFactorization_projection_pullback_comparison F P (Y.p.map c) ≫
                    mappedRight := by
                      simp [lhs, Q, Category.assoc]
          _ = g ≫ c' ≫
                adjointFactorization_projection_pullback_left_hom F P (Y.p.map c) ≫
                  P.obj.hom := by
                    simpa [mappedRight, Category.assoc] using
                      congrArg (fun k ↦ g ≫ c' ≫ k)
                        (adjointFactorization_projection_pullback_comparison_fac F P (Y.p.map c))
          _ = g ≫ c ≫ P.obj.hom := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ g ≫ k ≫ P.obj.hom) hc'fac
      have hwpost : lhs ≫ mappedRight = rhs ≫ mappedRight := by
        exact hlhs_post.trans hτrhs
      exact
        Functor.IsStronglyCartesian.ext
          (p := Y.p)
          (f := adjointFactorization_projection_pullback_target_base F P (Y.p.map c))
          (φ := mappedRight)
          (g := Y.p.map g)
          (ψ := lhs)
          (ψ' := rhs)
          hwpost
    let χ : R ⟶ Q :=
      ObjectProperty.homMk
        { left := g
          right := χright
          w := hχw }
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · -- The new morphism projects to `g` because we fixed the left component to be exactly `g`.
      simpa [adjointFactorizationToTargetFunctor, χ] using
        (show (adjointFactorizationToTargetFunctor F).IsHomLift
            ((adjointFactorizationToTargetFunctor F).map χ) χ from inferInstance)
    · -- The factorization through `η` is componentwise the chosen right pullback factorization.
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact hτleft.symm
      · simpa [χ, η, Q, Category.assoc] using hχright.2
    · intro ξ hξ
      have hξlift : (adjointFactorizationToTargetFunctor F).IsHomLift g ξ := hξ.1
      have hξleft :
          ξ.hom.left = g := by
        letI : (adjointFactorizationToTargetFunctor F).IsHomLift g ξ := hξlift
        have hfac :
            g = (adjointFactorizationToTargetFunctor F).map ξ := by
          simpa using (IsHomLift.fac
            (p := adjointFactorizationToTargetFunctor F)
            (f := g)
            (φ := ξ))
        simpa [adjointFactorizationToTargetFunctor] using hfac.symm
      have hξleftLift :
          Y.p.IsHomLift (Y.p.map g) ξ.hom.left := by
        rw [hξleft]
        exact (show Y.p.IsHomLift (Y.p.map g) g from inferInstance)
      have hξproj :
          (adjointFactorizationProjection F).IsHomLift (Y.p.map g) ξ := by
        exact (adjointFactorization_toTarget_hom_isHomLift_iff F (Y.p.map g) ξ).1 hξleftLift
      have hξright :
          X.p.IsHomLift (Y.p.map g) ξ.hom.right := by
        exact (adjointFactorization_toSource_hom_isHomLift_iff F (Y.p.map g) ξ).2 hξproj
      have hξright_fac :
          ξ.hom.right ≫ adjointFactorization_projection_pullback_right_hom F P (Y.p.map c) =
            τ.hom.right := by
        simpa [χ, η, Q, Category.assoc] using congrArg (fun f ↦ f.hom.right) hξ.2
      have hχright_self : χ.hom.right = χright := rfl
      have hξright_eq : ξ.hom.right = χ.hom.right := by
        exact (hχright_uniq _ ⟨hξright, hξright_fac⟩).trans hχright_self.symm
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact hξleft.trans rfl
      · exact hξright_eq

/-- The target projection `X' ⟶ Y` is fibred on the underlying total categories. -/
theorem adjointFactorizationToTarget_isFibered
    (F : X ⟶ Y) :
    (toFunctor (adjointFactorizationToTarget F)).IsFibered := by
  -- Close fibredness once the textbook target-side lift has been isolated as a reusable helper.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro P y' c
  -- The helper supplies the strongly cartesian lift over the chosen arrow `c : y' ⟶ P.obj.left`.
  exact adjointFactorization_toTarget_lift_exists_isStronglyCartesian F P y' c

/-- The canonical source map followed by the target projection recovers `F`. -/
theorem adjointFactorization_comp
    (F : X ⟶ Y) :
    adjointFactorizationFromSource F ≫ adjointFactorizationToTarget F = F := by
  -- The canonical object `(x, F(x), id)` projects back to `F(x)` with map component `F.map`.
  rfl

-- Proof sketch: use the vertical full subcategory of `Comma (𝟭 Y.S) (toFunctor F)`. Its
-- projection to `X` is left adjoint over `C` to the canonical source map
-- `x ↦ (F(x) ⟶ F(x))`, that source map is fully faithful, and the projection to `Y` is fibred and
-- composes with it to recover `F` in the category of fibred categories over `C`.
/-- Lemma 4.33.14: every `1`-morphism of fibred categories over `C` factors through a fully
faithful `1`-morphism admitting a left adjoint over `C`, followed by a fibred functor to the
target. -/
theorem exists_adjoint_fibred_factorization
    (F : X ⟶ Y) :
    ∃ X' : FibredCategoryOver C,
      ∃ u : X ⟶ X',
              ∃ v : X' ⟶ Y,
            ∃ w : X' ⟶ X,
              ∃ _ : (toFunctor u).FullyFaithful,
              ∃ _ : w ⊣ u,
                ∃ _ : (toFunctor v).IsFibered,
                  (u ≫ v : X ⟶ Y) = F := by
  show ∃ X' : FibredCategoryOver C,
      ∃ u : X ⟶ X',
        ∃ v : X' ⟶ Y,
          ∃ w : X' ⟶ X,
            ∃ _ : (toFunctor u).FullyFaithful,
              ∃ _ : w ⊣ u,
                ∃ _ : (toFunctor v).IsFibered,
                  (u ≫ v : X ⟶ Y) = F
  refine ⟨adjointFactorization F, adjointFactorizationFromSource F, adjointFactorizationToTarget F,
    adjointFactorizationToSource F, ?_, ?_, ?_, ?_⟩
  · simpa using adjointFactorizationFromSource_fullyFaithful F
  · simpa using adjointFactorizationToSource_adjunction F
  · simpa using adjointFactorizationToTarget_isFibered F
  · simpa using adjointFactorization_comp F

end

end CategoryTheory.FibredCategoryMor
