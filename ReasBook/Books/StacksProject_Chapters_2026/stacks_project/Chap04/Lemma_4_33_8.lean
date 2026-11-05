module

public import stacks_project.Chap04.Definition_4_32_1
public import stacks_project.Chap04.Definition_4_33_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u vS uS

namespace CategoryTheory

open BasedFunctor
open Bicategory
open Functor IsHomLift IsStronglyCartesian
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : BasedCategory.{vS, uS} C}

/- Domain-style sampling for Lemma 4.33.8:
- primary domain: fibered categories over a fixed base, and invariance of strong cartesianness /
  fibredness under equivalence in `Cat/C`;
- sampled owner API:
  `BasedFunctor.IsEquivalenceOverBase`,
  `Functor.IsStronglyCartesian`,
  `Functor.IsFibered`,
  `Functor.isFibered_iff_exists_isStronglyCartesian`,
  `BasedCategory` and `BasedFunctor`;
- best owner abstractions: `BasedFunctor.IsEquivalenceOverBase` for equivalences in `Cat/C`,
  together with `Functor.IsStronglyCartesian` and `Functor.IsFibered` for the transported owner
  properties.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a based equivalence over `C` preserves fibredness;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase`, `Functor.IsStronglyCartesian`, and
  `Functor.IsFibered`;
- `bridge/view`: the explicit `EquivalenceOverBase` data attached to an owner-level
  `IsEquivalenceOverBase` hypothesis, used to transport strongly cartesian lifts across the
  quasi-inverse and the vertical unit/counit isomorphisms.

Primitive-vs-derived split:
- primitive data: the based categories `X`, `Y`, the based functor `F : X ⥤ᵇ Y`, the owner
  predicate `F.IsEquivalenceOverBase`, and the upstream owner predicates on the projection
  functors `X.p` and `Y.p`;
- derived API: the transport theorem for strongly cartesian morphisms and the resulting
  equivalence-invariance statement for fibredness. -/

namespace BasedFunctor

/-- Helper for Lemma 4.33.8: pulling a lifting problem back across the inverse in an explicit
equivalence over the base preserves the same base morphism. -/
lemma inverse_transport_lift_over_base
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (ψ : z ⟶ F.obj y)
    [Y.p.IsHomLift (g ≫ Y.p.map (F.map φ)) ψ] :
    X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ)
      (e.inverse.map ψ ≫ e.unitIso.inv.app y) := by
  -- Rewrite the target lifting problem into the source base coordinates using the over-base
  -- equation attached to `F`.
  have hψY : Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ := by
    refine IsHomLift.of_fac Y.p _ ψ rfl (F.w_obj y) ?_
    have hbase :
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
      calc
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ
            = g ≫ Y.p.map (F.map φ) ≫ eqToHom (F.w_obj y) := by
                simpa [Category.assoc] using
                  (congrArg (fun k ↦ g ≫ k ≫ eqToHom (F.w_obj y))
                    (Functor.congr_hom F.w φ)).symm
        _ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ eqToHom (F.w_obj y))
                  (IsHomLift.eq_of_isHomLift Y.p (g ≫ Y.p.map (F.map φ)) ψ)
    simpa [Category.assoc] using hbase
  -- Pull the given lifted arrow back across the quasi-inverse.
  have hψX : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) :=
    (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ).2 hψY
  -- The unit component is vertical, so composing with it keeps the same base map.
  have hη : X.p.IsHomLift (𝟙 (X.p.obj y)) (e.unitIso.inv.app y) := by
    simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj y = X.p.obj y)
  exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
    (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) hψX
    (X.p.obj y) (e.unitIso.inv.app y) hη

/-- Helper for Lemma 4.33.8: pushing a lifted morphism forward across the chosen equivalence over
the base preserves the same base morphism. -/
lemma forward_transport_lift_over_base
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (g : Y.p.obj z ⟶ X.p.obj x)
    (ξ : e.inverse.obj z ⟶ x)
    [X.p.IsHomLift g ξ] :
    Y.p.IsHomLift g (e.toEquivalence.counit.inv.app z ≫ F.map ξ) := by
  let E := e.toEquivalence
  -- Push the source lift forward along `F`, then precompose with the vertical counit inverse.
  have hξY : Y.p.IsHomLift g (F.map ξ) :=
    (F.isHomLift_iff g ξ).2 (show X.p.IsHomLift g ξ from inferInstance)
  -- The counit component is vertical, so precomposing with it preserves the base map.
  have hε : Y.p.IsHomLift (𝟙 (Y.p.obj z)) (E.counit.inv.app z) := by
    simpa [E] using BasedNatTrans.isHomLift E.counit.inv
      (rfl : Y.p.obj z = Y.p.obj z)
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
    (Y.p.obj z) (E.counit.inv.app z) hε _ _ g (F.map ξ) hξY

/-- Helper for Lemma 4.33.8: appending the canonical base-change isomorphism from `F.w_obj`
does not change whether a target morphism is a lift. -/
lemma isHomLift_over_target_eq_iff
    (F : X ⥤ᵇ Y) {z : Y.obj} {x : X.obj}
    (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (θ : z ⟶ F.obj x) :
    Y.p.IsHomLift g θ ↔ Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) θ := by
  -- The extra `eqToHom` only rewrites the codomain to the source-side base coordinates.
  simpa using IsHomLift.lift_comp_eqToHom_iff Y.p g θ (F.w_obj x)

/-- Helper for Lemma 4.33.8: a target-side factorization pulls back along the inverse together
with the unit inverse to the corresponding source-side factorization. -/
lemma pullback_factorization_of_map_factorization
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} {τ' : z ⟶ F.obj x} {ψ' : z ⟶ F.obj y}
    (hτ' : τ' ≫ F.map φ = ψ') :
    (e.inverse.map τ' ≫ e.unitIso.inv.app x) ≫ φ =
      e.inverse.map ψ' ≫ e.unitIso.inv.app y := by
  -- Rewrite the pulled-back `F.map φ` term using naturality of the unit inverse.
  calc
    (e.inverse.map τ' ≫ e.unitIso.inv.app x) ≫ φ
        = e.inverse.map τ' ≫ (e.unitIso.inv.app x ≫ φ) := by
            simp [Category.assoc]
    _ = e.inverse.map τ' ≫ (e.inverse.map (F.map φ) ≫ e.unitIso.inv.app y) := by
          simpa [Category.assoc] using
            (congrArg (fun k ↦ e.inverse.map τ' ≫ k) (e.unitIso.inv.naturality φ)).symm
    _ = e.inverse.map (τ' ≫ F.map φ) ≫ e.unitIso.inv.app y := by
          simp [Functor.map_comp, Category.assoc]
    _ = e.inverse.map ψ' ≫ e.unitIso.inv.app y := by
          rw [hτ']

/-- Helper for Lemma 4.33.8: after forgetting the based data, the component of the adjointified
left triangle is exactly the corresponding component equality of ordinary natural isomorphisms. -/
lemma adjointified_left_triangle_component_iso
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    ((BasedNatTrans.forgetful X Y).mapIso
        (Bicategory.leftZigzagIso e.toEquivalence.unit e.toEquivalence.counit)).hom.app x =
      ((BasedNatTrans.forgetful X Y).mapIso
        (λ_ e.toEquivalence.hom ≪≫ (ρ_ e.toEquivalence.hom).symm)).hom.app x := by
  -- Forget the based 2-isomorphism to the ordinary functor category and evaluate at `x`.
  let Φ := congrArg (Functor.mapIso (BasedNatTrans.forgetful X Y)) e.toEquivalence.left_triangle
  -- This is the component form of the adjointified left triangle in the underlying category.
  exact congrArg (fun η => η.hom.app x) Φ

/-- Helper for Lemma 4.33.8: the inverse component of the forgotten adjointified left triangle is
the raw inverse comparison that underlies the desired push-pull identity. -/
lemma adjointified_left_triangle_inverse_component_iso
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    ((BasedNatTrans.forgetful X Y).mapIso
        (Bicategory.leftZigzagIso e.toEquivalence.unit e.toEquivalence.counit)).inv.app x =
      ((BasedNatTrans.forgetful X Y).mapIso
        (λ_ e.toEquivalence.hom ≪≫ (ρ_ e.toEquivalence.hom).symm)).inv.app x := by
  -- Take the inverse component of the same forgotten left-triangle isomorphism.
  let Φ := congrArg (Functor.mapIso (BasedNatTrans.forgetful X Y)) e.toEquivalence.left_triangle
  -- This is the unsimplified inverse triangle comparison used in the remaining blocker.
  exact congrArg (fun η => η.inv.app x) Φ

/-- Helper for Lemma 4.33.8: the strict associator component in the forgotten functor-category
left-triangle comparison is the identity map on each object. -/
lemma forgotten_triangle_associator_component_eq_id
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    (CategoryTheory.Bicategory.associator (e.toEquivalence.hom) (e.toEquivalence.inv) F).hom.app x =
      𝟙 (((e.toEquivalence.hom ≫ e.toEquivalence.inv) ≫ F).obj x) := by
  -- In the strict bicategory of categories over `C`, the associator is an `eqToIso`, so its
  -- component forgets to the identity arrow.
  simp [CategoryTheory.Bicategory.Strict.associator_eqToIso]
  rfl

/-- Helper for Lemma 4.33.8: the left unitor component on a based functor is the identity on each
object after forgetting to the underlying functor category. -/
lemma forgotten_triangle_left_unitor_component_eq_id
    (F : X ⥤ᵇ Y) (x : X.obj) :
    (CategoryTheory.Bicategory.leftUnitor (B := BasedCategory C) F).hom.app x = 𝟙 (F.obj x) := by
  -- The strict left unitor is also an `eqToIso`, hence has identity components.
  simp [CategoryTheory.Bicategory.Strict.leftUnitor_eqToIso]
  rfl

/-- Helper for Lemma 4.33.8: the inverse right-unitor component on a based functor is the
identity on each object after forgetting to the underlying functor category. -/
lemma forgotten_triangle_right_unitor_inv_component_eq_id
    (F : X ⥤ᵇ Y) (x : X.obj) :
    (CategoryTheory.Bicategory.rightUnitor (B := BasedCategory C) F).inv.app x =
      𝟙 (F.obj x) := by
  -- The strict right unitor is an `eqToIso`, so its inverse component is still the identity.
  simp [CategoryTheory.Bicategory.Strict.rightUnitor_eqToIso]
  rfl

/-- Helper for Lemma 4.33.8: the forgotten left-zigzag component is the ordinary composite of the
unit component followed by the counit component. -/
lemma forgotten_left_zigzag_hom_app
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    (CategoryTheory.Bicategory.leftZigzag e.toEquivalence.unit.hom
        e.toEquivalence.counit.hom).app x =
      F.map (e.unitIso.hom.app x) ≫ e.toEquivalence.counit.hom.app (F.obj x) := by
  -- Expand the inserted bicategorical coherence, then collapse the strict associator and the
  -- whiskered identity component.
  change F.map (e.unitIso.hom.app x) ≫
      ((CategoryTheory.BicategoricalCoherence.iso.hom :
        ((e.toEquivalence.hom ≫ e.toEquivalence.inv) ≫ e.toEquivalence.hom) ⟶
          e.toEquivalence.hom ≫ (e.toEquivalence.inv ≫ e.toEquivalence.hom)).app x) ≫
      e.toEquivalence.counit.hom.app (F.obj x) = _
  dsimp [CategoryTheory.BicategoricalCoherence.iso, CategoryTheory.BicategoricalCoherence.assoc]
  change F.map (e.unitIso.hom.app x) ≫
      ((α_ e.toEquivalence.hom e.toEquivalence.inv e.toEquivalence.hom).hom.app x ≫
        (CategoryTheory.BasedCategory.whiskerRight
          (CategoryTheory.BasedNatTrans.id F) (e.inverse ⋙ F)).app x) ≫
      e.toEquivalence.counit.hom.app (F.obj x) = _
  have hassoc :
      (α_ e.toEquivalence.hom e.toEquivalence.inv e.toEquivalence.hom).hom.app x =
        𝟙 (((e.toEquivalence.hom ≫ e.toEquivalence.inv) ≫ e.toEquivalence.hom).obj x) := by
    -- The strict associator contributes only the identity component after forgetting.
    simpa using forgotten_triangle_associator_component_eq_id F e x
  rw [hassoc]
  simp [CategoryTheory.BasedCategory.whiskerRight, CategoryTheory.BasedNatTrans.id]

/-- Helper for Lemma 4.33.8: the forgotten hom-side right-hand comparison in the left triangle is
the identity map on each object. -/
lemma forgotten_left_triangle_rhs_hom_app_eq_id
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    ((λ_ e.toEquivalence.hom).hom ≫ (ρ_ e.toEquivalence.hom).inv).app x = 𝟙 (F.obj x) := by
  -- Both unitors are strict identities in `BasedCategory`, so the composite stays the identity.
  change (CategoryTheory.BasedNatTrans.comp (CategoryTheory.BasedNatTrans.id F)
      (CategoryTheory.BasedNatTrans.id F)).app x = _
  rw [CategoryTheory.BasedNatTrans.comp]
  simp [CategoryTheory.BasedNatTrans.id]

/-- Helper for Lemma 4.33.8: after forgetting the based adjointified left triangle, the hom-side
component reduces to the ordinary unit-counit cancellation formula. -/
lemma forgotten_left_triangle_hom_component_simplified
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    F.map (e.unitIso.hom.app x) ≫ e.toEquivalence.counit.hom.app (F.obj x) = 𝟙 (F.obj x) := by
  -- Route correction: evaluate the bicategorical left triangle at `x`, then rewrite its two sides
  -- into the ordinary unit-counit composite and the identity map on `F.obj x`.
  have htriangle :=
    congrArg (fun η ↦ η.app x) (CategoryTheory.Bicategory.Equivalence.left_triangle_hom
      e.toEquivalence)
  have htriangle' :
      (CategoryTheory.Bicategory.leftZigzag e.toEquivalence.unit.hom
          e.toEquivalence.counit.hom).app x =
        ((λ_ e.toEquivalence.hom).hom ≫ (ρ_ e.toEquivalence.hom).inv).app x := by
    simpa using htriangle
  -- The adapter lemmas identify the two bicategorical sides with the ordinary maps used
  -- downstream in the transport proof.
  exact (forgotten_left_zigzag_hom_app F e x).symm.trans <|
    htriangle'.trans (forgotten_left_triangle_rhs_hom_app_eq_id F e x)

/-- Helper for Lemma 4.33.8: the inverse counit component of the adjointified equivalence
cancels the raw unit inverse on each target object. -/
lemma adjointified_left_triangle_inverse_component_simplified
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    e.toEquivalence.counit.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) = 𝟙 (F.obj x) := by
  -- Package the forgotten based data as an ordinary equivalence and use its inverse triangle
  -- identity instead of normalizing the inverse left-triangle component directly.
  let E : X.obj ≌ Y.obj :=
    CategoryTheory.Equivalence.mk'
      F.toFunctor e.inverse.toFunctor
      ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
      ((BasedNatTrans.forgetful Y Y).mapIso e.toEquivalence.counit)
      (fun x ↦ by
        simpa using forgotten_left_triangle_hom_component_simplified F e x)
  simpa [E] using E.counitIso_functor_comp x

/-- Helper for Lemma 4.33.8: pushing the pulled-back morphism forward with the adjointified
counit inverse recovers the original target morphism. -/
lemma pushforward_pullback_eq
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (θ : z ⟶ F.obj x) :
    e.toEquivalence.counit.inv.app z ≫
        F.map (e.inverse.map θ ≫ e.unitIso.inv.app x) = θ := by
  -- Move `θ` across the counit inverse, then collapse the remaining counit-unit tail.
  rw [Functor.map_comp]
  have hnat :
      e.toEquivalence.counit.inv.app z ≫ F.map (e.inverse.map θ) ≫
          F.map (e.unitIso.inv.app x) =
        θ ≫ e.toEquivalence.counit.inv.app (F.obj x) ≫
          F.map (e.unitIso.inv.app x) := by
    simpa [Functor.comp_map, Category.assoc] using
      (congrArg (fun k ↦ k ≫ F.map (e.unitIso.inv.app x))
        (e.toEquivalence.counit.inv.naturality θ)).symm
  have htail :
      θ ≫ e.toEquivalence.counit.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) = θ := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ θ ≫ k)
        (adjointified_left_triangle_inverse_component_simplified F e x)
  exact hnat.trans htail

/-- An equivalence over the base category sends strongly cartesian morphisms to strongly
cartesian morphisms. The base map is taken in the owner form from the source morphism `φ`. -/
theorem isStronglyCartesian_map_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase)
    {x y : X.obj} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  refine
    { toIsHomLift := by
        infer_instance
      universal_property' := ?_ }
  intro z g ψ' hψ'
  -- Pull the problem back to `X` and solve it there using the strong cartesianness of `φ`.
  let ψX : e.inverse.obj z ⟶ y := e.inverse.map ψ' ≫ e.unitIso.inv.app y
  have hψXlift :
      X.p.IsHomLift ((g ≫ eqToHom (F.w_obj x)) ≫ X.p.map φ) ψX :=
    by simpa [ψX] using inverse_transport_lift_over_base F e φ g ψ'
  letI : X.p.IsHomLift ((g ≫ eqToHom (F.w_obj x)) ≫ X.p.map φ) ψX := hψXlift
  obtain ⟨ξ, hξ, hξuniq⟩ :=
    IsStronglyCartesian.universal_property X.p (X.p.map φ) φ
      (g ≫ eqToHom (F.w_obj x))
      (((g ≫ eqToHom (F.w_obj x)) ≫ X.p.map φ)) rfl ψX
  -- Push the source lift forward along the adjointified counit.
  let E := e.toEquivalence
  letI : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) ξ := hξ.1
  let ξ' : z ⟶ F.obj x := E.counit.inv.app z ≫ F.map ξ
  have hξ'base :
      Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) ξ' :=
    forward_transport_lift_over_base F e (g ≫ eqToHom (F.w_obj x)) ξ
  have hξ' : Y.p.IsHomLift g ξ' :=
    (isHomLift_over_target_eq_iff F g ξ').mpr hξ'base
  have hpushψ : E.counit.inv.app z ≫ F.map ψX = ψ' := by
    change e.toEquivalence.counit.inv.app z ≫
        F.map (e.inverse.map ψ' ≫ e.unitIso.inv.app y) = ψ'
    simpa [ψX, E, Functor.map_comp, Category.assoc] using
      pushforward_pullback_eq F e ψ'
  refine ⟨ξ', ⟨hξ', ?_⟩, ?_⟩
  · -- The pushed-forward lift factors through `F.map φ` by the pull-push comparison lemma.
    have hstep1 : ξ' ≫ F.map φ = E.counit.inv.app z ≫ F.map (ξ ≫ φ) := by
      simp [ξ', E, Functor.map_comp, Category.assoc]
    have hstep2 : E.counit.inv.app z ≫ F.map (ξ ≫ φ) = E.counit.inv.app z ≫ F.map ψX := by
      simpa [E] using congrArg (fun k ↦ E.counit.inv.app z ≫ F.map k) hξ.2
    exact hstep1.trans <| hstep2.trans hpushψ
  · intro η hη
    -- Pull any competing target lift back to `X` and compare there by uniqueness.
    have hηbase :
        Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) η :=
      (isHomLift_over_target_eq_iff F g η).mp hη.1
    have hηpull :
        X.p.IsHomLift (g ≫ eqToHom (F.w_obj x))
          (e.inverse.map η ≫ e.unitIso.inv.app x) := by
      have hηpre : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) (e.inverse.map η) :=
        (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj x)) η).2 hηbase
      have hηunit : X.p.IsHomLift (𝟙 (X.p.obj x)) (e.unitIso.inv.app x) := by
        simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj x = X.p.obj x)
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        (g ≫ eqToHom (F.w_obj x)) (e.inverse.map η) hηpre
        (X.p.obj x) (e.unitIso.inv.app x) hηunit
    have hηfac :
        (e.inverse.map η ≫ e.unitIso.inv.app x) ≫ φ = ψX := by
      simpa [ψX] using pullback_factorization_of_map_factorization F e φ hη.2
    have hηeq : e.inverse.map η ≫ e.unitIso.inv.app x = ξ :=
      hξuniq _ ⟨hηpull, hηfac⟩
    -- Push the equality back to the target using the same comparison lemma.
    have hpushη :
        η = E.counit.inv.app z ≫ F.map (e.inverse.map η ≫ e.unitIso.inv.app x) := by
      symm
      change e.toEquivalence.counit.inv.app z ≫
          F.map (e.inverse.map η ≫ e.unitIso.inv.app x) = η
      simpa [E, Functor.map_comp, Category.assoc] using
        pushforward_pullback_eq F e η
    have hstepη :
        E.counit.inv.app z ≫ F.map (e.inverse.map η ≫ e.unitIso.inv.app x) =
          E.counit.inv.app z ≫ F.map ξ := by
      simpa [E] using congrArg (fun k ↦ E.counit.inv.app z ≫ F.map k) hηeq
    exact hpushη.trans <| hstepη.trans rfl

/-- Helper for Lemma 4.33.8: if a morphism is already strongly cartesian, then any other lift of
the same arrow through the same morphism has the same strong-cartesian structure. -/
lemma isStronglyCartesian_rebase_of_same_lift
    {𝒮 : Type u} {𝒳 : Type uS} [Category.{v} 𝒮] [Category.{vS} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {a b : 𝒳} {f f' : p.obj a ⟶ p.obj b} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f' φ] :
    p.IsStronglyCartesian f' φ := by
  -- Both lift witnesses identify their base arrows with `p.map φ`, so the structure rebases by
  -- substitution.
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  have hf' : f' = p.map φ := IsHomLift.eq_of_isHomLift p f' φ
  subst hf
  subst hf'
  infer_instance

/-- Helper for Lemma 4.33.8: an owner-level strong-cartesian structure rebases along any external
lift witness for the same morphism. -/
lemma isStronglyCartesian_of_external_hom_lift
    {𝒮 : Type u} {𝒳 : Type uS} [Category.{v} 𝒮] [Category.{vS} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian (p.map φ) φ] [p.IsHomLift f φ] :
    p.IsStronglyCartesian f φ := by
  -- Normalize the external base objects to the actual source and target of `φ`, then rebase
  -- along the two lift witnesses for the same morphism.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = S := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase_of_same_lift (p := p) (f := p.map φ) (f' := f) φ

/-- Helper for Lemma 4.33.8: if the codomain of a strongly cartesian morphism is identified with
an external target object, then the strong-cartesian structure rebases to the owner map
`p.map φ`. -/
lemma isStronglyCartesian_rebase_over_target_eq
    {𝒮 : Type u} {𝒳 : Type uS} [Category.{v} 𝒮] [Category.{vS} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} (hb : p.obj b = S)
    {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] :
    p.IsStronglyCartesian (p.map φ) φ := by
  -- Reindex both ends of the external base morphism to the actual source and target of `φ`.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase_of_same_lift (p := p) (f := f) (f' := p.map φ) φ

/-- Helper for Lemma 4.33.8: an equivalence over the base sends fibredness forward. -/
private theorem isFibered_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) :
    X.p.IsFibered → Y.p.IsFibered := by
  intro hX
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  -- Use the strongly-cartesian lift criterion, transporting a chosen source lift and then
  -- composing with the vertical counit component to land over the original target object.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro y V f
  letI : X.p.IsFibered := hX
  obtain ⟨x, φ, hφcart⟩ := IsPreFibered.exists_isCartesian X.p (e.inverse.w_obj y) f
  letI : X.p.IsCartesian f φ := hφcart
  -- Route correction: first rebase the chosen source lift to its owner map, then transport it
  -- across `F` and compose with the vertical counit component over `y`.
  have hφstrong : X.p.IsStronglyCartesian f φ :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f φ
  have hφowner : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    letI : X.p.IsStronglyCartesian f φ := hφstrong
    exact isStronglyCartesian_rebase_over_target_eq (p := X.p) (hb := e.inverse.w_obj y)
      (f := f) φ
  have hFφstrong_owner : Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) :=
    isStronglyCartesian_map_of_isEquivalenceOverBase F hF φ hφowner
  have hFφlift : Y.p.IsHomLift f (F.map φ) :=
    (F.isHomLift_iff f φ).2 (show X.p.IsHomLift f φ from inferInstance)
  have hFφstrong : Y.p.IsStronglyCartesian f (F.map φ) := by
    -- Rebase the owner-level strong-cartesian structure using the explicit external lift over `f`.
    letI : Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := hFφstrong_owner
    letI : Y.p.IsHomLift f (F.map φ) := hFφlift
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := f) (φ := F.map φ)
  have hεlift : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.hom.app y) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.hom (rfl : Y.p.obj y = Y.p.obj y)
  have hεstrong : Y.p.IsStronglyCartesian (𝟙 (Y.p.obj y)) (e.counitIso.hom.app y) := by
    let epsIso := (BasedNatTrans.forgetful Y Y).mapIso e.counitIso
    refine
      { toIsHomLift := hεlift
        universal_property' := ?_ }
    intro z g τ hτ
    -- Any lifting problem through the vertical counit is solved by composing with its inverse.
    let χ : z ⟶ F.obj (e.inverse.obj y) := τ ≫ e.counitIso.inv.app y
    have hτ' : Y.p.IsHomLift g τ := by
      simpa using hτ
    have hεinv : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
      simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)
    have hχ : Y.p.IsHomLift g χ := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
        g τ hτ' (Y.p.obj y) (e.counitIso.inv.app y) hεinv
    refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
    · simpa [χ, epsIso, Category.assoc] using
        congrArg (fun k ↦ τ ≫ k) (epsIso.inv_hom_id_app y)
    · intro η hη
      have hηcomp : η = η ≫ e.counitIso.hom.app y ≫ e.counitIso.inv.app y := by
        rw [← Category.assoc]
        simpa [epsIso] using
          congrArg (fun k ↦ η ≫ k) (epsIso.hom_inv_id_app y).symm
      calc
        η = η ≫ e.counitIso.hom.app y ≫ e.counitIso.inv.app y := hηcomp
        _ = τ ≫ e.counitIso.inv.app y := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ e.counitIso.inv.app y) hη.2
        _ = χ := rfl
  let ψ : F.obj x ⟶ y := F.map φ ≫ e.counitIso.hom.app y
  have hψstrong : Y.p.IsStronglyCartesian f ψ := by
    let epsIso := (BasedNatTrans.forgetful Y Y).mapIso e.counitIso
    -- First record that the composite `ψ` still lies over the original external base map `f`.
    have hψlift : Y.p.IsHomLift f ψ := by
      simpa [ψ, Category.assoc] using
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          f (F.map φ) hFφlift (Y.p.obj y) (e.counitIso.hom.app y) hεlift
    refine
      { toIsHomLift := hψlift
        universal_property' := ?_ }
    intro z g τ hτ
    -- Cancel the vertical counit component on the right and solve the remaining lifting problem
    -- through `F.map φ`.
    let τ' : z ⟶ F.obj (e.inverse.obj y) := τ ≫ e.counitIso.inv.app y
    have hτ' : Y.p.IsHomLift (g ≫ f) τ' := by
      have hτlift : Y.p.IsHomLift (g ≫ f) τ := by
        simpa using hτ
      have hεinv : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
        simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)
      simpa [τ'] using
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          (g ≫ f) τ hτlift (Y.p.obj y) (e.counitIso.inv.app y) hεinv
    letI : Y.p.IsStronglyCartesian f (F.map φ) := hFφstrong
    letI : Y.p.IsHomLift (g ≫ f) τ' := hτ'
    obtain ⟨χ, hχ, hχuniq⟩ :=
      IsStronglyCartesian.universal_property Y.p f (F.map φ) g (g ≫ f) rfl τ'
    refine ⟨χ, ⟨hχ.1, ?_⟩, ?_⟩
    · -- Compose the solved factorization back with the counit component to recover `τ`.
      have hτcancel : τ' ≫ e.counitIso.hom.app y = τ := by
        calc
          τ' ≫ e.counitIso.hom.app y
              = τ ≫ (e.counitIso.inv.app y ≫ e.counitIso.hom.app y) := by
                  simp [τ', Category.assoc]
          _ = τ := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ τ ≫ k) (epsIso.inv_hom_id_app y)
      have hχψ : χ ≫ ψ = τ' ≫ e.counitIso.hom.app y := by
        calc
          χ ≫ ψ = (χ ≫ F.map φ) ≫ e.counitIso.hom.app y := by
              simp [ψ, Category.assoc]
          _ = τ' ≫ e.counitIso.hom.app y := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ e.counitIso.hom.app y) hχ.2
      exact hχψ.trans (by simpa using hτcancel)
    · intro η hη
      have hηcancel : (η ≫ ψ) ≫ e.counitIso.inv.app y = η ≫ F.map φ := by
        calc
          (η ≫ ψ) ≫ e.counitIso.inv.app y
              = η ≫ F.map φ ≫ (e.counitIso.hom.app y ≫ e.counitIso.inv.app y) := by
                  simp [ψ, Category.assoc]
          _ = η ≫ F.map φ := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ η ≫ F.map φ ≫ k) (epsIso.hom_inv_id_app y)
      have hηfac :
          η ≫ F.map φ = τ' := by
        have hηstep2 : (η ≫ ψ) ≫ e.counitIso.inv.app y = τ ≫ e.counitIso.inv.app y := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ e.counitIso.inv.app y) hη.2
        have hηstep3 : τ ≫ e.counitIso.inv.app y = τ' := by
          simpa [τ']
        exact hηcancel.symm.trans (hηstep2.trans hηstep3)
      exact hχuniq _ ⟨hη.1, hηfac⟩
  exact ⟨F.obj x, ψ, hψstrong⟩

/-- Lemma 4.33.8: if `F : X ⥤ᵇ Y` is an equivalence over `C`, then `X` is fibred over `C` if and
only if `Y` is fibred over `C`. -/
theorem isFibered_iff_of_equivalence_over_base
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) :
    X.p.IsFibered ↔ Y.p.IsFibered := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  constructor
  · -- Transport fibredness forward along `F`.
    exact isFibered_of_isEquivalenceOverBase F hF
  · -- Apply the same forward argument to the chosen quasi-inverse.
    exact isFibered_of_isEquivalenceOverBase e.inverse e.inverse_isEquivalenceOverBase

end BasedFunctor

end CategoryTheory
