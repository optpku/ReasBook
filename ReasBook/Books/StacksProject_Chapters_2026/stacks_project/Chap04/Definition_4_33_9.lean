module

public import Mathlib.CategoryTheory.FiberedCategory.HasFibers
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import stacks_project.Chap04.Definition_4_29_2
public import stacks_project.Chap04.Definition_4_32_1
public import stacks_project.Chap04.Definition_4_33_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v vS w

namespace CategoryTheory

open BasedFunctor
open Bicategory
open Functor IsHomLift IsStronglyCartesian
open scoped Bicategory

/- Domain-style sampling for Definition 4.33.9:
- primary domain: fibred categories over a fixed base, organized as a full sub-`2`-category of
  `Cat/C`.
- inspected owner-level declarations:
  `CategoryOver`,
  `BasedFunctor.PreservesStronglyCartesian`,
  `Functor.IsFibered`,
  `Functor.IsStronglyCartesian`,
  `SubTwoCategory`.
- best owner abstraction: `SubTwoCategory (CategoryOver C)`.
- primitive data: the ambient predicate `X.p.IsFibered` on objects of `Cat/C` and the ambient
  predicate that a based functor over `C` preserves strongly cartesian arrows.
- derived API: the source-facing object owner `FibredCategoryOver C` together with the helper
  namespace `FibredCategoryMor` on the canonical ambient homs `X ⟶ Y`, keeping only the genuine
  bridge constructor from based functors preserving strongly cartesian arrows and otherwise using
  the ambient owner accessor `SubTwoCategory.Hom.toHom` and its induced coercion.

Source/core/bridge triage:
- `source-facing`: fibred categories over `C` and morphisms preserving strongly cartesian arrows.
- `core/canonical`: the sub-`2`-category `fibredCategoryOverSubTwoCategory C`.
- `bridge/view`: the bundled object owner `FibredCategoryOver` and the constructor
  `FibredCategoryMor.ofBasedFunctor`, with the ambient owner homs viewed through the canonical
  accessor `SubTwoCategory.Hom.toHom`. -/

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

variable {X Y : CategoryOver C}

/-- A based functor over `C` preserves strongly cartesian morphisms if it sends every strongly
cartesian arrow in the source fibred category to a strongly cartesian arrow in the target. -/
def PreservesStronglyCartesian
    (G : X ⥤ᵇ Y) : Prop :=
  ∀ ⦃a b : X.obj⦄ (φ : a ⟶ b),
    X.p.IsStronglyCartesian (X.p.map φ) φ →
      Y.p.IsStronglyCartesian (Y.p.map (G.map φ)) (G.map φ)

end BasedFunctor

/-- Helper for Definition 4.33.9: the canonical pullback system on a fibred category, extracted
locally from the basic `PullbackChoice` API so this item file does not depend on later coherence
development. -/
noncomputable abbrev localCanonicalPullbackChoice
    {S : Type w} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered] :
    PullbackChoice p :=
  let _ : HasFibers p := HasFibers.canonical p
  { obj := fun f x ↦ HasFibers.mkPullback f x.2
    map := fun f x ↦ HasFibers.pullbackMap f x.2
    isStronglyCartesian := fun f x ↦
      Functor.IsFibered.isStronglyCartesian_of_isCartesian p f (HasFibers.pullbackMap f x.2) }

namespace BasedFunctor

variable {X Y : BasedCategory.{vS, w} C}

attribute [local simp] bicategoricalComp
attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
  Strict.associator_eqToIso

/-- Helper for Definition 4.33.9: pulling a lifting problem back across the inverse in an
explicit equivalence over the base preserves the same base morphism. -/
private lemma inverse_transport_lift_over_base
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (ψ : z ⟶ F.obj y)
    [Y.p.IsHomLift (g ≫ Y.p.map (F.map φ)) ψ] :
    X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ ≫ e.unitIso.inv.app y) := by
  -- Rewrite the target lifting problem into the source base coordinates using the over-base equation.
  have hψY : Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ := by
    refine IsHomLift.of_fac Y.p _ ψ rfl (F.w_obj y) ?_
    have hbase :
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
      calc
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ
            = g ≫ Y.p.map (F.map φ) ≫ eqToHom (F.w_obj y) := by
                simpa [Category.assoc] using
                  (congrArg (fun k ↦ g ≫ k ≫ eqToHom (F.w_obj y)) (Functor.congr_hom F.w φ)).symm
        _ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ eqToHom (F.w_obj y))
                  (IsHomLift.eq_of_isHomLift Y.p (g ≫ Y.p.map (F.map φ)) ψ)
    simpa [Category.assoc] using hbase
  -- The inverse preserves the transported lift, and the unit component is vertical.
  have hψX : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) :=
    (e.inverse.isHomLift_iff _ ψ).2 hψY
  have hη : X.p.IsHomLift (𝟙 (X.p.obj y)) (e.unitIso.inv.app y) := by
    simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj y = X.p.obj y)
  exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
    (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) hψX
    (X.p.obj y) (e.unitIso.inv.app y) hη

/-- Helper for Definition 4.33.9: any vertical counit inverse over a chosen quasi-inverse pushes
an `X`-lift forward to a `Y`-lift over the same base morphism. -/
private lemma forward_transport_lift_over_base_with_counit
    {F : X ⥤ᵇ Y} {G : Y ⥤ᵇ X} (eps : G ⋙ F ≅ 𝟭 Y)
    {x : X.obj} {z : Y.obj} (g : Y.p.obj z ⟶ X.p.obj x)
    (ξ : G.obj z ⟶ x)
    [X.p.IsHomLift g ξ] :
    Y.p.IsHomLift g (eps.inv.app z ≫ F.map ξ) := by
  -- Push the source lift forward along `F`.
  have hξY : Y.p.IsHomLift g (F.map ξ) :=
    (F.isHomLift_iff g ξ).2 (show X.p.IsHomLift g ξ from inferInstance)
  -- The counit component is vertical, so precomposing with it preserves the base map.
  have hε : Y.p.IsHomLift (𝟙 (Y.p.obj z)) (eps.inv.app z) := by
    simpa using BasedNatTrans.isHomLift eps.inv (rfl : Y.p.obj z = Y.p.obj z)
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
    (Y.p.obj z) (eps.inv.app z) hε _ _ g (F.map ξ) hξY

/-- Helper for Definition 4.33.9: pushing a lifted morphism forward across the chosen
equivalence over the base preserves the same base morphism. -/
private lemma forward_transport_lift_over_base
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
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

/-- Helper for Definition 4.33.9: the strict associator inserted by bicategorical composition
forgets to the identity component on each object. -/
private lemma strict_associator_component_eqToHom
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    (eqToIso (BasedFunctor.comp_assoc F e.inverse F)).hom.toNatTrans.app x =
      𝟙 (F.obj (e.inverse.obj (F.obj x))) := by
  -- In the strict bicategory `BasedCategory`, the associator is the identity after reducing the
  -- composition equality `BasedFunctor.comp_assoc`.
  simp

/-- Helper for Definition 4.33.9: forgetting the adjointified left triangle and evaluating at
`x` gives the ordinary component comparison between the left zigzag and the unitors. -/
private theorem forgotten_left_triangle_component
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    (leftZigzag e.toEquivalence.unit.hom e.toEquivalence.counit.hom).app x =
      ((BasedNatTrans.forgetful X Y).mapIso
        (λ_ e.toEquivalence.hom ≪≫ (ρ_ e.toEquivalence.hom).symm)).hom.app x := by
  -- Forget the based left-triangle isomorphism to the ordinary functor category.
  let Φ := congrArg (Functor.mapIso (BasedNatTrans.forgetful X Y)) e.toEquivalence.left_triangle
  -- Evaluating the forgotten comparison at `x` gives the desired component identity.
  exact congrArg (fun η => η.hom.app x) Φ

/-- Helper for Definition 4.33.9: the forgotten left-zigzag component is the ordinary composite
of the unit component followed by the counit component. -/
private theorem forgotten_left_zigzag_hom_app
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    (CategoryTheory.Bicategory.leftZigzag e.toEquivalence.unit.hom
        e.toEquivalence.counit.hom).app x =
      F.map (e.unitIso.hom.app x) ≫ e.toEquivalence.counit.hom.app (F.obj x) := by
  -- Expand the bicategorical coherence to the strict associator and the whiskered identity.
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
    -- In the strict bicategory `BasedCategory`, the associator contributes only the identity.
    simp [CategoryTheory.Bicategory.Strict.associator_eqToIso]
    rfl
  rw [hassoc]
  -- The remaining whiskered identity component is definitionally trivial.
  simp [CategoryTheory.BasedCategory.whiskerRight, CategoryTheory.BasedNatTrans.id]

/-- Helper for Definition 4.33.9: the forgotten hom-side right-hand comparison in the left
triangle is the identity map on each object. -/
private theorem forgotten_left_triangle_rhs_hom_app_eq_id
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    ((λ_ e.toEquivalence.hom).hom ≫ (ρ_ e.toEquivalence.hom).inv).app x = 𝟙 (F.obj x) := by
  -- Both unitors are strict identities in `BasedCategory`, so the component stays the identity.
  change (CategoryTheory.BasedNatTrans.comp (CategoryTheory.BasedNatTrans.id F)
      (CategoryTheory.BasedNatTrans.id F)).app x = _
  rw [CategoryTheory.BasedNatTrans.comp]
  simp [CategoryTheory.BasedNatTrans.id]

/-- Helper for Definition 4.33.9: the adjointified left triangle reduces to the ordinary
unit-counit cancellation formula on each target object. -/
private theorem adjointified_triangle_component
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    F.map (e.unitIso.hom.app x) ≫ e.toEquivalence.counit.hom.app (F.obj x) = 𝟙 (F.obj x) := by
  -- Route correction: evaluate the bicategorical left triangle at `x` before simplifying each
  -- side into the ordinary composite and the identity component.
  have htriangle :=
    congrArg (fun η ↦ η.app x)
      (CategoryTheory.Bicategory.Equivalence.left_triangle_hom e.toEquivalence)
  have htriangle' :
      (CategoryTheory.Bicategory.leftZigzag e.toEquivalence.unit.hom
          e.toEquivalence.counit.hom).app x =
        ((λ_ e.toEquivalence.hom).hom ≫ (ρ_ e.toEquivalence.hom).inv).app x := by
    -- This is the component form of the adjointified left triangle after forgetting based data.
    simpa using htriangle
  -- The two adapter lemmas identify the bicategorical sides with the ordinary source formula.
  exact (forgotten_left_zigzag_hom_app (e := e) x).symm.trans <|
    htriangle'.trans (forgotten_left_triangle_rhs_hom_app_eq_id (e := e) x)

/-- Helper for Definition 4.33.9: the inverse components of the adjointified unit and counit
cancel on each object in the target. -/
private theorem adjointified_inverse_triangle_component
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    e.toEquivalence.counit.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) = 𝟙 (F.obj x) := by
  -- Package the forgotten adjointified data as an ordinary equivalence and apply its inverse
  -- triangle identity.
  let E : X.obj ≌ Y.obj :=
    CategoryTheory.Equivalence.mk'
      F.toFunctor e.inverse.toFunctor
      ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
      ((BasedNatTrans.forgetful Y Y).mapIso e.toEquivalence.counit)
      (fun x ↦ by
        simpa using adjointified_triangle_component (e := e) x)
  simpa [E] using E.counitIso_functor_comp x

/-- Helper for Definition 4.33.9: appending the canonical base-change isomorphism from
`F.w_obj` does not change whether a target morphism is a lift. -/
private lemma isHomLift_over_target_eq_iff
    {F : X ⥤ᵇ Y} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (θ : z ⟶ F.obj x) :
    Y.p.IsHomLift g θ ↔ Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) θ := by
  -- The extra `eqToHom` only rewrites the codomain to the source-side base coordinates.
  exact (IsHomLift.lift_comp_eqToHom_iff Y.p g θ (F.w_obj x)).symm

/-- Helper for Definition 4.33.9: a target-side factorization pulls back along the inverse
together with the unit inverse to the corresponding source-side factorization. -/
private lemma pullback_factorization_of_map_factorization
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
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

/-- Helper for Definition 4.33.9: pushing the pulled-back morphism forward with the
adjointified counit inverse recovers the original target morphism. -/
private lemma pushforward_pullback_eq
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
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
        (adjointified_inverse_triangle_component e x)
  exact hnat.trans htail

/-- Helper for Definition 4.33.9: an equivalence over the base sends strongly cartesian
morphisms to strongly cartesian morphisms. -/
private theorem preserves_strongly_cartesian_of_equivalence_over_base
    {F : X ⥤ᵇ Y} (hF : F.IsEquivalenceOverBase) :
    BasedFunctor.PreservesStronglyCartesian F := by
  -- Route correction: prove the transport theorem locally so this definition file is independent
  -- of the missing `Lemma_4_33_8.olean`.
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  intro a b φ hφ
  refine
    { toIsHomLift := by
        infer_instance
      universal_property' := ?_ }
  intro z g ψ' hψ'
  -- Pull the problem back to `X` and solve it there using the strong cartesianness of `φ`.
  let ψX : e.inverse.obj z ⟶ b := e.inverse.map ψ' ≫ e.unitIso.inv.app b
  have hψXlift :
      X.p.IsHomLift ((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ) ψX := by
    simpa [ψX] using inverse_transport_lift_over_base e φ g ψ'
  letI : X.p.IsHomLift ((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ) ψX := hψXlift
  obtain ⟨ξ, hξ, hξuniq⟩ :=
    IsStronglyCartesian.universal_property X.p (X.p.map φ) φ
      (g ≫ eqToHom (F.w_obj a))
      (((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ)) rfl ψX
  -- Push the source lift forward along the adjointified counit.
  let E := e.toEquivalence
  letI : X.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) ξ := hξ.1
  let ξ' : z ⟶ F.obj a := E.counit.inv.app z ≫ F.map ξ
  have hξ'base :
      Y.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) ξ' :=
    forward_transport_lift_over_base e (g ≫ eqToHom (F.w_obj a)) ξ
  have hξ' : Y.p.IsHomLift g ξ' :=
    (isHomLift_over_target_eq_iff g ξ').mpr hξ'base
  have hpushψ : E.counit.inv.app z ≫ F.map ψX = ψ' := by
    change e.toEquivalence.counit.inv.app z ≫
        F.map (e.inverse.map ψ' ≫ e.unitIso.inv.app b) = ψ'
    simpa [ψX, E, Functor.map_comp, Category.assoc] using
      pushforward_pullback_eq e ψ'
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
        Y.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) η :=
      (isHomLift_over_target_eq_iff g η).mp hη.1
    have hηpull :
        X.p.IsHomLift (g ≫ eqToHom (F.w_obj a))
          (e.inverse.map η ≫ e.unitIso.inv.app a) := by
      have hηpre : X.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) (e.inverse.map η) :=
        (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj a)) η).2 hηbase
      have hηunit : X.p.IsHomLift (𝟙 (X.p.obj a)) (e.unitIso.inv.app a) := by
        simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj a = X.p.obj a)
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        (g ≫ eqToHom (F.w_obj a)) (e.inverse.map η) hηpre
        (X.p.obj a) (e.unitIso.inv.app a) hηunit
    have hηfac :
        (e.inverse.map η ≫ e.unitIso.inv.app a) ≫ φ = ψX := by
      simpa [ψX] using pullback_factorization_of_map_factorization e φ hη.2
    have hηeq : e.inverse.map η ≫ e.unitIso.inv.app a = ξ :=
      hξuniq _ ⟨hηpull, hηfac⟩
    -- Push the equality back to the target using the same comparison lemma.
    have hpushη :
        η = E.counit.inv.app z ≫ F.map (e.inverse.map η ≫ e.unitIso.inv.app a) := by
      symm
      change e.toEquivalence.counit.inv.app z ≫
          F.map (e.inverse.map η ≫ e.unitIso.inv.app a) = η
      simpa [E, Functor.map_comp, Category.assoc] using
        pushforward_pullback_eq e η
    have hstepη :
        E.counit.inv.app z ≫ F.map (e.inverse.map η ≫ e.unitIso.inv.app a) =
          E.counit.inv.app z ≫ F.map ξ := by
      simpa [E] using congrArg (fun k ↦ E.counit.inv.app z ≫ F.map k) hηeq
    exact hpushη.trans <| hstepη.trans rfl

/-- Helper for Definition 4.33.9: an equivalence over the base canonically preserves strongly
cartesian morphisms. -/
theorem preservesStronglyCartesian_of_isEquivalenceOverBase
    {F : X ⥤ᵇ Y} (hF : F.IsEquivalenceOverBase) :
    BasedFunctor.PreservesStronglyCartesian F :=
  preserves_strongly_cartesian_of_equivalence_over_base hF

/-- Helper for Definition 4.33.9: the inverse functor in explicit equivalence-over-base data
preserves strongly cartesian morphisms. -/
theorem inverse_preserves_strongly_cartesian_of_equivalence_data
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    BasedFunctor.PreservesStronglyCartesian e.inverse := by
  -- Reuse the general transport theorem for the inverse equivalence-over-base datum.
  exact preserves_strongly_cartesian_of_equivalence_over_base e.inverse_isEquivalenceOverBase

end BasedFunctor

theorem fibredCategoryMor_id_preservesStronglyCartesian
    (X : CategoryOver C) :
    BasedFunctor.PreservesStronglyCartesian (𝟙 X) := by
  intro _ _ _ hφ
  simpa using hφ

theorem fibredCategoryMor_comp_preservesStronglyCartesian
    {X Y Z : CategoryOver C}
    {F : X ⥤ᵇ Y}
    {G : Y ⥤ᵇ Z}
    (hF : BasedFunctor.PreservesStronglyCartesian F)
    (hG : BasedFunctor.PreservesStronglyCartesian G) :
    BasedFunctor.PreservesStronglyCartesian (F ⋙ G) := by
  intro a b φ hφ
  exact hG (F.map φ) (hF φ hφ)

/-- Definition 4.33.9 at the canonical owner level: fibred categories over `C` and
strongly-cartesian-preserving functors form the full sub-`2`-category of `Cat/C` cut out by
fibred objects and cartesian-preserving `1`-morphisms. -/
abbrev fibredCategoryOverSubTwoCategory (C : Type u) [Category.{v} C] :
    SubTwoCategory (CategoryOver C) where
  obj := fun X ↦ X.p.IsFibered
  hom _ _ := {
    obj := BasedFunctor.PreservesStronglyCartesian
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem X := fibredCategoryMor_id_preservesStronglyCartesian X.obj
  comp_mem hF hG := fibredCategoryMor_comp_preservesStronglyCartesian hF hG
  whiskerLeft_mem _ _ _ _ := by
    trivial
  whiskerRight_mem _ _ _ _ := by
    trivial

/-- Definition 4.33.9: categories fibred over `C` are the objects of the owner sub-`2`-category
`fibredCategoryOverSubTwoCategory C`. -/
abbrev FibredCategoryOver (C : Type u) [Category.{v} C] :=
  (fibredCategoryOverSubTwoCategory C).Obj

instance : Bicategory (FibredCategoryOver C) :=
  SubTwoCategory.bicategoryObj (fibredCategoryOverSubTwoCategory C)

instance : Bicategory.Strict (FibredCategoryOver C) :=
  SubTwoCategory.strictObj (fibredCategoryOverSubTwoCategory C)

instance fibredCategoryOverCategory : Category (FibredCategoryOver C) :=
  StrictBicategory.category (FibredCategoryOver C)

namespace FibredCategoryOver

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredCategoryOver C) :
    CategoryOver C :=
  X.obj

/-- The total category of a fibred category over `C`. -/
abbrev S (X : FibredCategoryOver C) :=
  X.toCategoryOver.obj

/-- The projection functor to the base category. -/
abbrev p (X : FibredCategoryOver C) :=
  X.toCategoryOver.p

/-- Forget a fibred category over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredCategoryOver C) :
    BasedCategory.{vS, w} C :=
  X.toCategoryOver

instance : CoeOut (FibredCategoryOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

instance : CoeOut (FibredCategoryOver C) (BasedCategory.{vS, w} C) where
  coe X := X.toBasedCategory

instance isFibred (X : FibredCategoryOver C) : X.p.IsFibered :=
  by
    simpa [FibredCategoryOver.p, fibredCategoryOverSubTwoCategory]
      using X.property

/-- Build a fibred category over `C` from a fibred functor to `C`. -/
abbrev ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered] :
    FibredCategoryOver C :=
  ⟨BasedCategory.ofFunctor p, by
    simpa [fibredCategoryOverSubTwoCategory, BasedCategory.ofFunctor] using
      (inferInstance : p.IsFibered)⟩

end FibredCategoryOver

variable (X Y : FibredCategoryOver C)

/- Definition 4.33.9: for fibred categories over `C`, the canonical `1`-morphisms are the
ambient homs `X ⟶ Y` in the owner bicategory. -/
#check (X ⟶ Y)

variable {X Y}

/-- Stable chapter vocabulary for the owner hom-category of morphisms of fibred categories over
`C`. -/
abbrev FibredCategoryMor (X Y : FibredCategoryOver C) :=
  X ⟶ Y

namespace FibredCategoryMor

variable {X Y : FibredCategoryOver C}

/-- The object property on based functors over `C` underlying morphisms of fibred categories. -/
abbrev objectProperty (X Y : FibredCategoryOver C) :
    ObjectProperty (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :=
  BasedFunctor.PreservesStronglyCartesian

/-- The underlying based functor of a morphism of fibred categories over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  show X.toBasedCategory ⥤ᵇ Y.toBasedCategory from F.toHom

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  toBasedFunctor F |>.fiberFunctor U

/-- The underlying functor between total categories. -/
abbrev toFunctor (F : X ⟶ Y) :
    X.S ⥤ Y.S :=
  toBasedFunctor F |>.toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) :
    toFunctor F ⋙ Y.p = X.p :=
  toBasedFunctor F |>.w

/-- Every object of every target fiber is locally in the essential image of the corresponding
fiber functor. This is the canonical site-local essential-surjectivity predicate for a morphism of
fibred categories over `C`. -/
def LocallyEssentiallySurjectiveOnObjects
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  ∀ (U : C) (y : Y.p.Fiber U),
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      ∃ x : X.p.Fiber I.Y,
        Nonempty (((fiberFunctor F I.Y).obj x) ≅ I.f ^*[localCanonicalPullbackChoice Y.p] y)

/-- A morphism of fibred categories over `C` is an equivalence over the base if its underlying
based functor is. -/
abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  BasedFunctor.IsEquivalenceOverBase (toBasedFunctor F)

/-- Strongly cartesian morphisms are preserved by a morphism of fibred categories. -/
theorem map_stronglyCartesian
    (F : X ⟶ Y) {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map ((toFunctor F).map φ)) ((toFunctor F).map φ) :=
  F.obj.property φ hφ

instance : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

/-- Build a morphism of fibred categories from a based functor preserving strongly cartesian
morphisms. -/
abbrev ofBasedFunctor (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hG : G.PreservesStronglyCartesian) : X ⟶ Y :=
  ⟨⟨G, by
      simpa [fibredCategoryOverSubTwoCategory] using hG⟩⟩

/-- Lift the full subcategory of based functors preserving strongly cartesian morphisms to the
owner hom-category `X ⟶ Y`. -/
abbrev ofObjectProperty (X Y : FibredCategoryOver C) :
    (objectProperty X Y).FullSubcategory ⥤ (X ⟶ Y) where
  obj F := ofBasedFunctor F.obj F.property
  map η := ⟨ObjectProperty.homMk η.hom, trivial⟩

noncomputable def ownerIsoOfBasedFunctorIso
    {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Convert an isomorphism of owner morphisms into the corresponding isomorphism of underlying
based functors over `C`. -/
noncomputable def basedFunctorIsoOfOwnerIso
    {F G : X ⟶ Y} (e : F ≅ G) :
    toBasedFunctor F ≅ toBasedFunctor G :=
  Functor.mapIso (((fibredCategoryOverSubTwoCategory C).hom X Y).inclusion) e

/-- Explicit equivalence-over-base data on the underlying based functor of `F` induce a
bicategorical equivalence with forward morphism `F`. -/
noncomputable def ofEquivalenceOverBase
    (F : X ⟶ Y)
    (e : BasedFunctor.EquivalenceOverBase (toBasedFunctor F)) :
    Bicategory.Equivalence X Y :=
  let G : Y ⟶ X :=
    -- Route correction: after removing the unfinished chapter import, use the local inverse
    -- preservation theorem derived directly from the explicit equivalence-over-base data.
    ofBasedFunctor e.inverse (BasedFunctor.inverse_preserves_strongly_cartesian_of_equivalence_data e)
  let eta : (𝟙 X : X ⟶ X) ≅ F ≫ G := by
    simpa [G] using ownerIsoOfBasedFunctorIso e.unitIso
  let eps : G ≫ F ≅ (𝟙 Y : Y ⟶ Y) := by
    simpa [G] using ownerIsoOfBasedFunctorIso e.counitIso
  Bicategory.Equivalence.mkOfAdjointifyCounit eta eps

/-- A morphism of fibred categories over `C` that is an equivalence over the base admits a
bicategorical equivalence with forward morphism `F`. -/
theorem exists_equivalence
    (F : X ⟶ Y) (hF : FibredCategoryMor.IsEquivalenceOverBase F) :
    ∃ e : Bicategory.Equivalence X Y, e.hom = F := by
  rcases hF.nonempty with ⟨e⟩
  exact ⟨ofEquivalenceOverBase F e, rfl⟩

end FibredCategoryMor

-- Proof sketch: a morphism in the owner hom-category `X ⟶ Y` is a morphism between the
-- underlying based functors, hence a `BasedNatTrans`; its components are therefore vertical
-- over the identity on the corresponding base objects by the defining field of
-- `CategoryTheory.BasedNatTrans`.
/-- Any `2`-morphism between morphisms of fibred categories is vertical over the identity on each
source object. -/
theorem fibredCategoryMor_hom_isHomLift_id
    {X Y : FibredCategoryOver C} {F G : X ⟶ Y}
    (τ : F ⟶ G) (a : X.S) :
    Functor.IsHomLift Y.p (𝟙 (X.p.obj a))
      ((τ.hom.hom).toNatTrans.app a) := by
  exact (τ.hom.hom).isHomLift rfl

namespace FibredCategoryOver

variable {X Y : FibredCategoryOver C}

/- The `1`-morphism underlying a bicategorical equivalence of fibred categories over `C` is an
equivalence over the base. -/
theorem hom_isEquivalenceOverBase
    (e : Bicategory.Equivalence X Y) :
    FibredCategoryMor.IsEquivalenceOverBase e.hom := by
  let hHom : X ⟶ Y := e.hom
  let hInv : Y ⟶ X := e.inv
  change BasedFunctor.IsEquivalenceOverBase (FibredCategoryMor.toBasedFunctor hHom)
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      (FibredCategoryMor.toBasedFunctor hInv)
      (by
        change (𝟙 X.toBasedCategory) ≅
            (FibredCategoryMor.toBasedFunctor hHom ⋙
              FibredCategoryMor.toBasedFunctor hInv)
        simpa [hHom, hInv] using FibredCategoryMor.basedFunctorIsoOfOwnerIso e.unit)
      (by
        change
          (FibredCategoryMor.toBasedFunctor hInv ⋙
              FibredCategoryMor.toBasedFunctor hHom) ≅
            𝟙 Y.toBasedCategory
        simpa [hHom, hInv] using FibredCategoryMor.basedFunctorIsoOfOwnerIso e.counit)

end FibredCategoryOver

end CategoryTheory
