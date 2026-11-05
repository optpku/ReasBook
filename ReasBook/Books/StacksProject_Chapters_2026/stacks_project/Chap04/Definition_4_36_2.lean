module

public import stacks_project.Chap04.Definition_4_32_1
public import stacks_project.Chap04.Lemma_4_33_8
public import stacks_project.Chap04.Example_4_36_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open BasedFunctor
open Functor IsHomLift IsStronglyCartesian
open Opposite
open scoped Bicategory
open scoped BasedFunctor
variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

open Pseudofunctor

/- Domain-style sampling for Definition 4.36.2:
- primary domain: fibred categories over a fixed base and split models coming from contravariant
  `Cat`-valued functors via the co-Grothendieck construction.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.toPseudofunctor'`,
  `CoGrothendieck.forget`,
  `BasedCategory.ofFunctor`,
  `BasedFunctor.IsEquivalenceOverBase`.
- best owner abstraction: the source-facing predicate `Functor.IsSplitFibredCategory p`, built
  directly from the canonical co-Grothendieck model and the canonical category-over-base owner
  `BasedCategory`, with the comparison expressed as an isomorphism in `Cat/C`.
- primitive data: the functor `p : S ⥤ C` together with a contravariant functor
  `F : Cᵒᵖ ⥤ Cat` and an isomorphism over `C` from `p` to the associated co-Grothendieck model.
- derived API: the induced fibredness of `p`, transported from the canonical fibredness instance on
  `Pseudofunctor.CoGrothendieck.forget (F.toPseudofunctor')` via the isomorphism's induced
  equivalence-over-base.

Source/core/bridge triage:
- `source-facing`: `Functor.IsSplitFibredCategory p`.
- `core/canonical`: `Functor.IsFibered`.
- `bridge/view`: `Functor.toPseudofunctor'`, `Pseudofunctor.CoGrothendieck.forget`, and the
  canonical isomorphism in `Cat/C`, together with the transport theorem
  `BasedFunctor.isFibered_iff_of_equivalence_over_base` applied to its forward morphism. -/

/-- Definition 4.36.2: a functor `p : S ⥤ C` is a split fibred category if it is isomorphic over
`C` to the co-Grothendieck construction attached to a contravariant category-valued functor on
`C`; the fibredness of `p` is then derived from this model. -/
class IsSplitFibredCategory (p : S ⥤ C) : Prop where
  existsCoGrothendieckModel :
    ∃ (F : Cᵒᵖ ⥤ Cat.{v₂, u₂})
      (e : BasedCategory.ofFunctor p ⥤ᵇ
        BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))
      (eInv : BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')) ⥤ᵇ
        BasedCategory.ofFunctor p),
      e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
        eInv ⋙ e = 𝟙 (BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))

namespace IsSplitFibredCategory

variable {X Y : BasedCategory.{v₂, u₂} C}

/-- Helper for Definition 4.36.2: adjointifying the counit of explicit equivalence-over-base data
produces the canonical bicategorical equivalence over the base. -/
private noncomputable abbrev adjointifiedEquivalence
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    X ≌ Y :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.unitIso e.counitIso

/-- Helper for Definition 4.36.2: pulling a lifting problem back across the inverse in an
equivalence over the base preserves the same base morphism after translating along `F.w_obj`. -/
private theorem inverse_transport_lift_over_base
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (ψ : z ⟶ F.obj y)
    [Y.p.IsHomLift (g ≫ Y.p.map (F.map φ)) ψ] :
    X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ)
      (e.inverse.map ψ ≫ e.unitIso.inv.app y) := by
  -- First rewrite the target lifting problem into the source base coordinates.
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
  -- Pull the lifted arrow back across the chosen quasi-inverse.
  have hψX : X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) :=
    (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ).2 hψY
  -- The unit component is vertical, so postcomposing with it keeps the same base map.
  have hη : X.p.IsHomLift (𝟙 (X.p.obj y)) (e.unitIso.inv.app y) := by
    simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj y = X.p.obj y)
  exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
    (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) hψX
    (X.p.obj y) (e.unitIso.inv.app y) hη

/-- Helper for Definition 4.36.2: pushing a source lift forward across the equivalence and then
precomposing with the counit inverse preserves the same base morphism. -/
private theorem forward_transport_lift_over_base
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (g : Y.p.obj z ⟶ X.p.obj x)
    (ξ : e.inverse.obj z ⟶ x)
    [X.p.IsHomLift g ξ] :
    Y.p.IsHomLift g (e.toEquivalence.counit.inv.app z ≫ F.map ξ) := by
  let E := e.toEquivalence
  -- First push the source lift forward along `F`.
  have hξY : Y.p.IsHomLift g (F.map ξ) :=
    (F.isHomLift_iff g ξ).2 (show X.p.IsHomLift g ξ from inferInstance)
  -- Then precompose with the vertical counit inverse.
  have hε : Y.p.IsHomLift (𝟙 (Y.p.obj z)) (E.counit.inv.app z) := by
    simpa [E] using BasedNatTrans.isHomLift E.counit.inv
      (rfl : Y.p.obj z = Y.p.obj z)
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
    (Y.p.obj z) (E.counit.inv.app z) hε _ _ g (F.map ξ) hξY

/-- Helper for Definition 4.36.2: appending the canonical base-change isomorphism from `F.w_obj`
does not change whether a target morphism is a lift. -/
private theorem isHomLift_over_target_eq_iff
    (F : X ⥤ᵇ Y) {z : Y.obj} {x : X.obj}
    (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (θ : z ⟶ F.obj x) :
    Y.p.IsHomLift g θ ↔ Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) θ := by
  -- The trailing `eqToHom` only rewrites the target object into source coordinates.
  simpa using IsHomLift.lift_comp_eqToHom_iff Y.p g θ (F.w_obj x)

/-- Helper for Definition 4.36.2: a target-side factorization pulls back along the inverse and the
unit inverse to the corresponding source-side factorization. -/
private theorem pullback_factorization_of_map_factorization
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} {τ' : z ⟶ F.obj x} {ψ' : z ⟶ F.obj y}
    (hτ' : τ' ≫ F.map φ = ψ') :
    (e.inverse.map τ' ≫ e.unitIso.inv.app x) ≫ φ =
      e.inverse.map ψ' ≫ e.unitIso.inv.app y := by
  -- Move the source morphism past the unit inverse using naturality.
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

/-- Helper for Definition 4.36.2: the inverse counit component of the adjointified equivalence
cancels the raw unit inverse on each target object. -/
private theorem adjointified_counit_unit_inverse_comp
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F) (x : X.obj) :
    e.toEquivalence.counit.inv.app (F.obj x) ≫ F.map (e.unitIso.inv.app x) = 𝟙 (F.obj x) := by
  -- Reuse the earlier equivalence-over-base triangle comparison from Lemma 4.33.8.
  exact BasedFunctor.adjointified_left_triangle_inverse_component_simplified F e x

/-- Helper for Definition 4.36.2: pushing the pulled-back morphism forward with the adjointified
counit inverse recovers the original target morphism. -/
private theorem pushforward_pullback_eq
    (F : X ⥤ᵇ Y) (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (θ : z ⟶ F.obj x) :
    e.toEquivalence.counit.inv.app z ≫
        F.map (e.inverse.map θ ≫ e.unitIso.inv.app x) = θ := by
  -- Reuse the established push-pull comparison over an equivalence of based categories.
  exact BasedFunctor.pushforward_pullback_eq F e θ

/-- Helper for Definition 4.36.2: an equivalence over the base sends strongly cartesian morphisms
to strongly cartesian morphisms after applying the based functor. -/
private theorem isStronglyCartesian_map_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase)
    {x y : X.obj} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := by
  -- The strong-cartesian transport statement is already proved in Lemma 4.33.8.
  exact BasedFunctor.isStronglyCartesian_map_of_isEquivalenceOverBase F hF φ hφ

/-- Helper for Definition 4.36.2: fibredness transports forward along an equivalence over the base
category. -/
private theorem isFibered_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) :
    X.p.IsFibered → Y.p.IsFibered := by
  intro hX
  -- Transport fibredness forward using the earlier equivalence-over-base invariance theorem.
  exact (BasedFunctor.isFibered_iff_of_equivalence_over_base F hF).mp hX

/-- Helper for Definition 4.36.2: fibredness transports backward along an equivalence over the
base category. -/
private theorem isFibered_of_equivalence_over_base
    {X : BasedCategory.{v₂, u₂} C}
    {Y : BasedCategory.{max v₁ v₂, max u₁ u₂} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ X)
    (hFG : F ⋙ G = 𝟙 X) (hGF : G ⋙ F = 𝟙 Y)
    (hY : Y.p.IsFibered) :
    X.p.IsFibered := by
  let hFGfun : F.toFunctor ⋙ G.toFunctor = 𝟭 X.obj := congrArg BasedFunctor.toFunctor hFG
  let hGFfun : G.toFunctor ⋙ F.toFunctor = 𝟭 Y.obj := congrArg BasedFunctor.toFunctor hGF
  letI : F.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' G.toFunctor (eqToIso hFGfun.symm) (eqToIso hGFfun)
  -- The proof follows the source construction: choose a strongly cartesian lift in the model
  -- and pull it back along the strict inverse over the base.
  refine (Functor.isFibered_iff_exists_isStronglyCartesian X.p).2 ?_
  intro x V f
  rcases (Functor.isFibered_iff_exists_isStronglyCartesian Y.p).1 hY (F.obj x) V
      (f ≫ eqToHom (F.w_obj x).symm) with ⟨z, ψ, hψ⟩
  let ξ : G.obj z ⟶ x :=
    G.map ψ ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)
  refine ⟨G.obj z, ξ, ?_⟩
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · -- The pulled-back comparison morphism lies over the original base arrow after rewriting the
    -- strict inverse relation on the codomain.
    have hGψ : X.p.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) (G.map ψ) :=
      (G.isHomLift_iff (f ≫ eqToHom (F.w_obj x).symm) ψ).2
        (show Y.p.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) ψ from hψ.toIsHomLift)
    have hEq : X.p.IsHomLift (𝟙 (X.p.obj x))
        (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) :=
      IsHomLift.eqToHom_codomain_lift_id (p := X.p)
        (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG) (rfl : X.p.obj x = X.p.obj x)
    have hComp : X.p.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) ξ := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        (f ≫ eqToHom (F.w_obj x).symm) (G.map ψ) hGψ
        (X.p.obj x) (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) hEq
    simpa [ξ] using hComp
  · intro w g τ hτ
    -- Push the source lifting problem into the model category and solve it there using the
    -- strongly cartesian lift `ψ`.
    have hτYbase : Y.p.IsHomLift (g ≫ f) (F.map τ) :=
      (F.isHomLift_iff (g ≫ f) τ).2 (show X.p.IsHomLift (g ≫ f) τ from hτ)
    have hτY : Y.p.IsHomLift (g ≫ (f ≫ eqToHom (F.w_obj x).symm)) (F.map τ) := by
      have : Y.p.IsHomLift ((g ≫ f) ≫ eqToHom (F.w_obj x).symm) (F.map τ) :=
        (IsHomLift.lift_comp_eqToHom_iff Y.p (g ≫ f) (F.map τ) (F.w_obj x).symm).2 hτYbase
      simpa [Category.assoc] using this
    letI : Y.p.IsHomLift (g ≫ (f ≫ eqToHom (F.w_obj x).symm)) (F.map τ) := hτY
    obtain ⟨χ', hχ', hχ'uniq⟩ :=
      IsStronglyCartesian.universal_property Y.p (f ≫ eqToHom (F.w_obj x).symm) ψ g _ rfl
        (F.map τ)
    let χ : w ⟶ G.obj z :=
      eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫ G.map χ'
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · -- Pull the model-side factor back across the strict inverse on the source object.
      have hGχ' : X.p.IsHomLift g (G.map χ') :=
        (G.isHomLift_iff g χ').2 (show Y.p.IsHomLift g χ' from hχ'.1)
      have hEq : X.p.IsHomLift (𝟙 (X.p.obj w))
          (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm) :=
        IsHomLift.eqToHom_domain_lift_id (p := X.p)
          (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm (rfl : X.p.obj w = X.p.obj w)
      have hComp : X.p.IsHomLift g χ := by
        exact @IsHomLift.comp_lift_id_left' _ _ _ _ X.p _ _ _
          (X.p.obj w) (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm) hEq
          _ _ g (G.map χ') hGχ'
      simpa [χ] using hComp
    · -- The strict inverse equations turn the pulled-back factorization into the original one.
      dsimp [χ, ξ]
      calc
        (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫ G.map χ') ≫
            (G.map ψ ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG))
            = eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫
                G.map (χ' ≫ ψ) ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG) := by
                  simp [Functor.map_comp, Category.assoc]
        _ = eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫
              G.map (F.map τ) ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG) := by
                rw [hχ'.2]
        _ = τ := by
              have hτraw : G.map (F.map τ) =
                  eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG) ≫ τ ≫
                    eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG).symm := by
                simpa [Functor.comp_map] using Functor.congr_hom hFGfun τ
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫ k ≫
                    eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG))
                  hτraw
    · intro κ hκ
      -- Push any competing factor back to the model and use uniqueness there.
      have hκY : Y.p.IsHomLift g
          (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) := by
        have hFκ : Y.p.IsHomLift g (F.map κ) :=
          (F.isHomLift_iff g κ).2 (show X.p.IsHomLift g κ from hκ.1)
        have hEq : Y.p.IsHomLift (𝟙 (Y.p.obj z))
            (eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) :=
          IsHomLift.eqToHom_codomain_lift_id (p := Y.p)
            (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) (rfl : Y.p.obj z = Y.p.obj z)
        exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          g (F.map κ) hFκ
          (Y.p.obj z) (eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) hEq
      have hκfac :
          (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫ ψ = F.map τ := by
        have hψnat :
            F.map (G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF) =
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) ≫ ψ := by
          have hψraw : F.map (G.map ψ) =
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) ≫ ψ ≫
                eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF).symm := by
            simpa [Functor.comp_map] using Functor.congr_hom hGFfun ψ
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF))
              hψraw
        have hFGmap :
            F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) =
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF) := by
          simp [eqToHom_map]
        have hstep0 :
            (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫ ψ =
              F.map κ ≫
                (F.map (G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF)) := by
          calc
            (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫ ψ
                = F.map κ ≫
                    (eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) ≫ ψ) := by
                      simp [Category.assoc]
            _ = F.map κ ≫
                  (F.map (G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF)) := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun t ↦ F.map κ ≫ t)
                        hψnat.symm
        have hstep1 :
            F.map (κ ≫ G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF) =
              F.map (κ ≫ G.map ψ) ≫
                F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ F.map (κ ≫ G.map ψ) ≫ t) hFGmap.symm
        have hstep2 :
            F.map κ ≫
                (F.map (G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF)) =
              F.map (κ ≫ G.map ψ) ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj x)) hGF) := by
          simp [Functor.map_comp, Category.assoc]
        have hstep3 :
            F.map (κ ≫ G.map ψ) ≫
                F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) =
              F.map (κ ≫ G.map ψ ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) := by
          simp [Functor.map_comp, Category.assoc]
        have hstep4 :
            F.map (κ ≫ G.map ψ ≫ eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj x) hFG)) = F.map τ := by
          simpa [ξ, Functor.map_comp, Category.assoc] using congrArg F.map hκ.2
        exact hstep0.trans <| hstep2.trans <| hstep1.trans <| hstep3.trans hstep4
      have hκeq : F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF) = χ' :=
        hχ'uniq _ ⟨hκY, hκfac⟩
      have hχmap : F.map χ = χ' ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
        have hχraw : F.map (G.map χ') =
            eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj (F.obj w)) hGF) ≫ χ' ≫
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
          simpa [Functor.comp_map] using Functor.congr_hom hGFfun χ'
        dsimp [χ]
        calc
          F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm ≫ G.map χ')
              = F.map (eqToHom (congrArg (fun H : X ⥤ᵇ X => H.obj w) hFG).symm) ≫ F.map (G.map χ') := by
                  simp [Functor.map_comp]
          _ = χ' ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
                simp [eqToHom_map, hχraw]
      have hstep1 : F.map κ =
          (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫
            eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
        simp [Category.assoc]
      have hstep2 :
          (F.map κ ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF)) ≫
              eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm =
            χ' ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫ eqToHom (congrArg (fun H : Y ⥤ᵇ Y => H.obj z) hGF).symm)
            hκeq
      have hκmap : F.map κ = F.map χ := by
        rw [hstep1, hstep2, hχmap]
      exact F.toFunctor.map_injective hκmap

theorem isFibered {p : S ⥤ C} (hp : Functor.IsSplitFibredCategory p) : p.IsFibered := by
  -- Unpack the split model promised by the definition.
  rcases hp.existsCoGrothendieckModel with ⟨F, e, eInv, hη, hε⟩
  -- Transfer fibredness from the canonical co-Grothendieck model back to `p`.
  let hModel : (CoGrothendieck.forget (F.toPseudofunctor')).IsFibered := inferInstance
  exact
    isFibered_of_equivalence_over_base
      (X := BasedCategory.ofFunctor p)
      (Y := BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor')))
      e eInv hη hε
      (show (BasedCategory.ofFunctor (CoGrothendieck.forget (F.toPseudofunctor'))).p.IsFibered from
        hModel)

end IsSplitFibredCategory

instance (p : S ⥤ C) [Functor.IsSplitFibredCategory p] : p.IsFibered :=
  IsSplitFibredCategory.isFibered inferInstance

end Functor

end CategoryTheory
