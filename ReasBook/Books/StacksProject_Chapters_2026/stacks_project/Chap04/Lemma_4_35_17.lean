module

public import stacks_project.Chap04.Lemma_4_33_8
public import stacks_project.Chap04.Lemma_4_34_1
public import stacks_project.Chap04.Lemma_4_35_2
public import stacks_project.Chap04.Lemma_4_35_16

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryOver

universe u v vW uA uB uS uT uW uX uX' uX'' uY uZ

namespace CategoryTheory

open BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{v, uX} C}
variable {X' : BasedCategory.{v, uX'} C}
variable {X'' : BasedCategory.{v, uX''} C}
variable {Y : BasedCategory.{v, uY} C}

/- Domain-style sampling for Lemma 4.35.17:
- primary domain: factorizations in `Cat/C` through categories fibred in groupoids over a fixed
  target, compared up to equivalence over the base and over the target;
- sampled owner-level declarations:
  `BasedCategory.ofFunctor`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `BasedFunctor.hom_isEquivalenceOverBase`,
  `fibredInGroupoidsFactorizationFromSource`;
- best owner abstraction: the main comparison data lives on based functors and their owner
  predicate `IsEquivalenceOverBase`; Lemma `4.35.16` already supplies the canonical explicit
  factorization model, so this file should add only the source-facing comparison theorems and the
  minimal target-over-target bridge helpers they need.

Primitive-vs-derived split:
- primitive data: the two factorizations `a ⋙ f` and `b ⋙ g` of `F`;
- derived API: the comparison equivalence over `Y`, its forgotten comparison over `C`, and in the
  strict case the induced `2`-isomorphism in `Cat/Y`.

Source/core/bridge triage:
- `source-facing`: the two comparison theorems in this file;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase` and the explicit factorization owner from
  Lemma `4.35.16`;
- `bridge/view`: the thin helpers `forgetTarget` and `overTargetOfCompEq`, which only re-express the
  same functors at the target-over-target level needed by the theorem statements. -/

namespace BasedFunctor

variable {F : X ⥤ᵇ Y} {f : X' ⥤ᵇ Y} {g : X'' ⥤ᵇ Y}

/-- A morphism in `Cat/Y` canonically forgets to a morphism in `Cat/C`. -/
abbrev forgetTarget
    (h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor) :
    X'' ⥤ᵇ X' :=
  { toFunctor := h.toFunctor
    w := by
      calc
        h.toFunctor ⋙ X'.p = h.toFunctor ⋙ (f.toFunctor ⋙ Y.p) := by
          simpa [Functor.assoc] using congrArg (Functor.comp h.toFunctor) f.w.symm
        _ = (h.toFunctor ⋙ f.toFunctor) ⋙ Y.p := by rw [Functor.assoc]
        _ = g.toFunctor ⋙ Y.p := by
          simpa [Functor.assoc] using
            congrArg (fun q : X''.obj ⥤ Y.obj ↦ q ⋙ Y.p) h.w
        _ = X''.p := g.w }

/-- A strict factorization `a ⋙ f = F` is the same data as a morphism in `Cat/Y`. -/
abbrev overTargetOfCompEq
    (a : X ⥤ᵇ X') (ha : a ⋙ f = F) :
    BasedCategory.ofFunctor F.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor :=
  { toFunctor := a.toFunctor
    w := congrArg toFunctor ha }

end BasedFunctor

section TriangleComparison

variable {F : X ⥤ᵇ Y}
variable {Z : BasedCategory.{v, uZ} C}
variable (u : X ⥤ᵇ Z) (v : Z ⥤ᵇ Y)

/-- Helper for Lemma 4.35.17: two based functors are equal once their underlying functors agree. -/
private theorem basedFunctor_ext
    {A : BasedCategory.{v, uA} C} {B : BasedCategory.{v, uB} C}
    {F G : A ⥤ᵇ B} (h : F.toFunctor = G.toFunctor) :
    F = G := by
  -- The based structure is determined by the underlying functor and its compatibility witness.
  cases F
  cases G
  cases h
  rfl

/-- Helper for Lemma 4.35.17: whisker a `2`-commutative triangle `u ⋙ v ≅ F` with a chosen
quasi-inverse of `u` to obtain the comparison isomorphism `u⁻¹ ⋙ F ≅ v`. -/
private noncomputable def inverse_whisker_target_iso
    (e : BasedFunctor.EquivalenceOverBase u)
    (σ : u ⋙ v ≅ F) :
    BasedFunctor.comp e.inverse F ≅ v := by
  let hσ : BasedFunctor.comp e.inverse (u ⋙ v) ≅ BasedFunctor.comp e.inverse F :=
    -- The source proof first transports the triangle along the chosen quasi-inverse to `u`.
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft e.inverse.toFunctor
        ((BasedNatTrans.forgetful X Y).mapIso σ))
      (BasedCategory.whiskerLeft e.inverse σ.hom).isHomLift'
  let hε : BasedFunctor.comp (BasedFunctor.comp e.inverse u) v ≅ v :=
    -- Reassociate to expose the counit of the chosen equivalence over `C`.
      eqToIso (BasedFunctor.comp_assoc e.inverse u v) ≪≫
      BasedNatIso.mkNatIso
        (Functor.isoWhiskerRight
          ((BasedNatTrans.forgetful Z Z).mapIso e.counitIso) v.toFunctor)
        (BasedCategory.whiskerRight e.counitIso.hom v).isHomLift' ≪≫
      eqToIso (BasedFunctor.comp_id v)
  exact hσ.symm ≪≫ hε

/-- Helper for Lemma 4.35.17: the chosen quasi-inverse to a triangle factorization gives an
explicit functor over `Y` from that factorization to the canonical factorization
`X ×_{F,Y,\mathrm{id}} Y`. -/
private noncomputable def triangle_comparison_to_canonical_factorization
    (e : BasedFunctor.EquivalenceOverBase u)
    (σ : u ⋙ v ≅ F) :
    BasedCategory.ofFunctor v.toFunctor ⥤ᵇ
      BasedCategory.ofFunctor (fibredInGroupoidsFactorizationToTarget F).toFunctor :=
  let θ := inverse_whisker_target_iso (F := F) u v e σ
  { toFunctor :=
      { obj := fun z ↦
          { U := Z.p.obj z
            obj :=
              { fst := ⟨e.inverse.obj z, e.inverse.w_obj z⟩
                snd := ⟨v.obj z, v.w_obj z⟩
                iso :=
                  { hom := Functor.Fiber.homMk Y.p (Z.p.obj z) (θ.hom.app z)
                    inv := Functor.Fiber.homMk Y.p (Z.p.obj z) (θ.inv.app z)
                    hom_inv_id := by
                      apply Functor.Fiber.hom_ext
                      simpa using
                        ((BasedNatTrans.forgetful Z Y).mapIso θ).hom_inv_id_app z
                    inv_hom_id := by
                      apply Functor.Fiber.hom_ext
                      simpa using
                        ((BasedNatTrans.forgetful Z Y).mapIso θ).inv_hom_id_app z } } }
        map := fun η ↦
          { base := Z.p.map η
            a := e.inverse.map η
            a_over := by infer_instance
            b := v.map η
            b_over := by infer_instance
            comm := by
              -- Naturality of the whiskered comparison gives the pullback square condition.
              refine ⟨?_⟩
              simpa using θ.hom.naturality η }
        map_id := fun z ↦ by
          apply CategoryOver.ExplicitTwoFibreProductHom.ext (F := F) (G := BasedFunctor.id Y)
          · dsimp
            change e.inverse.map (𝟙 z) = 𝟙 (e.inverse.obj z)
            exact e.inverse.toFunctor.map_id z
          · dsimp
            change v.map (𝟙 z) = 𝟙 (v.obj z)
            exact v.toFunctor.map_id z
        map_comp := fun η ζ ↦ by
          apply CategoryOver.ExplicitTwoFibreProductHom.ext (F := F) (G := BasedFunctor.id Y)
          · dsimp
            change e.inverse.map (η ≫ ζ) = e.inverse.map η ≫ e.inverse.map ζ
            exact e.inverse.toFunctor.map_comp η ζ
          · dsimp
            change v.map (η ≫ ζ) = v.map η ≫ v.map ζ
            exact v.toFunctor.map_comp η ζ }
    w := rfl }

/-- Helper for Lemma 4.35.17: the stored comparison morphism of the canonical source object is the
identity on `F.obj x`. -/
private theorem triangle_source_comparison_id (x : X.obj) :
    ExplicitTwoFibreProductObject.comparison F (BasedFunctor.id Y)
      ((fibredInGroupoidsFactorizationFromSource F).obj x) =
      𝟙 (F.obj x) := by
  rfl
/-- Helper for Lemma 4.35.17: the left whiskering step contributes the inverse component of
`σ` after evaluating at the chosen quasi-inverse object. -/
private theorem inverse_whisker_target_iso_triangle_component_app
    (e : BasedFunctor.EquivalenceOverBase u)
    (σ : u ⋙ v ≅ F) (z : Z.obj) :
    (BasedNatIso.mkNatIso
        (Functor.isoWhiskerLeft e.inverse.toFunctor
          ((BasedNatTrans.forgetful X Y).mapIso σ))
        (BasedCategory.whiskerLeft e.inverse σ.hom).isHomLift').inv.app z =
      (show (BasedFunctor.comp e.inverse F).obj z ⟶
          (BasedFunctor.comp e.inverse (u ⋙ v)).obj z from
        σ.inv.app (e.inverse.obj z)) := by
  -- The left-whiskered triangle isomorphism is definitional on components.
  rfl

/-- Helper for Lemma 4.35.17: the counit-whiskering step contributes the `v`-image of the counit
component. -/
private theorem inverse_whisker_target_iso_counit_component_app
    (e : BasedFunctor.EquivalenceOverBase u)
    (z : Z.obj) :
    (BasedNatIso.mkNatIso
        (Functor.isoWhiskerRight
          ((BasedNatTrans.forgetful Z Z).mapIso e.counitIso) v.toFunctor)
        (BasedCategory.whiskerRight e.counitIso.hom v).isHomLift').hom.app z =
      (show (BasedFunctor.comp (BasedFunctor.comp e.inverse u) v).obj z ⟶
          v.obj z from
        v.map (e.counitIso.hom.app z)) := by
  -- The right-whiskered counit isomorphism is likewise definitional on components.
  rfl

/-- Helper for Lemma 4.35.17: the source proof’s pair `(β_x, α_x)` should package into an
isomorphism from the canonical source map to the comparison functor composed with `u`. -/
private noncomputable def triangle_comparison_component_iso
    (e : BasedFunctor.EquivalenceOverBase u)
    (σ : u ⋙ v ≅ F) (x : X.obj) :
    ((fibredInGroupoidsFactorizationFromSource F).obj x) ≅
      ((BasedFunctor.comp u
          (BasedFunctor.forgetTarget
            (triangle_comparison_to_canonical_factorization (F := F) u v e σ))).obj x) := by
  let θ := inverse_whisker_target_iso (F := F) u v e σ
  refine
    { hom := ?_
      inv := ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · refine
      { base := eqToHom (u.w_obj x).symm
        a := e.unitIso.hom.app x
        a_over := ?_
        b := F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x)
        b_over := ?_
        comm := ?_ }
    · have hunit :
        X.p.IsHomLift (𝟙 (X.p.obj x)) (e.unitIso.hom.app x) := by
        simpa using BasedNatTrans.isHomLift e.unitIso.hom (rfl : X.p.obj x = X.p.obj x)
      letI := hunit
      refine
        IsHomLift.of_fac' X.p (eqToHom (u.w_obj x).symm) (e.unitIso.hom.app x)
          rfl (e.inverse.w_obj (u.obj x)) ?_
      simpa [BasedFunctor.comp, Category.assoc] using
        (IsHomLift.fac' X.p (𝟙 (X.p.obj x)) (e.unitIso.hom.app x))
    · have hunit :
        X.p.IsHomLift (𝟙 (X.p.obj x)) (e.unitIso.hom.app x) := by
        simpa using BasedNatTrans.isHomLift e.unitIso.hom (rfl : X.p.obj x = X.p.obj x)
      have hmap :
        Y.p.IsHomLift (eqToHom (u.w_obj x).symm) (F.map (e.unitIso.hom.app x)) := by
        exact (F.isHomLift_iff (eqToHom (u.w_obj x).symm) (e.unitIso.hom.app x)).2 <|
          IsHomLift.of_fac' X.p (eqToHom (u.w_obj x).symm) (e.unitIso.hom.app x)
            rfl (e.inverse.w_obj (u.obj x)) (by
              letI := hunit
              simpa [BasedFunctor.comp, Category.assoc] using
                (IsHomLift.fac' X.p (𝟙 (X.p.obj x)) (e.unitIso.hom.app x)))
      have hθ :
        Y.p.IsHomLift (𝟙 (Z.p.obj (u.obj x))) (θ.hom.app (u.obj x)) := by
        simpa using
          BasedNatTrans.isHomLift θ.hom
            (rfl : Z.p.obj (u.obj x) = Z.p.obj (u.obj x))
      letI : Y.p.IsHomLift (eqToHom (u.w_obj x).symm) (F.map (e.unitIso.hom.app x)) := hmap
      letI : Y.p.IsHomLift (𝟙 (Z.p.obj (u.obj x))) (θ.hom.app (u.obj x)) := hθ
      have hcomp :
        Y.p.IsHomLift
          (eqToHom (u.w_obj x).symm ≫ 𝟙 (Z.p.obj (u.obj x)))
          (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x)) :=
        @IsHomLift.comp _ _ _ _ Y.p _ _ _ _ _ _
          (eqToHom (u.w_obj x).symm)
          (𝟙 (Z.p.obj (u.obj x)))
          (F.map (e.unitIso.hom.app x))
          (θ.hom.app (u.obj x))
          hmap
          hθ
      simpa using hcomp
    · change
        CommSq
          (F.map (e.unitIso.hom.app x))
          (ExplicitTwoFibreProductObject.comparison F (BasedFunctor.id Y)
            ((fibredInGroupoidsFactorizationFromSource F).obj x))
          (θ.hom.app (u.obj x))
          (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x))
      refine ⟨?_⟩
      change
        F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x) =
          𝟙 (F.obj x) ≫ (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x))
      simp
  · refine
      { base := eqToHom (u.w_obj x)
        a := e.unitIso.inv.app x
        a_over := ?_
        b := θ.inv.app (u.obj x) ≫ F.map (e.unitIso.inv.app x)
        b_over := ?_
        comm := ?_ }
    · have hunit :
        X.p.IsHomLift (𝟙 (X.p.obj x)) (e.unitIso.inv.app x) := by
        simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj x = X.p.obj x)
      letI := hunit
      refine
        IsHomLift.of_fac' X.p (eqToHom (u.w_obj x)) (e.unitIso.inv.app x)
          (e.inverse.w_obj (u.obj x)) rfl ?_
      simpa [BasedFunctor.comp, Category.assoc] using
        (IsHomLift.fac' X.p (𝟙 (X.p.obj x)) (e.unitIso.inv.app x))
    · have hunit :
        X.p.IsHomLift (𝟙 (X.p.obj x)) (e.unitIso.inv.app x) := by
        simpa using BasedNatTrans.isHomLift e.unitIso.inv (rfl : X.p.obj x = X.p.obj x)
      have hmap :
        Y.p.IsHomLift (eqToHom (u.w_obj x)) (F.map (e.unitIso.inv.app x)) := by
        exact (F.isHomLift_iff (eqToHom (u.w_obj x)) (e.unitIso.inv.app x)).2 <|
          IsHomLift.of_fac' X.p (eqToHom (u.w_obj x)) (e.unitIso.inv.app x)
            (e.inverse.w_obj (u.obj x)) rfl (by
              letI := hunit
              simpa [BasedFunctor.comp, Category.assoc] using
                (IsHomLift.fac' X.p (𝟙 (X.p.obj x)) (e.unitIso.inv.app x)))
      have hθ :
        Y.p.IsHomLift (𝟙 (Z.p.obj (u.obj x))) (θ.inv.app (u.obj x)) := by
        simpa using
          BasedNatTrans.isHomLift θ.inv
            (rfl : Z.p.obj (u.obj x) = Z.p.obj (u.obj x))
      letI : Y.p.IsHomLift (𝟙 (Z.p.obj (u.obj x))) (θ.inv.app (u.obj x)) := hθ
      letI : Y.p.IsHomLift (eqToHom (u.w_obj x)) (F.map (e.unitIso.inv.app x)) := hmap
      have hcomp :
        Y.p.IsHomLift
          (𝟙 (Z.p.obj (u.obj x)) ≫ eqToHom (u.w_obj x))
          (θ.inv.app (u.obj x) ≫ F.map (e.unitIso.inv.app x)) :=
        @IsHomLift.comp _ _ _ _ Y.p _ _ _ _ _ _
          (𝟙 (Z.p.obj (u.obj x)))
          (eqToHom (u.w_obj x))
          (θ.inv.app (u.obj x))
          (F.map (e.unitIso.inv.app x))
          hθ
          hmap
      simpa using hcomp
    · change
        CommSq
          (F.map (e.unitIso.inv.app x))
          (θ.hom.app (u.obj x))
          (ExplicitTwoFibreProductObject.comparison F (BasedFunctor.id Y)
            ((fibredInGroupoidsFactorizationFromSource F).obj x))
          (θ.inv.app (u.obj x) ≫ F.map (e.unitIso.inv.app x))
      refine ⟨?_⟩
      change
        F.map (e.unitIso.inv.app x) ≫ 𝟙 (F.obj x) =
          θ.hom.app (u.obj x) ≫ (θ.inv.app (u.obj x) ≫ F.map (e.unitIso.inv.app x))
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ F.map (e.unitIso.inv.app x))
          (((BasedNatTrans.forgetful Z Y).mapIso θ).hom_inv_id_app (u.obj x)).symm
  · apply CategoryOver.ExplicitTwoFibreProductHom.ext (F := F) (G := BasedFunctor.id Y)
    · change e.unitIso.hom.app x ≫ e.unitIso.inv.app x = 𝟙 x
      simpa using ((BasedNatTrans.forgetful X X).mapIso e.unitIso).hom_inv_id_app x
    · change
        (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x)) ≫
            (θ.inv.app (u.obj x) ≫ F.map (e.unitIso.inv.app x)) =
          𝟙 (F.obj x)
      calc
        (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x)) ≫
            (θ.inv.app (u.obj x) ≫ F.map (e.unitIso.inv.app x)) =
            F.map (e.unitIso.hom.app x) ≫
              (θ.hom.app (u.obj x) ≫ θ.inv.app (u.obj x)) ≫
                F.map (e.unitIso.inv.app x) := by simp [Category.assoc]
        _ = F.map (e.unitIso.hom.app x) ≫
              𝟙 (F.obj (e.inverse.obj (u.obj x))) ≫
                F.map (e.unitIso.inv.app x) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    F.map (e.unitIso.hom.app x) ≫ k ≫
                      F.map (e.unitIso.inv.app x))
                  (((BasedNatTrans.forgetful Z Y).mapIso θ).hom_inv_id_app (u.obj x))
        _ = F.map (e.unitIso.hom.app x ≫ e.unitIso.inv.app x) := by
              simp [Functor.map_comp]
        _ = 𝟙 (F.obj x) := by
              simpa [Functor.map_comp] using
                congrArg F.map
                  (((BasedNatTrans.forgetful X X).mapIso e.unitIso).hom_inv_id_app x)
  · apply CategoryOver.ExplicitTwoFibreProductHom.ext (F := F) (G := BasedFunctor.id Y)
    · change e.unitIso.inv.app x ≫ e.unitIso.hom.app x = 𝟙 (e.inverse.obj (u.obj x))
      simpa using ((BasedNatTrans.forgetful X X).mapIso e.unitIso).inv_hom_id_app x
    · change
        (θ.inv.app (u.obj x) ≫ F.map (e.unitIso.inv.app x)) ≫
            (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x)) =
          𝟙 (v.obj (u.obj x))
      calc
        (θ.inv.app (u.obj x) ≫ F.map (e.unitIso.inv.app x)) ≫
            (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x)) =
            θ.inv.app (u.obj x) ≫
              (F.map (e.unitIso.inv.app x) ≫ F.map (e.unitIso.hom.app x)) ≫
                θ.hom.app (u.obj x) := by simp [Category.assoc]
        _ = θ.inv.app (u.obj x) ≫
              𝟙 (F.obj (e.inverse.obj (u.obj x))) ≫
                θ.hom.app (u.obj x) := by
              simpa [Functor.map_comp, Category.assoc] using
                congrArg
                  (fun k ↦ θ.inv.app (u.obj x) ≫ F.map k ≫ θ.hom.app (u.obj x))
                  (((BasedNatTrans.forgetful X X).mapIso e.unitIso).inv_hom_id_app x)
        _ = 𝟙 (v.obj (u.obj x)) := by
              simpa [Category.assoc] using
                ((BasedNatTrans.forgetful Z Y).mapIso θ).inv_hom_id_app (u.obj x)

/-- Helper for Lemma 4.35.17: the objectwise comparison isomorphisms assemble into a natural
isomorphism from the canonical source factorization to the comparison functor composed with `u`. -/
private noncomputable def triangle_comparison_from_source_iso
    (e : BasedFunctor.EquivalenceOverBase u)
    (σ : u ⋙ v ≅ F) :
    fibredInGroupoidsFactorizationFromSource F ≅
      BasedFunctor.comp u
        (BasedFunctor.forgetTarget
          (triangle_comparison_to_canonical_factorization (F := F) u v e σ)) := by
  -- Route correction: package the objectwise unit/canonical-comparison pair first, then check
  -- naturality by the unit naturality of `e` and the naturality of the whiskered target iso.
  refine BasedNatIso.mkNatIso ?_ ?_
  · refine NatIso.ofComponents (fun x ↦ triangle_comparison_component_iso (F := F) u v e σ x) ?_
    intro x x' φ
    apply CategoryOver.ExplicitTwoFibreProductHom.ext (F := F) (G := BasedFunctor.id Y)
    · change
        φ ≫ e.unitIso.hom.app x' =
          e.unitIso.hom.app x ≫ e.inverse.map (u.map φ)
      simpa [BasedFunctor.comp, Category.assoc] using
        ((BasedNatTrans.forgetful X X).mapIso e.unitIso).hom.naturality φ
    · let θ := inverse_whisker_target_iso (F := F) u v e σ
      change
        F.map φ ≫ (F.map (e.unitIso.hom.app x') ≫ θ.hom.app (u.obj x')) =
          (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x)) ≫ v.map (u.map φ)
      calc
        F.map φ ≫ (F.map (e.unitIso.hom.app x') ≫ θ.hom.app (u.obj x')) =
            F.map (φ ≫ e.unitIso.hom.app x') ≫ θ.hom.app (u.obj x') := by
              simp [Functor.map_comp, Category.assoc]
        _ = F.map (e.unitIso.hom.app x ≫ e.inverse.map (u.map φ)) ≫
              θ.hom.app (u.obj x') := by
              congr 1
              simpa [Functor.map_comp, BasedFunctor.comp, Category.assoc] using
                congrArg F.map
                  (((BasedNatTrans.forgetful X X).mapIso e.unitIso).hom.naturality φ)
        _ = (F.map (e.unitIso.hom.app x) ≫ F.map (e.inverse.map (u.map φ))) ≫
              θ.hom.app (u.obj x') := by
              simp [Functor.map_comp, Category.assoc]
        _ = F.map (e.unitIso.hom.app x) ≫
              (θ.hom.app (u.obj x) ≫ v.map (u.map φ)) := by
              rw [Category.assoc]
              congr 1
              simpa [BasedFunctor.comp, Category.assoc] using
                θ.hom.naturality (u.map φ)
        _ = (F.map (e.unitIso.hom.app x) ≫ θ.hom.app (u.obj x)) ≫
              v.map (u.map φ) := by
              simp [Category.assoc]
  · intro x
    refine
      IsHomLift.of_fac' (fibredInGroupoidsFactorization F).p (𝟙 (X.p.obj x))
        ((triangle_comparison_component_iso (F := F) u v e σ x).hom)
        rfl
        ((BasedFunctor.comp u
            (BasedFunctor.forgetTarget
              (triangle_comparison_to_canonical_factorization (F := F) u v e σ))).w_obj x) ?_
    change
      eqToHom (u.w_obj x).symm =
        eqToHom rfl ≫ 𝟙 (X.p.obj x) ≫
          eqToHom
            ((BasedFunctor.comp u
                (BasedFunctor.forgetTarget
                  (triangle_comparison_to_canonical_factorization (F := F) u v e σ))).w_obj x).symm
    change
      eqToHom (u.w_obj x).symm =
        eqToHom rfl ≫ 𝟙 (X.p.obj x) ≫ eqToHom (u.w_obj x).symm
    simp

/-- Helper for Lemma 4.35.17: the explicit comparison functor from a `2`-commutative triangle to
the canonical factorization is already an equivalence of the underlying categories. -/
private theorem triangle_comparison_to_canonical_factorization_isEquivalence
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
    [IsFibredInGroupoids v.toFunctor]
    (e : BasedFunctor.EquivalenceOverBase u)
    (σ : u ⋙ v ≅ F) :
    (triangle_comparison_to_canonical_factorization (F := F) u v e σ).toFunctor.IsEquivalence := by
  -- Forget the source comparison isomorphism to the underlying categories, then cancel the given
  -- equivalence `u` on the left.
  have hSource :
      (fibredInGroupoidsFactorizationFromSource F).toFunctor.IsEquivalence :=
    fibredInGroupoidsFactorizationFromSource_isEquivalence F
  have hIso :
      fibredInGroupoidsFactorizationFromSource F ≅
        BasedFunctor.comp u
          (BasedFunctor.forgetTarget
            (triangle_comparison_to_canonical_factorization (F := F) u v e σ)) :=
    triangle_comparison_from_source_iso (F := F) u v e σ
  have hComp :
      (u.toFunctor ⋙
        (triangle_comparison_to_canonical_factorization (F := F) u v e σ).toFunctor).IsEquivalence := by
    exact
      (Functor.isEquivalence_iff_of_iso
        (((BasedNatTrans.forgetful _ _).mapIso hIso).symm)).2 hSource
  have hUbase : u.IsEquivalenceOverBase := ⟨⟨e⟩⟩
  have hU : u.toFunctor.IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase u hUbase
  letI : u.toFunctor.IsEquivalence := hU
  letI :
      (u.toFunctor ⋙
        (triangle_comparison_to_canonical_factorization (F := F) u v e σ).toFunctor).IsEquivalence :=
    hComp
  simpa using
    Functor.isEquivalence_of_comp_left
      u.toFunctor
      (triangle_comparison_to_canonical_factorization (F := F) u v e σ).toFunctor

/-- Helper for Lemma 4.35.17: for categories fibred in groupoids over the fixed base `Y`, an
same-universe equivalence of the underlying categories upgrades to an equivalence over `Y`. -/
private theorem basedFunctor_isEquivalenceOverBase_of_isEquivalence_fixed_base_same_universe
    {S : Type uS} [Category.{vW} S]
    {T : Type uS} [Category.{vW} T]
    {p : S ⥤ Y.obj} {q : T ⥤ Y.obj}
    [IsFibredInGroupoids p] [IsFibredInGroupoids q]
    (c : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (hC : c.toFunctor.IsEquivalence) :
    c.IsEquivalenceOverBase := by
  -- In the same-universe case the fixed-base owner accepts both total categories directly, so the
  -- public Lemma `4.35.9` upgrade applies without any further transport.
  let P : FibredInGroupoidsOver Y.obj := FibredInGroupoidsOver.ofFunctor p
  let Q : FibredInGroupoidsOver Y.obj := FibredInGroupoidsOver.ofFunctor q
  let cMor : P ⟶ Q := FibredInGroupoidsMor.ofBasedFunctor c
  have hMor :
      FibredInGroupoidsMor.IsEquivalenceOverBase cMor :=
    FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence cMor (by
      simpa [P, Q, cMor, FibredInGroupoidsMor.G, FibredInGroupoidsMor.ofBasedFunctor] using hC)
  simpa [P, Q, cMor, FibredInGroupoidsMor.IsEquivalenceOverBase,
    FibredInGroupoidsMor.ofBasedFunctor] using hMor

/-- Helper for Lemma 4.35.17: transport a fixed-base fibred category to a common `AsSmall`
universe on the target side. -/
private abbrev fixed_base_target_small
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) :
    AsSmall.{uW} S ⥤ Y.obj :=
  -- Shrink the total category to a common universe and keep the same target functor to `Y.obj`.
  (AsSmall.down : AsSmall.{uW} S ⥤ S) ⋙ p

/-- Helper for Lemma 4.35.17: forget the target-side `AsSmall` wrapper as a based functor over
`Y.obj`. -/
private abbrev fixed_base_target_small_down
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) :
    BasedCategory.ofFunctor (fixed_base_target_small (Y := Y) (_W := _W) p) ⥤ᵇ
      BasedCategory.ofFunctor p :=
  -- This is the ordinary `AsSmall.down` functor, viewed over the fixed target `Y.obj`.
  { toFunctor :=
      (show (BasedCategory.ofFunctor (fixed_base_target_small (Y := Y) (_W := _W) p)).obj ⥤
          (BasedCategory.ofFunctor p).obj from
        (AsSmall.down : AsSmall.{uW} S ⥤ S))
    w := rfl }

/-- Helper for Lemma 4.35.17: insert the target-side `AsSmall` wrapper as a based functor over
`Y.obj`. -/
private abbrev fixed_base_target_small_up
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) :
    BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor (fixed_base_target_small (Y := Y) (_W := _W) p) :=
  -- This is the ordinary `AsSmall.up` functor, again over the fixed target `Y.obj`.
  { toFunctor :=
      (show (BasedCategory.ofFunctor p).obj ⥤
          (BasedCategory.ofFunctor (fixed_base_target_small (Y := Y) (_W := _W) p)).obj from
        (AsSmall.up : S ⥤ AsSmall.{uW} S))
    w := rfl }

/-- Helper for Lemma 4.35.17: inserting the target-side `AsSmall` wrapper and then forgetting it
is the strict identity on the transported total category. -/
private theorem fixed_base_target_small_down_up
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) :
    BasedFunctor.comp
        (fixed_base_target_small_down (_W := _W) p)
        (fixed_base_target_small_up (_W := _W) p) =
      BasedFunctor.id
        (BasedCategory.ofFunctor (fixed_base_target_small (_W := _W) p)) :=
  by
  -- `AsSmall.down ⋙ AsSmall.up` is strict identity on the shrunken total category.
  rfl

/-- Helper for Lemma 4.35.17: forgetting the target-side `AsSmall` wrapper and then reinserting
it is the strict identity on the original total category. -/
private theorem fixed_base_target_small_up_down
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) :
    BasedFunctor.comp
        (fixed_base_target_small_up (_W := _W) p)
        (fixed_base_target_small_down (_W := _W) p) =
      BasedFunctor.id (BasedCategory.ofFunctor p) :=
  by
  -- `AsSmall.up ⋙ AsSmall.down` is strict identity on the original total category.
  rfl

/-- Helper for Lemma 4.35.17: forgetting the target-side `AsSmall` wrapper is an equivalence
over `Y.obj`. -/
private theorem fixed_base_target_small_down_isEquivalenceOverBase
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) :
    (fixed_base_target_small_down (_W := _W) p).IsEquivalenceOverBase := by
  -- The strict up/down identities package the required equivalence-over-base data.
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    (fixed_base_target_small_up (_W := _W) p) ?_ ?_
  · simpa using eqToIso (fixed_base_target_small_down_up (_W := _W) p).symm
  · simpa using eqToIso (fixed_base_target_small_up_down (_W := _W) p)

/-- Helper for Lemma 4.35.17: inserting the target-side `AsSmall` wrapper is an equivalence over
`Y.obj`. -/
private theorem fixed_base_target_small_up_isEquivalenceOverBase
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) :
    (fixed_base_target_small_up (_W := _W) p).IsEquivalenceOverBase := by
  -- The same strict identities give the inverse equivalence in the opposite direction.
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    (fixed_base_target_small_down (_W := _W) p) ?_ ?_
  · simpa using eqToIso (fixed_base_target_small_up_down (_W := _W) p).symm
  · simpa using eqToIso (fixed_base_target_small_down_up (_W := _W) p)

/-- Helper for Lemma 4.35.17: fibredness transports backward along a strict equivalence over the
fixed target `Y.obj`, even when the two total categories live in different universes. -/
private theorem isFibered_of_isEquivalenceOverBase_over_target
    {S : Type uS} [Category.{v} S]
    {T : Type uT} [Category.{v} T]
    {p : S ⥤ Y.obj} {q : T ⥤ Y.obj}
    (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (hF : F.IsEquivalenceOverBase)
    (hq : q.IsFibered) :
    p.IsFibered := by
  -- The imported heterogeneous over-base transport theorem already applies on this fixed target.
  let e : BasedFunctor.EquivalenceOverBase F := Classical.choice hF.nonempty
  exact
    BasedFunctor.isFibered_of_equivalence_over_base_heterogeneous e
      (show (BasedCategory.ofFunctor q).p.IsFibered from hq)

/-- Helper for Lemma 4.35.17: fibredness transports backward along a strict equivalence over the
fixed target `Y.obj`, even when the two total categories live in different universes. -/
private theorem isFibered_of_strict_equivalence_over_target
    {S : Type uS} [Category.{vW} S]
    {T : Type uT} [Category.{v} T]
    {p : S ⥤ Y.obj} {q : T ⥤ Y.obj}
    (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (G : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p)
    (hFG : F ⋙ G = 𝟙 (BasedCategory.ofFunctor p))
    (hGF : G ⋙ F = 𝟙 (BasedCategory.ofFunctor q))
    (hq : q.IsFibered) :
    p.IsFibered := by
  let hFGfun : F.toFunctor ⋙ G.toFunctor = 𝟭 S := congrArg BasedFunctor.toFunctor hFG
  let hGFfun : G.toFunctor ⋙ F.toFunctor = 𝟭 T := congrArg BasedFunctor.toFunctor hGF
  letI : F.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' G.toFunctor (eqToIso hFGfun.symm) (eqToIso hGFfun)
  -- Route correction: copy the strict inverse transport proof from Definition 4.36.2 and run it
  -- over the fixed target `Y.obj`, where the `AsSmall` comparison only gives strict identities.
  refine (Functor.isFibered_iff_exists_isStronglyCartesian p).2 ?_
  intro x V f
  rcases (Functor.isFibered_iff_exists_isStronglyCartesian q).1 hq (F.obj x) V
      (f ≫ eqToHom (F.w_obj x).symm) with ⟨z, ψ, hψ⟩
  let ξ : G.obj z ⟶ x :=
    G.map ψ ≫ eqToHom (congrArg (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦
      H.obj x) hFG)
  refine ⟨G.obj z, ξ, ?_⟩
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · -- Pull the chosen lift back across the strict inverse and rewrite its codomain back to `x`.
    have hGψ : p.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) (G.map ψ) :=
      (G.isHomLift_iff (f ≫ eqToHom (F.w_obj x).symm) ψ).2
        (show q.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) ψ from hψ.toIsHomLift)
    have hEq : p.IsHomLift (𝟙 (p.obj x))
        (eqToHom (congrArg
          (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x) hFG)) :=
      IsHomLift.eqToHom_codomain_lift_id (p := p)
        (congrArg
          (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x) hFG)
        (rfl : p.obj x = p.obj x)
    have hComp : p.IsHomLift (f ≫ eqToHom (F.w_obj x).symm) ξ := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ p _ _ _ _ _
        (f ≫ eqToHom (F.w_obj x).symm) (G.map ψ) hGψ
        (p.obj x)
        (eqToHom (congrArg
          (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x) hFG))
        hEq
    simpa [ξ] using hComp
  · intro w g τ hτ
    -- Push the source factorization problem forward to `q`, solve it using the chosen strongly
    -- cartesian lift, and then pull the unique factor back across the strict inverse.
    have hτYbase : q.IsHomLift (g ≫ f) (F.map τ) :=
      (F.isHomLift_iff (g ≫ f) τ).2 (show p.IsHomLift (g ≫ f) τ from hτ)
    have hτY : q.IsHomLift (g ≫ (f ≫ eqToHom (F.w_obj x).symm)) (F.map τ) := by
      have : q.IsHomLift ((g ≫ f) ≫ eqToHom (F.w_obj x).symm) (F.map τ) :=
        (IsHomLift.lift_comp_eqToHom_iff q (g ≫ f) (F.map τ) (F.w_obj x).symm).2 hτYbase
      simpa [Category.assoc] using this
    letI : q.IsStronglyCartesian (f ≫ eqToHom (F.w_obj x).symm) ψ := hψ
    letI : q.IsHomLift (g ≫ (f ≫ eqToHom (F.w_obj x).symm)) (F.map τ) := hτY
    obtain ⟨χ', hχ', hχ'uniq⟩ :=
      Functor.IsStronglyCartesian.universal_property q (f ≫ eqToHom (F.w_obj x).symm) ψ g _ rfl
        (F.map τ)
    let χ : w ⟶ G.obj z :=
      eqToHom (congrArg
        (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w) hFG).symm ≫
          G.map χ'
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · -- Pull the model-side factor back and rewrite the domain to the original source object.
      have hGχ' : p.IsHomLift g (G.map χ') :=
        (G.isHomLift_iff g χ').2 (show q.IsHomLift g χ' from hχ'.1)
      have hEq : p.IsHomLift (𝟙 (p.obj w))
          (eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
              hFG).symm) :=
        IsHomLift.eqToHom_domain_lift_id (p := p)
          (congrArg
            (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
              hFG).symm
          (rfl : p.obj w = p.obj w)
      have hComp : p.IsHomLift g χ := by
        exact @IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _
          (p.obj w)
          (eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
              hFG).symm)
          hEq
          _ _ g (G.map χ') hGχ'
      simpa [χ] using hComp
    · -- The strict inverse identities collapse the pulled-back factorization to the original `τ`.
      dsimp [χ, ξ]
      calc
        (eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
              hFG).symm ≫ G.map χ') ≫
            (G.map ψ ≫ eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x) hFG))
            =
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                  hFG).symm ≫
                G.map (χ' ≫ ψ) ≫
                  eqToHom (congrArg
                    (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x)
                      hFG) := by
                  simp [Functor.map_comp, Category.assoc]
        _ = eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                hFG).symm ≫
              G.map (F.map τ) ≫
                eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x)
                    hFG) := by
              have hχ'map0 : G.map (χ' ≫ ψ) = G.map (F.map τ) := congrArg G.map hχ'.2
              have hχ'map : G.map χ' ≫ G.map ψ = G.map (F.map τ) := by
                simpa [Functor.map_comp] using hχ'map0
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    eqToHom (congrArg
                      (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                        hFG).symm ≫
                      k ≫
                        eqToHom (congrArg
                          (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦
                            H.obj x) hFG))
                  hχ'map
        _ = τ := by
              have hτraw : G.map (F.map τ) =
                  eqToHom (congrArg
                    (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                      hFG) ≫
                    τ ≫
                      eqToHom (congrArg
                        (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦
                          H.obj x) hFG).symm := by
                simpa [Functor.comp_map] using Functor.congr_hom hFGfun τ
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    eqToHom (congrArg
                      (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                        hFG).symm ≫
                      k ≫
                        eqToHom (congrArg
                          (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦
                            H.obj x) hFG))
                  hτraw
    · intro κ hκ
      -- Push any competing factor to `q`, use uniqueness there, and reflect equality back along
      -- the equivalence of underlying functors.
      have hκY : q.IsHomLift g
          (F.map κ ≫ eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF)) := by
        have hFκ : q.IsHomLift g (F.map κ) :=
          (F.isHomLift_iff g κ).2 (show p.IsHomLift g κ from hκ.1)
        have hEq : q.IsHomLift (𝟙 (q.obj z))
            (eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF)) :=
          IsHomLift.eqToHom_codomain_lift_id (p := q)
            (congrArg
              (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF)
            (rfl : q.obj z = q.obj z)
        exact @IsHomLift.comp_lift_id_right' _ _ _ _ q _ _ _ _ _
          g (F.map κ) hFκ
          (q.obj z)
          (eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF))
          hEq
      have hκfac :
          (F.map κ ≫ eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF)) ≫
              ψ =
            F.map τ := by
        have hψnat :
            F.map (G.map ψ) ≫ eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj x))
                hGF) =
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) ≫
                ψ := by
          have hψraw : F.map (G.map ψ) =
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) ≫
                ψ ≫
                  eqToHom (congrArg
                    (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦
                      H.obj (F.obj x)) hGF).symm := by
            simpa [Functor.comp_map] using Functor.congr_hom hGFfun ψ
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                k ≫
                  eqToHom (congrArg
                    (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦
                      H.obj (F.obj x)) hGF))
              hψraw
        have hFGmap :
            F.map (eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x) hFG)) =
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj x))
                  hGF) := by
          simp [eqToHom_map]
        have hstep0 :
            (F.map κ ≫ eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF)) ≫
                ψ =
              F.map κ ≫
                (F.map (G.map ψ) ≫ eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦
                    H.obj (F.obj x)) hGF)) := by
          calc
            (F.map κ ≫ eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF)) ≫
                  ψ =
                F.map κ ≫
                  (eqToHom (congrArg
                    (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) ≫
                    ψ) := by
                      simp [Category.assoc]
            _ = F.map κ ≫
                  (F.map (G.map ψ) ≫ eqToHom (congrArg
                    (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦
                      H.obj (F.obj x)) hGF)) := by
                    simpa [Category.assoc] using
                      congrArg (fun t ↦ F.map κ ≫ t) hψnat.symm
        have hstep1 :
            F.map (κ ≫ G.map ψ) ≫ eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj x))
                hGF) =
              F.map (κ ≫ G.map ψ) ≫
                F.map (eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x)
                    hFG)) := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ F.map (κ ≫ G.map ψ) ≫ t) hFGmap.symm
        have hstep2 :
            F.map κ ≫
                (F.map (G.map ψ) ≫ eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦
                    H.obj (F.obj x)) hGF)) =
              F.map (κ ≫ G.map ψ) ≫ eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj x))
                  hGF) := by
          simp [Functor.map_comp, Category.assoc]
        have hstep3 :
            F.map (κ ≫ G.map ψ) ≫
                F.map (eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x)
                    hFG)) =
              F.map (κ ≫ G.map ψ ≫ eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x)
                  hFG)) := by
          simp [Functor.map_comp, Category.assoc]
        have hstep4 :
            F.map (κ ≫ G.map ψ) ≫
                F.map (eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj x)
                    hFG)) =
              F.map τ := by
          have hstep4' : F.map (κ ≫ ξ) = F.map τ := congrArg F.map hκ.2
          simpa [ξ, Functor.map_comp, Category.assoc] using hstep4'
        exact hstep0.trans <| hstep2.trans <| hstep1.trans <| hstep4
      have hκeq : F.map κ ≫ eqToHom (congrArg
          (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) = χ' :=
        hχ'uniq _ ⟨hκY, hκfac⟩
      have hχeq :
          F.map χ ≫ eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) =
            χ' := by
        have hχraw : F.map (G.map χ') =
            eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                hGF) ≫
              χ' ≫
                eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                    hGF).symm := by
          simpa [Functor.comp_map] using Functor.congr_hom hGFfun χ'
        have hFeq :
            F.map (eqToHom (congrArg
              (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                hFG).symm) =
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                  hGF).symm := by
          simp [eqToHom_map]
        dsimp [χ]
        have hstep1 :
            F.map (eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                  hFG).symm ≫
                G.map χ') ≫
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) =
            (F.map (eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                  hFG).symm) ≫
                F.map (G.map χ')) ≫
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                k ≫ eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                    hGF))
              (F.toFunctor.map_comp
                (eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                    hFG).symm)
                (G.map χ'))
        have hstep2 :
            (F.map (eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p ↦ H.obj w)
                  hFG).symm) ≫
                F.map (G.map χ')) ≫
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) =
            (eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                  hGF).symm ≫
                (eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                    hGF) ≫
                  χ' ≫
                    eqToHom (congrArg
                      (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                        hGF).symm)) ≫
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) := by
          have hχraw' :
              (eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                    hGF).symm ≫
                  F.map (G.map χ')) ≫
                eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                    hGF) =
              (eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                    hGF).symm ≫
                  (eqToHom (congrArg
                    (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                      hGF) ≫
                    χ' ≫
                      eqToHom (congrArg
                        (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                          hGF).symm)) ≫
                eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                    hGF) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  (eqToHom (congrArg
                      (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦
                        H.obj (F.obj w)) hGF).symm ≫
                      k) ≫
                    eqToHom (congrArg
                      (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                        hGF))
                hχraw
          rw [hFeq]
          exact hχraw'
        have hstep3 :
            (eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                  hGF).symm ≫
                (eqToHom (congrArg
                  (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj (F.obj w))
                    hGF) ≫
                  χ' ≫
                    eqToHom (congrArg
                      (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                        hGF).symm)) ≫
              eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) =
            χ' := by
          simp [Category.assoc]
        exact hstep1.trans (hstep2.trans hstep3)
      have hκχ :
          F.map κ ≫ eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) =
          F.map χ ≫ eqToHom (congrArg
            (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z) hGF) := by
        rw [hκeq, hχeq]
      have hκmap : F.map κ = F.map χ := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              k ≫ eqToHom (congrArg
                (fun H : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor q ↦ H.obj z)
                  hGF).symm)
            hκχ
      exact F.toFunctor.map_injective hκmap

/-- Helper for Lemma 4.35.17: the target-side `AsSmall` model remains fibred over `Y.obj`. -/
private theorem fixed_base_target_small_isFibered
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) [IsFibredInGroupoids p] :
    (fixed_base_target_small (_W := _W) p).IsFibered := by
  -- Pull fibredness back along the strict `AsSmall.down ⊣ AsSmall.up` equivalence over `Y.obj`.
  exact
    isFibered_of_strict_equivalence_over_target
      (F := fixed_base_target_small_down (_W := _W) p)
      (G := fixed_base_target_small_up (_W := _W) p)
      (fixed_base_target_small_down_up (_W := _W) p)
      (fixed_base_target_small_up_down (_W := _W) p)
      (show p.IsFibered from inferInstance)

/-- Helper for Lemma 4.35.17: the target-side `AsSmall` model is again fibred in groupoids. -/
private theorem fixed_base_target_small_isFibredInGroupoids
    {_W : Type uW}
    {S : Type uS} [Category.{v} S]
    (p : S ⥤ Y.obj) [IsFibredInGroupoids p] :
    IsFibredInGroupoids (fixed_base_target_small (_W := _W) p) := by
  -- After transporting fibredness, each fiber stays a groupoid because `AsSmall.up` is already
  -- an equivalence on every fiber over `Y.obj`.
  refine isFibredInGroupoids_of_isFibered_and_fiber_groupoid
    (fixed_base_target_small (_W := _W) p)
    (fixed_base_target_small_isFibered (_W := _W) p) ?_
  intro U
  letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
    simpa using (inferInstance : IsGroupoid (p.Fiber U))
  exact
    BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase
      (fixed_base_target_small_up (_W := _W) p)
      (fixed_base_target_small_up_isEquivalenceOverBase (_W := _W) p)
      U

/-- Helper for Lemma 4.35.17: in the strict-triangle case, the whiskered comparison morphism is
just the `v`-image of the counit component of the chosen quasi-inverse. -/
private theorem inverse_whisker_target_iso_refl_hom_app
    (e : BasedFunctor.EquivalenceOverBase u) (z : Z.obj) :
    (inverse_whisker_target_iso (F := u ⋙ v) u v e (Iso.refl (u ⋙ v))).hom.app z =
      v.map (e.counitIso.hom.app z) := by
  -- Once the triangle is literally `Iso.refl`, the only nontrivial contribution comes from the
  -- whiskered counit.
  calc
    (inverse_whisker_target_iso (F := u ⋙ v) u v e (Iso.refl (u ⋙ v))).hom.app z =
        (BasedNatIso.mkNatIso
            (Functor.isoWhiskerRight
              ((BasedNatTrans.forgetful Z Z).mapIso e.counitIso) v.toFunctor)
            (BasedCategory.whiskerRight e.counitIso.hom v).isHomLift').hom.app z := by
          have hleft :=
            inverse_whisker_target_iso_triangle_component_app
              (F := u ⋙ v) (u := u) (v := v) e (Iso.refl (u ⋙ v)) z
          simp at hleft
          simpa [inverse_whisker_target_iso, hleft]
    _ = v.map (e.counitIso.hom.app z) :=
      inverse_whisker_target_iso_counit_component_app (u := u) (v := v) e z

/-- Helper for Lemma 4.35.17: for categories fibred in groupoids over the fixed base `Y`, an
equivalence of the underlying categories upgrades to an equivalence over `Y`. -/
private theorem basedFunctor_isEquivalenceOverBase_of_isEquivalence_fixed_base
    {S : Type uS} [Category.{v} S] {T : Type uT} [Category.{v} T]
    {p : S ⥤ Y.obj} {q : T ⥤ Y.obj}
    [IsFibredInGroupoids p] [IsFibredInGroupoids q]
    (c : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (hC : c.toFunctor.IsEquivalence) :
    c.IsEquivalenceOverBase := by
  -- Route correction: instead of forcing a heterogeneous owner bridge, shrink both fixed-base
  -- targets into one common `AsSmall` universe and transport the resulting equivalence back.
  let W := ULift.{max (max uS uT) (max uY v), 0} PUnit
  let cSmall :
      BasedCategory.ofFunctor (fixed_base_target_small (Y := Y) (_W := W) p) ⥤ᵇ
        BasedCategory.ofFunctor (fixed_base_target_small (Y := Y) (_W := W) q) :=
    fixed_base_target_small_down (Y := Y) (_W := W) p ⋙ c ⋙
      fixed_base_target_small_up (Y := Y) (_W := W) q
  letI : IsFibredInGroupoids (fixed_base_target_small (Y := Y) (_W := W) p) :=
    fixed_base_target_small_isFibredInGroupoids (Y := Y) (_W := W) p
  letI : IsFibredInGroupoids (fixed_base_target_small (Y := Y) (_W := W) q) :=
    fixed_base_target_small_isFibredInGroupoids (Y := Y) (_W := W) q
  have hDown :
      (fixed_base_target_small_down (Y := Y) (_W := W) p).toFunctor.IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase
      (fixed_base_target_small_down (Y := Y) (_W := W) p)
      (fixed_base_target_small_down_isEquivalenceOverBase (Y := Y) (_W := W) p)
  have hUp :
      (fixed_base_target_small_up (Y := Y) (_W := W) q).toFunctor.IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase
      (fixed_base_target_small_up (Y := Y) (_W := W) q)
      (fixed_base_target_small_up_isEquivalenceOverBase (Y := Y) (_W := W) q)
  letI : (fixed_base_target_small_down (Y := Y) (_W := W) p).toFunctor.IsEquivalence := hDown
  letI : c.toFunctor.IsEquivalence := hC
  letI : (fixed_base_target_small_up (Y := Y) (_W := W) q).toFunctor.IsEquivalence := hUp
  have hSmall :
      cSmall.toFunctor.IsEquivalence := by
    -- The smallified comparison is a composite of ordinary equivalences.
    dsimp [cSmall]
    infer_instance
  have hSmallOver :
      cSmall.IsEquivalenceOverBase :=
    basedFunctor_isEquivalenceOverBase_of_isEquivalence_fixed_base_same_universe
      (Y := Y) cSmall hSmall
  have hLeft :
      ((fixed_base_target_small_up (Y := Y) (_W := W) p) ⋙ cSmall).IsEquivalenceOverBase :=
    BasedFunctor.IsEquivalenceOverBase.comp
      (fixed_base_target_small_up_isEquivalenceOverBase (Y := Y) (_W := W) p)
      hSmallOver
  have hRecovered :
      (((fixed_base_target_small_up (Y := Y) (_W := W) p) ⋙ cSmall) ⋙
        (fixed_base_target_small_down (Y := Y) (_W := W) q)).IsEquivalenceOverBase :=
    BasedFunctor.IsEquivalenceOverBase.comp
      hLeft
      (fixed_base_target_small_down_isEquivalenceOverBase (Y := Y) (_W := W) q)
  -- The strict `up/down` identities reduce the transported comparison back to the original `c`.
  simpa [W, cSmall, BasedFunctor.comp_assoc, fixed_base_target_small_up_down,
    BasedFunctor.comp_id] using hRecovered

/-- Helper for Lemma 4.35.17: a `2`-commutative triangle with left side an equivalence over `C`
identifies the target category over `Y` with the canonical factorization of `F` over `Y`. -/
private theorem triangle_equivalence_to_canonical_factorization
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
    [IsFibredInGroupoids v.toFunctor]
    (hu_equiv : u.IsEquivalenceOverBase)
    (hcomm : Nonempty (u ⋙ v ≅ F)) :
    ∃ c : BasedCategory.ofFunctor v.toFunctor ⥤ᵇ
        BasedCategory.ofFunctor (fibredInGroupoidsFactorizationToTarget F).toFunctor,
      c.IsEquivalenceOverBase ∧
        Nonempty
          (fibredInGroupoidsFactorizationFromSource F ≅
            BasedFunctor.comp u (BasedFunctor.forgetTarget c)) := by
  classical
  letI : IsFibredInGroupoids (fibredInGroupoidsFactorizationToTarget F).toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids F
  let e : BasedFunctor.EquivalenceOverBase u := Classical.choice hu_equiv.nonempty
  let σ : u ⋙ v ≅ F := Classical.choice hcomm
  let c :
      BasedCategory.ofFunctor v.toFunctor ⥤ᵇ
        BasedCategory.ofFunctor (fibredInGroupoidsFactorizationToTarget F).toFunctor :=
    triangle_comparison_to_canonical_factorization (F := F) u v e σ
  refine ⟨c, ?_, ?_⟩
  · -- Route correction: repackage the comparison into the fixed-base fibred-groupoid owner over
    -- `Y`, then invoke Lemma `4.35.9` there instead of rebundling through the ambient owner.
    have hC :
        c.toFunctor.IsEquivalence :=
      triangle_comparison_to_canonical_factorization_isEquivalence
        (F := F) u v e σ
    exact
      basedFunctor_isEquivalenceOverBase_of_isEquivalence_fixed_base
        (Y := Y) c hC
  · -- Reuse the explicit comparison isomorphism assembled from the unit of `u` and the whiskered
    -- triangle comparison.
    exact ⟨triangle_comparison_from_source_iso (F := F) u v e σ⟩

/-- Helper for Lemma 4.35.17: when the triangle `u ⋙ v = F` commutes strictly, the explicit
source-comparison isomorphism already lives in `Cat/Y`. -/
private theorem adjointified_unit_hom_isHomLift
    (e : BasedFunctor.EquivalenceOverBase u) (x : X.obj) :
    X.p.IsHomLift (𝟙 (X.p.obj x))
      ((CategoryTheory.Equivalence.adjointifyη
          ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
          ((BasedNatTrans.forgetful Z Z).mapIso e.counitIso)).hom.app x) := by
  let ηAdj :=
    (CategoryTheory.Equivalence.adjointifyη
      ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
      ((BasedNatTrans.forgetful Z Z).mapIso e.counitIso)).hom.app x
  have hTriangle :
      u.map ηAdj ≫ e.counitIso.hom.app (u.obj x) = 𝟙 (u.obj x) := by
    -- The adjointified ordinary unit satisfies the forward triangle identity.
    simpa [ηAdj] using
      (CategoryTheory.Equivalence.adjointify_η_ε
        ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
        ((BasedNatTrans.forgetful Z Z).mapIso e.counitIso) x)
  have hEq : u.map ηAdj = e.counitIso.inv.app (u.obj x) := by
    -- Cancel the counit on the right to identify the forward image of the adjointified unit.
    have h₁ :
        u.map ηAdj = u.map ηAdj ≫ 𝟙 (u.obj (e.inverse.obj (u.obj x))) := by
      simp
    have h₂ :
        u.map ηAdj ≫ 𝟙 (u.obj (e.inverse.obj (u.obj x))) =
          u.map ηAdj ≫ (e.counitIso.hom.app (u.obj x) ≫ e.counitIso.inv.app (u.obj x)) := by
      simpa [Category.assoc] using congrArg (fun k ↦ u.map ηAdj ≫ k)
        (((BasedNatTrans.forgetful Z Z).mapIso e.counitIso).hom_inv_id_app (u.obj x)).symm
    have h₃ :
        u.map ηAdj ≫ (e.counitIso.hom.app (u.obj x) ≫ e.counitIso.inv.app (u.obj x)) =
          e.counitIso.inv.app (u.obj x) := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ e.counitIso.inv.app (u.obj x)) hTriangle
    exact h₁.trans (h₂.trans h₃)
  have hCounitInv :
      Z.p.IsHomLift (𝟙 (Z.p.obj (u.obj x))) (e.counitIso.inv.app (u.obj x)) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.inv
      (rfl : Z.p.obj (u.obj x) = Z.p.obj (u.obj x))
  have hMap : Z.p.IsHomLift (𝟙 (Z.p.obj (u.obj x))) (u.map ηAdj) := by
    rw [hEq]
    exact hCounitInv
  have hX : X.p.IsHomLift (𝟙 (Z.p.obj (u.obj x))) ηAdj := by
    exact (u.isHomLift_iff (𝟙 (Z.p.obj (u.obj x))) ηAdj).1 hMap
  rw [← u.w_obj x]
  simpa [ηAdj] using hX

/-- Helper for Lemma 4.35.17: replace the unit of an equivalence-over-base datum by its
adjointified ordinary unit while keeping the same inverse and counit. -/
private noncomputable def adjointified_equivalence_over_base
    (e : BasedFunctor.EquivalenceOverBase u) :
    BasedFunctor.EquivalenceOverBase u :=
  { inverse := e.inverse
    unitIso :=
      BasedNatIso.mkNatIso
        (CategoryTheory.Equivalence.adjointifyη
          ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
          ((BasedNatTrans.forgetful Z Z).mapIso e.counitIso))
        (adjointified_unit_hom_isHomLift (u := u) e)
    counitIso := e.counitIso }

/-- Helper for Lemma 4.35.17: for the adjointified unit, the strict-triangle target component is
the identity after mapping the ordinary adjointified triangle through `v`. -/
private theorem inverse_whisker_target_iso_identity_of_refl_triangle_of_adjointified_equivalence
    (e : BasedFunctor.EquivalenceOverBase u) (x : X.obj) :
    let eAdj := adjointified_equivalence_over_base (u := u) e
    v.map (u.map (eAdj.unitIso.hom.app x)) ≫
      (inverse_whisker_target_iso (F := u ⋙ v) u v eAdj (Iso.refl (u ⋙ v))).hom.app (u.obj x) =
        𝟙 (v.obj (u.obj x)) :=
  by
  let eAdj := adjointified_equivalence_over_base (u := u) e
  have hTriangle :
      u.map (eAdj.unitIso.hom.app x) ≫ eAdj.counitIso.hom.app (u.obj x) =
        𝟙 (u.obj x) := by
    -- The adjointified ordinary unit satisfies the forward triangle identity.
    simpa [eAdj, adjointified_equivalence_over_base] using
      (CategoryTheory.Equivalence.adjointify_η_ε
        ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
        ((BasedNatTrans.forgetful Z Z).mapIso e.counitIso) x)
  -- Rewrite the whiskered comparison component to the mapped counit, then map the ordinary
  -- triangle identity through `v`.
  dsimp [eAdj]
  rw [inverse_whisker_target_iso_refl_hom_app (u := u) (v := v) eAdj]
  have hTriangle' :
      u.map ((adjointified_equivalence_over_base (u := u) e).unitIso.hom.app x) ≫
        eAdj.counitIso.hom.app (u.obj x) =
          𝟙 (u.obj x) := by
    simpa [eAdj] using hTriangle
  simpa [Functor.map_comp] using congrArg v.map hTriangle'

/-- Helper for Lemma 4.35.17: after rewriting the strict triangle to `F = u ⋙ v`, the source
comparison component is vertical over the identity in `Cat/Y`. -/
private theorem triangle_comparison_from_source_component_over_target_id_of_strict_comm
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
    [IsFibredInGroupoids v.toFunctor]
    (e : BasedFunctor.EquivalenceOverBase u)
    (hu_strict : u ⋙ v = F) (x : X.obj) :
    ((fibredInGroupoidsFactorizationToTarget F).toFunctor).IsHomLift
      (𝟙 (F.obj x))
      (((BasedNatTrans.forgetful _ _).mapIso
          (triangle_comparison_from_source_iso
            (F := F) u v (adjointified_equivalence_over_base (u := u) e)
            (eqToIso hu_strict))).hom.app x) := by
  -- Route correction: rewrite to the literally strict triangle `F = u ⋙ v`, then the target
  -- projection of the comparison component is exactly the whiskered counit term.
  subst hu_strict
  let eAdj := adjointified_equivalence_over_base (u := u) e
  change
    ((fibredInGroupoidsFactorizationToTarget (u ⋙ v)).toFunctor).IsHomLift
      (𝟙 (v.obj (u.obj x)))
      ((triangle_comparison_component_iso
          (F := u ⋙ v) u v eAdj (Iso.refl (u ⋙ v)) x).hom)
  have hb :
      ((fibredInGroupoidsFactorizationToTarget (u ⋙ v)).toFunctor.map
          ((triangle_comparison_component_iso
              (F := u ⋙ v) u v eAdj (Iso.refl (u ⋙ v)) x).hom)) =
        𝟙 (v.obj (u.obj x)) := by
    change
      (u ⋙ v).map (eAdj.unitIso.hom.app x) ≫
          (inverse_whisker_target_iso
            (F := u ⋙ v) u v eAdj (Iso.refl (u ⋙ v))).hom.app (u.obj x) =
        𝟙 (v.obj (u.obj x))
    simpa [eAdj] using
      inverse_whisker_target_iso_identity_of_refl_triangle_of_adjointified_equivalence
        (u := u) (v := v) e x
  exact
    IsHomLift.of_fac'
      ((fibredInGroupoidsFactorizationToTarget (u ⋙ v)).toFunctor)
      (𝟙 (v.obj (u.obj x)))
      ((triangle_comparison_component_iso
          (F := u ⋙ v) u v eAdj (Iso.refl (u ⋙ v)) x).hom)
      rfl
      rfl
      (by simpa using hb)

/-- Helper for Lemma 4.35.17: when the triangle `u ⋙ v = F` commutes strictly, the explicit
source-comparison isomorphism already lives in `Cat/Y`. -/
private noncomputable def triangle_comparison_from_source_iso_over_target_of_strict_comm
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
    [IsFibredInGroupoids v.toFunctor]
    (e : BasedFunctor.EquivalenceOverBase u)
    (hu_strict : u ⋙ v = F) :
    BasedFunctor.overTargetOfCompEq
        (F := F)
        (f := fibredInGroupoidsFactorizationToTarget F)
        (fibredInGroupoidsFactorizationFromSource F)
        (fibredInGroupoidsFactorization_comp F) ≅
      BasedFunctor.comp
        (BasedFunctor.overTargetOfCompEq (F := F) (f := v) u hu_strict)
        (triangle_comparison_to_canonical_factorization (F := F) u v e (eqToIso hu_strict)) :=
  by
  let eAdj := adjointified_equivalence_over_base (u := u) e
  -- The underlying ordinary natural isomorphism is the source comparison already constructed in
  -- `Cat/C`; only the vertical-over-`Y` condition needs to be added componentwise.
  refine BasedNatIso.mkNatIso ?_ ?_
  · simpa [BasedFunctor.overTargetOfCompEq, eAdj] using
      ((BasedNatTrans.forgetful _ _).mapIso
        (triangle_comparison_from_source_iso
          (F := F) u v eAdj (eqToIso hu_strict)))
  · intro x
    exact
      triangle_comparison_from_source_component_over_target_id_of_strict_comm
        (F := F) (u := u) (v := v) e hu_strict x

end TriangleComparison

section

variable (F : X ⥤ᵇ Y)
variable (a : X ⥤ᵇ X') (f : X' ⥤ᵇ Y)
variable (b : X ⥤ᵇ X'') (g : X'' ⥤ᵇ Y)

variable [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
variable [IsFibredInGroupoids f.toFunctor] [IsFibredInGroupoids g.toFunctor]

omit [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
    [IsFibredInGroupoids f.toFunctor] [IsFibredInGroupoids g.toFunctor] in
/-- Helper for Lemma 4.35.17: forgetting the target from a strict factorization over `Y`
recovers the original comparison functor over `C`. -/
private theorem forgetTarget_overTargetOfCompEq
    {a : X ⥤ᵇ X'} {f : X' ⥤ᵇ Y} {F : X ⥤ᵇ Y}
    (ha : a ⋙ f = F) :
    BasedFunctor.forgetTarget (BasedFunctor.overTargetOfCompEq (F := F) (f := f) a ha) = a := by
  -- Both constructions keep the same underlying functor, so the result is definitional.
  rfl

/-- Helper for Lemma 4.35.17: the unit component of an equivalence over a fixed base is vertical
over that base. -/
private theorem unitIso_hom_isHomLift
    {B₁ : BasedCategory Y.obj} {B₂ : BasedCategory Y.obj}
    {H : B₁ ⥤ᵇ B₂}
    (e : BasedFunctor.EquivalenceOverBase H) (x : B₁.obj) :
    B₁.p.IsHomLift (𝟙 (B₁.p.obj x)) (e.unitIso.hom.app x) := by
  -- This is exactly the componentwise lifting statement stored in the based unit isomorphism.
  simpa using BasedNatTrans.isHomLift e.unitIso.hom (rfl : B₁.p.obj x = B₁.p.obj x)

/-- Helper for Lemma 4.35.17: the unit component of an equivalence in `Cat/Y` becomes the identity
after applying the target functor and the comparison to the source. -/
private theorem unit_component_target_eq_id
    {Z : BasedCategory C} {z : Z ⥤ᵇ Y}
    {c : BasedCategory.ofFunctor f.toFunctor ⥤ᵇ BasedCategory.ofFunctor z.toFunctor}
    (e : BasedFunctor.EquivalenceOverBase c) (x : X'.obj) :
    f.map (e.unitIso.hom.app x) ≫ eqToHom ((c ⋙ e.inverse).w_obj x) = 𝟙 (f.obj x) := by
  simpa [Functor.whiskerRight, Category.assoc] using
    NatTrans.congr_app (BasedNatTrans.over_id e.unitIso.hom) x

/-- Helper for Lemma 4.35.17: applying the base functor to the identity on `f.obj x` gives the
identity on the corresponding object of `C`. -/
private theorem target_map_id (x : X'.obj) :
    Y.p.map (𝟙 (f.obj x)) = 𝟙 (Y.p.obj (f.obj x)) := by
  simp

/-- Helper for Lemma 4.35.17: after applying `Y.p`, the forgotten unit component satisfies the
target-level over-identity equation in `C`. -/
private theorem forgetTarget_unit_component_mapped_eq_id
    {Z : BasedCategory C} {z : Z ⥤ᵇ Y}
    {c : BasedCategory.ofFunctor f.toFunctor ⥤ᵇ BasedCategory.ofFunctor z.toFunctor}
    (e : BasedFunctor.EquivalenceOverBase c) (x : X'.obj) :
    Y.p.map (f.map (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.app x)) ≫
      Y.p.map (eqToHom ((c ⋙ e.inverse).w_obj x)) =
        𝟙 (Y.p.obj (f.obj x)) := by
  -- Apply the base functor to the vertical unit equation, then normalize the image of the
  -- composite with functoriality.
  have hraw :
      Y.p.map
          (f.map (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.app x) ≫
            eqToHom ((c ⋙ e.inverse).w_obj x)) =
        Y.p.map (𝟙 (f.obj x)) := by
    exact congrArg Y.p.map (unit_component_target_eq_id (f := f) (z := z) e x)
  have hcomp :
      Y.p.map (f.map (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.app x)) ≫
          Y.p.map (eqToHom ((c ⋙ e.inverse).w_obj x)) =
        Y.p.map (𝟙 (f.obj x)) := by
    simpa [Functor.map_comp, Category.assoc] using hraw
  exact hcomp.trans (target_map_id (f := f) x)

/-- Helper for Lemma 4.35.17: whiskering a based natural isomorphism on the right preserves the
based over-base compatibility. -/
private noncomputable def whisker_right_iso
    {A B D : BasedCategory C} {F G : A ⥤ᵇ B}
    (α : F ≅ G) (H : B ⥤ᵇ D) :
    BasedFunctor.comp F H ≅ BasedFunctor.comp G H := by
  -- Forget to ordinary functors for the whiskered natural isomorphism, then repackage the same
  -- components as a based natural isomorphism.
  refine BasedNatIso.mkNatIso
    (Functor.isoWhiskerRight ((BasedNatTrans.forgetful _ _).mapIso α) H.toFunctor)
    (BasedCategory.whiskerRight α.hom H).isHomLift'

/-- Helper for Lemma 4.35.17: whiskering a based natural isomorphism on the left preserves the
based over-base compatibility. -/
private noncomputable def whisker_left_iso
    {A B D : BasedCategory C} (H : A ⥤ᵇ B) {F G : B ⥤ᵇ D}
    (α : F ≅ G) :
    BasedFunctor.comp H F ≅ BasedFunctor.comp H G := by
  -- The left whisker is handled in the same way, using the owner-level left whiskering helper.
  refine BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft H.toFunctor ((BasedNatTrans.forgetful _ _).mapIso α))
    (BasedCategory.whiskerLeft H α.hom).isHomLift'

/-- Helper for Lemma 4.35.17: forgetting the unit isomorphism of an equivalence in `Cat/Y`
produces the corresponding unit isomorphism in `Cat/C`. -/
private noncomputable def forgetTarget_unitIso
    {Z : BasedCategory C} {z : Z ⥤ᵇ Y}
    {c : BasedCategory.ofFunctor f.toFunctor ⥤ᵇ BasedCategory.ofFunctor z.toFunctor}
    (e : BasedFunctor.EquivalenceOverBase c) :
    𝟭 X' ≅
      BasedFunctor.comp (BasedFunctor.forgetTarget c) (BasedFunctor.forgetTarget e.inverse) := by
  -- Forget the unit in `Cat/Y`, then transport its components back to lifts over `X'.p`.
  refine BasedNatIso.mkNatIso ((BasedNatTrans.forgetful _ _).mapIso e.unitIso) ?_
  intro x
  -- First show that the mapped component is vertical for `Y.p`, then pull that lift back along
  -- the structure functor `f : X' ⥤ᵇ Y`.
  refine
    (f.isHomLift_iff (𝟙 (X'.p.obj x))
      (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.app x)).1 ?_
  refine
    IsHomLift.of_commsq Y.p
      (𝟙 (X'.p.obj x))
      (f.map (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.app x))
      (f.w_obj x)
      ((congrArg (Functor.obj Y.p) ((c ⋙ e.inverse).w_obj x)).trans (f.w_obj x)) ?_
  -- The target-side over-identity equation from the fixed-base unit gives the needed commutative
  -- square after composing with the base-change isomorphism coming from `f.w`.
  calc
    Y.p.map (f.map (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.app x)) ≫
        eqToHom ((congrArg (Functor.obj Y.p) ((c ⋙ e.inverse).w_obj x)).trans (f.w_obj x)) =
      (Y.p.map (f.map (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.app x)) ≫
          Y.p.map (eqToHom ((c ⋙ e.inverse).w_obj x))) ≫
        eqToHom (f.w_obj x) := by
          simp [eqToHom_map, Category.assoc]
    _ = 𝟙 (Y.p.obj (f.obj x)) ≫ eqToHom (f.w_obj x) := by
          exact congrArg (fun k ↦ k ≫ eqToHom (f.w_obj x))
            (forgetTarget_unit_component_mapped_eq_id (f := f) (z := z) e x)
    _ = eqToHom (f.w_obj x) ≫ 𝟙 (X'.p.obj x) := by
          simp

-- Proof sketch: both `X'` and `X''` are equivalent over `Y` to the explicit `2`-fibre-product
-- factorization of `F` from Lemma `4.35.16`; compose one equivalence with a quasi-inverse to the
-- other and compare the resulting composite with `a` using the given `2`-commutative triangles.
/-- Lemma 4.35.17: if `F : X ⥤ᵇ Y` admits two factorizations through categories fibred in
groupoids over `Y`, and the comparison functors `a : X ⥤ᵇ X'` and `b : X ⥤ᵇ X''` are equivalences
over `C`, then there is an equivalence of categories over `Y` from `g` to `f` whose underlying
functor over `C` makes `b ⋙ h` `2`-isomorphic to `a`. -/
theorem exists_equivalence_over_target_between_fibred_groupoid_factorizations
    (ha_equiv : a.IsEquivalenceOverBase)
    (hb_equiv : b.IsEquivalenceOverBase)
    (ha_comm : Nonempty (a ⋙ f ≅ F))
    (hb_comm : Nonempty (b ⋙ g ≅ F)) :
    ∃ h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor,
      h.IsEquivalenceOverBase ∧
        Nonempty (BasedFunctor.comp b (forgetTarget h) ≅ a) := by
  classical
  letI : IsFibredInGroupoids (fibredInGroupoidsFactorizationToTarget F).toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids F
  obtain ⟨cA, hcA, ⟨isoA⟩⟩ :=
    triangle_equivalence_to_canonical_factorization
      (F := F) (u := a) (v := f) ha_equiv ha_comm
  obtain ⟨cB, hcB, ⟨isoB⟩⟩ :=
    triangle_equivalence_to_canonical_factorization
      (F := F) (u := b) (v := g) hb_equiv hb_comm
  let eA : BasedFunctor.EquivalenceOverBase cA := Classical.choice hcA.nonempty
  let h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor :=
    BasedFunctor.comp cB eA.inverse
  refine ⟨h, ?_, ?_⟩
  · -- Compose the `X''`-comparison with a chosen inverse to the `X'`-comparison.
    exact BasedFunctor.IsEquivalenceOverBase.comp hcB eA.inverse_isEquivalenceOverBase
  · refine ⟨?_⟩
    have hUnit :
        𝟭 X' ≅
          BasedFunctor.comp (BasedFunctor.forgetTarget cA)
            (BasedFunctor.forgetTarget eA.inverse) :=
      forgetTarget_unitIso (f := f) eA
    have hCancel :
        BasedFunctor.comp (BasedFunctor.comp a (BasedFunctor.forgetTarget cA))
          (BasedFunctor.forgetTarget eA.inverse) ≅ a := by
      -- Cancel the `a`-comparison by whiskering the forgotten unit isomorphism of `eA`.
      refine
        (eqToIso
          (BasedFunctor.comp_assoc a (BasedFunctor.forgetTarget cA)
            (BasedFunctor.forgetTarget eA.inverse))).symm ≪≫
          whisker_left_iso a hUnit.symm ≪≫
          eqToIso (BasedFunctor.comp_id a)
    -- Compare `b ⋙ h` to the canonical factorization, then cancel the `a`-comparison by its unit.
    refine
      (eqToIso
        (BasedFunctor.comp_assoc b (BasedFunctor.forgetTarget cB)
          (BasedFunctor.forgetTarget eA.inverse))).symm ≪≫
      whisker_right_iso isoB.symm (BasedFunctor.forgetTarget eA.inverse) ≪≫
      whisker_right_iso isoA (BasedFunctor.forgetTarget eA.inverse) ≪≫
      hCancel

-- Proof sketch: in the strict case the same construction as in the main theorem gives `h`. Since
-- both triangles commute on the nose, the comparison isomorphism between `b ⋙ h` and `a` is
-- vertical already over `Y`, not just after projecting further to `C`.
/-- Under strict commutativity of the two triangles, the comparison `2`-isomorphism `b ⋙ h ≅ a`
can be chosen in `Cat/Y`. -/
theorem exists_equivalence_over_target_between_fibred_groupoid_factorizations_of_strict_comm
    (ha_equiv : a.IsEquivalenceOverBase)
    (hb_equiv : b.IsEquivalenceOverBase)
    (ha_strict : a ⋙ f = F)
    (hb_strict : b ⋙ g = F) :
    ∃ h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor,
      h.IsEquivalenceOverBase ∧
        Nonempty (BasedFunctor.comp b (forgetTarget h) ≅ a) ∧
          Nonempty
            (BasedFunctor.comp (overTargetOfCompEq b hb_strict) h ≅
              overTargetOfCompEq a ha_strict) := by
  classical
  letI : IsFibredInGroupoids (fibredInGroupoidsFactorizationToTarget F).toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids F
  let eA0 : BasedFunctor.EquivalenceOverBase a := Classical.choice ha_equiv.nonempty
  let eB0 : BasedFunctor.EquivalenceOverBase b := Classical.choice hb_equiv.nonempty
  let cA :
      BasedCategory.ofFunctor f.toFunctor ⥤ᵇ
        BasedCategory.ofFunctor (fibredInGroupoidsFactorizationToTarget F).toFunctor :=
    triangle_comparison_to_canonical_factorization (F := F) a f eA0 (eqToIso ha_strict)
  let cB :
      BasedCategory.ofFunctor g.toFunctor ⥤ᵇ
        BasedCategory.ofFunctor (fibredInGroupoidsFactorizationToTarget F).toFunctor :=
    triangle_comparison_to_canonical_factorization (F := F) b g eB0 (eqToIso hb_strict)
  have hcA : cA.IsEquivalenceOverBase := by
    -- Upgrade the explicit comparison functor to an equivalence over `Y`.
    have hC : cA.toFunctor.IsEquivalence :=
      triangle_comparison_to_canonical_factorization_isEquivalence
        (F := F) a f eA0 (eqToIso ha_strict)
    exact basedFunctor_isEquivalenceOverBase_of_isEquivalence_fixed_base (Y := Y) cA hC
  have hcB : cB.IsEquivalenceOverBase := by
    -- The same fixed-base upgrade applies to the right comparison triangle.
    have hC : cB.toFunctor.IsEquivalence :=
      triangle_comparison_to_canonical_factorization_isEquivalence
        (F := F) b g eB0 (eqToIso hb_strict)
    exact basedFunctor_isEquivalenceOverBase_of_isEquivalence_fixed_base (Y := Y) cB hC
  let eA : BasedFunctor.EquivalenceOverBase cA := Classical.choice hcA.nonempty
  let h : BasedCategory.ofFunctor g.toFunctor ⥤ᵇ BasedCategory.ofFunctor f.toFunctor :=
    BasedFunctor.comp cB eA.inverse
  have hSourceA :
      BasedFunctor.overTargetOfCompEq
          (F := F)
          (f := fibredInGroupoidsFactorizationToTarget F)
          (fibredInGroupoidsFactorizationFromSource F)
          (fibredInGroupoidsFactorization_comp F) ≅
        BasedFunctor.comp
          (BasedFunctor.overTargetOfCompEq (F := F) (f := f) a ha_strict)
          cA :=
    triangle_comparison_from_source_iso_over_target_of_strict_comm
      (F := F) (u := a) (v := f) eA0 ha_strict
  have hSourceB :
      BasedFunctor.overTargetOfCompEq
          (F := F)
          (f := fibredInGroupoidsFactorizationToTarget F)
          (fibredInGroupoidsFactorizationFromSource F)
          (fibredInGroupoidsFactorization_comp F) ≅
        BasedFunctor.comp
          (BasedFunctor.overTargetOfCompEq (F := F) (f := g) b hb_strict)
          cB :=
    triangle_comparison_from_source_iso_over_target_of_strict_comm
      (F := F) (u := b) (v := g) eB0 hb_strict
  have hCancelY :
      BasedFunctor.comp
          (BasedFunctor.comp (BasedFunctor.overTargetOfCompEq (F := F) (f := f) a ha_strict) cA)
          eA.inverse ≅
        BasedFunctor.overTargetOfCompEq (F := F) (f := f) a ha_strict := by
    -- Cancel the `a`-comparison inside `Cat/Y` using the unit of the chosen inverse to `cA`.
    refine
      (eqToIso
        (BasedFunctor.comp_assoc
          (BasedFunctor.overTargetOfCompEq (F := F) (f := f) a ha_strict)
          cA eA.inverse)).symm ≪≫
        whisker_left_iso
          (BasedFunctor.overTargetOfCompEq (F := F) (f := f) a ha_strict)
          eA.unitIso.symm ≪≫
        eqToIso
          (BasedFunctor.comp_id
            (BasedFunctor.overTargetOfCompEq (F := F) (f := f) a ha_strict))
  have hcompY :
      BasedFunctor.comp (BasedFunctor.overTargetOfCompEq (F := F) (f := g) b hb_strict) h ≅
        BasedFunctor.overTargetOfCompEq (F := F) (f := f) a ha_strict := by
    -- Compare both strict factorizations with the common canonical factorization over `Y`, then
    -- cancel the `a`-comparison by the unit of `eA`.
    refine
      (eqToIso
        (BasedFunctor.comp_assoc
          (BasedFunctor.overTargetOfCompEq (F := F) (f := g) b hb_strict)
          cB eA.inverse)).symm ≪≫
        whisker_right_iso hSourceB.symm eA.inverse ≪≫
        whisker_right_iso hSourceA eA.inverse ≪≫
        hCancelY
  have hcompC : Nonempty (BasedFunctor.comp b (forgetTarget h) ≅ a) := by
    -- Rebuild the forgotten comparison exactly as in the non-strict theorem, using the same
    -- canonical-factorization comparisons and the forgotten unit of `eA`.
    refine ⟨?_⟩
    have hIso :
        BasedFunctor.comp b (forgetTarget h) ≅ a := by
      have hIsoA :
          fibredInGroupoidsFactorizationFromSource F ≅
            BasedFunctor.comp a (BasedFunctor.forgetTarget cA) :=
        triangle_comparison_from_source_iso (F := F) a f eA0 (eqToIso ha_strict)
      have hIsoB :
          fibredInGroupoidsFactorizationFromSource F ≅
            BasedFunctor.comp b (BasedFunctor.forgetTarget cB) :=
        triangle_comparison_from_source_iso (F := F) b g eB0 (eqToIso hb_strict)
      have hUnit :
          𝟭 X' ≅
            BasedFunctor.comp (BasedFunctor.forgetTarget cA)
              (BasedFunctor.forgetTarget eA.inverse) :=
        forgetTarget_unitIso (f := f) eA
      have hCancel :
          BasedFunctor.comp (BasedFunctor.comp a (BasedFunctor.forgetTarget cA))
            (BasedFunctor.forgetTarget eA.inverse) ≅ a := by
        -- Cancel the `a`-comparison after forgetting from `Cat/Y` to `Cat/C`.
        refine
          (eqToIso
            (BasedFunctor.comp_assoc a (BasedFunctor.forgetTarget cA)
              (BasedFunctor.forgetTarget eA.inverse))).symm ≪≫
            whisker_left_iso a hUnit.symm ≪≫
            eqToIso (BasedFunctor.comp_id a)
      -- Compare `b ⋙ h` to the common canonical factorization and then cancel the `a`-side.
      refine
        (eqToIso
          (BasedFunctor.comp_assoc b (BasedFunctor.forgetTarget cB)
            (BasedFunctor.forgetTarget eA.inverse))).symm ≪≫
          whisker_right_iso hIsoB.symm (BasedFunctor.forgetTarget eA.inverse) ≪≫
          whisker_right_iso hIsoA (BasedFunctor.forgetTarget eA.inverse) ≪≫
          hCancel
    exact hIso
  refine ⟨h, ?_, hcompC, ⟨hcompY⟩⟩
  -- The explicit comparison equivalences compose exactly as in the non-strict theorem.
  exact BasedFunctor.IsEquivalenceOverBase.comp hcB eA.inverse_isEquivalenceOverBase

end

end CategoryTheory
