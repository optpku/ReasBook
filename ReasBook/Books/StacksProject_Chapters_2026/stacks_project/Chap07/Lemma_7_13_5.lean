module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_13_4
public import stacks_project.Chap07.Lemma_7_12_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Presheaf

universe u₁ u₂ v₁ v₂

/-
Domain-style sampling:
- primary domain: pullback of sheaves along a continuous functor of sites and its action on
  sheafified representables;
- sampled owner API:
  `Functor.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafPullbackIso`,
  `GrothendieckTopology.uliftSheafifiedRepresentable`,
  `Presheaf.compULiftYonedaIsoULiftYonedaCompLan`;
- source-facing layer: the Stacks comparison `h_{u(U)}^# ⟶ u_sh(h_U^#)`;
- core/canonical owners: `K.uliftSheafifiedRepresentable (u.obj U)` and
  `(u.sheafPullback (Type ...) J K).obj (J.uliftSheafifiedRepresentable U)`;
- bridge/view: the proof passes through the explicit Kan-extension model
  `Functor.sheafPullbackConstruction.sheafPullback`, and only at the end moves to the chosen
  owner `u.sheafPullback` via `sheafPullbackIso`.

Primitive data are the continuous functor `u`, the sheafified representable owner
`uliftSheafifiedRepresentable`, and the Kan-extension comparison
`compULiftYonedaIsoULiftYonedaCompLan`. The public isomorphism is derived from that canonical data,
so the file should expose the owner-level comparison directly rather than storing a parallel raw
comparison morphism as a separate local API.
-/

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
variable [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
variable [Functor.IsContinuous u J K]
variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), u.op.HasLeftKanExtension P]

/-- Lemma 7.13.5: for a continuous functor of sites, the sheaf pullback of the sheafified
representable `h_U^#` is canonically isomorphic to the sheafified representable `h_{u(U)}^#`. -/
noncomputable def continuous_sheafified_representable_iso (U : C) :
    uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K (u.obj U) ≅
      (u.sheafPullback (Type (max u₁ u₂ v₁ v₂)) J K).obj
        (uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) :=
  let A := Type (max u₁ u₂ v₁ v₂)
  let P : Cᵒᵖ ⥤ A := uliftYoneda.{max (max u₁ u₂ v₁ v₂) v₂, v₁, u₁}.obj U
  let e₁ :
      uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K (u.obj U) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj P) :=
    Functor.mapIso (presheafToSheaf K A)
      ((compULiftYonedaIsoULiftYonedaCompLan.{max u₁ u₂ v₁ v₂} u).app U)
  let _ : IsIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify P))) :=
    continuous_pullback_sheafification_comparison_isIso u J K P
  let e₂Presheaf :
      (sheafToPresheaf K A).obj ((presheafToSheaf K A).obj ((u.op.lan).obj P)) ≅
        (sheafToPresheaf K A).obj
          ((presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P))) :=
    (plusPlusIsoSheafify K A ((u.op.lan).obj P)).symm ≪≫
      asIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify P))) ≪≫
        plusPlusIsoSheafify K A ((u.op.lan).obj (J.sheafify P))
  let e₂ :
      (presheafToSheaf K A).obj ((u.op.lan).obj P) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P)) :=
    (fullyFaithfulSheafToPresheaf K A).preimageIso e₂Presheaf
  let e₃ :
      (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P)) ≅
        (sheafPullback u A J K).obj
          (uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) :=
    Functor.mapIso (presheafToSheaf K A)
      (Functor.mapIso (u.op.lan) (plusPlusIsoSheafify J A P))
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫
    (sheafPullbackIso u (Type (max u₁ u₂ v₁ v₂)) J K).symm.app
      (uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U)

/-- The morphism underlying `continuous_sheafified_representable_iso` is an isomorphism. -/
-- Proof sketch: use the explicit isomorphism `continuous_sheafified_representable_iso u J K U`
-- and take the `IsIso` instance of its `hom`.
theorem continuous_sheafified_representable_iso_isIso
    (U : C) :
    IsIso (continuous_sheafified_representable_iso u J K U).hom := by
  -- The comparison map is the forward morphism of an explicit isomorphism.
  infer_instance

end
