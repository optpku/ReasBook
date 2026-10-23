module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open BasedNatTrans
open Bicategory
open Functor.IsHomLift
open scoped Bicategory

universe u v uS uX uY vS vX vY

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 4.32.1:
- primary domain: categories over a fixed base, with `1`- and `2`-morphisms.
- sampled owner-level declarations:
  `BasedCategory`,
  `BasedFunctor`,
  `BasedNatTrans`,
  `Bicategory.Equivalence`.
- best owner abstraction: `BasedCategory C` with its ambient bicategorical homs `X ⥤ᵇ Y`; when
  source and target lie in one `BasedCategory` universe, the canonical equivalence owner is
  `X ≌ Y`.
- primitive data: entirely owned upstream by those canonical declarations; for the heterogeneous
  based-functor setting, the primitive over-base equivalence data are exactly a based
  quasi-inverse together with based unit and counit isomorphisms.
- derived API kept here: the short chapter-wide vocabulary `CategoryOver`, the induced functor on
  fibres, the heterogeneous bridge datum `EquivalenceOverBase F`, the owner predicate
  `F.IsEquivalenceOverBase`, the bridge from the over-base predicate to an ordinary equivalence of
  underlying categories, and the textbook bridge between vertical natural transformations and the
  over-identity equation.

Source/core/bridge triage:
- `source-facing`: categories over `C`, morphisms over `C`, `2`-morphisms over `C`, and the
  source-level predicate that a based functor is an equivalence over the base.
- `core/canonical`: `BasedCategory`, `BasedFunctor`, `BasedNatTrans`, and same-universe
  bicategorical equivalences `X ≌ Y`.
- `bridge/view`: the heterogeneous explicit datum `EquivalenceOverBase F`, used only to connect
  the source-facing owner predicate to the canonical bicategorical equivalence when the universes
  match. -/

/- Definition 4.32.1: a category over `C` is the canonical based category
`CategoryTheory.BasedCategory C`. -/
recall CategoryTheory.BasedCategory

/- Definition 4.32.1: a `1`-morphism in `Cat/C` is the canonical based functor
`X ⥤ᵇ Y`. -/
recall CategoryTheory.BasedFunctor

/- Definition 4.32.1: a `2`-morphism in `Cat/C` is the canonical based natural transformation,
i.e. a morphism in the hom-category `X ⥤ᵇ Y`. -/
recall CategoryTheory.BasedNatTrans

/-- Definition 4.32.1: `CategoryOver C` is the stable chapter-local vocabulary for the canonical
owner `BasedCategory C` of categories over `C`. This abbreviation is kept because it is the
high-reuse ambient name throughout the chapter, not a one-off compatibility wrapper. -/
abbrev CategoryOver (C : Type u) [Category.{v} C] := BasedCategory C

namespace BasedCategory

variable {X : BasedCategory.{vX, uX} C}

/-- The canonical morphism in `Cat/C` from a category over `C` to the base object `(C, 𝟭 C)`. -/
abbrev toBase (X : BasedCategory.{vX, uX} C) : X ⥤ᵇ ofFunctor (𝟭 C) :=
  { toFunctor := X.p
    w := by
      simpa using Functor.comp_id X.p }

/-- A category over `C` carries the canonical projection functor to the base category. -/
-- Proof sketch: unfold `CategoryOver` to `BasedCategory` and then unfold `BasedCategory.toBase`.
theorem categoryOver_toBase_toFunctor_eq_projection
    (X : CategoryOver C) :
    X.toBase.toFunctor = X.p := by
  -- Unfolding the chapter-local abbreviation and the canonical map to the base reduces the goal
  -- to definitional equality of the stored projection functor.
  rfl

end BasedCategory

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

theorem fiberFunctor_comp_eq_const
    (F : X ⥤ᵇ Y) (U : C) :
    (Functor.Fiber.fiberInclusion : Functor.Fiber X.p U ⥤ X.obj) ⋙ F.toFunctor ⋙ Y.p =
      (Functor.const (Functor.Fiber X.p U)).obj U := by
  have h :
      (Functor.Fiber.fiberInclusion : Functor.Fiber X.p U ⥤ X.obj) ⋙ X.p =
        (Functor.const (Functor.Fiber X.p U)).obj U :=
    Functor.Fiber.fiberInclusion_comp_eq_const
  calc
    (Functor.Fiber.fiberInclusion : Functor.Fiber X.p U ⥤ X.obj) ⋙ F.toFunctor ⋙ Y.p =
        (Functor.Fiber.fiberInclusion : Functor.Fiber X.p U ⥤ X.obj) ⋙ X.p := by
          simpa using congrArg
            (fun q ↦ Functor.comp (Functor.Fiber.fiberInclusion : Functor.Fiber X.p U ⥤ X.obj) q)
            F.w
    _ = (Functor.const (Functor.Fiber X.p U)).obj U := h

/-- The canonical functor on the fibre over `U` induced by a morphism in `Cat/C`. -/
abbrev fiberFunctor
    (F : X ⥤ᵇ Y) (U : C) :
    Functor.Fiber X.p U ⥤ Functor.Fiber Y.p U :=
  let G : Functor.Fiber X.p U ⥤ Y.obj :=
    (Functor.Fiber.fiberInclusion : Functor.Fiber X.p U ⥤ X.obj) ⋙ F.toFunctor
  let hG : G ⋙ Y.p = (Functor.const (Functor.Fiber X.p U)).obj U :=
    fiberFunctor_comp_eq_const F U
  Functor.Fiber.inducedFunctor hG

/-- A heterogeneous-universe equivalence-over-base datum on a based functor. When source and
target lie in a common `BasedCategory` universe, this upgrades to the canonical bicategorical
equivalence object in `Cat/C`. -/
structure EquivalenceOverBase (F : X ⥤ᵇ Y) where
  /-- A based quasi-inverse to `F`. -/
  inverse : Y ⥤ᵇ X
  /-- The unit isomorphism of the equivalence over `C`. -/
  unitIso : 𝟭 X ≅ F ⋙ inverse
  /-- The counit isomorphism of the equivalence over `C`. -/
  counitIso : inverse ⋙ F ≅ 𝟭 Y

/-- A based functor over `C` is an equivalence over the base when it admits an
`EquivalenceOverBase` structure. -/
class IsEquivalenceOverBase (F : X ⥤ᵇ Y) : Prop where
  nonempty : Nonempty (EquivalenceOverBase F)

namespace IsEquivalenceOverBase

/-- To prove that a based functor is an equivalence over the base, it suffices to provide a based
quasi-inverse together with based unit and counit isomorphisms. -/
theorem mkPrime (G : Y ⥤ᵇ X) (eta : 𝟭 X ≅ F ⋙ G) (eps : G ⋙ F ≅ 𝟭 Y) :
    F.IsEquivalenceOverBase :=
  ⟨⟨⟨G, eta, eps⟩⟩⟩

end IsEquivalenceOverBase

namespace EquivalenceOverBase

variable {F : X ⥤ᵇ Y}

/-- The inverse functor in an explicit equivalence-over-base datum is again an equivalence over
the base category. -/
theorem inverse_isEquivalenceOverBase (e : EquivalenceOverBase F) :
    BasedFunctor.IsEquivalenceOverBase e.inverse :=
  ⟨⟨⟨F, e.counitIso.symm, e.unitIso.symm⟩⟩⟩

variable {Z : BasedCategory.{vS, uS} C} {G : Y ⥤ᵇ Z}

set_option backward.isDefEq.respectTransparency false in
/-- Explicit equivalence-over-base data compose. -/
def trans (e : EquivalenceOverBase F) (f : EquivalenceOverBase G) :
    EquivalenceOverBase (F ⋙ G) where
  inverse := f.inverse ⋙ e.inverse
  unitIso :=
    let h : F ≅ BasedFunctor.comp (BasedFunctor.comp F G) f.inverse :=
      (eqToIso (BasedFunctor.comp_id F)).symm ≪≫
        BasedNatIso.mkNatIso
          (show (F ⋙ 𝟭 Y).toFunctor ≅ (F ⋙ (G ⋙ f.inverse)).toFunctor from
            Functor.isoWhiskerLeft F.toFunctor ((BasedNatTrans.forgetful Y Y).mapIso f.unitIso))
          (BasedCategory.whiskerLeft F f.unitIso.hom).isHomLift' ≪≫
        (eqToIso (BasedFunctor.comp_assoc F G f.inverse)).symm
    let h' :
        BasedFunctor.comp F e.inverse ≅
          BasedFunctor.comp (BasedFunctor.comp (BasedFunctor.comp F G) f.inverse) e.inverse :=
      BasedNatIso.mkNatIso
        (show (F ⋙ e.inverse).toFunctor ≅
            (((F ⋙ G) ⋙ f.inverse) ⋙ e.inverse).toFunctor from
          Functor.isoWhiskerRight ((BasedNatTrans.forgetful X Y).mapIso h) e.inverse.toFunctor)
        (BasedCategory.whiskerRight h.hom e.inverse).isHomLift'
    e.unitIso ≪≫ h' ≪≫ eqToIso (BasedFunctor.comp_assoc (F ⋙ G) f.inverse e.inverse)
  counitIso :=
    let h : BasedFunctor.comp (BasedFunctor.comp f.inverse e.inverse) F ≅ f.inverse :=
      eqToIso (BasedFunctor.comp_assoc f.inverse e.inverse F) ≪≫
        BasedNatIso.mkNatIso
          (show (f.inverse ⋙ (e.inverse ⋙ F)).toFunctor ≅ (f.inverse ⋙ 𝟭 Y).toFunctor from
            Functor.isoWhiskerLeft f.inverse.toFunctor
              ((BasedNatTrans.forgetful Y Y).mapIso e.counitIso))
          (BasedCategory.whiskerLeft f.inverse e.counitIso.hom).isHomLift' ≪≫
        eqToIso (BasedFunctor.comp_id f.inverse)
    let h' :
        BasedFunctor.comp (BasedFunctor.comp (BasedFunctor.comp f.inverse e.inverse) F) G ≅
          BasedFunctor.comp f.inverse G :=
      BasedNatIso.mkNatIso
        (show (((f.inverse ⋙ e.inverse) ⋙ F) ⋙ G).toFunctor ≅
            (f.inverse ⋙ G).toFunctor from
          Functor.isoWhiskerRight ((BasedNatTrans.forgetful Z Y).mapIso h) G.toFunctor)
        (BasedCategory.whiskerRight h.hom G).isHomLift'
    (eqToIso (BasedFunctor.comp_assoc (f.inverse ⋙ e.inverse) F G)).symm ≪≫ h' ≪≫ f.counitIso

end EquivalenceOverBase

namespace IsEquivalenceOverBase

variable {Z : BasedCategory.{vS, uS} C} {F : X ⥤ᵇ Y} {G : Y ⥤ᵇ Z}

/-- Equivalences over the base are closed under composition. -/
theorem comp (hF : F.IsEquivalenceOverBase) (hG : G.IsEquivalenceOverBase) :
    (F ⋙ G).IsEquivalenceOverBase :=
  ⟨⟨(Classical.choice hF.nonempty).trans (Classical.choice hG.nonempty)⟩⟩

end IsEquivalenceOverBase

section SameUniverse

variable {X : BasedCategory.{vS, uS} C} {Y : BasedCategory.{vS, uS} C}

namespace EquivalenceOverBase

variable {F : X ⥤ᵇ Y}

/-- In the same-universe case, explicit equivalence-over-base data package into the canonical
bicategorical equivalence object in `Cat/C`. -/
noncomputable def toEquivalence (e : EquivalenceOverBase F) : X ≌ Y :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.unitIso e.counitIso

@[simp] theorem toEquivalence_hom (e : EquivalenceOverBase F) :
    e.toEquivalence.hom = F :=
  rfl

@[simp] theorem toEquivalence_inv (e : EquivalenceOverBase F) :
    e.toEquivalence.inv = e.inverse :=
  rfl

end EquivalenceOverBase

/-- The forward `1`-morphism of a bicategorical equivalence in `Cat/C` is an equivalence over the
base. -/
theorem hom_isEquivalenceOverBase (e : X ≌ Y) :
    e.hom.IsEquivalenceOverBase :=
  IsEquivalenceOverBase.mkPrime e.inv e.unit e.counit

end SameUniverse

end BasedFunctor

namespace BasedNatTrans

variable {X : BasedCategory.{v, uX} C} {Y : BasedCategory.{v, uY} C}
variable {F G : X ⥤ᵇ Y}

/-- The textbook over-identity equation recovered from the canonical based natural
transformation. -/
theorem over_id (η : F ⟶ G) :
    eqToHom F.w.symm ≫ Functor.whiskerRight η.toNatTrans Y.p ≫ eqToHom G.w = 𝟙 X.p := by
  ext a
  simpa using (IsHomLift.fac Y.p (𝟙 (X.p.obj a)) (η.toNatTrans.app a)).symm

/-- Build a based natural transformation from the textbook over-identity equation. -/
def of_over_id (τ : F.toFunctor ⟶ G.toFunctor)
    (over_id : eqToHom F.w.symm ≫ Functor.whiskerRight τ Y.p ≫ eqToHom G.w = 𝟙 X.p) :
    F ⟶ G where
  toNatTrans := τ
  isHomLift' := fun a ↦
    IsHomLift.of_fac Y.p (𝟙 (X.p.obj a)) (τ.app a) (F.w_obj a) (G.w_obj a) <| by
      simpa using (NatTrans.congr_app over_id a).symm

end BasedNatTrans

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- Forgetting the base data, an equivalence over the base is an equivalence of the underlying
categories. -/
theorem isEquivalence_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : IsEquivalenceOverBase F) :
    F.toFunctor.IsEquivalence := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  refine Functor.IsEquivalence.mk' e.inverse.toFunctor ?_ ?_
  · simpa using (BasedNatTrans.forgetful X X).mapIso e.unitIso
  · simpa using (BasedNatTrans.forgetful Y Y).mapIso e.counitIso

/-- An equivalence over the base category induces an equivalence on every standard fiber. -/
theorem fiberFunctor_isEquivalence_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : IsEquivalenceOverBase F) (U : C) :
    (F.fiberFunctor U).IsEquivalence := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  letI : F.toFunctor.IsEquivalence := isEquivalence_of_isEquivalenceOverBase F hF
  letI : (F.fiberFunctor U).Faithful := by
    refine ⟨?_⟩
    intro a b f g h
    apply Functor.Fiber.hom_ext
    exact F.toFunctor.map_injective (congrArg Subtype.val h)
  letI : (F.fiberFunctor U).Full := by
    refine ⟨?_⟩
    intro a b φ
    let ψ : a.1 ⟶ b.1 := F.toFunctor.preimage φ.1
    have hψ : X.p.IsHomLift (𝟙 U) ψ := by
      have hFψ : Y.p.IsHomLift (𝟙 U) (F.toFunctor.map ψ) := by
        simpa [ψ] using (φ.2 : Y.p.IsHomLift (𝟙 U) φ.1)
      exact (F.isHomLift_iff (𝟙 U) ψ).1 hFψ
    refine ⟨Functor.Fiber.homMk X.p U ψ, ?_⟩
    apply Functor.Fiber.hom_ext
    exact F.toFunctor.map_preimage φ.1
  letI : (F.fiberFunctor U).EssSurj := by
    refine ⟨?_⟩
    intro y
    let eps := e.counitIso
    let epsHom := eps.hom
    let epsInv := eps.inv
    have hhom : Y.p.IsHomLift (𝟙 U) (epsHom.app y.1) := by
      simpa [y.2] using epsHom.isHomLift y.2
    have hinv : Y.p.IsHomLift (𝟙 U) (epsInv.app y.1) := by
      simpa [y.2] using epsInv.isHomLift y.2
    letI := hhom
    letI := hinv
    refine ⟨(e.inverse.fiberFunctor U).obj y, ⟨?_⟩⟩
    refine
      ⟨Functor.Fiber.homMk Y.p U (epsHom.app y.1),
        Functor.Fiber.homMk Y.p U (epsInv.app y.1), ?_, ?_⟩
    · apply Functor.Fiber.hom_ext
      change epsHom.app y.1 ≫ epsInv.app y.1 = 𝟙 _
      exact NatTrans.congr_app (congrArg toNatTrans eps.hom_inv_id) y.1
    · apply Functor.Fiber.hom_ext
      change epsInv.app y.1 ≫ epsHom.app y.1 = 𝟙 _
      exact NatTrans.congr_app (congrArg toNatTrans eps.inv_hom_id) y.1
  refine Functor.IsEquivalence.mk' (e.inverse.fiberFunctor U) ?_ ?_
  · refine NatIso.ofComponents (fun x ↦ ?_) ?_
    · let eta := e.unitIso
      let etaHom := eta.hom
      let etaInv := eta.inv
      let etaIso := (forgetful X X).mapIso eta
      have hhom : X.p.IsHomLift (𝟙 U) (etaHom.app x.1) := by
        simpa [x.2] using etaHom.isHomLift x.2
      have hinv : X.p.IsHomLift (𝟙 U) (etaInv.app x.1) := by
        simpa [x.2] using etaInv.isHomLift x.2
      letI := hhom
      letI := hinv
      refine
        { hom := Functor.Fiber.homMk X.p U (etaHom.app x.1)
          inv := Functor.Fiber.homMk X.p U (etaInv.app x.1)
          hom_inv_id := by
            apply Functor.Fiber.hom_ext
            change etaHom.app x.1 ≫ etaInv.app x.1 = 𝟙 _
            simpa using etaIso.hom_inv_id_app x.1
          inv_hom_id := by
            apply Functor.Fiber.hom_ext
            change etaInv.app x.1 ≫ etaHom.app x.1 = 𝟙 _
            simpa using etaIso.inv_hom_id_app x.1 }
    · intro x y f
      let etaHom := e.unitIso.hom
      let etaIso := (forgetful X X).mapIso e.unitIso
      apply Functor.Fiber.hom_ext
      change f.1 ≫ etaHom.app y.1 = etaHom.app x.1 ≫ (F ⋙ e.inverse).map f.1
      simpa using etaIso.hom.naturality f.1
  · refine NatIso.ofComponents (fun y ↦ ?_) ?_
    · let eps := e.counitIso
      let epsHom := eps.hom
      let epsInv := eps.inv
      let epsIso := (forgetful Y Y).mapIso eps
      have hhom : Y.p.IsHomLift (𝟙 U) (epsHom.app y.1) := by
        simpa [y.2] using epsHom.isHomLift y.2
      have hinv : Y.p.IsHomLift (𝟙 U) (epsInv.app y.1) := by
        simpa [y.2] using epsInv.isHomLift y.2
      letI := hhom
      letI := hinv
      refine
        { hom := Functor.Fiber.homMk Y.p U (epsHom.app y.1)
          inv := Functor.Fiber.homMk Y.p U (epsInv.app y.1)
          hom_inv_id := by
            apply Functor.Fiber.hom_ext
            change epsHom.app y.1 ≫ epsInv.app y.1 = 𝟙 _
            simpa using epsIso.hom_inv_id_app y.1
          inv_hom_id := by
            apply Functor.Fiber.hom_ext
            change epsInv.app y.1 ≫ epsHom.app y.1 = 𝟙 _
            simpa using epsIso.inv_hom_id_app y.1 }
    · intro x y f
      let epsHom := e.counitIso.hom
      let epsIso := (forgetful Y Y).mapIso e.counitIso
      apply Functor.Fiber.hom_ext
      change (e.inverse ⋙ F).map f.1 ≫ epsHom.app y.1 = epsHom.app x.1 ≫ f.1
      simpa using epsIso.hom.naturality f.1

/-- An equivalence over the base transports the groupoid structure on each fiber forward along
the induced fiber equivalence. -/
theorem fiber_isGroupoid_of_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) (hF : IsEquivalenceOverBase F) (U : C) [IsGroupoid (X.p.Fiber U)] :
    IsGroupoid (Y.p.Fiber U) := by
  letI : (F.fiberFunctor U).IsEquivalence :=
    fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U
  exact isGroupoid_of_reflects_iso (F.fiberFunctor U).asEquivalence.inverse

instance
    (F : X ⥤ᵇ Y) [F.IsEquivalenceOverBase] :
    F.toFunctor.IsEquivalence :=
  isEquivalence_of_isEquivalenceOverBase F inferInstance

end BasedFunctor

end CategoryTheory
