module

public import stacks_project.Chap04.«4_34_2_1»
public import stacks_project.Chap04.«4_34_2_2»
public import stacks_project.Chap04.Definition_4_39_2
public import stacks_project.Chap04.Lemma_4_35_9
public import stacks_project.Chap04.Lemma_4_35_12

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe uC uS v

namespace CategoryTheory

open CategoryOver
open BasedNatIso
open BasedNatTrans
open Functor.Fiber

variable {C : Type uC} [Category.{v} C]
variable {S : Type uS} [Category.{v} S]

/- Domain-style sampling for Lemma 4.39.7:
- primary domain: absolute/relative inertia of a fibred category over a fixed base `C`;
- inspected project owners:
  `RelativeInertiaObject`,
  `relativeInertiaStructureFunctor`,
  `CategoryOver.relativeInertiaStructureMap`,
  `IsFibredInSetoids`;
- best owner abstraction: the core/canonical owner is the functor
  `relativeInertiaStructureFunctor p`; the absolute `Cat/C` map is the specialization
  `CategoryOver.relativeInertiaStructureMap (BasedCategory.ofFunctor p).toBase`;
- primitive data: a relative inertia object is an object together with a vertical automorphism;
- derived API: the structure functor to `S` and its based-category packaging
  `relativeInertiaStructureMap (BasedCategory.ofFunctor p).toBase`.

Source/core/bridge triage:
- source-facing: the canonical map `I_S ⥤ S` is an equivalence;
- core/canonical: the owner theorem
  `relativeInertiaStructureFunctor_isEquivalence_iff_isFibredInSetoids`;
- bridge/view: the source-facing reformulation
  `absoluteInertiaStructureMap_isEquivalenceOverBase_iff_isFibredInSetoids`. -/

/-- Helper for Lemma 4.39.7: in a fibred-in-setoids category, every inertia automorphism is the
identity. -/
private theorem relativeInertiaObject_alpha_eq_refl_of_isFibredInSetoids
    (p : S ⥤ C) [IsFibredInGroupoids p] (hp : IsFibredInSetoids p)
    (X : RelativeInertiaObject p) :
    X.α = Iso.refl X.x := by
  -- Move the inertia automorphism into the fiber over `p.obj X.x`, where setoidness forces it
  -- to be the unique endomorphism.
  let x : p.Fiber (p.obj X.x) := ⟨X.x, rfl⟩
  let _ : p.IsHomLift (𝟙 (p.obj X.x)) X.α.hom :=
    IsHomLift.of_fac' p (𝟙 (p.obj X.x)) X.α.hom rfl rfl <| by
      simpa using X.map_hom_eq_id
  have hMapIso : p.mapIso X.α = Iso.refl (p.obj X.x) := by
    apply Iso.ext
    simpa using X.map_hom_eq_id
  have hInv : p.map X.α.inv = 𝟙 (p.obj X.x) := by
    simpa using congrArg Iso.inv hMapIso
  let _ : p.IsHomLift (𝟙 (p.obj X.x)) X.α.inv :=
    IsHomLift.of_fac' p (𝟙 (p.obj X.x)) X.α.inv rfl rfl <| by
      simpa using hInv
  let α : x ≅ x :=
    { hom := homMk p (p.obj X.x) X.α.hom
      inv := homMk p (p.obj X.x) X.α.inv
      hom_inv_id := by
        apply hom_ext
        change X.α.hom ≫ X.α.inv = 𝟙 X.x
        exact X.α.hom_inv_id
      inv_hom_id := by
        apply hom_ext
        change X.α.inv ≫ X.α.hom = 𝟙 X.x
        exact X.α.inv_hom_id
    }
  -- The fiber is a setoid, so the induced automorphism in that fiber is trivial.
  have hα : α = Iso.refl x := Subsingleton.elim _ _
  have hα_hom : α.hom = 𝟙 x := congrArg Iso.hom hα
  apply Iso.ext
  simpa [α, x] using congrArg
    (fun f ↦ (fiberInclusion : p.Fiber (p.obj X.x) ⥤ S).map f) hα_hom

/-- Helper for Lemma 4.39.7: when the fibers are setoids, the identity section is a quasi-inverse
to the inertia structure functor. -/
private noncomputable def relativeInertiaIdentitySection_unitIso_of_isFibredInSetoids
    (p : S ⥤ C) [IsFibredInGroupoids p] (hp : IsFibredInSetoids p) :
    𝟭 (RelativeInertiaObject p) ≅
      relativeInertiaStructureFunctor p ⋙ relativeInertiaIdentitySection p := by
  -- Route correction: the unit is built objectwise by collapsing each inertia automorphism to the
  -- identity, rather than by searching for a separate abstract equivalence first.
  let e :
      ∀ X : RelativeInertiaObject p,
        X ≅ (relativeInertiaStructureFunctor p ⋙ relativeInertiaIdentitySection p).obj X :=
    fun X ↦
      { hom :=
          { φ := 𝟙 X.x
            comm := by
              change X.α.hom ≫ 𝟙 X.x = 𝟙 X.x ≫ (Iso.refl X.x).hom
              rw [relativeInertiaObject_alpha_eq_refl_of_isFibredInSetoids p hp X]
              simp }
        inv :=
          { φ := 𝟙 X.x
            comm := by
              change (Iso.refl X.x).hom ≫ 𝟙 X.x = 𝟙 X.x ≫ X.α.hom
              rw [relativeInertiaObject_alpha_eq_refl_of_isFibredInSetoids p hp X]
              simp }
        hom_inv_id := by
          apply RelativeInertiaHom.ext
          change 𝟙 X.x ≫ 𝟙 X.x = 𝟙 X.x
          simp
        inv_hom_id := by
          apply RelativeInertiaHom.ext
          change 𝟙 X.x ≫ 𝟙 X.x = 𝟙 X.x
          simp }
  refine
    NatIso.ofComponents
      e
      (fun {X Y} f ↦ by
        apply RelativeInertiaHom.ext
        change f.φ ≫ (e Y).hom.φ = (e X).hom.φ ≫ f.φ
        exact (Category.comp_id f.φ).trans (Category.id_comp f.φ).symm)

-- Proof sketch: if `p` is fibred in setoids, every vertical automorphism is forced to be the
-- identity, so the inertia structure functor is an equivalence. Conversely, if it is an
-- equivalence, then every inertia object `(x, α)` is identified with `(x, 𝟙 x)`, forcing the
-- fibers to be setoids.
/-- Owner-level form of Lemma 4.39.7: for a category fibred in groupoids `p : S ⥤ C`, the
canonical structure functor from the absolute inertia of `p` to `S` is an equivalence if and only
if `p` is fibred in setoids. The source-facing `Cat/C` packaging is the companion theorem
`absoluteInertiaStructureMap_isEquivalenceOverBase_iff_isFibredInSetoids`. -/
theorem relativeInertiaStructureFunctor_isEquivalence_iff_isFibredInSetoids
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    (relativeInertiaStructureFunctor p).IsEquivalence ↔ IsFibredInSetoids p := by
  let F := relativeInertiaStructureFunctor p
  constructor
  · intro hF
    -- Use fullness to compare `(x, 𝟙)` with `(x, α)` and read the conjugacy relation as
    -- triviality of `α`.
    let _ : F.Full := hF.full
    have hAut : ∀ {U : C} (x : p.Fiber U) (α : x ≅ x), α = Iso.refl x := by
      intro U x α
      rcases x with ⟨x, rfl⟩
      let X₁ : RelativeInertiaObject p :=
        { x := x
          α := Iso.refl x
          map_hom_eq_id := by simp }
      let X₂ : RelativeInertiaObject p :=
        { x := x
          α := (fiberInclusion : p.Fiber (p.obj x) ⥤ S).mapIso α
          map_hom_eq_id := by
            let _ : p.IsHomLift (𝟙 (p.obj x)) α.hom.1 := α.hom.2
            simpa using (IsHomLift.eq_of_isHomLift p (𝟙 (p.obj x)) α.hom.1).symm }
      let f : X₁ ⟶ X₂ := F.preimage (show F.obj X₁ ⟶ F.obj X₂ from 𝟙 x)
      have hf : F.map f = (show F.obj X₁ ⟶ F.obj X₂ from 𝟙 x) := F.map_preimage _
      have hf' : f.φ = 𝟙 x := by
        simpa [F] using hf
      have hα_hom : α.hom.1 = 𝟙 x := by
        simpa [X₁, X₂, hf'] using f.comm.symm
      apply Iso.ext
      apply hom_ext
      simpa using hα_hom
    refine
      (isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_subsingleton_aut p).2
        ⟨inferInstance, ?_⟩
    intro U x
    exact ⟨fun α β ↦ (hAut x α).trans (hAut x β).symm⟩
  · intro hp
    -- Build the inverse equivalence from the identity section and the unit isomorphism above.
    change F.IsEquivalence
    let G := relativeInertiaIdentitySection p
    let η := relativeInertiaIdentitySection_unitIso_of_isFibredInSetoids p hp
    have hε : G ⋙ F = 𝟭 S := by
      dsimp [F, G]
    exact (Functor.IsEquivalence.mk' G η (eqToIso hε) : F.IsEquivalence)

-- Proof sketch: the source-facing absolute inertia morphism in `Cat/C` is the packaging of the
-- owner-level functor `relativeInertiaStructureFunctor p`, so the statement is just the bridge
-- form of the owner theorem above.
/-- Lemma 4.39.7: for a category fibred in groupoids `p : S ⥤ C`, the canonical `1`-morphism
from the absolute inertia `I_S` to `S` is an equivalence over `C` if and only if `p` is fibred
in setoids. In the chapter-local `Cat/C` API this map is the bridge
`relativeInertiaStructureMap (BasedCategory.ofFunctor p).toBase`. -/
theorem absoluteInertiaStructureMap_isEquivalenceOverBase_iff_isFibredInSetoids
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    (relativeInertiaStructureMap (BasedCategory.ofFunctor p).toBase).IsEquivalenceOverBase ↔
      IsFibredInSetoids p := by
  let B := BasedCategory.ofFunctor p
  change (relativeInertiaStructureMap B.toBase).IsEquivalenceOverBase ↔ IsFibredInSetoids p
  constructor
  · intro h
    -- Forgetting the over-base packaging recovers the owner-level equivalence statement.
    exact
      (relativeInertiaStructureFunctor_isEquivalence_iff_isFibredInSetoids p).1 <|
        BasedFunctor.isEquivalence_of_isEquivalenceOverBase
          (relativeInertiaStructureMap B.toBase) h
  · intro hp
    -- Repackage the owner-level quasi-inverse as an equivalence over the base category.
    let F : absoluteInertiaOver B ⥤ᵇ B := relativeInertiaStructureMap B.toBase
    let G : B ⥤ᵇ absoluteInertiaOver B := absoluteInertiaIdentitySection B
    let ηNat := relativeInertiaIdentitySection_unitIso_of_isFibredInSetoids p hp
    let I : absoluteInertiaOver B ⥤ᵇ absoluteInertiaOver B :=
      { toFunctor := 𝟭 (RelativeInertiaObject p)
        w := rfl }
    let FG : absoluteInertiaOver B ⥤ᵇ absoluteInertiaOver B :=
      { toFunctor := F.toFunctor ⋙ G.toFunctor
        w := rfl }
    have hη_over_id :
        eqToHom I.w.symm ≫ Functor.whiskerRight ηNat.hom (absoluteInertiaOver B).p ≫ eqToHom FG.w =
          𝟙 (absoluteInertiaOver B).p := by
      ext X
      cases X with
      | mk x α hα =>
          cases I.w
          cases FG.w
          dsimp [I, FG, ηNat, relativeInertiaIdentitySection_unitIso_of_isFibredInSetoids]
          simp only [eqToHom_app, Functor.comp_obj, Functor.id_obj, eqToHom_refl, Category.id_comp]
          let X : RelativeInertiaObject p := { x := x, α := α, map_hom_eq_id := hα }
          change (relativeInertiaOver B.toBase).p.map (𝟙 X) ≫ eqToHom rfl = 𝟙 (p.obj x)
          rw [eqToHom_refl, Category.comp_id]
          change p.map (𝟙 x) = 𝟙 (p.obj x)
          exact p.map_id x
    let η : I ⟶ FG := of_over_id ηNat.hom hη_over_id
    exact
      BasedFunctor.IsEquivalenceOverBase.mkPrime
        G
        (by simpa [I, FG] using mkNatIso ηNat η.isHomLift')
        (eqToIso (absoluteInertiaIdentitySection_comp_structureMap B))

end CategoryTheory
