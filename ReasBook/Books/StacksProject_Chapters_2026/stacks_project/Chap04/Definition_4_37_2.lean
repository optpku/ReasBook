module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import stacks_project.Chap04.Definition_4_36_2
public import stacks_project.Chap04.Example_4_37_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open Opposite

namespace CategoryTheory

open scoped Bicategory

namespace Functor

open BasedFunctor
open HasFibers
open Pseudofunctor
open Pseudofunctor.CoGrothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Definition 4.37.2:
- primary domain: split fibred categories over a fixed base whose split model comes from a
  groupoid-valued presheaf via the co-Grothendieck construction.
- inspected owner-level declarations:
  `Functor.IsSplitFibredCategory`,
  `IsFibredInGroupoids`,
  `Pseudofunctor.CoGrothendieck.groupoidPresheafProjection_isFibredInGroupoids`,
  `HasFibers.inducedFunctor`.
- best owner abstraction: the source-facing notion is the conjunction of the existing owners
  `Functor.IsSplitFibredCategory p` and `IsFibredInGroupoids p`; the textbook groupoid-valued
  model is bridge/view data, not a separate owner.
- primitive data: only the upstream split and fibred-in-groupoids owner predicates on `p`.
- derived API: the textbook existence of a presheaf `F : Cᵒᵖ ⥤ Grpd` whose co-Grothendieck model
  is isomorphic over `C` to `p`.

Source/core/bridge triage:
- `source-facing`: the conjunction `Functor.IsSplitFibredCategory p ∧ IsFibredInGroupoids p`.
- `core/canonical`: the owner predicates `Functor.IsSplitFibredCategory p` and
  `IsFibredInGroupoids p`.
- `bridge/view`: the textbook existential model by a groupoid-valued presheaf, the canonical
  example `groupoidPresheafProjection_isFibredInGroupoids`, and the fibre-identification
  equivalence `HasFibers.inducedFunctor`. -/

section

variable (p : S ⥤ C)

/- Definition 4.37.2: a functor `p : S ⥤ C` is split fibred in groupoids exactly when it
satisfies the existing owner predicates `p.IsSplitFibredCategory` and `IsFibredInGroupoids p`.
The groupoid-valued presheaf model constructed below is companion bridge data, not a separate
owner. -/
#check (p.IsSplitFibredCategory ∧ IsFibredInGroupoids p)

end

namespace IsSplitFibredCategory

/-- If `p` is split fibred and fibred in groupoids, then `p` admits the textbook
groupoid-valued split model over `C`. -/
theorem exists_groupoidPresheafModel
    (p : S ⥤ C) [p.IsSplitFibredCategory] [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{v₂, u₂},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        ∃ eInv : BasedCategory.ofFunctor
            (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) ⥤ᵇ
            BasedCategory.ofFunctor p,
          e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
            eInv ⋙ e =
              𝟙 (BasedCategory.ofFunctor
                (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor'))) := by
  rcases (inferInstance : p.IsSplitFibredCategory).existsCoGrothendieckModel with ⟨F, e, eInv, hη, hε⟩
  let pF := CoGrothendieck.forget (F.toPseudofunctor')
  have hpF_fiber (U : C) : IsGroupoid (pF.Fiber U) := by
    letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
      simpa using (inferInstance : IsGroupoid (p.Fiber U))
    let he : e.IsEquivalenceOverBase :=
      BasedFunctor.IsEquivalenceOverBase.mkPrime
        eInv
        (eqToIso hη.symm)
        (eqToIso hε)
    exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase e he U
  let FObjGrpd : ∀ U : Cᵒᵖ, Grpd.{v₂, u₂} := fun U ↦ by
    let G := HasFibers.inducedFunctor pF (unop U)
    letI : G.ReflectsIsomorphisms := inferInstance
    letI : IsGroupoid (pF.Fiber (unop U)) := hpF_fiber (unop U)
    letI : IsGroupoid (F.obj U) := by
      simpa [pF] using (isGroupoid_of_reflects_iso G)
    letI : Groupoid (F.obj U) := Groupoid.ofIsGroupoid
    exact Grpd.of (F.obj U)
  let FGrpd : Cᵒᵖ ⥤ Grpd.{v₂, u₂} :=
    { obj := FObjGrpd
      map := fun f ↦ by
        exact (F.map f).toFunctor
      map_id := fun U ↦ by
        change (F.map (𝟙 U)).toFunctor = 𝟭 (F.obj U)
        exact congrArg Cat.Hom.toFunctor (F.map_id U)
      map_comp := fun f g ↦ by
        change (F.map (f ≫ g)).toFunctor = (F.map f).toFunctor ⋙ (F.map g).toFunctor
        exact congrArg Cat.Hom.toFunctor (F.map_comp f g) }
  have hforget :
      CoGrothendieck.forget ((FGrpd ⋙ Grpd.forgetToCat).toPseudofunctor') = pF := by
    rfl
  refine ⟨FGrpd, ?_, ?_, ?_⟩
  · cases hforget
    exact e
  · cases hforget
    exact eInv
  · cases hforget
    exact ⟨hη, hε⟩

/-- Owner-level bridge: a split category fibred in groupoids is equivalent over the base to the
canonical co-Grothendieck model of a groupoid-valued presheaf. -/
theorem exists_groupoidPresheafModel_over_base
    (p : S ⥤ C) [p.IsSplitFibredCategory] [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{v₂, u₂},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        e.IsEquivalenceOverBase := by
  rcases IsSplitFibredCategory.exists_groupoidPresheafModel p with
    ⟨F, e, eInv, hη, hε⟩
  refine ⟨F, e, ?_⟩
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      eInv
      (eqToIso hη.symm)
      (eqToIso hε)

end IsSplitFibredCategory

/-- Companion specification for Definition 4.37.2: the owner-level conjunction
`p.IsSplitFibredCategory ∧ IsFibredInGroupoids p` is equivalent to the textbook existence of a
groupoid-valued presheaf model whose co-Grothendieck construction is isomorphic over `C` to
`p`. -/
theorem splitFibredCategory_and_fibredInGroupoids_iff_exists_groupoidPresheafModel
    {p : S ⥤ C} :
    (p.IsSplitFibredCategory ∧ IsFibredInGroupoids p) ↔
      ∃ F : Cᵒᵖ ⥤ Grpd.{v₂, u₂},
        ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
            BasedCategory.ofFunctor
              (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
          ∃ eInv : BasedCategory.ofFunctor
              (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) ⥤ᵇ
              BasedCategory.ofFunctor p,
            e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
              eInv ⋙ e =
                𝟙 (BasedCategory.ofFunctor
                  (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor'))) := by
  constructor
  · rintro ⟨hpSplit, hpGroupoids⟩
    letI := hpSplit
    letI := hpGroupoids
    exact IsSplitFibredCategory.exists_groupoidPresheafModel p
  · rintro ⟨F, e, eInv, hη, hε⟩
    let hpSplit : p.IsSplitFibredCategory := ⟨⟨(F ⋙ Grpd.forgetToCat), e, eInv, hη, hε⟩⟩
    let pF := CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')
    let hpGroupoids : IsFibredInGroupoids p := by
      letI : IsFibredInGroupoids pF := groupoidPresheafProjection_isFibredInGroupoids F
      exact
        isFibredInGroupoids_of_isFibered_and_fiber_groupoid p
          hpSplit.isFibered
          fun U ↦ by
            letI : IsGroupoid (pF.Fiber U) := IsFibredInGroupoids.fiber_isGroupoid U
            letI : IsGroupoid ((BasedCategory.ofFunctor pF).p.Fiber U) := by
              simpa using (inferInstance : IsGroupoid (pF.Fiber U))
            let heInv : eInv.IsEquivalenceOverBase :=
              BasedFunctor.IsEquivalenceOverBase.mkPrime
                e
                (eqToIso hε.symm)
                (eqToIso hη)
            exact
              BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase
                eInv heInv U
    exact ⟨hpSplit, hpGroupoids⟩

end Functor
end CategoryTheory
