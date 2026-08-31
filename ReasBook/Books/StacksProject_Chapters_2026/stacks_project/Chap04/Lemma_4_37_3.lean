module

public import stacks_project.Chap04.Lemma_4_35_2
public import stacks_project.Chap04.Lemma_4_36_4
public import stacks_project.Chap04.Example_4_37_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂ u₃

open Opposite

namespace CategoryTheory

open scoped Bicategory

open BasedFunctor
open HasFibers
open Pseudofunctor
open Pseudofunctor.CoGrothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

namespace IsFibredInGroupoids

/-- Helper for Lemma 4.37.3: the strictification comparison equivalence in
`FibredCategoryOver C` induces an equivalence over the base on the underlying based functors. -/
private theorem strictification_comparison_isEquivalenceOverBase
    (p : S ⥤ C) [IsFibredInGroupoids p]
    (Y : FibredCategoryOver C)
    (e : Bicategory.Equivalence (FibredCategoryOver.ofFunctor p) Y) :
    ((e.hom.obj.obj : (FibredCategoryOver.ofFunctor p).obj ⟶ Y.obj) :
      BasedCategory.ofFunctor p ⥤ᵇ Y.toBasedCategory).IsEquivalenceOverBase := by
  -- Forget the sub-`2`-category structure on the unit and counit to recover a based equivalence.
  let etaIso :
      𝟙 (BasedCategory.ofFunctor p) ≅
        (((e.hom.obj.obj : (FibredCategoryOver.ofFunctor p).obj ⟶ Y.obj) :
            BasedCategory.ofFunctor p ⥤ᵇ Y.toBasedCategory) ⋙
          ((e.inv.obj.obj : Y.obj ⟶ (FibredCategoryOver.ofFunctor p).obj) :
            Y.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor p)) := by
    simpa using
      Functor.mapIso
        (((fibredCategoryOverSubTwoCategory C).hom
          (FibredCategoryOver.ofFunctor p)
          (FibredCategoryOver.ofFunctor p)).inclusion)
        e.unit
  let epsIso :
      (((e.inv.obj.obj : Y.obj ⟶ (FibredCategoryOver.ofFunctor p).obj) :
          Y.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor p) ⋙
        ((e.hom.obj.obj : (FibredCategoryOver.ofFunctor p).obj ⟶ Y.obj) :
          BasedCategory.ofFunctor p ⥤ᵇ Y.toBasedCategory)) ≅
        𝟙 Y.toBasedCategory := by
    simpa using
      Functor.mapIso
        (((fibredCategoryOverSubTwoCategory C).hom Y Y).inclusion)
        e.counit
  let eBased : Bicategory.Equivalence (BasedCategory.ofFunctor p) Y.toBasedCategory :=
    Bicategory.Equivalence.mkOfAdjointifyCounit etaIso epsIso
  exact BasedFunctor.hom_isEquivalenceOverBase eBased

/-- Helper for Lemma 4.37.3: the based strictification equivalence over the base transports the
groupoid structure on each fiber from `p` to the strictified target. -/
private theorem strictification_target_fiber_isGroupoid
    (p : S ⥤ C) [IsFibredInGroupoids p]
    (Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C)
    (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p)
    (hF : F.IsEquivalenceOverBase) (U : C) :
    IsGroupoid (Y.p.Fiber U) := by
  -- Transport the source fiber groupoid structure across the strictification equivalence.
  letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
    simpa using (inferInstance : IsGroupoid (p.Fiber U))
  exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase F hF U

/-- Helper for Lemma 4.37.3: the strictification target is again fibred in groupoids once each
fiber has been transported from the source. -/
private theorem strictification_target_isFibredInGroupoids
    (p : S ⥤ C) [IsFibredInGroupoids p]
    (Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C)
    (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p)
    (hF : F.IsEquivalenceOverBase) :
    IsFibredInGroupoids Y.p := by
  -- Upgrade fiberwise groupoids on the strictification target using Lemma 4.35.2.
  exact
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid Y.p inferInstance
      (fun U ↦ strictification_target_fiber_isGroupoid p Y F hF U)

/-- Helper for Lemma 4.37.3: a split category fibred in groupoids admits the expected
groupoid-valued co-Grothendieck model over the base. -/
private theorem split_groupoidPresheafModel_over_base
    {T : Type u₃} [Category.{max v₁ v₂} T]
    (p : T ⥤ C) [p.IsSplitFibredCategory] [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{max v₁ v₂, u₃},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        e.IsEquivalenceOverBase := by
  -- Unpack the split Cat-valued model and then upgrade each fiber to a small groupoid.
  rcases (inferInstance : p.IsSplitFibredCategory).existsCoGrothendieckModel with
    ⟨F, e, eInv, hη, hε⟩
  let pF := CoGrothendieck.forget (F.toPseudofunctor')
  have hpF_fiber (U : C) : IsGroupoid (pF.Fiber U) := by
    -- Transport the source fiber groupoids across the given equivalence over the base.
    letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
      simpa using (inferInstance : IsGroupoid (p.Fiber U))
    let he : e.IsEquivalenceOverBase :=
      BasedFunctor.IsEquivalenceOverBase.mkPrime
        eInv
        (eqToIso hη.symm)
        (eqToIso hε)
    exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase e he U
  let FObjGrpd : ∀ U : Cᵒᵖ, Grpd.{max v₁ v₂, u₃} := fun U ↦ by
    -- Identify the model fiber with `F.obj U` and use that transported groupoid structure.
    let G := HasFibers.inducedFunctor pF (unop U)
    letI : G.ReflectsIsomorphisms := inferInstance
    letI : IsGroupoid (pF.Fiber (unop U)) := hpF_fiber (unop U)
    letI : IsGroupoid (F.obj U) := by
      simpa [pF] using (isGroupoid_of_reflects_iso G)
    letI : Groupoid (F.obj U) := Groupoid.ofIsGroupoid
    exact Grpd.of (F.obj U)
  let FGrpd : Cᵒᵖ ⥤ Grpd.{max v₁ v₂, u₃} :=
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
  refine ⟨FGrpd, ?_⟩
  cases hforget
  refine ⟨e, ?_⟩
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      eInv
      (eqToIso hη.symm)
      (eqToIso hε)

/-- Lemma 4.37.3: every category fibred in groupoids `p : S ⥤ C` is equivalent over `C` to the
split category attached to a contravariant groupoid-valued presheaf on `C`. -/
theorem exists_groupoidPresheafModel_over_base
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{max v₁ v₂, max u₁ (max u₂ v₁)},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget
              ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        e.IsEquivalenceOverBase := by
  -- Route correction: strictify only to obtain a split model over `C`, then apply the already
  -- proved split-case theorem from Definition 4.37.2 to that target and compose the equivalences.
  have hsplit :
      ∃ (Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C)
        (e : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p),
        e.IsEquivalenceOverBase ∧ Functor.IsSplitFibredCategory Y.p :=
    exists_split_fibred_category_over_base p
  rcases hsplit with ⟨Y, e, hStrict, hYsplit⟩
  have hYgroupoids : IsFibredInGroupoids Y.p :=
    strictification_target_isFibredInGroupoids p Y e hStrict
  letI := hYsplit
  letI := hYgroupoids
  -- Apply the split-case groupoid model to the strictified target and pull it back to `p`.
  rcases split_groupoidPresheafModel_over_base Y.p with ⟨F, eY, hY⟩
  refine ⟨F, e ⋙ eY, ?_⟩
  exact BasedFunctor.IsEquivalenceOverBase.comp hStrict hY

end IsFibredInGroupoids

end CategoryTheory
