module

public import stacks_project.Chap04.Lemma_4_31_11

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v u

namespace CategoryTheory.Limits

noncomputable section

variable {C : Type v} [Category.{v} C] [IsGroupoid C]
variable {S : Type v} [Category.{v} S] [IsGroupoid S]

variable (G₁ G₂ : C ⥤ S)

local notation "DiagonalPullback" =>
  CategoricalPullback (G₁.prod' G₂) (Functor.diag S)
local notation "IteratedPullback" =>
  CategoricalPullback (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C)

/- Domain-style sampling for Lemma 4.31.12:
- primary domain: bicategorical `2`-fibre products in `Cat`, expressed through the categorical
  pullback models attached to `(G₁.prod' G₂)` and `Functor.diag S`, together with the canonical
  iterated pullback owner of the induced cospan `π₁ G₁ G₂, π₂ G₁ G₂`;
- sampled owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `CatCommSqOver.toBicategoricalSquare`,
  `symmetricTwoFibreProductComparison`;
-- best owner abstraction: the source-facing square is still
  `BicategoricalTwoCommutativeSquare (G₁.prod' G₂).toCatHom (Functor.diag S).toCatHom`, with the
  `2`-fibre product condition expressed by `Bicategory.IsFinal`, but the target owner for the
  iterated pullback is the Stacks nested model
  `IteratedPullback = CategoricalPullback (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂))
    (Functor.diag C)`;
-- `CategoricalPullback` is the canonical owner abstraction, and `IteratedPullback` is exactly the
  textbook nested model `(C ×[S] C) ×[C × C] C`.  It is not the self-pullback
  `(π₁ G₁ G₂) ⊡ (π₂ G₁ G₂)`, which would have the wrong object set.

Primitive-vs-derived split:
- primitive data: the canonical diagonal square
  `Q : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback`,
  the induced square over `G₁` and `G₂`, and later an arbitrary source square
  `P : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) C'`;
-- derived API: the induced functor `DiagonalPullback ⥤ G₁ ⊡ G₂`, the resulting square over
  `Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)` and `Functor.diag C`, and the
  comparison/equivalence statements landing in the owner `IteratedPullback`. -/

/- Source/core/bridge triage for Lemma 4.31.12:
- `source-facing`: the displayed square over `(G₁.prod' G₂)` and `Δ_S`, viewed as a
  bicategorical square in `Cat`;
- `core/canonical`: `Bicategory.IsFinal` of that bicategorical square, with target owner
  `IteratedPullback`;
- `bridge/view`: `CatCommSqOver.toFunctorToCategoricalPullback`, together with Remark `4.31.5`
  identifying the textbook nested model `(C ×[S] C) ×[C × C] C` with `IteratedPullback`. -/

abbrev diagonalPullbackSourceSquare :
    CatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback :=
  (toCatCommSqOver (G₁.prod' G₂) (Functor.diag S) DiagonalPullback).obj (𝟭 _)

abbrev diagonalFirstPullbackSquare :
    CatCommSqOver G₁ G₂ DiagonalPullback :=
  let Q := diagonalPullbackSourceSquare G₁ G₂
  { fst := Q.fst
    snd := Q.fst
    iso :=
      (Functor.isoWhiskerLeft _ (Functor.prod'CompFst G₁ G₂).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight Q.iso (fst S S) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.prod'CompFst (𝟭 S) (𝟭 S)) ≪≫
          Functor.rightUnitor _) ≪≫
        (Functor.isoWhiskerLeft _ (Functor.prod'CompSnd G₁ G₂).symm ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight Q.iso (snd S S) ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Functor.prod'CompSnd (𝟭 S) (𝟭 S)) ≪≫
            Functor.rightUnitor _).symm }

abbrev diagonalFirstPullbackComparison :
    DiagonalPullback ⥤ G₁ ⊡ G₂ :=
  (toFunctorToCategoricalPullback G₁ G₂ DiagonalPullback).obj
    (diagonalFirstPullbackSquare G₁ G₂)

/-- Helper for Lemma 4.31.12: the first projection of the intermediate comparison functor is the
original `C`-leg of the diagonal pullback square. -/
theorem diagonal_first_comparison_fst_iso_naturality
    {X Y : DiagonalPullback} (f : X ⟶ Y) :
    (diagonalFirstPullbackComparison G₁ G₂ ⋙ π₁ G₁ G₂).map f ≫
        𝟙 ((diagonalPullbackSourceSquare G₁ G₂).fst.obj Y) =
      𝟙 ((diagonalPullbackSourceSquare G₁ G₂).fst.obj X) ≫
        ((diagonalPullbackSourceSquare G₁ G₂).fst.map f) := by
  -- Both sides are definitionally the same morphism on the shared first component.
  simp [diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalPullbackSourceSquare]

/-- Helper for Lemma 4.31.12: after projecting to the first factor, the intermediate comparison
is the identity on the original `C`-leg. -/
abbrev diagonal_first_comparison_fst_iso :
    diagonalFirstPullbackComparison G₁ G₂ ⋙ π₁ G₁ G₂ ≅ (diagonalPullbackSourceSquare G₁ G₂).fst :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun {_ _} f ↦ diagonal_first_comparison_fst_iso_naturality (G₁ := G₁) (G₂ := G₂) f)

/-- Helper for Lemma 4.31.12: the second projection of the intermediate comparison functor is also
the original `C`-leg of the diagonal pullback square. -/
theorem diagonal_first_comparison_snd_iso_naturality
    {X Y : DiagonalPullback} (f : X ⟶ Y) :
    (diagonalFirstPullbackComparison G₁ G₂ ⋙ π₂ G₁ G₂).map f ≫
        𝟙 ((diagonalPullbackSourceSquare G₁ G₂).fst.obj Y) =
      𝟙 ((diagonalPullbackSourceSquare G₁ G₂).fst.obj X) ≫
        ((diagonalPullbackSourceSquare G₁ G₂).fst.map f) := by
  -- The second leg was chosen to be the same functor, so the projected morphisms agree.
  simp [diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalPullbackSourceSquare]

/-- Helper for Lemma 4.31.12: after projecting to the second factor, the intermediate comparison
again recovers the original `C`-leg. -/
abbrev diagonal_first_comparison_snd_iso :
    diagonalFirstPullbackComparison G₁ G₂ ⋙ π₂ G₁ G₂ ≅ (diagonalPullbackSourceSquare G₁ G₂).fst :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun {_ _} f ↦ diagonal_first_comparison_snd_iso_naturality (G₁ := G₁) (G₂ := G₂) f)

/-- Helper for Lemma 4.31.12: the first component of the diagonal pullback square identifies
`G₁` of the first leg with the `S`-leg. -/
abbrev diagonal_source_first_component_iso :
    (diagonalPullbackSourceSquare G₁ G₂).fst ⋙ G₁ ≅ (diagonalPullbackSourceSquare G₁ G₂).snd :=
  let Q := diagonalPullbackSourceSquare G₁ G₂
  Functor.isoWhiskerLeft _ (Functor.prod'CompFst G₁ G₂).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight Q.iso (fst S S) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.prod'CompFst (𝟭 S) (𝟭 S)) ≪≫
    Functor.rightUnitor _

/-- Helper for Lemma 4.31.12: the comparison from the diagonal model to the iterated model is
natural after evaluating both product components. -/
theorem diagonal_iterated_pullback_iso_naturality
    {X Y : DiagonalPullback} (f : X ⟶ Y) :
    (diagonalFirstPullbackComparison G₁ G₂ ⋙
          Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)).map f ≫
        𝟙 (((diagonalPullbackSourceSquare G₁ G₂).fst ⋙ Functor.diag C).obj Y) =
      𝟙 (((diagonalPullbackSourceSquare G₁ G₂).fst ⋙ Functor.diag C).obj X) ≫
        ((diagonalPullbackSourceSquare G₁ G₂).fst ⋙ Functor.diag C).map f := by
  -- Both functors are objectwise the same diagonal `(c, c)`; only the packaging differs.
  simp [diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalPullbackSourceSquare]

/-- Helper for Lemma 4.31.12: the diagonal model carries a canonical square over the outer
iterated-pullback cospan. -/
abbrev diagonal_iterated_pullback_iso :
    diagonalFirstPullbackComparison G₁ G₂ ⋙
        Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂) ≅
      (diagonalPullbackSourceSquare G₁ G₂).fst ⋙ Functor.diag C :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun {_ _} f ↦ diagonal_iterated_pullback_iso_naturality (G₁ := G₁) (G₂ := G₂) f)

abbrev diagonalIteratedPullbackSquare :
    CatCommSqOver (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) DiagonalPullback where
  fst := diagonalFirstPullbackComparison G₁ G₂
  snd := (diagonalPullbackSourceSquare G₁ G₂).fst
  iso := diagonal_iterated_pullback_iso G₁ G₂

/-- The canonical comparison functor from the diagonal pullback model
`C ×[(S × S)] S` of Lemma 4.31.12 to the canonical iterated `2`-fibre-product owner
`IteratedPullback = (C ×[S] C) ×[C × C] C`. -/
abbrev categorical_pullback_diagonal_model_comparison :
    DiagonalPullback ⥤ IteratedPullback :=
  (toFunctorToCategoricalPullback (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C)
    DiagonalPullback).obj
    (diagonalIteratedPullbackSquare G₁ G₂)

/-- Helper for Lemma 4.31.12: the first projection of the iterated pullback identifies the inner
left object with the outer object. -/
abbrev iterated_pullback_first_projection_iso :
    π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ≅
      π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) :=
  NatIso.ofComponents
    (fun X ↦ by simpa using (fst C C).mapIso X.iso)
    (fun {_ _} f ↦ by simpa using congrArg _root_.Prod.fst f.w)

/-- Helper for Lemma 4.31.12: the second projection of the iterated pullback identifies the inner
right object with the outer object. -/
abbrev iterated_pullback_second_projection_iso :
    π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₂ G₁ G₂ ≅
      π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) :=
  NatIso.ofComponents
    (fun X ↦ by simpa using (snd C C).mapIso X.iso)
    (fun {_ _} f ↦ by simpa using congrArg _root_.Prod.snd f.w)

/-- Helper for Lemma 4.31.12: the inverse square uses the first outer projection to transport
`G₁(C₃)` back to `G₁(C₁)`. -/
abbrev iterated_pullback_first_component_iso :
    π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ G₁ ≅
      π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁ :=
  Functor.isoWhiskerRight (iterated_pullback_first_projection_iso (G₁ := G₁) (G₂ := G₂)).symm G₁

/-- Helper for Lemma 4.31.12: the inverse square uses the second outer projection together with
the inner pullback isomorphism to transport `G₂(C₃)` back to `G₁(C₁)`. -/
abbrev iterated_pullback_second_component_iso :
    π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ G₂ ≅
      π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁ :=
  Functor.isoWhiskerRight (iterated_pullback_second_projection_iso (G₁ := G₁) (G₂ := G₂)).symm
      G₂ ≪≫
    Functor.isoWhiskerLeft
      (π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C))
      (CatCommSq.iso (π₁ G₁ G₂) (π₂ G₁ G₂) G₁ G₂).symm

/-- Helper for Lemma 4.31.12: the inverse square from the iterated pullback model back to the
diagonal model is natural componentwise. -/
theorem iterated_pullback_to_diagonal_iso_naturality
    {X Y : IteratedPullback} (f : X ⟶ Y) :
    (π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙
          G₁.prod' G₂).map f ≫
        (Iso.prod
          ((iterated_pullback_first_component_iso G₁ G₂).app Y)
          ((iterated_pullback_second_component_iso G₁ G₂).app Y)).hom =
      (Iso.prod
          ((iterated_pullback_first_component_iso G₁ G₂).app X)
          ((iterated_pullback_second_component_iso G₁ G₂).app X)).hom ≫
        ((π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁) ⋙
            Functor.diag S).map f := by
  -- Route correction: after evaluating the product components, the two identities are exactly the
  -- inverse naturality equations for the outer and inner pullback structure morphisms.
  ext
  · -- The first coordinate is just the first inverse outer transport, mapped through `G₁`.
    simpa [Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ G₁.map t) (congrArg _root_.Prod.fst f.w')
  · -- The second coordinate combines the second inverse outer transport with the inverse
    -- naturality of the inner pullback structural isomorphism.
    have houter :
        G₂.map f.snd ≫ G₂.map Y.iso.inv.2 =
          G₂.map X.iso.inv.2 ≫ G₂.map f.fst.snd := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (fun t ↦ G₂.map t) (congrArg _root_.Prod.snd f.w')
    have hinner :
        G₂.map f.fst.snd ≫ Y.fst.iso.inv =
          X.fst.iso.inv ≫ G₁.map f.fst.fst := by
      simpa [Category.assoc] using congrArg _root_.Prod.snd f.fst.w'
    have houter' :
        G₂.map f.snd ≫ G₂.map Y.iso.inv.2 ≫ Y.fst.iso.inv =
          (G₂.map X.iso.inv.2 ≫ G₂.map f.fst.snd) ≫ Y.fst.iso.inv := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ Y.fst.iso.inv) houter
    have hinner' :
        (G₂.map X.iso.inv.2 ≫ G₂.map f.fst.snd) ≫ Y.fst.iso.inv =
          G₂.map X.iso.inv.2 ≫ X.fst.iso.inv ≫ G₁.map f.fst.fst := by
      simpa [Category.assoc] using congrArg (fun t ↦ G₂.map X.iso.inv.2 ≫ t) hinner
    simpa [iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
      iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso,
      Category.assoc] using
      (calc
        G₂.map f.snd ≫ G₂.map Y.iso.inv.2 ≫ Y.fst.iso.inv
            = (G₂.map X.iso.inv.2 ≫ G₂.map f.fst.snd) ≫ Y.fst.iso.inv := houter'
        _ = G₂.map X.iso.inv.2 ≫ X.fst.iso.inv ≫ G₁.map f.fst.fst := hinner')

/-- Helper for Lemma 4.31.12: the iterated pullback carries the textbook inverse square back to
the diagonal pullback model. -/
abbrev iterated_pullback_to_diagonal_iso :
    π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ G₁.prod' G₂ ≅
      (π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁) ⋙
        Functor.diag S :=
  NatIso.ofComponents
    (fun X ↦
      Iso.prod
        ((iterated_pullback_first_component_iso G₁ G₂).app X)
        ((iterated_pullback_second_component_iso G₁ G₂).app X))
    (fun {_ _} f ↦ iterated_pullback_to_diagonal_iso_naturality (G₁ := G₁) (G₂ := G₂) f)

/-- Helper for Lemma 4.31.12: the explicit inverse functor obtained from the iterated pullback
square. -/
abbrev iterated_pullback_to_diagonal :
    IteratedPullback ⥤ DiagonalPullback :=
  (toFunctorToCategoricalPullback (G₁.prod' G₂) (Functor.diag S) IteratedPullback).obj
    { fst := π₂ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C)
      snd := π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ⋙ π₁ G₁ G₂ ⋙ G₁
      iso := iterated_pullback_to_diagonal_iso G₁ G₂ }

/-- Helper for Lemma 4.31.12: the unit only changes the `S`-component by the first projection of
the diagonal source square. -/
abbrev diagonal_model_unit_second_component_obj_iso (X : DiagonalPullback) :
    X.snd ≅
      ((categorical_pullback_diagonal_model_comparison G₁ G₂ ⋙
            iterated_pullback_to_diagonal G₁ G₂).obj X).snd := by
  -- Route correction: package the unit objectwise so the nontrivial part is just the existing
  -- first-component identification from the diagonal source square.
  simpa [categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
    diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalPullbackSourceSquare,
    iterated_pullback_to_diagonal] using
    ((diagonal_source_first_component_iso G₁ G₂).app X).symm

/-- Helper for Lemma 4.31.12: objectwise, the nontrivial unit component is the inverse of the
first coordinate of the diagonal pullback structure isomorphism. -/
theorem diagonal_model_unit_second_component_obj_iso_hom (X : DiagonalPullback) :
    (diagonal_model_unit_second_component_obj_iso (G₁ := G₁) (G₂ := G₂) X).hom = X.iso.inv.1 := by
  simp [diagonal_model_unit_second_component_obj_iso,
    categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
    diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalPullbackSourceSquare,
    iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
    iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
    iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso]

/-- Helper for Lemma 4.31.12: after comparing to the iterated model and back, the resulting
diagonal structural map is the original one with the first coordinate normalized to the identity. -/
theorem diagonal_model_unit_target_iso_hom (X : DiagonalPullback) :
    ((categorical_pullback_diagonal_model_comparison G₁ G₂ ⋙
          iterated_pullback_to_diagonal G₁ G₂).obj X).iso.hom =
      (𝟙 (G₁.obj X.fst), X.iso.hom.2 ≫ X.iso.inv.1) := by
  simp [categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
    diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalPullbackSourceSquare,
    iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
    iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
    iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso,
    Category.assoc]

/-- Helper for Lemma 4.31.12: the unit of the explicit model equivalence. -/
abbrev iterated_pullback_to_diagonal_unitIso :
    𝟭 DiagonalPullback ≅
      categorical_pullback_diagonal_model_comparison G₁ G₂ ⋙
        iterated_pullback_to_diagonal G₁ G₂ := by
  -- Route correction: build the unit objectwise, with the `C`-component definitionally fixed.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine CategoricalPullback.mkIso (.refl _) (diagonal_model_unit_second_component_obj_iso
      (G₁ := G₁) (G₂ := G₂) X) ?_
    -- The pullback compatibility is exactly the diagonal square identity after unfolding.
    rw [diagonal_model_unit_second_component_obj_iso_hom (G₁ := G₁) (G₂ := G₂) X,
      diagonal_model_unit_target_iso_hom (G₁ := G₁) (G₂ := G₂) X]
    ext
    · symm
      have hfst :
          ((diagonal_source_first_component_iso G₁ G₂).app X).hom ≫
              ((diagonal_source_first_component_iso G₁ G₂).app X).inv =
            𝟙 (G₁.obj X.fst) := by
        exact ((diagonal_source_first_component_iso G₁ G₂).app X).hom_inv_id
      simpa [diagonal_source_first_component_iso, Category.assoc] using hfst
    · simp
  · intro X Y f
    -- Naturality is componentwise: the first projection is definitional, and the second is the
    -- naturality of `diagonal_source_first_component_iso`.
    apply CategoricalPullback.hom_ext
    · change f.fst ≫ 𝟙 Y.fst = 𝟙 X.fst ≫ f.fst
      simp
    · simpa [diagonal_model_unit_second_component_obj_iso_hom] using
        congrArg _root_.Prod.fst f.w'

/-- Helper for Lemma 4.31.12: after returning to the diagonal model and comparing back, the inner
pullback structural map is the original one transported along the second outer projection. -/
theorem iterated_pullback_counit_inner_target_iso_hom (X : IteratedPullback) :
    ((iterated_pullback_to_diagonal G₁ G₂ ⋙
          categorical_pullback_diagonal_model_comparison G₁ G₂).obj X).fst.iso.hom =
      G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫ G₂.map X.iso.hom.2 := by
  simp [categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
    diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalPullbackSourceSquare,
    iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
    iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
    iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso]

/-- Helper for Lemma 4.31.12: objectwise, the inverse second outer projection is literally the
second inverse component of the outer pullback isomorphism. -/
theorem iterated_pullback_second_projection_iso_symm_hom (X : IteratedPullback) :
    ((iterated_pullback_second_projection_iso G₁ G₂).app X).symm.hom = X.iso.inv.2 := by
  change ((Prod.snd C C).mapIso X.iso).inv = X.iso.inv.2
  rfl

/-- Helper for Lemma 4.31.12: the inner component of the counit is compatible with the inner
pullback structure. -/
abbrev iterated_pullback_counit_inner_obj_iso (X : IteratedPullback) :
    ((iterated_pullback_to_diagonal G₁ G₂ ⋙
          categorical_pullback_diagonal_model_comparison G₁ G₂).obj X).fst ≅ X.fst := by
  -- The inner pullback is recovered from the two outer projections back to the original `C ×[S] C`
  -- object.
  refine CategoricalPullback.mkIso
      (((iterated_pullback_first_projection_iso G₁ G₂).app X).symm)
      (((iterated_pullback_second_projection_iso G₁ G₂).app X).symm) ?_
  -- After unfolding the composite, this is the original inner pullback relation on `X.fst`.
  rw [iterated_pullback_counit_inner_target_iso_hom (G₁ := G₁) (G₂ := G₂) X]
  rw [iterated_pullback_second_projection_iso_symm_hom (G₁ := G₁) (G₂ := G₂) X]
  calc
    G₁.map X.iso.inv.1 ≫ X.fst.iso.hom
        = G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫ 𝟙 (G₂.obj X.fst.snd) := by simp
    _ = G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫
          G₂.map (X.iso.hom.2 ≫ X.iso.inv.2) := by
      have h₂ : 𝟙 (G₂.obj X.fst.snd) = G₂.map (X.iso.hom.2 ≫ X.iso.inv.2) := by
        symm
        have hsnd : X.iso.hom.2 ≫ X.iso.inv.2 = 𝟙 (X.fst.snd) := by
          exact congrArg _root_.Prod.snd X.iso.hom_inv_id
        simpa [Functor.map_id, ← Functor.map_comp] using
          congrArg (fun t ↦ G₂.map t) hsnd
      simpa [Category.assoc] using congrArg (fun t ↦ G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫ t) h₂
    _ = (G₁.map X.iso.inv.1 ≫ X.fst.iso.hom ≫ G₂.map X.iso.hom.2) ≫ G₂.map X.iso.inv.2 := by
      simp [Category.assoc]

/-- Helper for Lemma 4.31.12: the first component of the inner counit is the inverse first outer
projection. -/
theorem iterated_pullback_counit_inner_obj_iso_fst_hom (X : IteratedPullback) :
    (iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X).hom.fst = X.iso.inv.1 := by
  simp [iterated_pullback_counit_inner_obj_iso, iterated_pullback_first_projection_iso]

/-- Helper for Lemma 4.31.12: the second component of the inner counit is the inverse second outer
projection. -/
theorem iterated_pullback_counit_inner_obj_iso_snd_hom (X : IteratedPullback) :
    (iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X).hom.snd = X.iso.inv.2 := by
  simp [iterated_pullback_counit_inner_obj_iso, iterated_pullback_second_projection_iso]

/-- Helper for Lemma 4.31.12: the inner pullback component of the counit. -/
abbrev iterated_pullback_counit_inner_iso :
    iterated_pullback_to_diagonal G₁ G₂ ⋙ categorical_pullback_diagonal_model_comparison G₁ G₂ ⋙
        π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) ≅
      π₁ (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C) := by
  -- Package the recovered inner pullback objectwise before assembling the full counit.
  refine NatIso.ofComponents
      (fun X ↦ iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X) ?_
  intro X Y f
  -- Naturality is exactly the inverse naturality of the outer structural isomorphism.
  apply CategoricalPullback.hom_ext
  · simpa [iterated_pullback_counit_inner_obj_iso, categorical_pullback_diagonal_model_comparison,
      diagonalIteratedPullbackSquare, diagonalFirstPullbackComparison, diagonalFirstPullbackSquare,
      diagonalPullbackSourceSquare, iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
      iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
      iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso] using
    congrArg _root_.Prod.fst f.w'
  · simpa [iterated_pullback_counit_inner_obj_iso, categorical_pullback_diagonal_model_comparison,
      diagonalIteratedPullbackSquare, diagonalFirstPullbackComparison, diagonalFirstPullbackSquare,
      diagonalPullbackSourceSquare, iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
      iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
      iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso] using
    congrArg _root_.Prod.snd f.w'

/-- Helper for Lemma 4.31.12: the outer component of the counit is definitional. -/
theorem iterated_pullback_to_diagonal_counit_outer_coherence (X : IteratedPullback) :
    (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)).map
        (iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X).hom ≫
      X.iso.hom =
        ((iterated_pullback_to_diagonal G₁ G₂ ⋙
              categorical_pullback_diagonal_model_comparison G₁ G₂).obj X).iso.hom ≫
          (Functor.diag C).map (𝟙 X.snd) := by
  -- The outer component is fixed, so only the inner pullback object needs to be compared.
  simp [iterated_pullback_counit_inner_obj_iso, categorical_pullback_diagonal_model_comparison,
    diagonalIteratedPullbackSquare, diagonalFirstPullbackComparison, diagonalFirstPullbackSquare,
    diagonalPullbackSourceSquare, iterated_pullback_to_diagonal, iterated_pullback_to_diagonal_iso,
    iterated_pullback_first_component_iso, iterated_pullback_second_component_iso,
    iterated_pullback_first_projection_iso, iterated_pullback_second_projection_iso]

/-- Helper for Lemma 4.31.12: the counit of the explicit model equivalence. -/
abbrev iterated_pullback_to_diagonal_counitIso :
    iterated_pullback_to_diagonal G₁ G₂ ⋙ categorical_pullback_diagonal_model_comparison G₁ G₂ ≅
      𝟭 IteratedPullback := by
  -- The counit is again best packaged objectwise: recover the inner pullback and keep the outer
  -- `C`-object fixed.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine CategoricalPullback.mkIso
      (iterated_pullback_counit_inner_obj_iso (G₁ := G₁) (G₂ := G₂) X)
      (.refl _) ?_
    simpa using iterated_pullback_to_diagonal_counit_outer_coherence (G₁ := G₁) (G₂ := G₂) X
  · intro X Y f
    -- Naturality is componentwise: use the inner counit naturality and the definitional outer
    -- identity separately.
    apply CategoricalPullback.hom_ext
    · exact (iterated_pullback_counit_inner_iso (G₁ := G₁) (G₂ := G₂)).hom.naturality f
    · simp [categorical_pullback_diagonal_model_comparison, diagonalIteratedPullbackSquare,
        diagonalFirstPullbackComparison, diagonalFirstPullbackSquare, diagonalPullbackSourceSquare,
        iterated_pullback_to_diagonal]

-- Proof sketch: this is the omitted construction in the Stacks proof. The diagonal pullback model
-- `C ×[(S × S)] S` maps canonically to the iterated `2`-fibre-product owner
-- `(C ×[S] C) ×[C × C] C`.
/-- The model-comparison functor of Lemma 4.31.12 is an equivalence. -/
noncomputable instance categorical_pullback_diagonal_model_comparison_isEquivalence :
    (categorical_pullback_diagonal_model_comparison G₁ G₂).IsEquivalence := by
  -- The inverse functor and the objectwise unit/counit are now explicit, so the equivalence
  -- packaging is immediate once the quasi-inverse data is named explicitly.
  let G := iterated_pullback_to_diagonal G₁ G₂
  let η := iterated_pullback_to_diagonal_unitIso (G₁ := G₁) (G₂ := G₂)
  let ε := iterated_pullback_to_diagonal_counitIso (G₁ := G₁) (G₂ := G₂)
  exact Functor.IsEquivalence.mk' G η ε

variable {C' : Type v} [Category.{v} C'] [IsGroupoid C']
variable (P : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) C')

/-- The comparison functor from a `2`-commutative square over `(G₁.prod' G₂)` and `Δ_S`
to the canonical iterated `2`-fibre product of Lemma 4.31.12. -/
abbrev categorical_pullback_diagonal_comparison
    : C' ⥤ IteratedPullback :=
  (toFunctorToCategoricalPullback (G₁.prod' G₂) (Functor.diag S) C').obj P ⋙
    categorical_pullback_diagonal_model_comparison G₁ G₂

/-- The canonical comparison functor attached to a `2`-fibre product square over
`(G₁.prod' G₂)` and `Δ_S`, expressed through the chapter's owner predicate
`Bicategory.IsFinal`, is an equivalence. -/
noncomputable instance
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (categorical_pullback_diagonal_comparison G₁ G₂ P).IsEquivalence := by
  -- The generic comparison to the diagonal pullback model is already an equivalence by
  -- Lemma 4.31.11, and the model-comparison proved above is another equivalence.
  let _ :
      ((toFunctorToCategoricalPullback (G₁.prod' G₂) (Functor.diag S) C').obj P).IsEquivalence := by
    simpa using (toFunctorToCategoricalPullback_isEquivalence_of_isFinal (Q := P))
  let _ : (categorical_pullback_diagonal_model_comparison G₁ G₂).IsEquivalence := by infer_instance
  infer_instance

/-- Lemma 4.31.12: if
`\mathcal{C}' \to \mathcal{S} \leftarrow \mathcal{C}`
is a `2`-fibre product square for `(G₁.prod' G₂)` and `Δ_S`, then there is a canonical
equivalence to the owner-level iterated `2`-fibre product
`C' ≌ (C ×[S] C) ×[C × C] C`. -/
noncomputable def categorical_pullback_diagonal_square_equivalence
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    C' ≌ IteratedPullback :=
  (categorical_pullback_diagonal_comparison G₁ G₂ P).asEquivalence

/-- The forward functor of `categorical_pullback_diagonal_square_equivalence` is the canonical
comparison functor to the iterated `2`-fibre product owner. -/
-- Proof sketch: unfold `categorical_pullback_diagonal_square_equivalence`; it is defined by
-- `Functor.asEquivalence` on `categorical_pullback_diagonal_comparison G₁ G₂ P`, so the forward
-- functor is exactly that comparison functor.
theorem categorical_pullback_diagonal_square_equivalence_functor
    [Bicategory.IsFinal P.toBicategoricalSquare] :
    (categorical_pullback_diagonal_square_equivalence G₁ G₂ P).functor =
      categorical_pullback_diagonal_comparison G₁ G₂ P := by
  -- Unfolding `Functor.asEquivalence` shows that the forward functor is definitionally the
  -- comparison functor.
  rfl

end

end CategoryTheory.Limits
