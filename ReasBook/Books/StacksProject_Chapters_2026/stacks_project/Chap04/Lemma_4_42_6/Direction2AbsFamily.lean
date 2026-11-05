module

public import stacks_project.Chap04.Lemma_4_42_6.SliceRepresentable
public import stacks_project.Chap04.Lemma_4_42_6.Direction2Family

@[expose] public section

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)

variable {C : Type (max u v)} [Category.{v} C]

/-- Lightweight absolute two-fibre-product representability for two maps to the same target. -/
@[irreducible] noncomputable def absoluteTfpRep
    {A B T : FibredInGroupoidsOver C} (F : A ⟶ T) (G : B ⟶ T) : Prop :=
  (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable

/-- Package raw absolute two-fibre-product representability. -/
opaque absoluteTfpRep_of_isRepresentable
    {A B T : FibredInGroupoidsOver C} (F : A ⟶ T) (G : B ⟶ T) :
    (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable → absoluteTfpRep F G := by
  intro h
  unfold absoluteTfpRep
  exact h

/-- Unpack raw absolute two-fibre-product representability. -/
opaque absoluteTfpRep_to_isRepresentable
    {A B T : FibredInGroupoidsOver C} (F : A ⟶ T) (G : B ⟶ T) :
    absoluteTfpRep F G → (FibredInGroupoidsOver.twoFibreProduct F G).IsRepresentable := by
  intro h
  unfold absoluteTfpRep at h
  exact h

/-- Absolute tests for a morphism, expressed through `absoluteTfpRep`. -/
noncomputable def absoluteTfpFamily
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) : Prop :=
  ∀ ⦃W : C⦄ (H : ofFunctor (Over.forget W) ⟶ Y), absoluteTfpRep H F

/-- Build the wrapped absolute `absoluteTfpRep` testing family. -/
opaque absoluteTfpFamily_of_forall
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) :
    (∀ ⦃W : C⦄ (H : ofFunctor (Over.forget W) ⟶ Y), absoluteTfpRep H F) →
    absoluteTfpFamily F := by
  intro h
  unfold absoluteTfpFamily
  exact h

/-- Evaluate the wrapped absolute `absoluteTfpRep` testing family. -/
opaque absoluteTfpFamily_apply
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y)
    (hF : absoluteTfpFamily F)
    {W : C} (H : ofFunctor (Over.forget W) ⟶ Y) :
    absoluteTfpRep H F := by
  unfold absoluteTfpFamily at hF
  exact hF H

/-- Convert `absoluteTfpRep` tests into the lightweight slice-testing family. -/
opaque absoluteTfpFamily_to_isRepresentableFamily
    [Limits.HasPullbacks C]
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) :
    absoluteTfpFamily F → FibredInGroupoidsMor.IsRepresentableFamily F := by
  intro hAbs
  refine FibredInGroupoidsMor.isRepresentableFamily_of_forall F ?_
  intro W H
  apply (isRepresentable_iff_absolutize_isRepresentable _).mpr
  have hAt := absoluteTfpFamily_apply F hAbs H
  exact absolutize_sliceTwoFibreProduct_isRepresentable_of_twoFibreProduct F H
    (absoluteTfpRep_to_isRepresentable H F hAt)

/-- Convert `absoluteTfpRep` tests into ordinary representability. -/
opaque absoluteTfpFamily_to_isRepresentable
    [Limits.HasPullbacks C]
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) :
    absoluteTfpFamily F → FibredInGroupoidsMor.IsRepresentable F := by
  intro hAbs
  exact FibredInGroupoidsMor.isRepresentable_of_isRepresentableFamily F
    (absoluteTfpFamily_to_isRepresentableFamily F hAbs)

/-- Absolute `absoluteTfpRep` testing family specialized to the diagonal. -/
@[irreducible] noncomputable def diagonalTfpFamily
    (X : FibredInGroupoidsOver C) : Prop :=
  ∀ ⦃W : C⦄
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection),
    absoluteTfpRep H (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)

/-- Build the diagonal-specific testing family from the family of absolute tests.  Kept here (where
`twoFibreProduct` is transparent) so consumers never have to `unfold diagonalTfpFamily` on a goal,
which would re-form the bundled `absoluteTfpRep` target and overflow whnf. -/
opaque diagonalTfpFamily_of_forall
    (X : FibredInGroupoidsOver C) :
    (∀ ⦃W : C⦄
      (H : ofFunctor (Over.forget W) ⟶
        FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection),
      absoluteTfpRep H (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)) →
    diagonalTfpFamily X := by
  intro h
  unfold diagonalTfpFamily
  exact h

/-- Convert the diagonal-specific testing family into the generic absolute testing family. -/
opaque diagonalTfpFamily_to_absoluteTfpFamily
    (X : FibredInGroupoidsOver C) :
    diagonalTfpFamily X →
      absoluteTfpFamily (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) := by
  intro h
  refine absoluteTfpFamily_of_forall
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) ?_
  intro W H
  unfold diagonalTfpFamily at h
  exact h H

/-- Convert the diagonal-specific testing family into representability of the diagonal. -/
opaque diagonalTfpFamily_to_isRepresentable
    [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C) :
    diagonalTfpFamily X →
      FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) := by
  intro h
  exact absoluteTfpFamily_to_isRepresentable
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)
    (diagonalTfpFamily_to_absoluteTfpFamily X h)

/-- One absolute test for a morphism of fibred groupoids. -/
@[irreducible] noncomputable def absoluteRepresentableAt
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y)
    {W : C} (H : ofFunctor (Over.forget W) ⟶ Y) : Prop :=
  (FibredInGroupoidsOver.twoFibreProduct H F).IsRepresentable

/-- Absolute testing family for a morphism of fibred groupoids. -/
noncomputable def absoluteRepresentableFamily
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) : Prop :=
  ∀ ⦃W : C⦄ (H : ofFunctor (Over.forget W) ⟶ Y),
    absoluteRepresentableAt F H

/-- Package a raw absolute test at one slice morphism. -/
opaque absoluteRepresentableAt_of_isRepresentable
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y)
    {W : C} (H : ofFunctor (Over.forget W) ⟶ Y) :
    (FibredInGroupoidsOver.twoFibreProduct H F).IsRepresentable →
      absoluteRepresentableAt F H := by
  intro h
  unfold absoluteRepresentableAt
  exact h

/-- Unpack a raw absolute test at one slice morphism. -/
opaque absoluteRepresentableAt_to_isRepresentable
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y)
    {W : C} (H : ofFunctor (Over.forget W) ⟶ Y) :
    absoluteRepresentableAt F H →
      (FibredInGroupoidsOver.twoFibreProduct H F).IsRepresentable := by
  intro h
  unfold absoluteRepresentableAt at h
  exact h

/-- Build the wrapped absolute testing family from wrapped tests. -/
opaque absoluteRepresentableFamily_of_forall
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) :
    (∀ ⦃W : C⦄ (H : ofFunctor (Over.forget W) ⟶ Y),
      absoluteRepresentableAt F H) →
    absoluteRepresentableFamily F := by
  intro h
  unfold absoluteRepresentableFamily
  exact h

/-- Evaluate the wrapped absolute testing family. -/
opaque absoluteRepresentableFamily_apply
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y)
    (hF : absoluteRepresentableFamily F)
    {W : C} (H : ofFunctor (Over.forget W) ⟶ Y) :
    absoluteRepresentableAt F H := by
  unfold absoluteRepresentableFamily at hF
  exact hF H

/-- Convert absolute tests into the lightweight slice-testing family. -/
opaque absoluteRepresentableFamily_to_isRepresentableFamily
    [Limits.HasPullbacks C]
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) :
    absoluteRepresentableFamily F → FibredInGroupoidsMor.IsRepresentableFamily F := by
  intro hAbs
  refine FibredInGroupoidsMor.isRepresentableFamily_of_forall F ?_
  intro W H
  apply (isRepresentable_iff_absolutize_isRepresentable _).mpr
  have hAt := absoluteRepresentableFamily_apply F hAbs H
  exact absolutize_sliceTwoFibreProduct_isRepresentable_of_twoFibreProduct F H
    (absoluteRepresentableAt_to_isRepresentable F H hAt)

/-- Convert absolute tests into ordinary representability. -/
opaque absoluteRepresentableFamily_to_isRepresentable
    [Limits.HasPullbacks C]
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) :
    absoluteRepresentableFamily F → FibredInGroupoidsMor.IsRepresentable F := by
  intro hAbs
  exact FibredInGroupoidsMor.isRepresentable_of_isRepresentableFamily F
    (absoluteRepresentableFamily_to_isRepresentableFamily F hAbs)

end CategoryTheory
