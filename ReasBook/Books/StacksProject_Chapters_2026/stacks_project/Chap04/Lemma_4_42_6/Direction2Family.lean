module

public import stacks_project.Chap04.Lemma_4_42_6.Direction2Aux

@[expose] public section

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)

variable {C : Type (max u v)} [Category.{v} C]

namespace FibredInGroupoidsMor

/-- Helper for Lemma 4.42.6: a lightweight family form of
`FibredInGroupoidsMor.IsRepresentable`, kept irreducible so downstream direction `(2) -> (1)`
can pass the testing family without repeatedly unfolding the slice target. -/
@[irreducible] noncomputable def IsRepresentableFamily
    {X Y : FibredInGroupoidsOver C}
    (F : FibredInGroupoidsMor X Y) : Prop :=
  ∀ ⦃U : C⦄ (G : ofFunctor (Over.forget U) ⟶ Y),
    (sliceTwoFibreProduct F G).IsRepresentable

/-- Helper for Lemma 4.42.6: build morphism representability from the lightweight
slice-testing family. -/
opaque isRepresentable_of_isRepresentableFamily
    {X Y : FibredInGroupoidsOver C}
    (F : FibredInGroupoidsMor X Y) :
    IsRepresentableFamily F → F.IsRepresentable := by
  intro h
  unfold IsRepresentableFamily at h
  exact h

/-- Helper for Lemma 4.42.6: build the lightweight slice-testing family from the raw
testing function. -/
opaque isRepresentableFamily_of_forall
    {X Y : FibredInGroupoidsOver C}
    (F : FibredInGroupoidsMor X Y) :
    (∀ ⦃U : C⦄ (G : ofFunctor (Over.forget U) ⟶ Y),
      (sliceTwoFibreProduct F G).IsRepresentable) →
    IsRepresentableFamily F := by
  intro h
  unfold IsRepresentableFamily
  exact h

end FibredInGroupoidsMor

end CategoryTheory
