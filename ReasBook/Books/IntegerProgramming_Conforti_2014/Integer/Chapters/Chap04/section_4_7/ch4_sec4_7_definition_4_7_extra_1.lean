import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section Definition_4_7_extra_1

variable {β α : Type*} [Lattice β] [Preorder α] [Add α]

/-- Definition 4.7-extra-1, in its canonical lattice form. A function is submodular if it satisfies
the meet-join inequality `f (x ⊓ y) + f (x ⊔ y) ≤ f x + f y` for all `x` and `y`. -/
def Submodular (f : β → α) : Prop :=
  ∀ x y : β, f (x ⊓ y) + f (x ⊔ y) ≤ f x + f y

/-- Textbook orientation of the submodularity inequality. -/
theorem submodular_iff_ge (f : β → α) :
    Submodular f ↔
      ∀ x y : β, f x + f y ≥ f (x ⊓ y) + f (x ⊔ y) :=
  Iff.rfl

section Finset

variable {ι : Type*} [DecidableEq ι]

/-- Definition 4.7-extra-1 specialized to set functions on finite subsets. -/
theorem submodular_finset_iff (f : Finset ι → α) :
    Submodular f ↔
      ∀ S T : Finset ι, f (S ∩ T) + f (S ∪ T) ≤ f S + f T :=
  Iff.rfl

/-- Source-facing restatement of Definition 4.7-extra-1 in the textbook inequality orientation. -/
theorem submodular_finset_iff_ge (f : Finset ι → α) :
    Submodular f ↔
      ∀ S T : Finset ι, f S + f T ≥ f (S ∩ T) + f (S ∪ T) :=
  Iff.rfl

end Finset

end Definition_4_7_extra_1
