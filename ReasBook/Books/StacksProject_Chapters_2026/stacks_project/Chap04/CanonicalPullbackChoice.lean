module

public import stacks_project.Chap04.Definition_4_33_6
public import Mathlib.CategoryTheory.FiberedCategory.HasFibers
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-- The canonical chosen pullback system on a fibred category, obtained from the canonical fiber
categories and pullback maps supplied by `HasFibers.canonical`. This is the thin Chapter 4 owner
for the raw chosen pullback data used by later files that do not need the full coherence package
from Lemma 4.33.7. -/
noncomputable abbrev canonicalPullbackChoice
    (p : S ⥤ C) [p.IsFibered] :
    PullbackChoice p :=
  let _ : HasFibers p := HasFibers.canonical p
  { obj := fun f x ↦ HasFibers.mkPullback f x.2
    map := fun f x ↦ HasFibers.pullbackMap f x.2
    isStronglyCartesian := fun f x ↦
      Functor.IsFibered.isStronglyCartesian_of_isCartesian p f (HasFibers.pullbackMap f x.2) }

end CategoryTheory
