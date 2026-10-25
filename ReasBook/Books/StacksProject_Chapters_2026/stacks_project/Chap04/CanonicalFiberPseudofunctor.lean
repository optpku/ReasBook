module

public import stacks_project.Chap04.CanonicalFiberPseudofunctor.Coherence

@[expose] public section

/-!
# Canonical fiber pseudofunctor owner

This is the real public owner for the slim Chapter 4 surface used downstream: the comparison and
coherence package lives under `Chap04.CanonicalFiberPseudofunctor`, and this file exposes the
canonical pseudofunctor attached to the canonical pullback choice.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-- The canonical pseudofunctor of fibers attached to a fibred category, obtained from the
canonical pullback choice on the projection functor. This is the standard bridge from the slim
owner `canonicalPullbackChoice p` to the pseudofunctor surface used downstream. -/
noncomputable abbrev canonicalFiberPseudofunctor
    (p : S ⥤ C) [p.IsFibered] :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  -- The public bridge now points directly to the slim coherence owner.
  (canonicalPullbackChoice p).fiberPseudofunctor

end CategoryTheory
