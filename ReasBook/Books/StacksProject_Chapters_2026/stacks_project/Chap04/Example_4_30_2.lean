module

public import Mathlib.CategoryTheory.Category.Cat
public import stacks_project.Chap04.Definition_4_30_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

private theorem core_isoMk_eqToIso {C : Type u} [Category.{v} C] {x y : Core C} (e : x.of = y.of) :
    Core.isoMk (eqToIso e) = eqToIso (congrArg Core.mk e) := by
  cases x
  cases y
  cases e
  rfl

namespace Bicategory.Pith

variable {B : Type u} [Bicategory.{w, v} B] [Strict B]

/-- If a bicategory is strict, then its pith is strict as well. -/
instance strict : Strict (Pith B) where
  id_comp f := by
    exact congrArg Core.mk (Strict.id_comp f.of)
  comp_id f := by
    exact congrArg Core.mk (Strict.comp_id f.of)
  assoc f g h := by
    exact congrArg Core.mk (Strict.assoc f.of g.of h.of)
  leftUnitor_eqToIso f := by
    change Core.isoMk (λ_ f.of) = eqToIso (congrArg Core.mk (Strict.id_comp f.of))
    refine (congrArg Core.isoMk (Strict.leftUnitor_eqToIso f.of)).trans ?_
    exact core_isoMk_eqToIso (Strict.id_comp f.of)
  rightUnitor_eqToIso f := by
    change Core.isoMk (ρ_ f.of) = eqToIso (congrArg Core.mk (Strict.comp_id f.of))
    refine (congrArg Core.isoMk (Strict.rightUnitor_eqToIso f.of)).trans ?_
    exact core_isoMk_eqToIso (Strict.comp_id f.of)
  associator_eqToIso f g h := by
    change Core.isoMk (α_ f.of g.of h.of) = eqToIso (congrArg Core.mk (Strict.assoc f.of g.of h.of))
    refine (congrArg Core.isoMk (Strict.associator_eqToIso f.of g.of h.of)).trans ?_
    exact core_isoMk_eqToIso (Strict.assoc f.of g.of h.of)

end Bicategory.Pith

/- Example 4.30.2: categories, functors, and natural isomorphisms are formalized by the canonical
bridge/view `Pith Cat`. Since `Cat` is strict, the bridge carries the strictness half of
Definition 4.30.1 as well. -/
#check Pith Cat.{v, u}

/- The pith bridge for `Cat` is strict. -/
#check (inferInstance : Strict (Pith Cat.{v, u}))

/- The pith bridge for `Cat` is locally groupoidal, so together with strictness it realizes the
Stacks `(2,1)`-category example. -/
#check (inferInstance : IsLocallyGroupoid (Pith Cat.{v, u}))

end CategoryTheory
