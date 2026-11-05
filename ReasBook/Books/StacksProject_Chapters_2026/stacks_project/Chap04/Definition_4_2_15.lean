module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.NatTrans
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

/- Domain-style sampling for Definition 4.2.15:
- primary domain: functor categories and natural transformations in `CategoryTheory`.
- inspected owner declarations: `NatTrans`, `NatTrans.app`, `NatTrans.naturality`, and the chapter's
  based analogue `BasedNatTrans`.
- best owner abstraction: `NatTrans`; the textbook components and naturality square are primitive
  data of this owner, not local wrapper data.
- primitive-vs-derived split:
  primitive data: the component family `t.app` together with `t.naturality`, already owned
    upstream by `NatTrans`.
  derived API kept here: only the source-facing `CommSq` view `NatTrans.commSq` of
    `t.naturality f`. -/

/- Source/core/bridge triage for Definition 4.2.15:
- source-facing: the textbook description of a natural transformation by components and commuting
  squares.
- core/canonical: `NatTrans`.
- bridge/view: `NatTrans.commSq`, the `CommSq` packaging of `t.naturality f`. -/

/-
Definition 4.2.15: a natural transformation, or morphism of functors, between functors
`F G : C ⥤ D` is the canonical mathlib structure `NatTrans`, written `F ⟶ G`.
Its components are the morphisms `t.app X : F.obj X ⟶ G.obj X`.
-/
recall NatTrans

/- Definition 4.2.15: the component of a natural transformation `t : F ⟶ G` at `X`
is the canonical morphism `t.app X : F.obj X ⟶ G.obj X`. -/
recall NatTrans.app

/- For `t : F ⟶ G`, the commutative square in the textbook definition is exactly the built-in
naturality statement `t.naturality f`. -/
recall NatTrans.naturality

namespace NatTrans

/-- Bridge/view companion: the textbook commutative square is the canonical naturality identity
packaged as a `CommSq`. -/
theorem commSq {X Y : C} (t : F ⟶ G) (f : X ⟶ Y) :
    CommSq (F.map f) (t.app X) (t.app Y) (G.map f) :=
  ⟨t.naturality f⟩

end NatTrans

end CategoryTheory
