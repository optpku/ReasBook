module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import stacks_project.Chap04.Definition_4_30_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Bicategory
open Limits
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/- Domain-style sampling for Definition 4.31.1:
- `CategoryTheory.Limits.HasTerminal` is the canonical owner abstraction for “there exists a
  terminal object” in a category.
- `CategoryTheory.Limits.IsTerminal` is the canonical owner abstraction for a chosen terminal
  object.
- `CategoryTheory.Limits.IsTerminal.ofUnique` is the canonical constructor when a chosen object is
  shown terminal by a `Unique`-morphism API.
- `CategoryTheory.Bicategory.IsLocallyGroupoid` from Definition `4.30.1` is the project owner
  abstraction for the `(2,1)` condition that every `2`-morphism is invertible.

Primitive-vs-derived split:
- primitive data: for each `y : B`, terminal-object structure on the hom-category `y ⟶ x`.
- derived API: the chosen terminal `1`-morphism `⊤_ (y ⟶ x)`, the canonical comparison
  `2`-morphism `terminal.from _` in each hom-category, the induced uniqueness of `2`-morphisms in
  the locally groupoidal case, and the textbook existence-and-uniqueness reformulation. -/

/- Source/core/bridge triage for Definition 4.31.1:
- `source-facing`: `Bicategory.IsFinal x`.
- `core/canonical`: `HasTerminal (y ⟶ x)` and `IsTerminal f` in the hom-categories.
- `bridge/view`: `Bicategory.isFinal_iff_existsUnique_hom₂`. Its public surface is the Prop-valued
  existence-and-subsingleton restatement, while the reverse construction is driven internally by
  the canonical owner `Unique (f ⟶ g)`. -/

/-- Definition 4.31.1: an object `x` is bicategorically final if every hom-category `y ⟶ x` has a
terminal object. The textbook Stacks definition is only stated for `(2,1)`-categories, but this
owner notion itself is intrinsic to any bicategory. -/
class Bicategory.IsFinal (x : B) : Prop where
  /-- For every object `y`, the hom-category `y ⟶ x` has a terminal object. -/
  hasTerminal (y : B) : HasTerminal (y ⟶ x)

attribute [instance] Bicategory.IsFinal.hasTerminal

/-- A family of terminal hom-categories into `x` packages into bicategorical finality. -/
instance (x : B) [∀ y : B, HasTerminal (y ⟶ x)] : Bicategory.IsFinal x where
  hasTerminal _ := inferInstance

section

variable [IsLocallyGroupoid B]

namespace Bicategory.IsFinal

/-- In a locally groupoidal bicategory, every `1`-morphism into a final object is terminal in the
corresponding hom-category. -/
noncomputable def homIsTerminal {x y : B} [IsFinal x] (f : y ⟶ x) : IsTerminal f :=
  IsTerminal.ofIso terminalIsTerminal (asIso (terminal.from f)).symm

end Bicategory.IsFinal

/-- Any pair of `1`-morphisms into a final object has a unique `2`-morphism between them. -/
noncomputable instance {x y : B} [IsFinal x] (f g : y ⟶ x) : Unique (f ⟶ g) :=
  (isTerminalEquivUnique (Functor.empty (y ⟶ x)) g).toFun (IsFinal.homIsTerminal g) f

namespace Bicategory

/-- Definition 4.31.1 in textbook form: if every `2`-morphism is invertible, then `x` is final iff
for each object `y` there is a `1`-morphism `y ⟶ x`, and between any two such `1`-morphisms there
is a unique `2`-morphism. In the Stacks `(2,1)`-category setting, this local-groupoid hypothesis is
automatic, while strictness does not enter the statement. The theorem is Prop-valued, so the
existence-and-uniqueness clause is stated as `Nonempty` plus `Subsingleton`, while the reverse
construction uses the canonical owner `Unique (f ⟶ g)` internally. -/
theorem isFinal_iff_existsUnique_hom₂ (x : B) :
    IsFinal x ↔
      ∀ y : B, Nonempty (y ⟶ x) ∧
        ∀ f g : y ⟶ x, Nonempty (f ⟶ g) ∧ Subsingleton (f ⟶ g) := by
  constructor
  · intro _ y
    refine ⟨⟨⊤_ (y ⟶ x)⟩, ?_⟩
    intro f g
    let _ : Unique (f ⟶ g) := inferInstance
    exact ⟨⟨default⟩, inferInstance⟩
  · intro hx
    classical
    refine ⟨fun y ↦ ?_⟩
    rcases (hx y).1 with ⟨f⟩
    letI : ∀ g : y ⟶ x, Nonempty (g ⟶ f) := fun g ↦ ((hx y).2 g f).1
    letI : ∀ g : y ⟶ x, Subsingleton (g ⟶ f) := fun g ↦ ((hx y).2 g f).2
    exact hasTerminal_of_unique f

end Bicategory

end

end CategoryTheory
