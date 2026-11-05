module

public import Mathlib.CategoryTheory.Iso
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/- Domain-style sampling for Definition 4.2.4 (isomorphisms in a category):
- primary domain: invertible morphisms in an arbitrary category;
- sampled owner declarations: `IsIso`, `IsIso.out`, `IsIso.mk`, `asIso`;
- primitive data: the existence of a two-sided inverse for a morphism;
- derived API: the chosen inverse `inv`, the bundled isomorphism `asIso`, and the inverse
  identities;
- layer triage:
  - `source-facing`: the textbook inverse criterion for a morphism;
  - `core/canonical`: `IsIso`;
  - `bridge/view`: the constructor/field pair `IsIso.mk` and `IsIso.out`, which expose the
    source inverse criterion without introducing a parallel owner. -/

/- Definition 4.2.4: a morphism in a category is an isomorphism precisely when it admits a
two-sided inverse. This source notion is the canonical mathlib predicate `IsIso`. -/
recall IsIso

/- Source-facing inverse criterion, forward direction: from `IsIso f`, the field `IsIso.out`
extracts a morphism `g : Y ⟶ X` with `f ≫ g = 𝟙 X` and `g ≫ f = 𝟙 Y`. -/
recall IsIso.out

/- Source-facing inverse criterion, converse direction: a two-sided inverse for `f` yields the
canonical instance `IsIso f` via `IsIso.mk`. -/
recall IsIso.mk

end CategoryTheory
