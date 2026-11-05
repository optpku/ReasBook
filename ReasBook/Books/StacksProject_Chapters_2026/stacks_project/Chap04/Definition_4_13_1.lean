module

public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C} {f : X ⟶ Y} {g h : Z ⟶ X} {g' h' : Y ⟶ Z}

/- Domain-style sampling for Definition 4.13.1:
- primary domain: categorical monomorphisms and epimorphisms of a morphism.
- inspected owner declarations:
  `Mono`,
  `Epi`,
  `cancel_mono`,
  `cancel_epi`.
- sampled project owner reuse: `stacks_project/Items/Chap12/Definition_12_5_3.lean`
  recalls `Mono` and `Epi` directly.
- owner abstraction: the mathlib classes `Mono f` and `Epi f`.
- primitive data: the owner-class fields `Mono.right_cancellation` and `Epi.left_cancellation`.
- derived API: the textbook cancellation clauses `cancel_mono f` and `cancel_epi f`.

Source/core/bridge triage:
- `source-facing`: the textbook notions of monomorphism and epimorphism together with their
  cancellation properties;
- `core/canonical`: the mathlib owner classes `Mono` and `Epi`;
- `bridge/view`: the cancellation theorems `cancel_mono` and `cancel_epi`.

This numbered item is recall-only at the `core/canonical` layer, so no local wrapper definition
or characterization theorem should be introduced here. -/

/- Definition 4.13.1 (1), owner recall: for a morphism `f : X ⟶ Y`, the textbook notion that `f`
is a monomorphism is exactly the canonical mathlib owner predicate `Mono f`. -/
recall Mono

/- Companion recall: the textbook right-cancellation clause for a monomorphism is the canonical
theorem `cancel_mono`. -/
section

variable [Mono f]

#check (cancel_mono f : g ≫ f = h ≫ f ↔ g = h)

end

/- Definition 4.13.1 (2), owner recall: for a morphism `f : X ⟶ Y`, the textbook notion that `f`
is an epimorphism is exactly the canonical mathlib owner predicate `Epi f`. -/
recall Epi

/- Companion recall: the textbook left-cancellation clause for an epimorphism is the canonical
theorem `cancel_epi`. -/
section

variable [Epi f]

#check (cancel_epi f : f ≫ g' = f ≫ h' ↔ g' = h')

end

end CategoryTheory
