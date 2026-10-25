module

public import Mathlib.CategoryTheory.Limits.Types.Shapes
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory

/- Domain-style sampling for Definition 7.43.6:
- primary domain: closed subtopoi of a sheaf topos, cut out by a subterminal sheaf and described
  pointwise by the canonical product projection;
- sampled owner API:
  `IsSubterminal`,
  `IsSubterminal.mono_terminal_from`,
  `isSubterminal_of_mono_terminal_from`,
  `Functor.essImage`;
- best owner abstraction: the source-facing predicate `IsClosedSubtopos` on object properties of
  `Sheaf J (Type w)`, with `IsSubterminal U` as the canonical owner of the witness that `U` is
  subterminal;
- primitive data: a subterminal sheaf `U` and the induced object property
  `fun G ↦ IsIso (prod.fst : U ⨯ G ⟶ U)`;
- derived API: the bridge to `IsSubtopos` in the later chapter lemma.

Source/core/bridge triage:
- `source-facing`: `IsClosedSubtopos`;
- `core/canonical`: `IsSubterminal`;
- `bridge/view`: the later comparison theorem upgrading a closed subtopos to a subtopos. -/
/-- Definition 7.43.6: a subtopos of `Sh(C)` is closed if it consists of the sheaves `G` for
which `U × G ⟶ U` is an isomorphism for some subterminal sheaf `U`. -/
def IsClosedSubtopos
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ U : Sheaf J (Type w), IsSubterminal U ∧
    P = fun G ↦ IsIso (prod.fst : U ⨯ G ⟶ U)

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

-- Proof sketch: unfold `IsClosedSubtopos` and return the subterminal sheaf witness together with
-- the defining equality of the object property.
/-- A closed subtopos is presented by a subterminal sheaf whose first projection detects exactly
the objects lying in the subtopos. -/
theorem IsClosedSubtopos.exists_subterminal
    {P : ObjectProperty (Sheaf J (Type w))} (hP : IsClosedSubtopos P) :
    ∃ U : Sheaf J (Type w), IsSubterminal U ∧
      P = fun G ↦ IsIso (prod.fst : U ⨯ G ⟶ U) := by
  -- Unfold the definition to expose the subterminal witness that already defines a closed subtopos.
  simpa [IsClosedSubtopos] using hP

end

end CategoryTheory
