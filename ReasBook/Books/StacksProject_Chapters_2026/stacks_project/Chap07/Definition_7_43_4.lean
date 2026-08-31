module

public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory

/- Domain-style sampling for Definition 7.43.4:
- primary domain: open subtopoi of a sheaf topos arising from slice-topos inclusions at
  subterminal sheaves;
- sampled owner API:
  `IsSubterminal`,
  `IsSubterminal.mono_terminal_from`,
  `isSubterminal_of_mono_terminal_from`,
  `Functor.essImage`;
- best owner abstraction: the source-facing predicate `IsOpenSubtopos` on object properties of
  `Sheaf J (Type w)`, with `IsSubterminal U` as the canonical owner of the witness that `U` is
  subterminal;
- primitive data: a subterminal sheaf `U` and the induced object property `(Over.forget U).essImage`;
- derived API: the bridge-view reformulation via `Mono (terminal.from U)`, supplied canonically by
  mathlib's subterminal-object API.

Source/core/bridge triage:
- `source-facing`: `IsOpenSubtopos`;
- `core/canonical`: `IsSubterminal` and `Functor.essImage`;
- `bridge/view`: `Mono (terminal.from U)` via the equivalence between subterminal objects and
  monomorphisms to the terminal object. -/
/-- Definition 7.43.4: a subtopos of `Sh(C)` is open if it is the essential image of the
slice-topos inclusion `Sh(C)/U ⥤ Sh(C)` for some subterminal sheaf `U`. -/
def IsOpenSubtopos
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ U : Sheaf J (Type w), IsSubterminal U ∧ P = (Over.forget U).essImage

/-- An object property on `Sh(C)` is an open subtopos exactly when it is the essential image of
the slice-topos inclusion at a subterminal sheaf. -/
-- Proof sketch: unfold `IsOpenSubtopos`; this is the defining existential characterization.
theorem isOpenSubtopos_iff_exists_subterminal
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : ObjectProperty (Sheaf J (Type w))) :
    IsOpenSubtopos P ↔ ∃ U : Sheaf J (Type w), IsSubterminal U ∧ P = (Over.forget U).essImage :=
  by
  -- Unfold the predicate so the goal becomes the defining existential characterization.
  rfl

end CategoryTheory
