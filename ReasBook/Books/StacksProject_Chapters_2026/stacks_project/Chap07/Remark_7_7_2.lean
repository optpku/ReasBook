module

public import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

open Opposite CategoryTheory.Limits

namespace CategoryTheory

/- Domain-style sampling for Remark 7.7.2:
- primary domain: sheaf conditions for presieves and terminal objects in `Type`;
- sampled owner API:
  `Presieve.isTerminal_of_isSheafFor_empty_presieve`,
  `Types.isTerminalEquivUnique`,
  `TopCat.Sheaf.isTerminalOfEmpty`,
  `IsTerminal`;
- owner abstraction: the core/canonical owner is the terminal-object statement for
  `P.obj (op U)`, derived from the source-facing sheaf condition for the empty presieve;
- primitive data: only the presheaf `P`, the object `U`, and the sheaf-condition hypothesis;
- derived API: `Unique`-valued singleton-section reformulations.

Source/core/bridge triage:
- `source-facing`: the remark that the empty-presieve sheaf condition forces a unique section;
- `core/canonical`: `IsTerminal (P.obj (op U))`, already owned upstream by
  `Presieve.isTerminal_of_isSheafFor_empty_presieve`;
- `bridge/view`: the converse theorem below, and the canonical `IsTerminal`-to-`Unique`
  specialization supplied by `Types.isTerminalEquivUnique`.

The local wrapper returning `Unique` directly was duplicate bridge API, so this file keeps the
canonical owner statement and only records the converse direction as a local theorem. -/

/-
Remark 7.7.2: the canonical library-facing form of the remark is the theorem
`Presieve.isTerminal_of_isSheafFor_empty_presieve`, which says that a `Type`-valued presheaf that
is a sheaf for the empty presieve on `U` takes `U` to a terminal object of `Type`.
-/
recall Presieve.isTerminal_of_isSheafFor_empty_presieve

/-- Conversely, if the section type over `U` is a singleton, then a `Type`-valued presheaf is a
sheaf for the empty presieve on `U`. -/
theorem isSheafFor_empty_presieve_of_unique_sections
    {C : Type u} [Category.{v} C] {U : C} (P : Cᵒᵖ ⥤ Type w)
    (hU : Unique (P.obj (op U))) : (⊥ : Presieve U).IsSheafFor P := by
  let _ : Unique (P.obj (op U)) := hU
  intro x hx
  refine ⟨default, ?_, ?_⟩
  · intro Y f hf
    exact False.elim ((bot_apply f).mp hf)
  · intro t _
    exact Subsingleton.elim _ _

/- Companion recall: in `Type`, terminality is canonically equivalent to uniqueness. Combined
with the recalled theorem above, this yields the usual singleton-section reformulation of
Remark 7.7.2 without introducing a second local owner declaration. -/
#check (Types.isTerminalEquivUnique : ∀ X : Type w, IsTerminal X ≃ Unique X)

end CategoryTheory
