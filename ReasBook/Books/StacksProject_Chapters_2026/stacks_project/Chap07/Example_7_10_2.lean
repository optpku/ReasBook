module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_3_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

namespace TerminalPresheaf

/- Lean surface notation for the singleton terminal presheaf `*`. We write `*ₚ[C]` to keep the
presheaf and sheaf surfaces distinct while still exposing the source-facing star notation. -/
set_option quotPrecheck false in
scoped notation:max "*ₚ[" C "]" => (Functor.const Cᵒᵖ).obj PUnit

end TerminalPresheaf

namespace TerminalSheaf

/- Lean surface notation for the singleton terminal sheaf `*` on the site `(C, J)`. -/
scoped notation:max "*[" J "]" => Sheaf.terminal J Types.isTerminalPUnit

end TerminalSheaf

open scoped TerminalPresheaf TerminalSheaf

/- Domain-style sampling for Example 7.10.2:
- primary domain: terminal objects in presheaf and sheaf categories on a Grothendieck site;
- sampled owner API:
  `Functor.isTerminalConst`,
  `Presheaf.isSheaf_of_isTerminal`,
  `Sheaf.terminal`,
  `Sheaf.isTerminalTerminal`;
- best owner abstraction: the terminal-object owner API for the constant presheaf and the induced
  terminal sheaf on `(C, J)`, with source-facing `*` notation implemented directly as scoped
  notation over those canonical constructions;
- source/core/bridge triage:
  `source-facing`: the singleton-valued presheaf `*ₚ[C]` and sheaf `*[J]`;
  `core/canonical`: `Functor.isTerminalConst`, `Presheaf.isSheaf_of_isTerminal`,
    `Sheaf.terminal`, and `Sheaf.isTerminalTerminal`;
  `bridge/view`: the scoped notation `*ₚ[C]` and `*[J]`, which expose the source-facing star
  surface directly over the owner-level canonical constructions.

- primitive data: only the terminal object `PUnit` in `Type _`;
- derived API: terminality in presheaves, the sheaf condition, the bundled terminal sheaf, and its
  terminality in `Sheaf J (Type _)`.

The only new declarations below are the scoped notations `*ₚ[C]` and `*[J]`, exposing the
recurring source-facing object `*` without introducing parallel owner names.
-/
/- Example 7.10.2: the constant singleton-valued presheaf on `C` is terminal in the presheaf
category. This is owned canonically by `Functor.isTerminalConst`. -/
recall Functor.isTerminalConst

/- Companion specialization: the terminal presheaf `*ₚ[C]` is the constant presheaf with value
`PUnit`. -/
#check (show IsTerminal *ₚ[C] from Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit)

/- Example 7.10.2: because a terminal presheaf is a sheaf, the constant singleton-valued
presheaf satisfies the sheaf condition for every Grothendieck topology `J`. This is owned
canonically by `Presheaf.isSheaf_of_isTerminal`. -/
recall Presheaf.isSheaf_of_isTerminal

/- Companion specialization: the terminal presheaf `*ₚ[C]` is a sheaf on `(C, J)`. -/
#check (show Presheaf.IsSheaf J *ₚ[C] from Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)

/- Example 7.10.2: the sheaf `*[J]` is the canonical terminal singleton sheaf on `(C, J)`. -/
recall Sheaf.terminal

/- Companion specialization: on the site `(C, J)`, the singleton sheaf `*[J]` is the canonical
terminal sheaf. -/
#check (*[J] : Sheaf J (Type (max u v)))

/- Example 7.10.2: the sheaf `*[J]` is terminal in the category of sheaves on the site `(C, J)`.
This is owned canonically by
`Sheaf.isTerminalTerminal`. -/
recall Sheaf.isTerminalTerminal

/- Companion specialization: the singleton sheaf `*[J]` is terminal in `Sheaf J (Type _)`. -/
#check (show IsTerminal *[J] from Sheaf.isTerminalTerminal J Types.isTerminalPUnit)

end CategoryTheory
