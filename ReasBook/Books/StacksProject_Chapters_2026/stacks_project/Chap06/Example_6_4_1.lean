module

public import stacks_project.Chap06.Definition_6_3_2
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TopCat

universe u v

variable (X : TopCat.{u})

/- Domain-style sampling for Example 6.4.1:
- primary domain: set-valued presheaves on a topological space;
- sampled owner API:
  `((PUnit : Type v) ₚ X : X.Presheaf (Type v))`,
  `Functor.isTerminalConst`,
  `Types.isTerminalPUnit`,
  `IsTerminal`;
- source/core/bridge triage:
  `source-facing`: the singleton-valued constant presheaf on `X`;
  `core/canonical`: `Functor.isTerminalConst`;
  `bridge/view`: the specialization of the generic constant-functor owner to presheaves on `X`.

Primitive data are only the constant presheaf and the terminal object `PUnit` of `Type v`. The
terminality statement is derived API from `Functor.isTerminalConst`, so this example should use
that specialization directly rather than introducing a parallel local instance.
-/
/- Example 6.4.1: the constant singleton-valued presheaf on `X` is terminal in the category of
set-valued presheaves on `X`. This is the `PUnit` specialization of the canonical owner
`Functor.isTerminalConst`. -/
recall Functor.isTerminalConst

/-
Example 6.4.1 source-facing specialization: applying the owner theorem to the terminal object
`PUnit` of `Type v` gives that the constant singleton-valued presheaf is terminal.
-/
#check
  (Functor.isTerminalConst (Opens X)ᵒᵖ Types.isTerminalPUnit :
    IsTerminal ((PUnit : Type v) ₚ X))
