module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Example_7_10_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Limits
open scoped TerminalPresheaf

variable {C : Type u} [Category.{v} C]
variable (ℱ : Presheaf C)

/-
Domain-style sampling for Definition 7.45.1:
- primary domain: set-valued presheaves and their global sections;
- sampled owner API:
  `Presheaf`,
  `Functor.sectionsEquivHom`,
  `Functor.sections`,
  `Functor.isTerminalConst`,
  `Types.isTerminalPUnit`;
- best owner abstraction: `Functor.sections` is the canonical owner of global sections for a
  `Type`-valued presheaf, and the source formula
  `Γ(\mathcal C, \mathcal F) = \operatorname{Mor}_{PSh(\mathcal C)}(*, \mathcal F)` is its
  canonical bridge `Functor.sectionsEquivHom`;
- primitive data: only the presheaf `ℱ : Presheaf C`;
- derived API: the realization of the terminal presheaf as the constant singleton-valued presheaf
  and the induced equivalence from sections to morphisms out of that terminal object, now exposed
  by the source-facing notation `*ₚ[C]`;

Source/core/bridge triage:
- `source-facing`: the formula identifying global sections with morphisms from the terminal
  presheaf;
- `core/canonical`: `Functor.sections`;
- `bridge/view`: `Functor.sectionsEquivHom`, together with `Functor.isTerminalConst` for the
  singleton-valued terminal presheaf `*ₚ[C]`.

Accordingly this definition item is a bridge/view recall around the canonical owner
`Functor.sections`, not a new owner declaration.
-/
/-
Definition 7.45.1 (Stacks, tag `06UN`): for a presheaf of sets `ℱ : Presheaf C`, the source
formula
`Γ(\mathcal C, \mathcal F) = \operatorname{Mor}_{PSh(\mathcal C)}(*, \mathcal F)` is the
`PUnit` specialization of the canonical bridge `Functor.sectionsEquivHom`.
-/
recall Functor.sectionsEquivHom

/- Companion check: the singleton-valued terminal presheaf `*ₚ[C]` is terminal in
`Presheaf C`. -/
#check
  (Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit :
    IsTerminal *ₚ[C])

/- Source-facing specialization: global sections of `ℱ` identify with morphisms from the terminal
singleton-valued presheaf `*ₚ[C]` to `ℱ`. -/
#check
  (show ℱ.sections ≃ (*ₚ[C] ⟶ ℱ) from ℱ.sectionsEquivHom PUnit)

end CategoryTheory
