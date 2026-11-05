module

import Mathlib.Topology.Inseparable
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-
Domain-style sampling for specialization/generalization lifting:
- primitive owner predicates: `SpecializingMap f` and `GeneralizingMap f`
- derived canonical API in the same owner file: `SpecializingMap.comp`,
  `GeneralizingMap.comp`
- bridge/view layer: none needed here, since the Stacks statements are exactly the canonical
  composition lemmas

Layer triage:
- `source-facing`: lifting specializations/generalizations along a composite map
- `core/canonical`: the owner predicates `SpecializingMap` and `GeneralizingMap`
- `bridge/view`: none

Primitive data is the lifting predicate itself; composition is derived API, so this file should
recall the owner lemmas directly rather than introduce local wrapper theorems.
-/

/- Lemma 5.19.5: if specializations lift along both `f` and `g`, then specializations lift along
`g ∘ f`. This is exactly the canonical mathlib theorem `SpecializingMap.comp`. -/
recall SpecializingMap.comp

/- Lemma 5.19.5: similarly, if generalizations lift along both `f` and `g`, then generalizations
lift along `g ∘ f`. This is exactly the canonical mathlib theorem `GeneralizingMap.comp`. -/
recall GeneralizingMap.comp
