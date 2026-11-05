module

import Mathlib.Topology.Inseparable
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for Definition 5.19.4:
- primary domain: specialization/generalization lifting for maps of topological spaces
- owner declarations inspected: `SpecializingMap`, `GeneralizingMap`,
  `specializingMap_iff_closure_singleton_subset`, `SpecializingMap.comp`
- best owner abstraction: the canonical owner predicates `SpecializingMap f` and
  `GeneralizingMap f`
- primitive data: only the lifting predicates themselves
- derived API: closure/image criteria and composition lemmas already supplied upstream by mathlib

Layer triage:
- `source-facing`: the Stacks definitions of specializing and generalizing maps
- `core/canonical`: `SpecializingMap` and `GeneralizingMap`
- `bridge/view`: none

There is no extra mathematical structure to package here. The numbered item is a recall of the
canonical owner predicates, so the public API should stay on those owners directly.
-/

/- Definition 5.19.4 (1): for a continuous map `f : X → Y`, saying that specializations lift along
`f` is exactly the canonical predicate `SpecializingMap f`. -/
recall SpecializingMap

/- Definition 5.19.4 (2): for a continuous map `f : X → Y`, saying that generalizations lift along
`f` is exactly the canonical predicate `GeneralizingMap f`. -/
recall GeneralizingMap
