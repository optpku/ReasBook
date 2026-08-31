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

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for Lemma 5.19.6:
- primary domain: specialization/generalization-stable subsets in topology
- inspected owner declarations: `StableUnderSpecialization`, `StableUnderGeneralization`,
  `SpecializingMap.stableUnderSpecialization_image`,
  `GeneralizingMap.stableUnderGeneralization_image`
- best owner abstraction: the lifting predicates `SpecializingMap f` and `GeneralizingMap f`,
  together with their canonical image lemmas

Layer triage:
- `source-facing`: image-stability of specialization-stable and generalization-stable subsets
- `core/canonical`: `StableUnderSpecialization`, `StableUnderGeneralization`, `SpecializingMap`,
  `GeneralizingMap`
- `bridge/view`: none

Primitive data here is only a subset together with its stability predicate, plus a map satisfying
the corresponding lifting property. The image statements are derived API of the map-lifting owner
predicates, so local wrapper theorems or recall of secondary aliases would only duplicate the
canonical mathlib surface.
-/

/- Lemma 5.19.6 (1): the image of a specialization-stable subset under a specializing map is
again specialization-stable. This is exactly the canonical owner theorem
`SpecializingMap.stableUnderSpecialization_image`; the separate continuity hypothesis is
redundant. -/
recall SpecializingMap.stableUnderSpecialization_image

/- Lemma 5.19.6 (2): the image of a generalization-stable subset under a generalizing map is again
generalization-stable. This is exactly the canonical owner theorem
`GeneralizingMap.stableUnderGeneralization_image`; the separate continuity hypothesis is
redundant. -/
recall GeneralizingMap.stableUnderGeneralization_image
