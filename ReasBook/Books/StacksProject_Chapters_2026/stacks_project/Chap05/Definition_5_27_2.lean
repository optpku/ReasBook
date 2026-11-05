module

import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [TopologicalSpace X] (x : X)

/- Domain-style sampling for isolated points in a topological space:
- inspected canonical declarations: the owner proposition `IsOpen {x}`, the primary neighborhood
  reformulation `isOpen_singleton_iff_nhds_eq_pure`, the punctured-neighborhood reformulation
  `isOpen_singleton_iff_punctured_nhds`, and the downstream non-isolated-point API
  `[NeBot (𝓝[≠] x)]`.
- best owner abstraction: mathlib does not package isolated points as a separate predicate owner,
  so the canonical public surface is the proposition `IsOpen {x}` itself.
- primitive-vs-derived split:
  primitive data: openness of the singleton `{x}`.
  derived API: the equivalent neighborhood criteria `𝓝 x = pure x` and `𝓝[≠] x = ⊥`.

This item is therefore a `source-facing` recall of the canonical singleton-openness condition,
with neighborhood criteria kept as thin `bridge/view` companions.
-/

/- Source/core/bridge triage for Definition 5.27.2:
- `source-facing`: “`x` is an isolated point”.
- `core/canonical`: `IsOpen {x}`.
- `bridge/view`: `isOpen_singleton_iff_punctured_nhds x`. -/

/- Definition 5.27.2: a point `x` of a topological space is an isolated point exactly when its
singleton is open, i.e. when the canonical proposition `IsOpen {x}` holds. -/
#check IsOpen ({x} : Set X)

/- Companion recall: the primary neighborhood reformulation of isolatedness is the canonical
theorem `isOpen_singleton_iff_nhds_eq_pure`. -/
recall isOpen_singleton_iff_nhds_eq_pure

/- Companion recall: isolatedness is equivalently the punctured-neighborhood criterion
`𝓝[≠] x = ⊥`, namely `isOpen_singleton_iff_punctured_nhds`. -/
recall isOpen_singleton_iff_punctured_nhds

end
