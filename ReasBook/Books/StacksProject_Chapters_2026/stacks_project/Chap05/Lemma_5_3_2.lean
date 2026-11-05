module

public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for Hausdorff equalizer-closedness and graphs:
- owner abstraction: `isClosed_eq`
- same-domain declarations inspected:
  `isClosed_eq`,
  `IsClosed.isClosed_eq`,
  `Set.mem_graphOn`,
  `Set.graphOn_univ_eq_range`

Layer triage:
- `source-facing`: the graph `univ.graphOn f` of a continuous map
- `core/canonical`: the Hausdorff equalizer-closedness theorem `isClosed_eq`
- `bridge/view`: the graph-closedness specialization below

Primitive data is just the graph owner `Set.graphOn` and the continuity data needed by
`isClosed_eq`. The closed-graph statement is derived API, so this file should stay a thin bridge to
the canonical equalizer theorem rather than introducing a parallel owner for closed graphs.
-/

/- Companion recall: the canonical Hausdorff equalizer-closedness theorem is `isClosed_eq`. -/
recall isClosed_eq

/-- Helper for Lemma 5.3.2: the graph of `f` is the preimage of the diagonal under the map
`p ↦ (f p.1, p.2)`. -/
lemma graph_eq_preimage_diagonal {X : Type u} {Y : Type v} {f : X → Y} :
    (univ.graphOn f : Set (X × Y)) = (fun p : X × Y ↦ (f p.1, p.2)) ⁻¹' diagonal Y := by
  -- Unpack both sides pointwise so the graph condition becomes membership in the diagonal.
  ext p
  simp [mem_graphOn, Set.mem_diagonal_iff]

/-- Lemma 5.3.2: if `f : X → Y` is continuous and `Y` is Hausdorff, then the graph
`univ.graphOn f` is closed in `X × Y`. This is the inverse-image-of-the-diagonal argument
from Lemma 5.3.1. -/
theorem isClosed_graph {f : X → Y} (hf : Continuous f) [T2Space Y] :
    IsClosed (univ.graphOn f) := by
  -- Rewrite the graph as the pullback of the diagonal along the canonical pair map.
  rw [graph_eq_preimage_diagonal]
  -- The diagonal is closed in a Hausdorff space, and continuous preimages of closed sets are closed.
  exact isClosed_diagonal.preimage (hf.fst'.prodMk continuous_snd)
