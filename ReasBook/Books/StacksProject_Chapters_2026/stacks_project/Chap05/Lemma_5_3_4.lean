module

public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
variable {f : X → Z} {g : Y → Z}

/- Domain-style sampling for Hausdorff equalizer-closedness and fiber products:
- owner abstraction: `isClosed_eq`
- same-domain declarations inspected:
  `isClosed_eq`,
  `IsClosed.isClosed_eq`,
  `Continuous.fst'`,
  `Continuous.snd'`

Layer triage:
- `source-facing`: the fiber-product subset `{p : X × Y | f p.1 = g p.2}`
- `core/canonical`: the Hausdorff equalizer-closedness theorem `isClosed_eq`
- `bridge/view`: the fiber-product specialization below

Primitive data is just the equalizer subset in `X × Y` together with the continuity data needed by
`isClosed_eq`. The closed fiber-product statement is derived API, so this file should stay a thin
bridge to the canonical equalizer theorem rather than introducing a parallel local owner.
-/

/-
Companion recall: the canonical Hausdorff equalizer-closedness theorem is `isClosed_eq`.
-/
recall isClosed_eq

/-- Lemma 5.3.4: if `f : X → Z` and `g : Y → Z` are continuous and `Z` is Hausdorff, then the
fiber-product subset `X ×_Z Y = {p : X × Y | f p.1 = g p.2}` is closed in `X × Y`. This is the
canonical mathlib closed equalizer statement `isClosed_eq` applied to the maps
`fun p : X × Y ↦ f p.1` and `fun p : X × Y ↦ g p.2`. -/
theorem isClosed_fiberProduct_subset (hf : Continuous f) (hg : Continuous g) :
    IsClosed { p : X × Y | f p.1 = g p.2 } :=
  isClosed_eq hf.fst' hg.snd'
