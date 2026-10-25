module

public import Mathlib.Topology.Irreducible
import Mathlib.Topology.Connected.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for irreducibility under open maps:
- owner abstraction: `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`
- same-domain declarations inspected:
  `IrreducibleSpace.isIrreducible_univ`,
  `irreducibleSpace_def`,
  `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`,
  `IsIrreducible.preimage_of_isPreirreducible_fiber`

Layer triage:
- `source-facing`: the space-level irreducibility criterion in the Stacks lemma
- `core/canonical`: the set-level owner theorem
  `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`
- `bridge/view`: the `IsOpenMap`-owner theorem below together with `irreducibleSpace_def`,
  turning irreducibility of `univ` into `IrreducibleSpace`

Primitive data is the open-map hypothesis together with dense irreducibility information on the
fibers. The space-level conclusion is derived API, so this file should stay a thin bridge to the
owner theorem rather than repackage a parallel local irreducibility API.
-/

section

variable {f : X → Y}

namespace IsOpenMap

-- Proof sketch: use the dense set of points with irreducible fibers to get a point of `X`,
-- then apply the canonical set-level owner theorem
-- `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber` to `univ ⊆ Y`.
/-- Lemma 5.8.14: if `f : X → Y` is open, `Y` is irreducible, and the points of
`Y` with irreducible fiber form a dense subset, then `X` is irreducible. -/
theorem irreducibleSpace_of_dense_irreducible_fiber
    (hf : IsOpenMap f) (hY : IrreducibleSpace Y)
    (hdense : Dense { y : Y | IsIrreducible (f ⁻¹' {y}) }) : IrreducibleSpace X := by
  letI : IrreducibleSpace Y := hY
  have hdensePre : Dense { y : Y | IsPreirreducible (f ⁻¹' {y}) } :=
    hdense.mono fun y hy ↦ hy.isPreirreducible
  have hnonempty : (univ : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := hdense.nonempty
    exact hy.nonempty.mono (subset_univ _)
  refine (irreducibleSpace_def X).2 ⟨hnonempty, ?_⟩
  simpa [inter_univ] using
    IsPreirreducible.preimage_of_dense_isPreirreducible_fiber
      (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible f hf
      (by simpa [inter_univ] using hdensePre.closure_eq)

end IsOpenMap

end
