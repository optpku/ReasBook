module

public import Mathlib.Topology.Constructible
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/- Domain-style sampling for Noetherian spaces and retrocompact subsets:
- owner abstractions: `NoetherianSpace`, `CompactSpace`, `IsRetrocompact`
- same-domain declarations inspected:
  `NoetherianSpace.compactSpace`,
  `NoetherianSpace.isCompact`,
  `NoetherianSpace.to_quasiSeparatedSpace`,
  `IsCompact.isRetrocompact`

Layer triage:
- `source-facing`: Stacks Lemma 5.12.13, asserting quasi-compactness of the whole space and
  retrocompactness of every subset in a Noetherian space
- `core/canonical`: `NoetherianSpace`, `CompactSpace`, `IsRetrocompact`
- `bridge/view`: part (2) below is the source-facing specialization of `IsRetrocompact` obtained
  directly from the owner theorem `NoetherianSpace.isCompact`; there is no upstream theorem with
  the exact same interface, so the source-facing bridge is kept rather than replaced by a shell

Primitive data is only the `NoetherianSpace` hypothesis. Whole-space compactness and the
compactness of `s ∩ U` for compact open `U` are both derived from
`TopologicalSpace.NoetherianSpace.isCompact`, so no parallel wrapper API is needed here.
-/

/- Canonical recall: a Noetherian topological space carries the compact-space instance
`TopologicalSpace.NoetherianSpace.compactSpace`. -/
recall NoetherianSpace.compactSpace

/-- Lemma 5.12.13: every subset of a Noetherian topological space is retrocompact. -/
theorem isRetrocompact_of_noetherianSpace (s : Set X) : IsRetrocompact s :=
  fun _ _ _ ↦ NoetherianSpace.isCompact _

end
