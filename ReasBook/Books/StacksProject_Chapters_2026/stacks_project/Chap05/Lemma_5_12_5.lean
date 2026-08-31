module

public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain-style sampling for quasi-compact subsets in compact Hausdorff spaces:
- same-domain declarations inspected: `CompactSpace`, `IsClosed.isCompact`, `IsCompact.isClosed`
- chapter context checked: `Lemma_5_12_3` and `Lemma_5_12_4` are `recall`-only, so they do not
  supply a reusable project-level `↔` declaration
- best owner abstractions: whole-space `CompactSpace`, subset predicates `IsClosed`, `IsCompact`

Layer triage:
- `source-facing`: the Stacks equivalence between closedness and quasi-compactness for subsets of a
  quasi-compact Hausdorff space
- `core/canonical`: `CompactSpace X` for the ambient space and `IsCompact` for subset
  quasi-compactness
- `bridge/view`: the equivalence obtained by pairing the two canonical implications above

Primitive data here are only the ambient `CompactSpace X` and `T2Space X` structures. The two
directions are already canonical theorems, so this file should keep only the source-facing bridge
statement rather than introducing any parallel wrapper owner.
-/

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Lemma 5.12.5: for a subset `E` of a quasi-compact Hausdorff space `X`, the conditions (a) `E`
is closed in `X` and (b) `E` is quasi-compact are equivalent. Via Definition 5.12.1, subset
quasi-compactness is the canonical predicate `IsCompact`, and this lemma is the source-facing
bridge obtained by combining `IsClosed.isCompact` and `IsCompact.isClosed`. -/
theorem isClosed_iff_isCompact (E : Set X) : IsClosed E ↔ IsCompact E :=
  ⟨IsClosed.isCompact, IsCompact.isClosed⟩

end
