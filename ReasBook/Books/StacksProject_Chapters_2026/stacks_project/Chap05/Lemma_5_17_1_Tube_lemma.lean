module

import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling in topology/compactness:
- owner abstraction inspected first: `IsCompact`
- relevant core/product API: `IsCompact.nhdsSet_prod_eq`
- relevant source-facing theorem: `generalized_tube_lemma`
- relevant bridge/view theorem: `generalized_tube_lemma'`

Layer triage:
- `source-facing`: an open neighborhood of `A ×ˢ B` with `A` and `B` quasi-compact contains a
  product neighborhood `U ×ˢ V`
- `core/canonical`: compact subsets together with the neighborhood identity
  `IsCompact.nhdsSet_prod_eq`
- `bridge/view`: the relative `nhdsSetWithin` formulation `generalized_tube_lemma'`

Primitive data are only the compact subsets and the ambient open neighborhood in the product.
The sets `U` and `V` are derived output from the canonical theorem, so this file should recall
that source-facing theorem directly rather than rebuild a parallel local wrapper.
-/

/- Lemma 5.17.1 (Tube lemma): let `A ⊆ X` and `B ⊆ Y` be quasi-compact subsets and let
`A ×ˢ B ⊆ W ⊆ X × Y` with `W` open. Then there exist open neighborhoods `U` of `A` and `V` of
`B` such that `U ×ˢ V ⊆ W`. This is exactly the canonical mathlib theorem
`generalized_tube_lemma`, so the source-facing item should recall that theorem directly rather
than add a parallel local wrapper. -/
recall generalized_tube_lemma
