module

import Mathlib.Tactic.Recall
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Finite.Card
import Mathlib.Topology.Connected.CardComponents

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [ConnectedSpace Y] {f : X → Y}

/- Domain-style sampling for connected components under open and closed maps:
- owner abstractions:
  `IsOpenMap`,
  `ConnectedComponents`
- same-domain derived API inspected:
  `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`,
  `IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace`,
  `ConnectedComponents.discreteTopology_iff`,
  `IsClopen.eq_univ`

Layer triage:
- `source-facing`: the finite-cardinality bound on `ConnectedComponents X` in terms of a finite
  fiber of `f`
- `core/canonical`: `IsOpenMap`, `ConnectedComponents`, and the recalled `ENat.card` inequality
- `bridge/view`: the `Nat.card`/`Set.ncard` reformulation of the canonical `ENat.card` inequality

Primitive data are the open and closed map hypotheses together with connectedness of `Y` and
finiteness of one fiber as a set. Finiteness of `ConnectedComponents X` and the
`Nat.card`/`Set.ncard` reformulation are derived API off the `IsOpenMap` owner; they should stay a
thin bridge to the recalled owner statement rather than growing a parallel local convenience
family.
-/

/-
Canonical library form of Stacks tag `07VB`: the cardinality bound is already available in
mathlib in the `ENat.card`/`Set.encard` form, and it does not use the continuity hypothesis.
-/
recall IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) [ConnectedSpace Y] (y : Y) :
    ENat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).encard

namespace IsOpenMap

/-- Lemma 5.7.7: if `Y` is connected, `f` is open and closed, and the fiber over `y` is finite,
then `X` has at most `|f ⁻¹' {y}|` connected components. This is the finite-cardinal bridge form
of the canonical `ENat.card` inequality
`IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`, expressed with the
primitive set-cardinality `Set.ncard` on the fiber. -/
theorem natCard_connectedComponents_le_ncard_preimage_singleton
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) {y : Y}
    (hyfin : (f ⁻¹' {y}).Finite) :
    Nat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).ncard := by
  letI : Finite (ConnectedComponents X) :=
    hopen.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace hclosed hyfin
  have hcard : ENat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).encard :=
    hopen.enatCard_connectedComponents_le_encard_preimage_singleton hclosed y
  exact ENat.coe_le_coe.mp <| by
    simpa [ENat.card_eq_coe_natCard, hyfin.cast_ncard_eq] using hcard

end IsOpenMap

end
