module

import Mathlib.Topology.Constructible
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for constructible-set closure operations:
- primary domain: constructible subsets in a topological space, organized around the owner
  predicate `Topology.IsConstructible`;
- sampled canonical declarations:
  `Topology.IsConstructible`,
  `Topology.IsConstructible.compl`,
  `Topology.IsConstructible.union`,
  `Topology.IsConstructible.inter`;
- best owner abstraction: `Topology.IsConstructible`;
- primitive-vs-derived split:
  primitive data: membership in the canonical Boolean-subalgebra predicate `IsConstructible`;
  derived API: closure under complement, binary union, and binary intersection.

Layer triage:
- `source-facing`: Lemma 5.15.2 records that constructible subsets are closed under complements,
  unions, and intersections;
- `core/canonical`: the existing owner predicate `Topology.IsConstructible`;
- `bridge/view`: the closure-operation lemmas `isConstructible_compl`, `IsConstructible.union`, and
  `IsConstructible.inter`.

This file should therefore stay recall-only and use the source-faithful binary closure lemmas,
without upgrading the main entries to the stronger finite-family theorems `sUnion` and `sInter`. -/

/- Lemma 5.15.2 (complements): closure of constructible subsets under complements is exactly the
canonical directional theorem `Topology.IsConstructible.compl`. -/
recall IsConstructible.compl

/- Lemma 5.15.2 (unions): closure of constructible subsets under binary unions is exactly the
canonical theorem `Topology.IsConstructible.union`. -/
recall IsConstructible.union

/- Lemma 5.15.2 (intersections): closure of constructible subsets under binary intersections is
exactly the canonical theorem `Topology.IsConstructible.inter`. -/
recall IsConstructible.inter
