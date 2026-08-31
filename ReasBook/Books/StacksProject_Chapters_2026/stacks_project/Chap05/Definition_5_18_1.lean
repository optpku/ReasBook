module

public import Mathlib.Topology.JacobsonSpace
import Mathlib.Tactic.Recall
meta import Mathlib.Tactic.ToDual
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace

/- The textbook notation for the closed-point locus is `X₀`. Lean parses bare `X₀` as a single
identifier, so the reusable owner-level term notation is parenthesized: `(X)₀`. In a local
context with a fixed ambient space variable `X`, one can then add `local notation "X₀" => (X)₀`
to recover the usual surface form. -/
scoped macro:max X:term noWs "₀" : term => `(closedPoints $X)

end TopologicalSpace

/-
Domain-style sampling for Jacobson spaces:
- primitive owner for closed points: `closedPoints X`, with source-facing notation `(X)₀`
- core canonical owner: `JacobsonSpace X`
- derived textbook specification: `jacobsonSpace_iff`

Layer triage:
- `source-facing`: the definition of a Jacobson space via density of closed points in closed subsets
- `core/canonical`: the mathlib class `JacobsonSpace X`
- `bridge/view`: the closure characterization `jacobsonSpace_iff`

Primitive data is the owner class `JacobsonSpace X`; the closure statement is its canonical
specification theorem, not separate structure data.
-/

/- Companion recall: the closed-point locus of `X` is the canonical set `closedPoints X`. -/
recall closedPoints

/-
Definition 5.18.1 is recalled canonically by `JacobsonSpace X`: this is the mathlib class whose
field states that every closed subset is the closure of its closed points.
-/
recall JacobsonSpace

/- Companion recall: the textbook closure characterization of Jacobson spaces is the canonical
equivalence `jacobsonSpace_iff`. -/
recall jacobsonSpace_iff
