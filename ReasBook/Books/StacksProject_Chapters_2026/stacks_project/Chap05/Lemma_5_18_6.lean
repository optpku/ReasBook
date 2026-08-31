module

public import Mathlib.Topology.JacobsonSpace
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.18.6:
- primitive owner data in this domain: `closedPoints X`
- core canonical owner: `JacobsonSpace X`
- exact canonical bridge theorem: `JacobsonSpace.discreteTopology`
- finite-space corollary already supplied by the instance
  `[Finite X] [JacobsonSpace X] : DiscreteTopology X`

Layer triage:
- `source-facing`: finitely many closed points in a Jacobson space force discreteness
- `core/canonical`: `JacobsonSpace X`
- `bridge/view`: the exact existing theorem `JacobsonSpace.discreteTopology`

Primitive data is the finiteness of `closedPoints X`; discreteness is derived canonical structure,
so this file should recall the owner theorem directly rather than introduce a parallel local lemma.
-/
/-
Lemma 5.18.6: a Jacobson space with finitely many closed points has discrete topology; in
particular, every finite Jacobson space is discrete.
-/
recall JacobsonSpace.discreteTopology [JacobsonSpace X] (h : (closedPoints X).Finite) :
  DiscreteTopology X

-- Proof sketch: use the existing instance
-- `[Finite X] [JacobsonSpace X] : DiscreteTopology X`, which is obtained in mathlib from
-- `JacobsonSpace.discreteTopology` by observing that `closedPoints X` is finite when `X` is finite.
/-- A finite Jacobson space has discrete topology. -/
theorem discreteTopology_of_finite_jacobsonSpace [Finite X] [JacobsonSpace X] :
    DiscreteTopology X := by
  -- The finite-space corollary is already registered as a typeclass instance in mathlib.
  infer_instance
