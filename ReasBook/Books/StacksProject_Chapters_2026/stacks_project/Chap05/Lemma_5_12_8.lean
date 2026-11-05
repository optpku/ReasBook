module

public import Mathlib.Topology.JacobsonSpace

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T0Space X]

/-
Domain-style sampling for closed points in compact `T0` spaces:
- owner declaration: `closedPoints`
- canonical membership API: `mem_closedPoints_iff`
- canonical existence theorem on compact `T0` spaces: `IsClosed.exists_closed_singleton`

Layer triage:
- `source-facing`: existence of a closed point in a nonempty quasi-compact Kolmogorov space
- `core/canonical`: the owner set `closedPoints X`
- `bridge/view`: specialize `IsClosed.exists_closed_singleton` to `univ`

Primitive data is the owner `closedPoints X`; the existence statement is derived by the canonical
compact-`T0` singleton theorem rather than by a parallel local construction.
-/

-- Proof sketch: specialize `IsClosed.exists_closed_singleton` to the closed subset `univ` and
-- rewrite the resulting closed-singleton witness as membership in `closedPoints X`.
/-- Lemma 5.12.8: a nonempty quasi-compact Kolmogorov space has a closed point. -/
theorem exists_closed_point [Nonempty X] : (closedPoints X).Nonempty := by
  simpa [Set.nonempty_def, mem_closedPoints_iff] using
    isClosed_univ.exists_closed_singleton
      (Set.univ_nonempty : Set.Nonempty (Set.univ : Set X))
