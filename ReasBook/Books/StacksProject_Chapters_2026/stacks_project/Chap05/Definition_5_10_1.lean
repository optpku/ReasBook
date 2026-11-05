module

public import Mathlib.Topology.KrullDimension
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling:
- primary domain: topological Krull dimension, built from chains of irreducible closed subsets and
  then localized over open neighbourhoods of a point;
- sampled owner declarations:
  `Order.krullDim`,
  `Order.krullDim_eq_iSup_length`,
  `Order.krullDim_eq_bot_iff`,
  `topologicalKrullDim`,
  `OpenNhdsOf`.

Layer triage:
- `source-facing`: `topologicalKrullDimAt` and its minimum-attainment lemmas;
- `core/canonical`: `Order.krullDim`, `LTSeries`, and mathlib's `topologicalKrullDim`;
- `bridge/view`: the source-facing restatements of `topologicalKrullDim` via chain lengths and the
  empty-space criterion, together with the `sInf` reformulation of `topologicalKrullDimAt`.

Primitive data are only the point `x` and the owner-indexed family
`fun U : OpenNhdsOf x ↦ topologicalKrullDim U`; the set-valued `sInf` description, minimum
property, and realization lemmas are derived API from that indexed infimum.
-/

/-- Definition 5.10.1 (1): a chain of irreducible closed subsets of `X` is the canonical
order-theoretic notion `LTSeries`. -/
abbrev irreducible_closed_chain (X : Type u) [TopologicalSpace X] :=
  LTSeries (IrreducibleCloseds X)

-- Proof sketch: unfold the abbreviation.
/-- The chain abbreviation is exactly the canonical strict series type on irreducible closed
subsets. -/
theorem irreducible_closed_chain_def (X : Type u) [TopologicalSpace X] :
    irreducible_closed_chain X = LTSeries (IrreducibleCloseds X) := by
  -- Unfold the source-facing abbreviation to expose the canonical owner type.
  rfl

/-- Definition 5.10.1 (2): for a chain of irreducible closed subsets of `X`, its length is the
canonical field `p.length`, i.e. `RelSeries.length`. -/
abbrev irreducible_closed_chain_length {X : Type u} [TopologicalSpace X]
    (p : irreducible_closed_chain X) : ℕ :=
  p.length

-- Proof sketch: unfold the abbreviation.
/-- The chain-length abbreviation is exactly the length field of the underlying strict series. -/
theorem irreducible_closed_chain_length_def {X : Type u} [TopologicalSpace X]
    (p : irreducible_closed_chain X) :
    irreducible_closed_chain_length p = p.length := by
  -- Unfold the source-facing length abbreviation and read off the canonical projection.
  rfl

/- Canonical owner for the Krull dimension of a topological space. -/
recall topologicalKrullDim

/-- Bridge between the owner poset `IrreducibleCloseds X` and the underlying space: the poset of
irreducible closed subsets is empty exactly when the space itself is empty. -/
theorem isEmpty_irreducibleCloseds_iff :
    IsEmpty (IrreducibleCloseds X) ↔ IsEmpty X := by
  constructor
  · intro h
    exact ⟨fun x ↦ h.false
      ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩⟩
  · intro h
    exact ⟨fun Z ↦ by
      rcases Z.isIrreducible.nonempty with ⟨x, hx⟩
      exact h.false x⟩

-- Proof sketch: unfold `topologicalKrullDim` and `Order.krullDim`.
/-- Definition 5.10.1 (3): the Krull dimension of `X` is the supremum of the lengths of chains of
irreducible closed subsets of `X`. -/
theorem topologicalKrullDim_eq_iSup_length_irreducibleCloseds :
    topologicalKrullDim X =
      ⨆ p : LTSeries (IrreducibleCloseds X), (p.length : WithBot ℕ∞) :=
  rfl

-- Proof sketch: unfold `topologicalKrullDim` and apply the general order-theoretic characterization
-- `Order.krullDim_eq_bot_iff` to the poset `IrreducibleCloseds X`.
/-- Definition 5.10.1 (4): the Krull dimension of `X` is `-∞` exactly when `X` is empty. -/
theorem topologicalKrullDim_eq_bot_iff :
    topologicalKrullDim X = ⊥ ↔ IsEmpty X := by
  rw [topologicalKrullDim, krullDim_eq_bot_iff, isEmpty_irreducibleCloseds_iff]

/-- Definition 5.10.1 (5): the Krull dimension of `X` at a point `x` is the minimum of the Krull
dimensions of the open neighbourhoods of `x`. -/
noncomputable def topologicalKrullDimAt (x : X) : WithBot ℕ∞ :=
  ⨅ U : OpenNhdsOf x, topologicalKrullDim U

section LocalKrullDimAt

variable (x : X)

local notation "localKrullDimValues" =>
  Set.range fun U : OpenNhdsOf x ↦ topologicalKrullDim U

/-- Definition 5.10.1 (6): `topologicalKrullDimAt x` is the minimum of the dimensions of the open
neighbourhoods of `x`. -/
theorem isLeast_topologicalKrullDimAt :
    IsLeast localKrullDimValues (topologicalKrullDimAt x) := by
  simpa [topologicalKrullDimAt] using
    isLeast_csInf (Set.range_nonempty fun U : OpenNhdsOf x ↦ topologicalKrullDim U)

/-- The local Krull dimension is bounded above by the dimension of every open neighbourhood of the
point. -/
theorem topologicalKrullDimAt_le (U : OpenNhdsOf x) :
    topologicalKrullDimAt x ≤ topologicalKrullDim U := by
  exact (isLeast_topologicalKrullDimAt x).2 ⟨U, rfl⟩

/-- There is an open neighbourhood of `x` whose dimension realizes `topologicalKrullDimAt x`. -/
theorem exists_openNhdsOf_topologicalKrullDimAt_eq :
    ∃ U : OpenNhdsOf x, topologicalKrullDimAt x = topologicalKrullDim U := by
  rcases (isLeast_topologicalKrullDimAt x).1 with ⟨U, hU⟩
  exact ⟨U, hU.symm⟩

end LocalKrullDimAt
