module

public import Mathlib.Topology.Sober
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for generic points and sober spaces:
- primary domain: generic points, `T₀` separation, quasi-sobriety, and sobriety in topology;
- sampled canonical declarations:
  `IsGenericPoint`,
  `isGenericPoint_def`,
  `QuasiSober`,
  `quasiSober_iff`,
  `irreducibleSetEquivPoints`,
  `TopologicalSpace.IrreducibleCloseds`,
  `t0Space_iff_exists_isOpen_xor'_mem`;
- best owner abstraction: `IsGenericPoint` owns generic points, `QuasiSober` owns quasi-sobriety,
  and `irreducibleSetEquivPoints` is the canonical sober-space bridge on
  `IrreducibleCloseds X`; the chapter-level owner form of sobriety is the pair
  `[T0Space X] [QuasiSober X]`;
- primitive-vs-derived split: the primitive owner data is the field `QuasiSober.sober`; the
  bundled `IrreducibleCloseds` restatements, `irreducibleSetEquivPoints`, and the
  unique-generic-point reformulations are derived bridge API.

Layer triage:
- `source-facing`: the Stacks definitions phrased using generic points of irreducible closed sets;
- `core/canonical`: `IsGenericPoint`, `T0Space`, `QuasiSober`, and `IrreducibleCloseds`;
- `bridge/view`: the bundled `IrreducibleCloseds` companion theorems and the sober
  unique-generic-point characterization.
-/

/- Canonical recall: for an irreducible closed subset `Z` of `X`, a generic point is
expressed by the canonical predicate `IsGenericPoint`. -/
recall IsGenericPoint

/- Companion recall: the defining equation for a generic point is the canonical theorem
`isGenericPoint_def`. -/
recall isGenericPoint_def

/- Canonical recall: the Stacks notion of a Kolmogorov space is the canonical separation axiom
`T0Space`. -/
recall T0Space

-- Proof sketch: translate the open-set formulation of `T0Space` into the equivalent closed-set
-- separation statement by taking complements, and conversely recover the open-set separation of
-- two distinct points from the complement of a closed separator.
/-- Definition 5.8.6 (1): a topological space is Kolmogorov if any two distinct points are
separated by a closed subset containing exactly one of them. -/
theorem t0Space_iff_forall_ne_exists_closed_separating :
    T0Space X ↔
      ∀ ⦃x x' : X⦄ (_ : x ≠ x'),
        ∃ Z : Set X, IsClosed Z ∧ Xor' (x ∈ Z) (x' ∈ Z) := by
  constructor
  · intro hX x x' hxx'
    obtain ⟨U, hU, hxor⟩ := (t0Space_iff_exists_isOpen_xor'_mem X).1 hX hxx'
    refine ⟨Uᶜ, hU.isClosed_compl, ?_⟩
    simpa [Xor', and_comm, and_left_comm, and_assoc, or_comm, not_not] using hxor
  · intro hX
    rw [t0Space_iff_exists_isOpen_xor'_mem]
    intro x x' hxx'
    obtain ⟨Z, hZ, hxor⟩ := hX hxx'
    refine ⟨Zᶜ, hZ.isOpen_compl, ?_⟩
    simpa [Xor', and_comm, and_left_comm, and_assoc, or_comm, not_not] using hxor

/- Canonical recall: the Stacks notion of a quasi-sober space is the canonical mathlib class
`QuasiSober`. -/
recall QuasiSober

/- Companion recall: the canonical owner theorem `quasiSober_iff` unpacks quasi-sobriety on raw
irreducible closed subsets. -/
recall quasiSober_iff

-- Proof sketch: one direction unwraps `QuasiSober.sober` on the carrier of an
-- `IrreducibleCloseds X`; the converse repackages the irreducible and closed hypotheses into an
-- element of `IrreducibleCloseds X`.
/-- Companion bridge for Definition 5.8.6 (3), restated on bundled irreducible closed subsets. -/
theorem quasiSober_iff_forall_irreducibleCloseds_exists_genericPoint :
    QuasiSober X ↔
      ∀ Z : IrreducibleCloseds X, ∃ ξ : X, IsGenericPoint ξ (Z : Set X) := by
  rw [quasiSober_iff X]
  constructor
  · intro hX Z
    exact hX Z.isIrreducible Z.isClosed
  · intro hX S hS hSclosed
    simpa using hX ⟨S, hS, hSclosed⟩

/-
Canonical recall: the Stacks notion of a sober space is expressed canonically by the pair of
typeclasses `[T0Space X] [QuasiSober X]`. The source-facing unique-generic-point formulation
remains as the companion theorem below.
-/
#check (T0Space X ∧ QuasiSober X)

/- Companion recall: in a sober space, the canonical bundled bridge identifying irreducible closed
subsets with points is `irreducibleSetEquivPoints`. -/
recall irreducibleSetEquivPoints

-- Proof sketch: the forward implication combines the two canonical sober ingredients, namely
-- quasi-sobriety and the `T₀` uniqueness of generic points. Conversely, existence of generic
-- points gives `QuasiSober`, and uniqueness recovers the `T₀` condition from singleton closures.
/-- Definition 5.8.6 (2): a topological space is sober if every irreducible closed subset has a
unique generic point. -/
theorem sober_iff_forall_irreducibleCloseds_existsUnique_genericPoint :
    (T0Space X ∧ QuasiSober X) ↔
      ∀ Z : IrreducibleCloseds X, ∃! ξ : X, IsGenericPoint ξ (Z : Set X) := by
  constructor
  · intro hX
    letI : T0Space X := hX.1
    letI : QuasiSober X := hX.2
    intro Z
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober Z.isIrreducible Z.isClosed
    exact ⟨ξ, hξ, fun η hη ↦ IsGenericPoint.eq hη hξ⟩
  · intro hX
    have hT0 : T0Space X := by
      rw [t0Space_iff_inseparable]
      intro x y hxy
      let Z : IrreducibleCloseds X :=
        ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
      obtain ⟨ξ, hξ, huniq⟩ := hX Z
      have hx : IsGenericPoint x (Z : Set X) := by
        simpa [Z] using (isGenericPoint_closure : IsGenericPoint x (closure ({x} : Set X)))
      have hy : IsGenericPoint y (Z : Set X) := by
        simpa [Z, isGenericPoint_def] using (inseparable_iff_closure_eq.mp hxy).symm
      exact (huniq x hx).trans (huniq y hy).symm
    have hQuasiSober : QuasiSober X := by
      rw [quasiSober_iff X]
      intro S hS hSclosed
      obtain ⟨ξ, hξ, _⟩ := hX ⟨S, hS, hSclosed⟩
      exact ⟨ξ, hξ⟩
    exact ⟨hT0, hQuasiSober⟩
