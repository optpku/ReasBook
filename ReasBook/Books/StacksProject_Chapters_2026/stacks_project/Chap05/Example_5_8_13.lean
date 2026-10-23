module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Sober

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Example 5.8.13:
- primary domain: Hausdorff separation and sobriety of topological spaces;
- inspected owner declarations:
  `TopologicalSpace.IrreducibleCloseds`,
  `isIrreducible_iff_singleton`,
  `sober_iff_forall_irreducibleCloseds_existsUnique_genericPoint`,
  `T2Space.r1Space`,
  `R1Space.quasiSober`;
- best owner abstraction: the chapter owner for sobriety is the canonical pair
  `T0Space X ∧ QuasiSober X`, while irreducible closed subsets are owned by the bundled type
  `IrreducibleCloseds X`;
- primitive-vs-derived split: this file adds no primitive data; it only records source-facing
  consequences derived from the owner theorem `isIrreducible_iff_singleton` and the canonical
  instance chain `T2Space ⟶ T0Space`, `T2Space ⟶ R1Space ⟶ QuasiSober`. -/

/- Source/core/bridge triage for Example 5.8.13:
- `source-facing`: irreducible closed subsets of a Hausdorff space are singletons, and Hausdorff
  spaces are sober;
- `core/canonical`: `isIrreducible_iff_singleton`, `T2Space.r1Space`, `R1Space.quasiSober`, and
  the chapter sobriety owner `T0Space X ∧ QuasiSober X`;
- `bridge/view`: the bundled singleton theorem on `IrreducibleCloseds X` is a thin source-facing
  restatement of `isIrreducible_iff_singleton`, while the sobriety clause is direct owner use. -/

section Hausdorff

variable [T2Space X]

-- Proof sketch: the bundled irreducible closed subset `Z` is in particular an irreducible subset
-- of `X`, so the stronger canonical theorem `isIrreducible_iff_singleton` applies directly.
/-- Example 5.8.13 (1): every irreducible closed subset of a Hausdorff space is a singleton. -/
theorem IrreducibleCloseds.exists_eq_singleton (Z : IrreducibleCloseds X) :
    ∃ x : X, Z = {x} := by
  rcases isIrreducible_iff_singleton.mp Z.isIrreducible with ⟨x, hx⟩
  exact ⟨x, IrreducibleCloseds.ext hx⟩

/- Companion recall: in a Hausdorff space, the stronger canonical theorem
`isIrreducible_iff_singleton` characterizes all irreducible subsets, not just irreducible closed
subsets. Applied to `univ`, it also gives the ambient-space statement from the source text. -/
recall isIrreducible_iff_singleton

-- Proof sketch: combine the canonical separation-instance chain `T2Space ⟶ T1Space ⟶ T0Space`
-- with the sober-instance chain `T2Space ⟶ R1Space ⟶ QuasiSober`. As in Definition 5.8.6, the
-- public sober owner here is the pair `T0Space X ∧ QuasiSober X`, so no extra wrapper theorem is
-- needed.
/-- Example 5.8.13 (2): every Hausdorff space is sober, expressed canonically by `T₀` and quasi-sobriety. -/
theorem t2Space_sober : T0Space X ∧ QuasiSober X :=
  ⟨inferInstance, inferInstance⟩

end Hausdorff
