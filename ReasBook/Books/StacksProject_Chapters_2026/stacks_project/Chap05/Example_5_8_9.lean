module

public import Mathlib.Topology.Sober

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

/-
Domain-style sampling for Example 5.8.9:
- primary domain: separation axioms and quasi-sobriety of topological spaces
- inspected owner declarations:
  `R1Space`,
  `R1Space.quasiSober`,
  `Set.iUnion_of_singleton`,
  `Subtype.t0Space`
- best owner abstraction: `R1Space` is the canonical owner for the indiscrete-space argument,
  while the singleton cover is already owned by `Set.iUnion_of_singleton`
- primitive-vs-derived split: the only primitive ingredient not already packaged upstream is the
  bridge instance `[IndiscreteTopology X] → [R1Space X]`; quasi-sobriety is then derived by the
  canonical owner instance `R1Space.quasiSober`, and the singleton-cover/subspace facts remain
  direct canonical recalls or instance consequences

Source/core/bridge triage:
- `source-facing`: indiscrete spaces are quasi-sober but, when nontrivial, not Kolmogorov; the
  singleton subsets cover the ambient set and their subspaces are discrete and `T₀`
- `core/canonical`: `R1Space`, `R1Space.quasiSober`, `Set.iUnion_of_singleton`
- `bridge/view`: the instance `[IndiscreteTopology X] → [R1Space X]` is a thin canonical bridge to
  the owner abstraction; it is not a second owner abstraction
-/

section IndiscreteSpace

variable {X : Type u} [TopologicalSpace X]

instance [IndiscreteTopology X] : R1Space X where
  specializes_or_disjoint_nhds x y := Or.inl (Inseparable.all x y).specializes

-- Proof sketch: an indiscrete space is `R₁` by the bridge instance above, and the canonical
-- instance `R1Space.quasiSober` then yields quasi-sobriety.
/-- Example 5.8.9 (1): an indiscrete space is quasi-sober. -/
theorem indiscrete_quasiSober [IndiscreteTopology X] : QuasiSober X := by
  -- The local `R₁` bridge instance upgrades directly to quasi-sobriety.
  infer_instance

-- Proof sketch: if the topology is indiscrete, any two points are inseparable. In a nontrivial
-- space this contradicts the `T0` separation condition, so the space is not Kolmogorov.
/-- Example 5.8.9 (2): a nontrivial indiscrete space is not Kolmogorov. -/
theorem indiscrete_not_kolmogorov [IndiscreteTopology X] [Nontrivial X] : ¬ T0Space X := by
  intro hT0
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  -- In an indiscrete space, no two points can be separated by neighborhoods.
  have hInsep : Inseparable x y := Inseparable.all x y
  -- A `T₀` space forces inseparable points to coincide, contradicting `x ≠ y`.
  exact hxy ((t0Space_iff_inseparable X).1 hT0 x y hInsep)

end IndiscreteSpace

section SingletonSubspaces

variable {X : Type u} [TopologicalSpace X]

-- Proof sketch: `Set.iUnion_of_singleton` gives the cover, and each singleton subtype is a
-- subsingleton topological space, hence discrete.
/-- Example 5.8.9 (3): the family of singleton subsets covers `X`, and each singleton subspace is
discrete, hence Kolmogorov. -/
theorem singletons_cover_by_discrete_subspaces :
    (⋃ x : X, ({x} : Set X)) = univ ∧ ∀ x : X, DiscreteTopology ({x} : Set X) := by
  constructor
  · -- The ambient space is the union of its singleton subsets.
    simpa using Set.iUnion_of_singleton X
  · intro x
    -- A singleton subtype is subsingleton, so its topology is automatically discrete.
    infer_instance

end SingletonSubspaces
