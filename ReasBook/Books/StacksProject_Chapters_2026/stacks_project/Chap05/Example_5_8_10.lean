module

public import Mathlib.Topology.Sober
import Mathlib.Tactic.Recall
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

/- Domain-style sampling for Example 5.8.10:
- primary domain: separation and quasi-sober topological spaces for the cofinite topology;
- inspected owner declarations: `T0Space`, `QuasiSober`, `genericPoint`, `genericPoint_closure`,
  the `T1Space (CofiniteTopology Y)` instance, and the irreducibility instance on
  `CofiniteTopology`;
- best owner abstraction: `T0Space` is the core owner for the Kolmogorov clause, `QuasiSober` is
  the core owner for the quasi-sober clause, and `genericPoint` is the canonical derived API for
  the irreducible closed subset `univ` in an irreducible space;
- primitive-vs-derived split: the primitive data is only the cofinite topology on a type, with
  infinitude needed only for the non-quasi-sober clause; the ambient `T₀` statement,
  irreducibility of the ambient space, and the closure of its generic point are derived from the
  canonical owner API.

Source/core/bridge triage:
- `source-facing`: the infinite cofinite space is Kolmogorov but fails to be quasi-sober, even
  though it is covered by singleton subspaces that are closed, irreducible, and sober;
- `core/canonical`: `T0Space`, `QuasiSober`, `genericPoint`, `genericPoint_closure`, and the
  instance `IrreducibleSpace (CofiniteTopology Y)`;
- `bridge/view`: the singleton-subspace examples are companion views of the source cover; they do
  not introduce a second owner abstraction, and the ambient `T₀` clause is read off from the
  stronger upstream `T1Space (CofiniteTopology Y)` instance. -/

section Ambient

variable {Y : Type u}

local notation "X" => CofiniteTopology Y

/- The cofinite topology on any set is `T₁`, hence in particular Kolmogorov (`T₀`). The
source-facing ambient separation clause is therefore the canonical owner `T0Space X`. -/
example : T0Space X := inferInstance

/-
The singleton subsets cover the underlying set of `X`. This is the canonical theorem
`Set.iUnion_of_singleton`.
-/
recall Set.iUnion_of_singleton

/- The singleton subsets provide the local irreducible closed pieces discussed in the source. In
the infinite case they are not irreducible components of the ambient cofinite space, since that
ambient space is itself irreducible. -/
example (y : X) : IsIrreducible ({y} : Set X) := isIrreducible_singleton

example (y : X) : IsClosed ({y} : Set X) := isClosed_singleton

-- Proof sketch: a singleton subtype is a subsingleton type, hence carries the discrete topology.
/-- Each singleton subspace of the cofinite space is discrete. -/
theorem singleton_discreteTopology (y : X) : DiscreteTopology ({y} : Set X) := by
  -- A singleton subtype is subsingleton, so its subspace topology is automatically discrete.
  infer_instance

-- Proof sketch: a discrete singleton space is Hausdorff, hence in particular `T₀` and
-- quasi-sober.
/-- Each singleton subspace is sober, expressed canonically as `T0Space` plus `QuasiSober`. -/
theorem singleton_t0Space_and_quasiSober (y : X) :
    T0Space ({y} : Set X) ∧ QuasiSober ({y} : Set X) := by
  -- First record the discrete topology, then read off the canonical separation and sobriety
  -- instances on the singleton subtype.
  have hDiscrete : DiscreteTopology ({y} : Set X) := singleton_discreteTopology y
  constructor <;> infer_instance

end Ambient

section Infinite

variable {Y : Type u} [Infinite Y]

local notation "X" => CofiniteTopology Y

/-- Helper for Example 5.8.10: quasi-sobriety would force the generic point singleton to fill the
entire infinite cofinite space. -/
lemma genericPoint_singleton_eq_univ [QuasiSober X] : ({genericPoint X} : Set X) = univ := by
  -- In the irreducible cofinite space, the generic point is dense.
  have hclosure : closure ({genericPoint X} : Set X) = (univ : Set X) := genericPoint_closure X
  -- Singletons are closed in a `T₁` space, so their closure is the singleton itself.
  have hclosed : IsClosed ({genericPoint X} : Set X) := isClosed_singleton
  simpa [hclosed.closure_eq] using hclosure

-- Proof sketch: in an irreducible quasi-sober space, `genericPoint_closure` gives
-- `closure {genericPoint} = univ`. In the infinite cofinite topology every singleton is closed, so
-- this forces `univ` to be a singleton, contradicting infinitude.
/-- Example 5.8.10: the cofinite topology on an infinite set is not quasi-sober. -/
theorem infinite_cofiniteTopology_not_quasiSober : ¬ QuasiSober X := by
  intro hQuasi
  letI : QuasiSober X := hQuasi
  -- Quasi-sobriety gives a generic point for the irreducible ambient space.
  have hsingleton : ({genericPoint X} : Set X) = (univ : Set X) := genericPoint_singleton_eq_univ
  -- If the whole space is a singleton, then the cofinite type synonym itself is subsingleton.
  have hSubsingleton : Subsingleton X := by
    refine ⟨fun x z => ?_⟩
    have hxmem : x ∈ ({genericPoint X} : Set X) := by
      simp [hsingleton]
    have hzmem : z ∈ ({genericPoint X} : Set X) := by
      simp [hsingleton]
    have hx : x = genericPoint X := by
      simpa using hxmem
    have hz : z = genericPoint X := by
      simpa using hzmem
    exact hx.trans hz.symm
  -- Transport subsingletonity back along the identity equivalence to contradict infinitude of `Y`.
  have hSubsingletonY : Subsingleton Y := by
    refine ⟨fun y z => ?_⟩
    simpa using hSubsingleton.elim (CofiniteTopology.of y) (CofiniteTopology.of z)
  exact not_subsingleton Y hSubsingletonY

end Infinite
