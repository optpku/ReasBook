module

public import Mathlib.Topology.Sober
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Example_5_8_10
import stacks_project.Chap05.Example_5_8_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Topology

section

variable (X : Type u) [TopologicalSpace X]
variable (Y : Type v)

local notation "S" => X ⊕ CofiniteTopology Y

/- Domain-style sampling for Example 5.8.11:
- primary domain: separation and quasi-sobriety behavior under coproduct inclusions;
- inspected owner declarations:
  `Topology.IsEmbedding.t0Space`,
  `Topology.IsOpenEmbedding.quasiSober`,
  `indiscrete_not_kolmogorov`,
  `infinite_cofiniteTopology_not_quasiSober`;
- best owner abstraction: `T0Space` and `QuasiSober` remain the ambient owners, while the coproduct
  maps `Sum.inl` and `Sum.inr` are the canonical bridge/view API transporting those properties to
  the summands;
- primitive-vs-derived split: the only primitive input here is the left indiscrete/nontrivial
  hypothesis and the right infinite cofinite space. The contradiction arguments are entirely
  derived from the canonical inclusion APIs, so this file should not keep extra local wrapper maps
  or redundant left-side assumptions on the quasi-sober clause.

Source/core/bridge triage:
- `source-facing`: the disjoint union in the source example is neither Kolmogorov nor quasi-sober;
- `core/canonical`: `T0Space`, `QuasiSober`, `indiscrete_not_kolmogorov`,
  `infinite_cofiniteTopology_not_quasiSober`;
- `bridge/view`: `IsEmbedding.inl` and `IsOpenEmbedding.inr` transfer those owner properties to the
  coproduct summands. -/

/-- Example 5.8.11 (1): if `X` has the indiscrete topology and at least two points, and `Y` is an
infinite set with the cofinite topology, then the disjoint union `X ⊕ CofiniteTopology Y` is not a
Kolmogorov (`T₀`) space. -/
theorem sum_not_kolmogorov_of_indiscrete_left
    [IndiscreteTopology X] [Nontrivial X] :
    ¬ T0Space S := by
  intro hS
  letI : T0Space S := hS
  letI : T0Space X :=
    (IsEmbedding.inl : IsEmbedding (Sum.inl : X → S)).t0Space
  have hX : ¬ T0Space X := indiscrete_not_kolmogorov
  exact hX inferInstance

/-- Example 5.8.11 (2): if `X` has the indiscrete topology and at least two points, and `Y` is an
infinite set with the cofinite topology, then the disjoint union `X ⊕ CofiniteTopology Y` is not
quasi-sober. -/
theorem sum_not_quasiSober_of_infinite_cofinite_right
    [Infinite Y] :
    ¬ QuasiSober S := by
  intro hS
  letI : QuasiSober S := hS
  letI : QuasiSober (CofiniteTopology Y) :=
    (IsOpenEmbedding.inr :
      IsOpenEmbedding (Sum.inr : CofiniteTopology Y → S)).quasiSober
  have hY : ¬ QuasiSober (CofiniteTopology Y) := infinite_cofiniteTopology_not_quasiSober
  exact hY inferInstance

/-- Example 5.8.11 (3): if `X` has the indiscrete topology and at least two points, and `Y` is an
infinite set with the cofinite topology, then the disjoint union `X ⊕ CofiniteTopology Y` is
neither Kolmogorov nor quasi-sober. -/
theorem sum_not_kolmogorov_not_quasiSober_of_indiscrete_left_infinite_cofinite_right
    [IndiscreteTopology X] [Nontrivial X] [Infinite Y] :
    ¬ T0Space S ∧ ¬ QuasiSober S :=
  ⟨sum_not_kolmogorov_of_indiscrete_left X Y,
    sum_not_quasiSober_of_infinite_cofinite_right X Y⟩

end
