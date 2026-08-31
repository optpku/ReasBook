module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.CompletePartialOrder
import stacks_project.Chap05.Example_5_8_13

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Order TopologicalSpace

universe u

variable (X : Type u) [TopologicalSpace X]

/- Domain-style sampling for topological Krull dimension in Hausdorff spaces:
- primary domain: topological Krull dimension via the poset `IrreducibleCloseds X`;
- same-domain declarations inspected:
  `topologicalKrullDim`,
  `Order.krullDim_nonpos_iff_forall_isMax`,
  `Order.krullDim_nonneg_iff`,
  `IrreducibleCloseds.exists_eq_singleton`;
- best owner abstraction: `topologicalKrullDim X`, reduced to the order-theoretic owner
  `krullDim (IrreducibleCloseds X)`;
- primitive-vs-derived split: the primitive input is only the Hausdorff and nonempty structure on
  `X`; the singleton description of irreducible closed subsets is already derived upstream in
  `Example_5_8_13`, and the Euclidean-space statement is a specialization of the general theorem.

Layer triage:
- `source-facing`: `topologicalKrullDim_eq_zero_of_nonempty_t2`;
- `core/canonical`: `topologicalKrullDim` and the order-theoretic `krullDim` lemmas;
- `bridge/view`: `euclideanSpace_topologicalKrullDim_eq_zero`.
-/

-- Proof sketch: reuse the upstream chapter theorem that every irreducible closed subset of a
-- Hausdorff space is a singleton, so every element of `IrreducibleCloseds X` is maximal. The
-- order-theoretic criterion `krullDim_nonpos_iff_forall_isMax` gives `topologicalKrullDim X ≤ 0`,
-- and `krullDim_nonneg_iff` turns nonemptiness of `X` into the reverse inequality.
/-- A nonempty Hausdorff space has topological Krull dimension `0`. -/
theorem topologicalKrullDim_eq_zero_of_nonempty_t2 [T2Space X] [Nonempty X] :
    topologicalKrullDim X = 0 := by
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDim, krullDim_nonpos_iff_forall_isMax]
    intro Z Y hZY
    obtain ⟨z, hZ⟩ := IrreducibleCloseds.exists_eq_singleton Z
    obtain ⟨y, hY⟩ := IrreducibleCloseds.exists_eq_singleton Y
    have hz : z = y := by
      have : z ∈ (Y : Set X) := hZY <| by simp [hZ]
      simp [hY] at this
      exact this
    simp [hZ, hY, hz]
  · rw [topologicalKrullDim, krullDim_nonneg_iff]
    exact ‹Nonempty X›.map fun x ↦ ({x} : IrreducibleCloseds X)

/-- Example 5.10.3: the topological Krull dimension of the usual Euclidean space `ℝ^n`, modeled as
`EuclideanSpace ℝ (Fin n)`, is `0`. -/
theorem euclideanSpace_topologicalKrullDim_eq_zero (n : ℕ) :
    topologicalKrullDim (EuclideanSpace ℝ (Fin n)) = 0 := by
  simpa using topologicalKrullDim_eq_zero_of_nonempty_t2 (EuclideanSpace ℝ (Fin n))
