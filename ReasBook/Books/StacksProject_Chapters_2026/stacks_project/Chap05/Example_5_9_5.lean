module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import stacks_project.Chap05.Definition_5_9_1
import Mathlib.Data.PNat.Interval
import Mathlib.Data.PNat.Order

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology TopologicalSpace
open Topology.WithLowerSet Topology.IsLowerSet

-- Proof sketch: for `x : WithLowerSet ℕ+`, the initial segment `Iic x` is the canonical
-- neighbourhood of `x` in the lower-set topology and is finite, hence Noetherian as a subspace.
/-- The lower-set topology on the positive integers is locally Noetherian. -/
instance : TopologicalSpace.LocallyNoetherianSpace (WithLowerSet ℕ+) where
  exists_open x := by
    let _ : Finite (Iic x : Set (WithLowerSet ℕ+)) := by
      simpa [ofLowerSetOrderIso.preimage_Iic] using
        (Set.finite_Iic (ofLowerSet x)).preimage_embedding ofLowerSetOrderIso.toEquiv.toEmbedding
    refine ⟨⟨Iic x, isOpen_iff_isLowerSet.2 (isLowerSet_Iic x)⟩, by simp, inferInstance⟩

-- Proof sketch: in the lower-set topology, closed subsets are exactly upper sets. If `x` were a
-- closed point, then `{x}` would be an upper set, hence would also contain `x + 1`, absurd.
/-- Example 5.9.5: the positive integers with the lower-set topology have no closed points, i.e.
`closedPoints (WithLowerSet ℕ+) = ∅`. -/
theorem pnat_withLowerSet_has_no_closed_points :
    closedPoints (WithLowerSet ℕ+) = ∅ := by
  ext x
  rw [Set.mem_empty_iff_false, mem_closedPoints_iff, isClosed_iff_isUpper]
  constructor
  · intro hx
    let y : WithLowerSet ℕ+ := toLowerSet (ofLowerSet x + 1)
    have hxy : x < y := by
      change ofLowerSet x < ofLowerSet y
      simp [y]
    have hy : y ∈ ({x} : Set (WithLowerSet ℕ+)) := hx hxy.le (by simp)
    exact (ne_of_lt hxy) <| by simpa [y] using hy.symm
  · intro hx
    cases hx
