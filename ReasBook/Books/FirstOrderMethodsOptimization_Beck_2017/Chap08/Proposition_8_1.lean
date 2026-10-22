/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {ι : Type v} [PseudoMetricSpace E] [Fintype ι] [Nonempty ι]

/-- The pointwise maximum of the distances to the sets in a finite family. -/
noncomputable def max_infDist_to_family (S : ι → Set E) : E → ℝ :=
  fun x ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Metric.infDist x (S i))

/-- Helper for Proposition 8.1: the local max-distance objective is exactly the Chapter 8 owner
`convex_feasibility_max_distance`. -/
theorem max_infDist_to_family_eq_convex_feasibility_max_distance (S : ι → Set E) :
    max_infDist_to_family S = convex_feasibility_max_distance S := by
  -- Both source-facing objectives are the same finite maximum of point-to-set distances.
  rfl

-- Proof sketch: unfold `max_infDist_to_family`.
/-- Evaluating `max_infDist_to_family S` at `x` gives the finite maximum of the distances from
`x` to the sets `S i`. -/
@[simp] theorem max_infDist_to_family_apply (S : ι → Set E) (x : E) :
    max_infDist_to_family S x =
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Metric.infDist x (S i)) := by
  -- Unfold the local source-facing definition to read off its value at `x`.
  rfl

/-- Helper for Proposition 8.1: the max-distance objective is everywhere nonnegative. -/
theorem max_infDist_to_family_nonneg (S : ι → Set E) (x : E) :
    0 ≤ max_infDist_to_family S x := by
  -- Rewrite to the finite maximum and compare `0` with one coordinate distance first.
  rw [max_infDist_to_family_apply]
  obtain ⟨i, hi⟩ := (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
  exact le_trans
    (Metric.infDist_nonneg (x := x) (s := S i))
    (Finset.le_sup' (s := (Finset.univ : Finset ι))
      (f := fun j ↦ Metric.infDist x (S j)) hi)

-- Proof sketch: each term `Metric.infDist x (S i)` vanishes because `x ∈ S i`, so the finite
-- maximum of these distances is `0`.
/-- A point in the total intersection has zero maximum distance to the family. -/
theorem max_infDist_to_family_eq_zero_of_mem_iInter
    (S : ι → Set E) {x : E} (hx : x ∈ ⋂ i, S i) :
    max_infDist_to_family S x = 0 := by
  -- Rewrite to the finite maximum and show that each coordinate distance vanishes.
  rw [max_infDist_to_family_apply]
  refine Finset.sup'_eq_of_forall
    (s := (Finset.univ : Finset ι))
    (H := Finset.univ_nonempty)
    (f := fun i ↦ Metric.infDist x (S i))
    (a := 0) ?_
  intro i hi
  -- Membership in each set collapses each point-to-set distance to zero.
  exact Metric.infDist_zero_of_mem ((Set.mem_iInter.mp hx) i)

-- Proof sketch: if `x` minimizes the objective, then the value must be `0` by the nonempty
-- intersection hypothesis. Since each set is closed, `Metric.infDist x (S i) = 0` implies
-- `x ∈ S i`, so every minimizer lies in `⋂ i, S i`. Conversely, every point of `⋂ i, S i` has
-- objective value `0`, hence is optimal.
/-- Proposition 8.1 (1): if a finite family of closed sets has nonempty intersection, then the
global minimizer set of the pointwise maximum of the distance functions is exactly that
intersection. -/
theorem global_minimizers_max_infDist_to_family
    (S : ι → Set E) (hclosed : ∀ i, IsClosed (S i))
    (hnonempty : (⋂ i, S i).Nonempty) :
    {x | IsMinOn (max_infDist_to_family S) Set.univ x} = ⋂ i, S i := by
  ext x
  -- Rewrite the minimization problem to the canonical owner and use its exact characterization.
  simpa [max_infDist_to_family_eq_convex_feasibility_max_distance S] using
    (isMinOn_convex_feasibility_max_distance_iff_mem_iInter
      (S := S) hclosed hnonempty (x := x))

-- Proof sketch: the nonempty intersection provides a point where the objective equals `0`, so the
-- infimum is at most `0`. Every distance is nonnegative, hence the objective is nonnegative
-- everywhere, giving the reverse inequality and therefore optimal value `0`.
/-- Proposition 8.1 (2): if the total intersection is nonempty, then the optimal value of the
pointwise maximum of the distance functions is `0`. -/
theorem sInf_range_max_infDist_to_family_eq_zero
    (S : ι → Set E) (hnonempty : (⋂ i, S i).Nonempty) :
    sInf (Set.range (max_infDist_to_family S)) = 0 := by
  rcases hnonempty with ⟨x, hx⟩
  have hzero_mem : 0 ∈ Set.range (max_infDist_to_family S) := by
    -- A feasible point from the total intersection realizes the value `0`.
    exact ⟨x, max_infDist_to_family_eq_zero_of_mem_iInter S hx⟩
  have hbounded : BddBelow (Set.range (max_infDist_to_family S)) := by
    -- Nonnegativity of each distance term makes `0` a global lower bound for the range.
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact max_infDist_to_family_nonneg S z
  refine le_antisymm ?_ ?_
  · -- The feasible witness places `0` inside the range, so the infimum is at most `0`.
    exact csInf_le hbounded hzero_mem
  · -- The lower bound `0` on the whole range pushes the infimum back above `0`.
    refine le_csInf ?_ ?_
    · exact ⟨0, hzero_mem⟩
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      exact max_infDist_to_family_nonneg S z

-- Proof sketch: each function `x ↦ Metric.infDist x (S i)` is `1`-Lipschitz by
-- `Metric.lipschitz_infDist_pt`. Repeatedly combine these bounds using the fact that the maximum
-- of finitely many `1`-Lipschitz real-valued functions is again `1`-Lipschitz.
/-- Proposition 8.1 (3): the pointwise maximum of the distance functions is Lipschitz continuous
with constant `1`. -/
theorem lipschitzWith_max_infDist_to_family (S : ι → Set E) :
    LipschitzWith 1 (max_infDist_to_family S) := by
  -- Control the finite maximum by the coordinatewise inf-distance estimate from mathlib.
  refine LipschitzWith.of_le_add fun x y ↦ ?_
  rw [max_infDist_to_family_apply, max_infDist_to_family_apply]
  refine Finset.sup'_le _ _ fun i hi ↦ ?_
  -- Each coordinate distance changes by at most `dist x y`, so the same is true for the maximum.
  exact le_trans
    (Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := S i))
    (add_le_add_left
      (Finset.le_sup' (s := (Finset.univ : Finset ι))
        (f := fun j ↦ Metric.infDist y (S j)) hi)
      _)

end
