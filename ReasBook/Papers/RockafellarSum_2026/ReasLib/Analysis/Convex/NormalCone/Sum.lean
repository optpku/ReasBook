/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.Convex.NormalCone

/-!
# Normal-cone sum estimates

This module proves graph membership, monotonicity, and quadratic bounds for
adding a normal-cone operator.
-/

public section

open scoped Pointwise

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/-- A normal-cone value has nonnegative quadratic pairing with its base point
when the constraint set contains zero. -/
theorem quadratic_nonneg_of_mem_normalCone
    (P : DualPairing X Xstar) (C : Set X) (h_zero : 0 ∈ C)
    (x : X) (nstar : Xstar) (h_normal : nstar ∈ P.normalCone C x) :
    0 ≤ P.quadratic (x, nstar) := by
  have hx := (P.mem_normalCone C x nstar).1 h_normal
  have hineq := hx.2 0 h_zero
  rw [P.toLinearPairing_apply] at hineq
  have hquad : P.quadratic (x, nstar) = P.toDual nstar x := by
    rw [P.quadratic_apply]
  rw [hquad]
  have hineq' : -(P.toDual nstar x) ≤ 0 := by
    simpa [sub_eq_add_neg, map_neg] using hineq
  exact neg_nonpos.mp hineq'

/-- A local nonnegativity law for an operator extends to its sum with the
normal cone of a constraint set contained in the local region. -/
theorem quadratic_nonneg_of_mem_graph_add_normalCone
    (P : DualPairing X Xstar) (M : SetValuedOperator X Xstar) (C U : Set X)
    (h_zero : 0 ∈ C) (h_subset : C ⊆ U)
    (h_localNonneg : ∀ x xstar,
      (x, xstar) ∈ M.graph → x ∈ U → 0 ≤ P.quadratic (x, xstar))
    (x : X) (ystar : Xstar)
    (h_graph : (x, ystar) ∈ (M + P.normalCone C).graph) :
    0 ≤ P.quadratic (x, ystar) := by
  rw [SetValuedOperator.mem_graph_add] at h_graph
  rcases h_graph with ⟨m, hm, n, hn, hsum⟩
  have hxC : x ∈ C := (P.mem_normalCone C x n).1 hn |>.1
  have hmgraph : (x, m) ∈ M.graph := by
    rw [SetValuedOperator.mem_graph]
    exact hm
  have hlocal := h_localNonneg x m hmgraph (h_subset hxC)
  have hnormal := quadratic_nonneg_of_mem_normalCone P C h_zero x n hn
  rw [P.quadratic_apply]
  rw [← hsum, map_add]
  have hqm : P.quadratic (x, m) = P.toDual m x := by rw [P.quadratic_apply]
  have hqn : P.quadratic (x, n) = P.toDual n x := by rw [P.quadratic_apply]
  rw [hqm] at hlocal
  rw [hqn] at hnormal
  simp only [add_apply] at *
  linarith

end DualPairing
