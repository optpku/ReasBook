/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_3.ch9_sec9_3_proposition_9_13
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open Set

section Example912

/-- The permutation `π = (3,1,2)` from Example 9.12, encoded on `Fin 3` as
`0 ↦ 2`, `1 ↦ 0`, and `2 ↦ 1`. Under `permute_binary_solution`, the induced coordinate action
is given by `example_9_12_perm.symm`. -/
def example_9_12_perm : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv i := by
    fin_cases i <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

/-- The vector `(1,0,1)` singled out in node `N_a` in Example 9.12. -/
def example_9_12_node_a_solution : Fin 3 → Bool :=
  ![true, false, true]

/-- The vector `(1,1,0)` singled out in node `N_b` in Example 9.12. -/
def example_9_12_node_b_solution : Fin 3 → Bool :=
  ![true, true, false]

/-- The node `N_a` from Fig. 9.6, with `x₁ = 1` and `x₂ = 0`, recorded as the corresponding
enumeration-tree node of feasible binary solutions. -/
def example_9_12_node_a (feasible : Set (Fin 3 → Bool)) : EnumerationNode (Fin 3) where
  fixedZero := ({1} : Set (Fin 3))
  fixedOne := ({0} : Set (Fin 3))
  solutions :=
    {x | x ∈ feasible ∧
      (∀ i ∈ ({0} : Set (Fin 3)), x i = true) ∧
      ∀ i ∈ ({1} : Set (Fin 3)), x i = false}

/-- The node `N_b` from Fig. 9.6, with `x₁ = 1` and `x₃ = 0`, recorded as the corresponding
enumeration-tree node of feasible binary solutions. -/
def example_9_12_node_b (feasible : Set (Fin 3 → Bool)) : EnumerationNode (Fin 3) where
  fixedZero := ({2} : Set (Fin 3))
  fixedOne := ({0} : Set (Fin 3))
  solutions :=
    {x | x ∈ feasible ∧
      (∀ i ∈ ({0} : Set (Fin 3)), x i = true) ∧
      ∀ i ∈ ({2} : Set (Fin 3)), x i = false}

/-- Example 9.12 (1). With `t = 2`, the node `N_a` and the concrete solution `(1,0,1)` satisfy
the pruning data `1 ∈ F_a^1`, `x_{π(1)} = x_3 = 1`, `2 ∈ F_a^0`, and `x_{π(2)} = x_1 = 1`,
written here in `0,1,2` coordinates. -/
theorem example_9_12_node_a_pruning_witness
    (feasible : Set (Fin 3 → Bool)) :
    (0 : Fin 3) ∈ (example_9_12_node_a feasible).fixedOne ∧
      example_9_12_node_a_solution (example_9_12_perm 0) = true ∧
      (1 : Fin 3) ∈ (example_9_12_node_a feasible).fixedZero ∧
      example_9_12_node_a_solution (example_9_12_perm 1) = true := by
  simp [example_9_12_node_a, example_9_12_node_a_solution, example_9_12_perm]

/-- Example 9.12 (2). Assuming feasibility for the underlying binary integer program, the vector
`(1,0,1)` is a solution in node `N_a`. -/
theorem example_9_12_node_a_solution_in_node
    (feasible : Set (Fin 3 → Bool))
    (hfeasible : example_9_12_node_a_solution ∈ feasible) :
    example_9_12_node_a_solution ∈ (example_9_12_node_a feasible).solutions := by
  refine ⟨hfeasible, ?_, ?_⟩ <;> simp [example_9_12_node_a_solution]

/-- Example 9.12 (3). The coordinate action induced by `π = (3,1,2)` sends the pruned node-`N_a`
solution `(1,0,1)` to the node-`N_b` solution `(1,1,0)`. -/
theorem example_9_12_permute_node_a_solution :
    permute_binary_solution example_9_12_perm.symm example_9_12_node_a_solution =
      example_9_12_node_b_solution := by
  funext i
  fin_cases i <;> rfl

/-- Example 9.12 (3), rephrased using the canonical image-set owner
`permuted_node_solutions`: if `(1,0,1)` is feasible in `N_a`, then `(1,1,0)` lies in the
solution set obtained by relabelling `N_a` with `π = (3,1,2)`. -/
theorem example_9_12_node_b_solution_mem_permuted_node_a
    (feasible : Set (Fin 3 → Bool))
    (hfeasible : example_9_12_node_a_solution ∈ feasible) :
    example_9_12_node_b_solution ∈
      permuted_node_solutions example_9_12_perm.symm (example_9_12_node_a feasible) := by
  refine ⟨example_9_12_node_a_solution, example_9_12_node_a_solution_in_node feasible hfeasible, ?_⟩
  exact example_9_12_permute_node_a_solution

/-- Example 9.12 (3), rephrased using the canonical solution-isomorphism owner from
Proposition 9.13. Any symmetry group containing `π⁻¹` witnesses that `(1,0,1)` and `(1,1,0)` are
isomorphic solutions. -/
theorem example_9_12_solutions_are_isomorphic
    (Γ : Subgroup (Equiv.Perm (Fin 3)))
    (hperm : example_9_12_perm.symm ∈ Γ) :
    solutions_are_isomorphic Γ example_9_12_node_a_solution example_9_12_node_b_solution := by
  exact ⟨example_9_12_perm.symm, hperm, example_9_12_permute_node_a_solution⟩

/-- Example 9.12 (4). Assuming feasibility for the underlying binary integer program, the vector
`(1,1,0)` is a solution in node `N_b`. -/
theorem example_9_12_node_b_solution_in_node
    (feasible : Set (Fin 3 → Bool))
    (hfeasible : example_9_12_node_b_solution ∈ feasible) :
    example_9_12_node_b_solution ∈ (example_9_12_node_b feasible).solutions := by
  refine ⟨hfeasible, ?_, ?_⟩ <;> simp [example_9_12_node_b_solution]

end Example912
