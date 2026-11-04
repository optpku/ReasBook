/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_34.Problem

open scoped BigOperators

universe u w

namespace AsymmetricTravelingSalesmanProblem

variable {V : Type u} {A : Type w}

section Feasibility

variable [Fintype V] [Fintype A]

/-- The Miller-Tucker-Zemlin feasibility constraints for the asymmetric traveling salesman
problem `P` with distinguished root vertex `root`. They consist of unit outgoing degree,
unit incoming degree, the MTZ order inequalities away from `root`, and binary arc variables. -/
def mtzFeasible
    (P : AsymmetricTravelingSalesmanProblem V A) (root : V)
    (x : A → ℝ) (u : V → ℝ) : Prop :=
  (∀ v : V, outgoing_flow P.tail x v = 1) ∧
    (∀ v : V, incoming_flow P.head x v = 1) ∧
      (∀ a : A, P.tail a ≠ root → P.head a ≠ root →
        u (P.tail a) - u (P.head a) + 1 ≤ (Fintype.card V : ℝ) * (1 - x a)) ∧
        ∀ a : A, x a = 0 ∨ x a = 1

/-- Membership in `P.mtzFeasible root x u` is exactly the conjunction of unit outgoing degree,
unit incoming degree, the MTZ order inequalities away from `root`, and binary arc variables. -/
theorem mtzFeasible_iff
    {P : AsymmetricTravelingSalesmanProblem V A} {root : V}
    {x : A → ℝ} {u : V → ℝ} :
    P.mtzFeasible root x u ↔
      (∀ v : V, outgoing_flow P.tail x v = 1) ∧
        (∀ v : V, incoming_flow P.head x v = 1) ∧
          (∀ a : A, P.tail a ≠ root → P.head a ≠ root →
            u (P.tail a) - u (P.head a) + 1 ≤ (Fintype.card V : ℝ) * (1 - x a)) ∧
            ∀ a : A, x a = 0 ∨ x a = 1 := by
  -- The feasibility predicate is already defined by this conjunction.
  rfl

/-- The outgoing-degree equations extracted from `P.mtzFeasible root x u`. -/
theorem mtzFeasible_outgoing
    {P : AsymmetricTravelingSalesmanProblem V A} {root : V}
    {x : A → ℝ} {u : V → ℝ}
    (h_feasible : P.mtzFeasible root x u) (v : V) :
    outgoing_flow P.tail x v = 1 := by
  -- Read off the first conjunct of the MTZ feasibility data.
  exact h_feasible.1 v

/-- The incoming-degree equations extracted from `P.mtzFeasible root x u`. -/
theorem mtzFeasible_incoming
    {P : AsymmetricTravelingSalesmanProblem V A} {root : V}
    {x : A → ℝ} {u : V → ℝ}
    (h_feasible : P.mtzFeasible root x u) (v : V) :
    incoming_flow P.head x v = 1 := by
  -- Read off the second conjunct of the MTZ feasibility data.
  exact h_feasible.2.1 v

/-- The MTZ order inequalities away from `root` extracted from `P.mtzFeasible root x u`. -/
theorem mtzFeasible_order
    {P : AsymmetricTravelingSalesmanProblem V A} {root : V}
    {x : A → ℝ} {u : V → ℝ}
    (h_feasible : P.mtzFeasible root x u) (a : A)
    (htail : P.tail a ≠ root) (hhead : P.head a ≠ root) :
    u (P.tail a) - u (P.head a) + 1 ≤ (Fintype.card V : ℝ) * (1 - x a) := by
  -- Read off the third conjunct and apply it to the given arc away from `root`.
  exact h_feasible.2.2.1 a htail hhead

/-- The binary arc-variable conditions extracted from `P.mtzFeasible root x u`. -/
theorem mtzFeasible_binary
    {P : AsymmetricTravelingSalesmanProblem V A} {root : V}
    {x : A → ℝ} {u : V → ℝ}
    (h_feasible : P.mtzFeasible root x u) (a : A) :
    x a = 0 ∨ x a = 1 := by
  -- Read off the final conjunct of the MTZ feasibility data.
  exact h_feasible.2.2.2 a

end Feasibility

section Objective

variable [Fintype A]

/-- The MTZ linear objective attached to `P`, evaluated on arc variables `x`. -/
def mtzObjective
    (P : AsymmetricTravelingSalesmanProblem V A) (x : A → ℝ) : ℝ :=
  ∑ a, P.cost a * x a

/-- Unfolding equation for `P.mtzObjective x`. -/
theorem mtzObjective_def
    (P : AsymmetricTravelingSalesmanProblem V A) (x : A → ℝ) :
    P.mtzObjective x = ∑ a, P.cost a * x a := by
  -- The objective function was defined by this finite sum.
  rfl

end Objective

section ObjectiveValues

variable [Fintype V] [Fintype A]

/-- The attained objective values of the Miller-Tucker-Zemlin formulation of `P` with root
vertex `root`. -/
def mtzObjectiveValues
    (P : AsymmetricTravelingSalesmanProblem V A) (root : V) : Set ℝ :=
  {r | ∃ x : A → ℝ, ∃ u : V → ℝ, P.mtzFeasible root x u ∧ P.mtzObjective x = r}

/-- A feasible MTZ solution contributes its attained cost to `P.mtzObjectiveValues root`. -/
theorem mtzObjective_mem_mtzObjectiveValues
    {P : AsymmetricTravelingSalesmanProblem V A} {root : V}
    {x : A → ℝ} {u : V → ℝ}
    (h_feasible : P.mtzFeasible root x u) :
    P.mtzObjective x ∈ P.mtzObjectiveValues root := by
  -- Package the given MTZ-feasible arc and potential variables as witnesses.
  exact ⟨x, u, h_feasible, rfl⟩

end ObjectiveValues

end AsymmetricTravelingSalesmanProblem
