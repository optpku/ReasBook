/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Cuts
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_38.Problem
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19.Cuts
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.incident_edge_finset

open SimpleGraph
open scoped BigOperators

noncomputable section

namespace SymmetricTravelingSalesmanProblem

universe u

variable {V : Type u} [Fintype V]

namespace DFJ

section Feasible

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (P : SymmetricTravelingSalesmanProblem V)

/-- The DFJ feasibility constraints on the edge variables `x` require degree `2` at every vertex,
all proper-cut subtour inequalities, and binary edge values. -/
def feasible (x : P.graph.edgeSet → ℝ) : Prop :=
  (∀ v : V, (incidentEdgeFinset P.graph v).sum x = 2) ∧
    (∀ S : Finset V, SimpleGraph.IsProperCutSide S →
      2 ≤ (δ[P.graph] (S : Set V)).sum x) ∧
      ∀ e : P.graph.edgeSet, x e = 0 ∨ x e = 1

/-- Membership in `feasible P x` is exactly the conjunction of the degree equations, proper-cut
subtour inequalities, and binary edge constraints. -/
theorem feasible_iff
    {x : P.graph.edgeSet → ℝ} :
    feasible P x ↔
      (∀ v : V, (incidentEdgeFinset P.graph v).sum x = 2) ∧
        (∀ S : Finset V, SimpleGraph.IsProperCutSide S →
          2 ≤ (δ[P.graph] (S : Set V)).sum x) ∧
          ∀ e : P.graph.edgeSet, x e = 0 ∨ x e = 1 := by
  -- This is the defining conjunction, so unfolding the owner predicate closes the goal.
  rfl

/-- The degree equation extracted from `feasible P x`. -/
theorem feasible_degree_eq_two
    {x : P.graph.edgeSet → ℝ}
    (h_feasible : feasible P x)
    (v : V) :
    (incidentEdgeFinset P.graph v).sum x = 2 := by
  -- Project the vertex-degree component of the feasibility conjunction.
  exact h_feasible.1 v

/-- The proper-cut subtour inequality extracted from `feasible P x`. -/
theorem feasible_subtour_ge_two
    {x : P.graph.edgeSet → ℝ}
    (h_feasible : feasible P x)
    {S : Finset V}
    (hS : SimpleGraph.IsProperCutSide S) :
    2 ≤ (δ[P.graph] (S : Set V)).sum x := by
  -- Project the cut-inequality component and apply it to the chosen proper cut.
  exact h_feasible.2.1 S hS

/-- The binary edge-variable condition extracted from `feasible P x`. -/
theorem feasible_binary
    {x : P.graph.edgeSet → ℝ}
    (h_feasible : feasible P x)
    (e : P.graph.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  -- Project the integrality component of the feasibility conjunction.
  exact h_feasible.2.2 e

end Feasible

section Objective

variable {V : Type u} [Fintype V]
variable (P : SymmetricTravelingSalesmanProblem V)

/-- The edge coordinates of `P.graph`, regarded as a finset. -/
def edgeCoordinateFinset : Finset P.graph.edgeSet :=
  let _ : DecidableRel P.graph.Adj := Classical.decRel _
  let _ : Fintype P.graph.edgeSet := SimpleGraph.fintypeEdgeSet (G := P.graph)
  Finset.univ

/-- Every edge coordinate lies in `edgeCoordinateFinset P`. -/
theorem mem_edgeCoordinateFinset
    {e : P.graph.edgeSet} :
    e ∈ edgeCoordinateFinset P := by
  classical
  simp [edgeCoordinateFinset]

/-- The DFJ objective is the total edge cost weighted by the edge variables `x`. -/
def objective (x : P.graph.edgeSet → ℝ) : ℝ :=
  (edgeCoordinateFinset P).sum fun e ↦ P.cost e * x e

/-- Unfolding equation for `objective P x`. -/
theorem objective_def
    (x : P.graph.edgeSet → ℝ) :
    objective P x =
      (edgeCoordinateFinset P).sum fun e ↦ P.cost e * x e := by
  rfl

end Objective

section ObjectiveValues

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (P : SymmetricTravelingSalesmanProblem V)

/-- The attained objective values of the DFJ formulation on `P`. -/
def objectiveValues : Set ℝ :=
  {r | ∃ x : P.graph.edgeSet → ℝ, feasible P x ∧ objective P x = r}

/-- Membership in `objectiveValues P` means that some DFJ-feasible edge vector attains `r`. -/
theorem mem_objectiveValues_iff
    {r : ℝ} :
    r ∈ objectiveValues P ↔
      ∃ x : P.graph.edgeSet → ℝ, feasible P x ∧ objective P x = r := by
  -- Membership unfolds directly to the existential specification stored in the set builder.
  rfl

end ObjectiveValues

end DFJ

end SymmetricTravelingSalesmanProblem
