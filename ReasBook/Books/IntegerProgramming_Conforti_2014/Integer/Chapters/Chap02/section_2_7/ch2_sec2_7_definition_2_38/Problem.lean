/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image

public section

universe u

/-- The weighted undirected-graph data underlying a symmetric traveling salesman problem. -/
structure SymmetricTravelingSalesmanProblem (V : Type u) where
  graph : SimpleGraph V
  cost : graph.edgeSet → ℝ

namespace SymmetricTravelingSalesmanProblem

variable {V : Type u}

/-- Build a symmetric traveling salesman problem from an undirected graph and edge costs. -/
def ofGraph (graph : SimpleGraph V) (cost : graph.edgeSet → ℝ) :
    SymmetricTravelingSalesmanProblem V :=
  { graph := graph, cost := cost }

/-- A closed walk in the graph of `P`, recorded together with its start vertex. -/
structure ClosedWalk (P : SymmetricTravelingSalesmanProblem V) where
  start : V
  walk : P.graph.Walk start start

/-- Build a closed-walk datum from a closed walk in the graph of `P`. -/
def ClosedWalk.ofWalk (P : SymmetricTravelingSalesmanProblem V) {v : V}
    (walk : P.graph.Walk v v) :
    P.ClosedWalk :=
  { start := v, walk := walk }

/-- A Hamiltonian tour in `P` is a closed walk whose underlying walk is a Hamiltonian cycle. -/
def IsHamiltonianTour [DecidableEq V]
    (P : SymmetricTravelingSalesmanProblem V) (t : P.ClosedWalk) : Prop :=
  t.walk.IsHamiltonianCycle

/-- Membership in `P.IsHamiltonianTour t` is exactly the canonical Hamiltonian-cycle condition on
`t.walk`. -/
theorem isHamiltonianTour_iff [DecidableEq V]
    {P : SymmetricTravelingSalesmanProblem V} {t : P.ClosedWalk} :
    P.IsHamiltonianTour t ↔ t.walk.IsHamiltonianCycle := by
  -- This theorem just exposes the defining predicate of Hamiltonian tours.
  rfl

/-- The feasible tours of `P` are its Hamiltonian tours. -/
def feasibleSet [DecidableEq V] (P : SymmetricTravelingSalesmanProblem V) : Set P.ClosedWalk :=
  {t | P.IsHamiltonianTour t}

/-- Membership in `P.feasibleSet` means that the chosen closed walk is a Hamiltonian tour. -/
theorem mem_feasibleSet_iff [DecidableEq V]
    {P : SymmetricTravelingSalesmanProblem V} {t : P.ClosedWalk} :
    t ∈ P.feasibleSet ↔ P.IsHamiltonianTour t := by
  -- Membership in the feasible set is exactly the defining predicate.
  rfl

/-- The total cost of a closed walk is the sum of the costs of its traversed edges in order. -/
def objective (P : SymmetricTravelingSalesmanProblem V) (t : P.ClosedWalk) : ℝ :=
  (t.walk.edges.attach.map fun e ↦ P.cost ⟨e.1, t.walk.edges_subset_edgeSet e.2⟩).sum

/-- Unfolding equation for `P.objective`. -/
theorem objective_def
    (P : SymmetricTravelingSalesmanProblem V) (t : P.ClosedWalk) :
    P.objective t =
      (t.walk.edges.attach.map fun e ↦ P.cost ⟨e.1, t.walk.edges_subset_edgeSet e.2⟩).sum := by
  -- The objective is defined to be the sum of the traversed edge costs.
  rfl

/-- The attained objective values of the symmetric traveling salesman problem `P`. -/
def objectiveValues [DecidableEq V] (P : SymmetricTravelingSalesmanProblem V) : Set ℝ :=
  P.objective '' P.feasibleSet

/-- Membership in `P.objectiveValues` means that some Hamiltonian tour attains the value `r`. -/
theorem mem_objectiveValues_iff [DecidableEq V]
    {P : SymmetricTravelingSalesmanProblem V} {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ t : P.ClosedWalk, P.IsHamiltonianTour t ∧ P.objective t = r := by
  -- Unfold the attained-value set to expose a feasible tour witness.
  simp [objectiveValues, feasibleSet]

end SymmetricTravelingSalesmanProblem
