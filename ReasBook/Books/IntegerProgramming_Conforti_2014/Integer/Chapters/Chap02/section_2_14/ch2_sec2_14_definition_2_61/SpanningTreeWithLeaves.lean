import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_5.ch4_sec4_5_theorem_4_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.incident_edge_finset

noncomputable section

open scoped BigOperators

namespace SimpleGraph
namespace SpanningTreeWithLeaves

universe u

variable {V : Type u} [Fintype V]

/-- The objective of the spanning-tree-with-leaves MILP formulation maximizes the sum of the leaf
variables. -/
def objective (z : V → ℝ) : ℝ :=
  ∑ v, z v

/-- Unfolding equation for `objective`. -/
theorem objective_def (z : V → ℝ) :
    objective z = ∑ v, z v := by
  rfl

section DecidableEq

variable [DecidableEq V]

/-- The five textbook constraints of the spanning-tree-with-leaves MILP formulation on the edge
variables `x` and leaf variables `z`. -/
def constraints (G : SimpleGraph V) (x : G.edgeSet → ℝ) (z : V → ℝ) : Prop :=
  (∑ e : G.edgeSet, x e) = (Fintype.card V : ℝ) - 1 ∧
    (∀ S : Finset V, 2 ≤ S.card →
      (G.inducedEdgeFinset (S : Set V)).sum x ≤ (S.card : ℝ) - 1) ∧
      (∀ v : V,
        (incidentEdgeFinset G v).sum x +
            (((incidentEdgeFinset G v).card : ℝ) - 1) * z v ≤
          ((incidentEdgeFinset G v).card : ℝ)) ∧
        (∀ e : G.edgeSet, x e = 0 ∨ x e = 1) ∧
          ∀ v : V, z v = 0 ∨ z v = 1

/-- Membership in `constraints G x z` is exactly the conjunction of the tree-cardinality,
induced-edge, leaf-degree, and binary constraints from the textbook formulation. -/
theorem constraints_iff
    {G : SimpleGraph V} {x : G.edgeSet → ℝ} {z : V → ℝ} :
    constraints G x z ↔
      (∑ e : G.edgeSet, x e) = (Fintype.card V : ℝ) - 1 ∧
        (∀ S : Finset V, 2 ≤ S.card →
          (G.inducedEdgeFinset (S : Set V)).sum x ≤ (S.card : ℝ) - 1) ∧
          (∀ v : V,
            (incidentEdgeFinset G v).sum x +
                (((incidentEdgeFinset G v).card : ℝ) - 1) * z v ≤
              ((incidentEdgeFinset G v).card : ℝ)) ∧
            (∀ e : G.edgeSet, x e = 0 ∨ x e = 1) ∧
              ∀ v : V, z v = 0 ∨ z v = 1 := by
  -- This companion theorem is just the definitional normal form of `constraints`.
  rfl

/-- A feasible point for the spanning-tree-with-leaves MILP formulation consists of a connected
graph together with edge and leaf variables satisfying `constraints`. -/
def feasible (G : SimpleGraph V) (x : G.edgeSet → ℝ) (z : V → ℝ) : Prop :=
  G.Connected ∧ constraints G x z

/-- Membership in `feasible G x z` is exactly graph connectedness together with the textbook MILP
constraints. -/
theorem feasible_iff
    {G : SimpleGraph V} {x : G.edgeSet → ℝ} {z : V → ℝ} :
    feasible G x z ↔ G.Connected ∧ constraints G x z := by
  -- This companion theorem unfolds the feasibility predicate once.
  rfl

/-- The attainable objective values of the spanning-tree-with-leaves MILP formulation on `G`. -/
def objectiveValues (G : SimpleGraph V) : Set ℝ :=
  {r | ∃ x : G.edgeSet → ℝ, ∃ z : V → ℝ, feasible G x z ∧ objective z = r}

/-- Membership in `objectiveValues G` means that some feasible edge/leaf assignment attains the
value `r`. -/
theorem mem_objectiveValues_iff
    {G : SimpleGraph V} {r : ℝ} :
    r ∈ objectiveValues G ↔
      ∃ x : G.edgeSet → ℝ, ∃ z : V → ℝ, feasible G x z ∧ objective z = r := by
  -- Membership is exactly set-builder membership for `objectiveValues`.
  rfl

/-- The tree-cardinality equality extracted from `constraints G x z`. -/
theorem constraints_edgeCount
    {G : SimpleGraph V} {x : G.edgeSet → ℝ} {z : V → ℝ}
    (h_constraints : constraints G x z) :
    (∑ e : G.edgeSet, x e) = (Fintype.card V : ℝ) - 1 := by
  -- Extract the first conjunct of the bundled constraint predicate.
  exact h_constraints.1

/-- The induced-edge inequality extracted from `constraints G x z`. -/
theorem constraints_inducedEdge_le
    {G : SimpleGraph V} {x : G.edgeSet → ℝ} {z : V → ℝ}
    (h_constraints : constraints G x z) {S : Finset V} (hS : 2 ≤ S.card) :
    (G.inducedEdgeFinset (S : Set V)).sum x ≤ (S.card : ℝ) - 1 := by
  -- Extract the quantified induced-edge inequality and specialize it at `S`.
  exact h_constraints.2.1 S hS

/-- The leaf-degree inequality extracted from `constraints G x z`. -/
theorem constraints_leafDegree_le
    {G : SimpleGraph V} {x : G.edgeSet → ℝ} {z : V → ℝ}
    (h_constraints : constraints G x z) (v : V) :
    (incidentEdgeFinset G v).sum x + (((incidentEdgeFinset G v).card : ℝ) - 1) * z v ≤
      ((incidentEdgeFinset G v).card : ℝ) := by
  -- Extract the leaf-degree inequality and specialize it at the chosen vertex.
  exact h_constraints.2.2.1 v

/-- The binary edge-variable condition extracted from `constraints G x z`. -/
theorem constraints_edge_binary
    {G : SimpleGraph V} {x : G.edgeSet → ℝ} {z : V → ℝ}
    (h_constraints : constraints G x z) (e : G.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  -- Extract the binary edge-variable condition and specialize it at `e`.
  exact h_constraints.2.2.2.1 e

/-- The binary leaf-variable condition extracted from `constraints G x z`. -/
theorem constraints_leaf_binary
    {G : SimpleGraph V} {x : G.edgeSet → ℝ} {z : V → ℝ}
    (h_constraints : constraints G x z) (v : V) :
    z v = 0 ∨ z v = 1 := by
  -- Extract the final conjunct giving binary leaf variables.
  exact h_constraints.2.2.2.2 v

end DecidableEq

end SpanningTreeWithLeaves
end SimpleGraph
