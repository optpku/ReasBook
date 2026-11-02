module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Real.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Cuts
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Weight

open scoped BigOperators

public section

namespace SimpleGraph
namespace MinimumCut

universe u

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

section CutObjectiveValues

variable [DecidableEq V]

/-- The objective values attained by proper cuts of `G` with respect to the edge weights `w`. -/
def cutObjectiveValues (w : G.edgeSet → ℝ) : Set ℝ :=
  {r | ∃ S : Finset V, SimpleGraph.IsProperCutSide S ∧ G.cutWeight w S = r}

/-- Membership in `cutObjectiveValues G w` means that some proper cut side of `G` attains the
value `r`. -/
theorem mem_cutObjectiveValues_iff
    {w : G.edgeSet → ℝ} {r : ℝ} :
    r ∈ cutObjectiveValues G w ↔
      ∃ S : Finset V, SimpleGraph.IsProperCutSide S ∧ G.cutWeight w S = r := by
  rfl

/-- The weight of every proper cut side belongs to `cutObjectiveValues G w`. -/
theorem cutWeight_mem_cutObjectiveValues
    (w : G.edgeSet → ℝ) {S : Finset V} (hS : SimpleGraph.IsProperCutSide S) :
    G.cutWeight w S ∈ cutObjectiveValues G w := by
  exact ⟨S, hS, rfl⟩

end CutObjectiveValues

/-- The sum of the edge variables `x` over the edges of the subgraph `T`, viewed inside the
ambient edge coordinates of `G`. -/
noncomputable def treeEdgeSum (x : G.edgeSet → ℝ) (T : G.Subgraph) : ℝ :=
  open scoped Classical in
    ∑ e : G.edgeSet, if e.1 ∈ T.edgeSet then x e else 0

/-- Unfolding equation for `treeEdgeSum`. -/
theorem treeEdgeSum_def
    (x : G.edgeSet → ℝ) (T : G.Subgraph) :
    treeEdgeSum G x T =
      (open scoped Classical in ∑ e : G.edgeSet, if e.1 ∈ T.edgeSet then x e else 0) := by
  rfl

/-- The `0`-`1` spanning-tree-cover constraints for the minimum-cut formulation on `G`. -/
def feasible (x : G.edgeSet → ℝ) : Prop :=
  (∀ T : G.Subgraph, T.spanningCoe.IsTree → 1 ≤ treeEdgeSum G x T) ∧
    ∀ e : G.edgeSet, x e = 0 ∨ x e = 1

/-- Membership in `feasible G x` means that `x` satisfies every spanning-tree covering inequality
and is binary on each edge. -/
theorem feasible_iff
    {x : G.edgeSet → ℝ} :
    feasible G x ↔
      (∀ T : G.Subgraph, T.spanningCoe.IsTree → 1 ≤ treeEdgeSum G x T) ∧
        ∀ e : G.edgeSet, x e = 0 ∨ x e = 1 := by
  rfl

/-- The spanning-tree covering inequality extracted from `feasible G x`. -/
theorem feasible_tree_ge_one
    {x : G.edgeSet → ℝ} (hx : feasible G x)
    {T : G.Subgraph} (hT : T.spanningCoe.IsTree) :
    1 ≤ treeEdgeSum G x T := by
  exact hx.1 T hT

/-- The binary edge-variable condition extracted from `feasible G x`. -/
theorem feasible_binary
    {x : G.edgeSet → ℝ} (hx : feasible G x) (e : G.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  exact hx.2 e

/-- The linear objective of the spanning-tree-cover minimum-cut formulation. -/
def objective (w : G.edgeSet → ℝ) (x : G.edgeSet → ℝ) : ℝ :=
  ∑ e : G.edgeSet, w e * x e

/-- Unfolding equation for `objective`. -/
theorem objective_def
    (w : G.edgeSet → ℝ) (x : G.edgeSet → ℝ) :
    objective G w x = ∑ e : G.edgeSet, w e * x e := by
  rfl

/-- The attainable objective values of the spanning-tree-cover minimum-cut formulation on `G`. -/
def objectiveValues (w : G.edgeSet → ℝ) : Set ℝ :=
  {r | ∃ x : G.edgeSet → ℝ, feasible G x ∧ objective G w x = r}

/-- Membership in `objectiveValues G w` means that some feasible edge assignment attains the value
`r`. -/
theorem mem_objectiveValues_iff
    {w : G.edgeSet → ℝ} {r : ℝ} :
    r ∈ objectiveValues G w ↔
      ∃ x : G.edgeSet → ℝ, feasible G x ∧ objective G w x = r := by
  rfl

end MinimumCut
end SimpleGraph
