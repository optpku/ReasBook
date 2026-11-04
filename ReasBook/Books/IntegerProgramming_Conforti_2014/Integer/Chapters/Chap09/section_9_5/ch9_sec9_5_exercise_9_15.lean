/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_example_8_12

open scoped BigOperators

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available via `tool_search` in this environment, so this file is formalized directly from the
-- local finite-family 1-tree/Lagrangian pattern used elsewhere in Chapters 8 and 9.

section Exercise915

variable {E : Type} [DecidableEq E]

/-- A branch-and-bound node for the symmetric traveling salesman problem records the edges already
forced into every descendant tour and the edges forbidden in every descendant tour. -/
structure SymmetricTspBranchNode (E : Type) where
  required : Finset E
  forbidden : Finset E

namespace SymmetricTspBranchNode

/-- A branch-and-bound node is consistent when no edge is simultaneously required and forbidden. -/
def Consistent (node : SymmetricTspBranchNode E) : Prop :=
  Disjoint node.required node.forbidden

/-- An edge set respects a branch-and-bound node when it contains every required edge and avoids
every forbidden edge. -/
def Allows (node : SymmetricTspBranchNode E) (F : Finset E) : Prop :=
  node.required ⊆ F ∧ Disjoint node.forbidden F

/-- The root node before any branching decisions are imposed. -/
def root : SymmetricTspBranchNode E where
  required := ∅
  forbidden := ∅

/-- Compatibility with a branch-and-bound node is decidable from finite edge-set membership. -/
instance instDecidableAllows (node : SymmetricTspBranchNode E) : DecidablePred node.Allows := by
  intro F
  dsimp [Allows]
  infer_instance

/-- The members of a finite candidate family that are compatible with a branch-and-bound node. -/
def compatibleFamily
    (node : SymmetricTspBranchNode E)
    (candidates : Finset (Finset E)) : Finset (Finset E) :=
  candidates.filter node.Allows

/-- Membership in `node.compatibleFamily candidates` means belonging to the candidate family and
respecting the node's required/forbidden edge decisions. -/
@[simp] theorem mem_compatibleFamily_iff
    (node : SymmetricTspBranchNode E)
    (candidates : Finset (Finset E))
    {F : Finset E} :
    F ∈ node.compatibleFamily candidates ↔ F ∈ candidates ∧ node.Allows F := by
  simp [compatibleFamily]

/-- The child node obtained by forcing the branching edge into every descendant tour. -/
def includeChild (node : SymmetricTspBranchNode E) (e : E) : SymmetricTspBranchNode E where
  required := insert e node.required
  forbidden := node.forbidden

/-- The child node obtained by forbidding the branching edge in every descendant tour. -/
def excludeChild (node : SymmetricTspBranchNode E) (e : E) : SymmetricTspBranchNode E where
  required := node.required
  forbidden := insert e node.forbidden

@[simp] theorem allows_root {E : Type} (F : Finset E) :
    (root : SymmetricTspBranchNode E).Allows F := by
  simp [Allows, root]

@[simp] theorem allows_includeChild_iff
    (node : SymmetricTspBranchNode E)
    (e : E)
    (F : Finset E) :
    (node.includeChild e).Allows F ↔ e ∈ F ∧ node.Allows F := by
  constructor
  · rintro ⟨hrequired, hforbidden⟩
    refine ⟨hrequired (Finset.mem_insert_self e node.required), ?_⟩
    refine ⟨?_, hforbidden⟩
    intro x hx
    exact hrequired (Finset.mem_insert_of_mem hx)
  · rintro ⟨he, hnode⟩
    rcases hnode with ⟨hrequired, hforbidden⟩
    refine ⟨?_, hforbidden⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact he
    · exact hrequired hx

@[simp] theorem allows_excludeChild_iff
    (node : SymmetricTspBranchNode E)
    (e : E)
    (F : Finset E) :
    (node.excludeChild e).Allows F ↔ e ∉ F ∧ node.Allows F := by
  constructor
  · rintro ⟨hrequired, hforbidden⟩
    have hdisjoint := Finset.disjoint_left.mp hforbidden
    refine ⟨?_, ⟨hrequired, ?_⟩⟩
    · intro he
      exact hdisjoint (Finset.mem_insert_self e node.forbidden) he
    · exact Finset.disjoint_left.mpr fun x hxF hx ↦ hdisjoint (Finset.mem_insert_of_mem hxF) hx
  · rintro ⟨he, hnode⟩
    rcases hnode with ⟨hrequired, hforbidden⟩
    have hdisjoint := Finset.disjoint_left.mp hforbidden
    refine ⟨hrequired, Finset.disjoint_left.mpr ?_⟩
    intro x hxF hx
    rcases Finset.mem_insert.mp hxF with rfl | hxF
    · exact he hx
    · exact hdisjoint hxF hx

/-- Branching on an edge partitions the compatible tours into the tours that use the edge and the
tours that avoid it; if the edge is already fixed, one child family is empty. -/
theorem compatibleFamily_eq_includeChild_union_excludeChild
    (tours : Finset (Finset E))
    (node : SymmetricTspBranchNode E)
    (e : E) :
    node.compatibleFamily tours =
      (node.includeChild e).compatibleFamily tours ∪
        (node.excludeChild e).compatibleFamily tours := by
  ext F
  by_cases heF : e ∈ F <;>
    simp [heF, and_comm]

/-- The root node is consistent, so it is a valid starting point for the branch-and-bound tree. -/
theorem root_consistent {E : Type} : (root : SymmetricTspBranchNode E).Consistent := by
  simp [Consistent, root]

end SymmetricTspBranchNode

open SymmetricTspBranchNode

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The Lagrangian objective obtained from the 1-tree relaxation `(8.7)` by penalizing the degree
equations at all vertices except the distinguished root. -/
def one_tree_lagrangian_objective
    (root : V)
    (delta : V → Finset E)
    (c : E → ℝ)
    (lam : V → ℝ)
    (T : Finset E) : ℝ :=
  one_tree_cost c T +
    Finset.sum (Finset.univ.erase root) fun i ↦ lam i * (((delta i ∩ T).card : ℝ) - 2)

/-- The node lower bound obtained by minimizing the 1-tree Lagrangian objective over the
1-trees compatible with the current branching decisions. -/
noncomputable def one_tree_lagrangian_node_bound
    (root : V)
    (delta : V → Finset E)
    (one_trees : Finset (Finset E))
    (c : E → ℝ)
    (node : SymmetricTspBranchNode E)
    (lam : V → ℝ) : WithTop ℝ :=
  sInf
    ((fun T : Finset E ↦
        (one_tree_lagrangian_objective root delta c lam T : WithTop ℝ)) ''
      (↑(node.compatibleFamily one_trees) : Set (Finset E)))

/-- A node is fathomed by the 1-tree Lagrangian bound when the incumbent tour cost is already no
greater than the lower bound computed at that node. -/
def node_fathomed_by_one_tree_bound
    (root : V)
    (delta : V → Finset E)
    (one_trees : Finset (Finset E))
    (c : E → ℝ)
    (node : SymmetricTspBranchNode E)
    (lam : V → ℝ)
    (incumbent : ℝ) : Prop :=
  (incumbent : WithTop ℝ) ≤ one_tree_lagrangian_node_bound root delta one_trees c node lam

/-- Exercise 9.15. Every node-compatible tour has cost at least the node's 1-tree Lagrangian bound
once the tour family is contained in the 1-tree family and every tour satisfies the degree-two
equations away from the distinguished root. This is the correctness guarantee behind the
branch-and-bound node bound derived from the `1`-tree relaxation `(8.7)`. -/
theorem one_tree_lagrangian_node_bound_le_tour_cost
    (root : V)
    (delta : V → Finset E)
    (tours one_trees : Finset (Finset E))
    (c : E → ℝ)
    (node : SymmetricTspBranchNode E)
    (lam : V → ℝ)
    (htour_subset : tours ⊆ one_trees)
    (hdegree_two : ∀ T ∈ tours, ∀ i, i ≠ root → (delta i ∩ T).card = 2)
    {T : Finset E}
    (hT : T ∈ node.compatibleFamily tours) :
    one_tree_lagrangian_node_bound root delta one_trees c node lam ≤
      (((one_tree_cost c T : ℝ) : WithTop ℝ)) := by
  -- Unpack node compatibility so the tour membership and node feasibility are available separately.
  have hT_data : T ∈ tours ∧ node.Allows T := by
    simpa using hT
  have hT_tours : T ∈ tours := hT_data.1
  have hT_oneTrees : T ∈ node.compatibleFamily one_trees := by
    simpa using And.intro (htour_subset hT_tours) hT_data.2
  -- On a tour, the degree-two equations force every Lagrangian penalty term to vanish.
  have hpenalty :
      Finset.sum (Finset.univ.erase root)
        (fun i ↦ lam i * (((delta i ∩ T).card : ℝ) - 2)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_ne : i ≠ root := (Finset.mem_erase.mp hi).1
    have hdeg : (((delta i ∩ T).card : ℝ) - 2) = 0 := by
      norm_num [hdegree_two T hT_tours i hi_ne]
    rw [hdeg]
    simp
  have hobjective :
      one_tree_lagrangian_objective root delta c lam T = one_tree_cost c T := by
    simp [one_tree_lagrangian_objective, hpenalty]
  -- Realizing the image defining the infimum at `T` gives the node lower bound inequality.
  have hbound :
      one_tree_lagrangian_node_bound root delta one_trees c node lam ≤
        (one_tree_lagrangian_objective root delta c lam T : WithTop ℝ) := by
    unfold one_tree_lagrangian_node_bound
    have himageFinite :
        (((fun S : Finset E ↦
            (one_tree_lagrangian_objective root delta c lam S : WithTop ℝ)) ''
          (↑(node.compatibleFamily one_trees) : Set (Finset E))) : Set (WithTop ℝ)).Finite := by
      exact (Finset.finite_toSet (node.compatibleFamily one_trees)).image _
    have himage :
        (one_tree_lagrangian_objective root delta c lam T : WithTop ℝ) ∈
          ((fun S : Finset E ↦
              (one_tree_lagrangian_objective root delta c lam S : WithTop ℝ)) ''
            (↑(node.compatibleFamily one_trees) : Set (Finset E))) :=
      Set.mem_image_of_mem _ hT_oneTrees
    exact csInf_le himageFinite.bddBelow himage
  -- Rewriting the realized objective value at the tour gives the desired cost bound.
  simpa [hobjective] using hbound

/-- A node-compatible `1`-tree solves the node subproblem for the chosen multiplier vector when it
belongs to the node-compatible family and attains the node's 1-tree Lagrangian bound. -/
def IsOptimalOneTreeLagrangianNodeSolution
    (root : V)
    (delta : V → Finset E)
    (one_trees : Finset (Finset E))
    (c : E → ℝ)
    (node : SymmetricTspBranchNode E)
    (lam : V → ℝ)
    (T : Finset E) : Prop :=
  T ∈ node.compatibleFamily one_trees ∧
    one_tree_lagrangian_node_bound root delta one_trees c node lam =
      (one_tree_lagrangian_objective root delta c lam T : WithTop ℝ)

namespace IsOptimalOneTreeLagrangianNodeSolution

theorem mem_compatibleFamily
    (root : V)
    (delta : V → Finset E)
    (one_trees : Finset (Finset E))
    (c : E → ℝ)
    {node : SymmetricTspBranchNode E}
    {lam : V → ℝ}
    {T : Finset E}
    (hT : IsOptimalOneTreeLagrangianNodeSolution root delta one_trees c node lam T) :
    T ∈ node.compatibleFamily one_trees :=
  hT.1

theorem bound_eq
    (root : V)
    (delta : V → Finset E)
    (one_trees : Finset (Finset E))
    (c : E → ℝ)
    {node : SymmetricTspBranchNode E}
    {lam : V → ℝ}
    {T : Finset E}
    (hT : IsOptimalOneTreeLagrangianNodeSolution root delta one_trees c node lam T) :
    one_tree_lagrangian_node_bound root delta one_trees c node lam =
      (one_tree_lagrangian_objective root delta c lam T : WithTop ℝ) :=
  hT.2

end IsOptimalOneTreeLagrangianNodeSolution

/-- An optimal node-compatible `1`-tree whose objective value is no less than the incumbent
certifies fathoming by the node's 1-tree Lagrangian lower bound. -/
theorem node_fathomed_by_one_tree_bound_of_isOptimalSolution
    (root : V)
    (delta : V → Finset E)
    (one_trees : Finset (Finset E))
    (c : E → ℝ)
    (node : SymmetricTspBranchNode E)
    (lam : V → ℝ)
    (T : Finset E)
    (incumbent : ℝ)
    (hoptimal : IsOptimalOneTreeLagrangianNodeSolution root delta one_trees c node lam T)
    (hincumbent :
      (incumbent : WithTop ℝ) ≤
        (one_tree_lagrangian_objective root delta c lam T : WithTop ℝ)) :
    node_fathomed_by_one_tree_bound root delta one_trees c node lam incumbent := by
  rw [node_fathomed_by_one_tree_bound,
    IsOptimalOneTreeLagrangianNodeSolution.bound_eq root delta one_trees c hoptimal]
  exact hincumbent

/-- Branch-and-bound step for Exercise 9.15. At a node for the symmetric traveling salesman
problem, one chooses a multiplier vector, evaluates the node's `1`-tree Lagrangian bound, fathoms
if the incumbent is already no greater than that bound, and otherwise branches on an edge not yet
fixed by the node into the include/exclude child nodes. -/
inductive OneTreeLagrangianBranchAndBoundStep
    (root : V)
    (delta : V → Finset E)
    (one_trees : Finset (Finset E))
    (c : E → ℝ)
    (incumbent : ℝ) :
    SymmetricTspBranchNode E → Prop
  /-- If the incumbent is no greater than the node's 1-tree Lagrangian lower bound, the node is
  fathomed. -/
  | fathom {node : SymmetricTspBranchNode E} {lam : V → ℝ}
      (hbounded : node_fathomed_by_one_tree_bound root delta one_trees c node lam incumbent) :
      OneTreeLagrangianBranchAndBoundStep root delta one_trees c incumbent node
  /-- Otherwise, after solving the node-compatible 1-tree Lagrangian subproblem for some
  multiplier vector, branch on an edge not yet fixed by the node. -/
  | branch {node : SymmetricTspBranchNode E} {lam : V → ℝ} {T : Finset E} {e : E}
      (hoptimal : IsOptimalOneTreeLagrangianNodeSolution root delta one_trees c node lam T)
      (hnot_fathomed :
        ¬ node_fathomed_by_one_tree_bound root delta one_trees c node lam incumbent)
      (hunfixed : e ∉ node.required ∪ node.forbidden) :
      OneTreeLagrangianBranchAndBoundStep root delta one_trees c incumbent node

end Exercise915
