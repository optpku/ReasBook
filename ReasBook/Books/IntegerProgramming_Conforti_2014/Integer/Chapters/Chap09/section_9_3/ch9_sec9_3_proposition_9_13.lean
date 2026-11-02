import Mathlib.GroupTheory.Perm.DomMulAct

-- Declarations for this item will be appended below by the statement pipeline.

open Set

-- Semantic search tool `lean_leansearch` was unavailable in this environment: `tool_search`
-- exposed no deferred Lean semantic-search tool, so this file uses a self-contained semantic API
-- for enumeration-tree nodes and isomorphism pruning.

section Proposition913

universe u

variable {α : Type u}

/-- A node of a `0/1` enumeration tree, recorded by the variables fixed to `0`, the variables
fixed to `1`, and the binary solutions feasible at that node. -/
structure EnumerationNode (α : Type u) where
  fixedZero : Set α
  fixedOne : Set α
  solutions : Set (α → Bool)

/-- The empty node is the default enumeration node. -/
instance : Inhabited (EnumerationNode α) where
  default :=
    { fixedZero := ∅
      fixedOne := ∅
      solutions := ∅ }

/-- Relabel a binary solution by the permutation `π` of the variable indices. -/
def permute_binary_solution (π : Equiv.Perm α) (x : α → Bool) : α → Bool :=
  x ∘ π.symm

/-- `permute_binary_solution` acts by precomposition with `π.symm`. -/
theorem permute_binary_solution_apply
    (π : Equiv.Perm α) (x : α → Bool) (a : α) :
    permute_binary_solution π x a = x (π.symm a) := rfl

/-- `permute_binary_solution π` is the canonical domain action of the inverse permutation `π⁻¹`
on binary solutions. -/
theorem permute_binary_solution_eq_domMulAct_smul
    (π : Equiv.Perm α) (x : α → Bool) :
    permute_binary_solution π x = DomMulAct.mk π⁻¹ • x := by
  rfl

/-- The feasible solutions of `node` after relabelling their coordinates by `π`. -/
def permuted_node_solutions (π : Equiv.Perm α) (node : EnumerationNode α) : Set (α → Bool) :=
  permute_binary_solution π '' node.solutions

/-- Membership in `permuted_node_solutions π node` means that the solution comes from a feasible
solution of `node` by applying the relabelling `π`. -/
theorem mem_permuted_node_solutions_iff
    (π : Equiv.Perm α) (node : EnumerationNode α) (x : α → Bool) :
    x ∈ permuted_node_solutions π node ↔
      ∃ y ∈ node.solutions, permute_binary_solution π y = x := Iff.rfl

namespace EnumerationNode

/-- Relabel all data of an enumeration node by the permutation `π`. -/
def permute (node : EnumerationNode α) (π : Equiv.Perm α) : EnumerationNode α where
  fixedZero := π '' node.fixedZero
  fixedOne := π '' node.fixedOne
  solutions := permuted_node_solutions π node

@[simp] theorem permute_fixedZero (node : EnumerationNode α) (π : Equiv.Perm α) :
    (node.permute π).fixedZero = π '' node.fixedZero := rfl

@[simp] theorem permute_fixedOne (node : EnumerationNode α) (π : Equiv.Perm α) :
    (node.permute π).fixedOne = π '' node.fixedOne := rfl

@[simp] theorem permute_solutions (node : EnumerationNode α) (π : Equiv.Perm α) :
    (node.permute π).solutions = permuted_node_solutions π node := rfl

/-- Membership in the solution set of `node.permute π` means that the solution comes from a
solution of `node` by relabelling its coordinates via `π`. -/
theorem mem_permute_solutions_iff
    (node : EnumerationNode α) (π : Equiv.Perm α) (x : α → Bool) :
    x ∈ (node.permute π).solutions ↔
      ∃ y ∈ node.solutions, permute_binary_solution π y = x :=
  mem_permuted_node_solutions_iff π node x

end EnumerationNode

/-- Two binary solutions are isomorphic if one is obtained from the other by a permutation from
the symmetry group `Γ`. -/
def solutions_are_isomorphic
    (Γ : Subgroup (Equiv.Perm α)) (x y : α → Bool) : Prop :=
  ∃ π ∈ Γ, permute_binary_solution π x = y

/-- Unfolding `solutions_are_isomorphic` gives a symmetry from `Γ` mapping `x` to `y`. -/
theorem solutions_are_isomorphic_iff
    (Γ : Subgroup (Equiv.Perm α)) (x y : α → Bool) :
    solutions_are_isomorphic Γ x y ↔ ∃ π ∈ Γ, permute_binary_solution π x = y := Iff.rfl

/-- `solutions_are_isomorphic` is the orbit relation for the canonical domain action of
permutations on binary solutions, expressed using the original subgroup `Γ`. -/
theorem solutions_are_isomorphic_iff_exists_domMulAct_smul
    (Γ : Subgroup (Equiv.Perm α)) (x y : α → Bool) :
    solutions_are_isomorphic Γ x y ↔ ∃ π ∈ Γ, DomMulAct.mk π • x = y := by
  constructor
  · rintro ⟨π, hπ, hxy⟩
    refine ⟨π⁻¹, Γ.inv_mem hπ, ?_⟩
    simpa [permute_binary_solution_eq_domMulAct_smul] using hxy
  · rintro ⟨π, hπ, hxy⟩
    refine ⟨π⁻¹, Γ.inv_mem hπ, ?_⟩
    simpa [permute_binary_solution_eq_domMulAct_smul] using hxy

/-- Solution isomorphism is symmetric because `Γ` is a subgroup. -/
theorem solutions_are_isomorphic_symm
    {Γ : Subgroup (Equiv.Perm α)} {x y : α → Bool}
    (hxy : solutions_are_isomorphic Γ x y) :
    solutions_are_isomorphic Γ y x := by
  rcases hxy with ⟨π, hπ, hπxy⟩
  refine ⟨π⁻¹, Γ.inv_mem hπ, ?_⟩
  funext a
  have h := congrFun hπxy (π a)
  simpa [permute_binary_solution_apply] using h.symm

/-- Two enumeration nodes are isomorphic when some permutation in `Γ` carries the fixed-to-`0`
set, the fixed-to-`1` set, and the feasible solution set of the second node onto those of the
first node. -/
def nodes_are_isomorphic
    (Γ : Subgroup (Equiv.Perm α)) (node₁ node₂ : EnumerationNode α) : Prop :=
  ∃ π ∈ Γ, node₂.permute π = node₁

/-- Unfolding `nodes_are_isomorphic` gives the relabelling data witnessing the node isomorphism. -/
theorem nodes_are_isomorphic_iff
    (Γ : Subgroup (Equiv.Perm α)) (node₁ node₂ : EnumerationNode α) :
    nodes_are_isomorphic Γ node₁ node₂ ↔
      ∃ π ∈ Γ,
        π '' node₂.fixedZero = node₁.fixedZero ∧
        π '' node₂.fixedOne = node₁.fixedOne ∧
        permuted_node_solutions π node₂ = node₁.solutions := by
  constructor
  · rintro ⟨π, hπ, hperm⟩
    refine ⟨π, hπ, ?_, ?_, ?_⟩
    · simpa using congrArg EnumerationNode.fixedZero hperm
    · simpa using congrArg EnumerationNode.fixedOne hperm
    · simpa using congrArg EnumerationNode.solutions hperm
  · rintro ⟨π, hπ, hzero, hone, hsolutions⟩
    refine ⟨π, hπ, ?_⟩
    cases node₂
    cases node₁
    cases hzero
    cases hone
    cases hsolutions
    rfl

/-- A node has an isomorphic node to its left when some earlier node in the enumeration order is
isomorphic to it via a permutation from `Γ`. -/
def has_isomorphic_node_to_left
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α) : Prop :=
  ∃ nodeLeft, leftOf nodeLeft node ∧ nodes_are_isomorphic Γ node nodeLeft

/-- Unfolding `has_isomorphic_node_to_left` yields an explicit left node together with the
isomorphism witness. -/
theorem has_isomorphic_node_to_left_iff
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α) :
    has_isomorphic_node_to_left Γ leftOf node ↔
      ∃ nodeLeft, leftOf nodeLeft node ∧ nodes_are_isomorphic Γ node nodeLeft := Iff.rfl

/-- The solutions of `node` that are already represented, up to isomorphism, by solutions in
nodes lying to the left of `node`. -/
def left_isomorphic_solution_set
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α) : Set (α → Bool) :=
  {x | ∃ nodeLeft, leftOf nodeLeft node ∧ ∃ y ∈ nodeLeft.solutions, solutions_are_isomorphic Γ x y}

/-- Unfolding `left_isomorphic_solution_set` says that `x` is represented by an isomorphic
solution in some node to the left. -/
theorem mem_left_isomorphic_solution_set_iff
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α)
    (x : α → Bool) :
    x ∈ left_isomorphic_solution_set Γ leftOf node ↔
      ∃ nodeLeft, leftOf nodeLeft node ∧
        ∃ y ∈ nodeLeft.solutions, solutions_are_isomorphic Γ x y := Iff.rfl

/-- A node is pruned by isomorphism when every feasible binary solution at that node is already
represented, up to isomorphism, by a solution in a node to its left. -/
def is_pruned_by_isomorphism
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α) : Prop :=
  node.solutions ⊆ left_isomorphic_solution_set Γ leftOf node

/-- Unfolding `is_pruned_by_isomorphism` yields the pointwise left-node isomorphic-covering
property. -/
theorem is_pruned_by_isomorphism_iff
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α) :
    is_pruned_by_isomorphism Γ leftOf node ↔
      ∀ x, x ∈ node.solutions →
        ∃ nodeLeft, leftOf nodeLeft node ∧
          ∃ y ∈ nodeLeft.solutions, solutions_are_isomorphic Γ x y := by
  constructor
  · intro hpruned x hx
    exact (mem_left_isomorphic_solution_set_iff Γ leftOf node x).1 (hpruned hx)
  · intro hpruned x hx
    exact (mem_left_isomorphic_solution_set_iff Γ leftOf node x).2 (hpruned x hx)

/-- Proposition 9.13 (1). If node `N_a` has an isomorphic node to its left in the enumeration
tree, then `N_a` is pruned by isomorphism. -/
theorem has_isomorphic_node_to_left_is_pruned_by_isomorphism
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α)
    (hleft : has_isomorphic_node_to_left Γ leftOf node) :
    is_pruned_by_isomorphism Γ leftOf node := by
  intro x hx
  rcases hleft with ⟨nodeLeft, hnodeLeft, π, hπ, hperm⟩
  have hx' : x ∈ (nodeLeft.permute π).solutions := by
    simpa [hperm] using hx
  rcases EnumerationNode.mem_permute_solutions_iff nodeLeft π x |>.1 hx' with ⟨y, hy, hyx⟩
  refine (mem_left_isomorphic_solution_set_iff Γ leftOf node x).2 ?_
  refine ⟨nodeLeft, hnodeLeft, y, hy, ?_⟩
  exact solutions_are_isomorphic_symm ⟨π, hπ, hyx⟩

/-- Proposition 9.13 (2). Conversely, if node `N_a` is pruned by isomorphism, then every
solution in `N_a` is isomorphic to a solution contained in some node to the left of `N_a`. -/
theorem pruned_by_isomorphism_has_left_isomorphic_solution
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α)
    (hpruned : is_pruned_by_isomorphism Γ leftOf node) :
    ∀ x, x ∈ node.solutions →
      ∃ nodeLeft, leftOf nodeLeft node ∧
        ∃ y ∈ nodeLeft.solutions, solutions_are_isomorphic Γ x y :=
  (is_pruned_by_isomorphism_iff Γ leftOf node).1 hpruned

end Proposition913
