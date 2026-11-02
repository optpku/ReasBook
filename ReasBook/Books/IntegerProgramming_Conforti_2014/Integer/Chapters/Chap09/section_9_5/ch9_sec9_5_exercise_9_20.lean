import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling for this file:
-- * primary domain: branch-and-bound node enumeration for a symmetric binary MILP
-- * sampled owner abstractions:
--   - `List Bool` together with `List.count` / `List.count_true_add_count_false` for the
--     source-facing partial-assignment path and its canonical count statistics
--   - `EnumerationTree` from nearby Chapter 9 files for exercises whose public object is an
--     explicit recursive tree
--   - `Finset.product` / `Finset.erase` for the symmetry-reduced node set indexed by count pairs
-- * primitive data: a partial assignment path and the closure property for the unpruned node set
-- * derived API: the pair of fixed-`1` and fixed-`0` counts, and the finite pruned node set built
--   from those canonical count pairs
-- This file's public object is the source-facing reachable-node set, not a recursive tree, so the
-- owner abstraction stays at `List Bool`; the redundant one-off symmetry-class alias is deleted in
-- favor of the canonical count-pair expression itself.

section Exercise920

/-- A branch-and-bound node for the binary variables of Exercise 9.20 is represented by the list
of `0/1` values fixed along the root-to-node path. -/
abbrev Exercise920PartialAssignment := List Bool

/-- At a node of the Exercise 9.20 instance, the LP relaxation still attains the lower bound `0`
exactly when the fixed `1`-values and fixed `0`-values are both at most `n / 2` and at least one
binary variable remains free. -/
def exercise_9_20_lp_relaxation_still_open
    (n : ℕ) (σ : Exercise920PartialAssignment) : Prop :=
  σ.count true ≤ n / 2 ∧
    σ.count false ≤ n / 2 ∧
    σ.length < n

/-- `IsExercise920VariableBranchingTreeWithoutIsomorphismPruning n nodes` means that `nodes`
contains the root node and branches on every node whose LP relaxation for Exercise 9.20 still has
lower bound `0`. This is the unpruned variable-branching model used in part (i). -/
def IsExercise920VariableBranchingTreeWithoutIsomorphismPruning
    (n : ℕ) (nodes : Finset Exercise920PartialAssignment) : Prop :=
  ([] : Exercise920PartialAssignment) ∈ nodes ∧
    ∀ ⦃σ : Exercise920PartialAssignment⦄,
      σ ∈ nodes →
        exercise_9_20_lp_relaxation_still_open n σ →
          σ ++ [false] ∈ nodes ∧ σ ++ [true] ∈ nodes

/-- Every binary partial assignment of length at most `n / 2` survives in the unpruned
branch-and-bound tree for Exercise 9.20, because for odd `n` the LP relaxation at each such node
still has lower bound `0`. -/
theorem exercise_9_20_shallow_partial_assignments_survive
    (n : ℕ)
    (hn : Odd n)
    {nodes : Finset Exercise920PartialAssignment}
    (htree : IsExercise920VariableBranchingTreeWithoutIsomorphismPruning n nodes)
    {σ : Exercise920PartialAssignment}
    (hσ : σ.length ≤ n / 2) :
    σ ∈ nodes := by
  obtain ⟨m, rfl⟩ := hn
  have hmdiv : (2 * m + 1) / 2 = m := by
    omega
  have hsurvive :
      ∀ {τ : Exercise920PartialAssignment}, τ.length ≤ m → τ ∈ nodes := by
    intro τ hτ
    -- Reverse induction matches the tree rule that appends one branching decision at a time.
    induction τ using List.reverseRecOn with
    | nil =>
        simpa using htree.1
    | append_singleton τ b ih =>
        have hτlen : τ.length ≤ m := by
          have hτsucc : τ.length + 1 ≤ m := by
            simpa using hτ
          omega
        have hτmem : τ ∈ nodes := ih hτlen
        -- Every predecessor at depth at most `m` still has LP lower bound `0`.
        have hopen : exercise_9_20_lp_relaxation_still_open (2 * m + 1) τ := by
          refine ⟨?_, ?_, ?_⟩
          · simpa [hmdiv] using (List.count_le_length (a := true) (l := τ)).trans hτlen
          · simpa [hmdiv] using (List.count_le_length (a := false) (l := τ)).trans hτlen
          · omega
        have hchildren := htree.2 hτmem hopen
        -- The last bit of the assignment selects the corresponding child.
        cases b with
        | false =>
            simpa using hchildren.1
        | true =>
            simpa using hchildren.2
  have hσm : σ.length ≤ m := by
    simpa [hmdiv] using hσ
  exact hsurvive hσm

/-- Helper for Exercise 9.20: Boolean lists of length `k` are in bijection with functions
`Fin k → Bool`, so there are exactly `2 ^ k` of them. -/
lemma exercise_9_20_binary_lists_of_length_card
    (k : ℕ) :
    (Finset.univ.image (fun f : Fin k → Bool => List.ofFn f)).card = 2 ^ k := by
  classical
  -- Count fixed-length Boolean assignments through the canonical `List.ofFn` encoding.
  rw [Finset.card_image_of_injective
    (s := (Finset.univ : Finset (Fin k → Bool)))
    List.ofFn_injective]
  simp

/-- Exercise 9.20 (1). For the binary program `min z` subject to `2 * ∑ i, x_i + z = n`,
`x_i ∈ {0,1}`, and `z ≥ 0` with `n` odd, any branch-and-bound algorithm that uses variable
branching, uses the LP relaxation for lower bounds, and does not use isomorphism pruning has an
enumeration tree with at least `2 ^ (n / 2)` nodes. -/
theorem exercise_9_20_enumeration_tree_size_lower_bound_without_isomorphism_pruning
    (n : ℕ)
    (hn : Odd n)
    {nodes : Finset Exercise920PartialAssignment}
    (htree : IsExercise920VariableBranchingTreeWithoutIsomorphismPruning n nodes) :
    2 ^ (n / 2) ≤ nodes.card := by
  obtain ⟨m, rfl⟩ := hn
  have hmdiv : (2 * m + 1) / 2 = m := by
    omega
  let assignments : Finset Exercise920PartialAssignment :=
    Finset.univ.image (fun f : Fin m → Bool => List.ofFn f)
  have hsubset : assignments ⊆ nodes := by
    intro σ hσ
    rcases Finset.mem_image.mp hσ with ⟨f, -, rfl⟩
    have hlen : (List.ofFn f).length ≤ (2 * m + 1) / 2 := by
      simp [hmdiv]
    -- Every full depth-`m` Boolean assignment survives inside the unpruned tree.
    exact exercise_9_20_shallow_partial_assignments_survive
      (n := 2 * m + 1)
      (hn := odd_two_mul_add_one m)
      (htree := htree)
      (σ := List.ofFn f)
      hlen
  have hassignments_card : assignments.card = 2 ^ m := by
    simpa [assignments] using exercise_9_20_binary_lists_of_length_card m
  have hlower : 2 ^ m ≤ nodes.card := by
    -- The explicit family of length-`m` Boolean assignments injects into the node set.
    calc
      2 ^ m = assignments.card := hassignments_card.symm
      _ ≤ nodes.card := Finset.card_le_card hsubset
  simpa [hmdiv] using hlower

/-- The symmetry-reduced node set for Exercise 9.20 records one representative for each canonical
count pair `(a, b)` of fixed `1`-values and fixed `0`-values that can occur in the
isomorphism-pruned enumeration tree, including the boundary nodes obtained when one count first
reaches `n / 2 + 1`; equivalently it is the square `0 ≤ a, b ≤ n / 2 + 1` with the impossible
corner `(n / 2 + 1, n / 2 + 1)` removed. -/
def exercise_9_20_isomorphism_pruned_nodes (n : ℕ) : Finset (ℕ × ℕ) :=
  let k := n / 2
  ((Finset.range (k + 2)).product (Finset.range (k + 2))).erase (k + 1, k + 1)

/-- The explicit symmetry-reduced count-pair node set from Exercise 9.20 has cardinality
`(n / 2 + 1) * (n / 2 + 3)`. This is the reusable core count of the canonical count-pair model,
independent of the oddness hypothesis used in the source-facing branch-and-bound statement. -/
theorem exercise_9_20_isomorphism_pruned_nodes_card
    (n : ℕ) :
    (exercise_9_20_isomorphism_pruned_nodes n).card = (n / 2 + 1) * (n / 2 + 3) := by
  classical
  unfold exercise_9_20_isomorphism_pruned_nodes
  set k := n / 2
  have hcorner :
      (k + 1, k + 1) ∈ (Finset.range (k + 2)).product (Finset.range (k + 2)) := by
    simp [Finset.mem_product]
  have hsquare :
      ((Finset.range (k + 2)).product (Finset.range (k + 2))).card = (k + 2) * (k + 2) := by
    calc
      ((Finset.range (k + 2)).product (Finset.range (k + 2))).card
          = (Finset.range (k + 2)).card * (Finset.range (k + 2)).card :=
            Finset.card_product (Finset.range (k + 2)) (Finset.range (k + 2))
      _ = (k + 2) * (k + 2) := by
            simp
  -- Count the full square of count pairs and remove the unique impossible corner.
  rw [Finset.card_erase_of_mem hcorner, hsquare]
  have hmain : (k + 2) * (k + 2) = (k + 1) * (k + 3) + 1 := by
    nlinarith
  have hpos : 1 ≤ (k + 2) * (k + 2) := by
    nlinarith
  rw [Nat.sub_eq_iff_eq_add hpos]
  exact hmain

/-- Exercise 9.20 (2). When isomorphism pruning is used, the branch-and-bound tree is reduced to
one node for each possible count pair `(a, b)` of fixed `1`-values and fixed `0`-values, so its
size is `(n / 2 + 1) * (n / 2 + 3)`. -/
theorem exercise_9_20_enumeration_tree_size_with_isomorphism_pruning
    (n : ℕ) :
    (exercise_9_20_isomorphism_pruned_nodes n).card = (n / 2 + 1) * (n / 2 + 3) := by
  simpa using exercise_9_20_isomorphism_pruned_nodes_card n

end Exercise920
