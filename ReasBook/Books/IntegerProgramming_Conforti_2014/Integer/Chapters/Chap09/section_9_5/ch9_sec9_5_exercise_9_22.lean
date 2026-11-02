import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_exercise_9_13

open scoped BigOperators

-- Domain-style sampling for this file:
-- * primary domain: branch-and-bound enumeration trees for a symmetric binary MILP
-- * sampled owner abstractions:
--   - Chapter 9.5 `EnumerationTree` with its canonical `rootLabel` and `size` API
--   - Exercise 9.20's explicit source-facing enumeration object, which keeps only the symmetry
--     reduced data instead of rebuilding tree owners
--   - Exercise 9.21's recall-only pattern for purely canonical upstream notions
-- * source/core/bridge triage:
--   - `Exercise922Node` and the recursive tree are source-facing
--   - `EnumerationTree` is the core/canonical owner
--   - the public root/size theorems are bridge facts derived from that owner API
-- * primitive data: the explicit node labels and the recursive left-spine/right-leaf tree shape
-- * derived API: canonical `EnumerationTree.rootLabel` and `EnumerationTree.size` facts

section Exercise922

/-- The `0,1` feasible set from Exercise 9.22: binary vectors whose coordinates satisfy the
triple inequalities `x_i + x_j + x_k ≤ 2` on distinct indices. -/
def exercise_9_22_feasible_set (n : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (∀ i : Fin n, x i = 0 ∨ x i = 1) ∧
      ∀ ⦃i j k : Fin n⦄, i < j → j < k → x i + x j + x k ≤ 2}

/-- The objective function `∑_{j=1}^n x_j` from Exercise 9.22. -/
def exercise_9_22_objective {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, x j

/-- A node in the explicit Exercise 9.22 branch-and-bound tree. `spine m` means that the first `m`
variables have been fixed to `0` by repeated left branches. `rightLeaf m` is the right child
obtained by branching on `x_m = 1`, after which orbital fixing sets every other still-unfixed
variable to `0`. -/
inductive Exercise922Node where
  /-- The left-spine node after fixing the first `m` variables to `0`. -/
  | spine (m : ℕ)
  /-- The right child obtained by fixing `x_m = 1` and all other unfixed variables to `0`. -/
  | rightLeaf (m : ℕ)

/-- The subtree obtained after `m` successive left branches, with `remaining` variables still
unfixed before the next branch or terminal LP solve. When at most two variables remain unfixed,
the LP relaxation is already integral and the node is a leaf. -/
def exercise_9_22_complete_enumeration_tree_aux (m : ℕ) : ℕ → EnumerationTree Exercise922Node
  | 0 => .leaf (.spine m)
  | 1 => .leaf (.spine m)
  | 2 => .leaf (.spine m)
  | k + 3 =>
      .branch (.spine m)
        (exercise_9_22_complete_enumeration_tree_aux (m + 1) (k + 2))
        (.leaf (.rightLeaf m))

/-- Exercise 9.22. For the `0,1` linear program
`max ∑_{j=1}^n x_j` with constraints `x_i + x_j + x_k ≤ 2` on distinct indices and `n ≥ 3`,
the complete branch-and-bound enumeration tree with isomorphism pruning and orbital fixing is the
left-spine tree that repeatedly branches on the next unfixed variable, fathoms each right child by
fixing all remaining variables to `0`, and terminates once only two variables remain unfixed. -/
def exercise_9_22_complete_enumeration_tree (n : ℕ) : EnumerationTree Exercise922Node :=
  exercise_9_22_complete_enumeration_tree_aux 0 n

/-- Once at most two variables remain unfixed, the Exercise 9.22 recursion stops and the current
left-spine node is fathomed as a leaf. -/
theorem exercise_9_22_complete_enumeration_tree_aux_eq_leaf
    (m remaining : ℕ)
    (hremaining : remaining ≤ 2) :
    exercise_9_22_complete_enumeration_tree_aux m remaining = .leaf (.spine m) := by
  cases remaining with
  | zero => rfl
  | succ remaining =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          cases remaining with
          | zero => rfl
          | succ remaining =>
              omega

/-- When at least three variables remain unfixed, the Exercise 9.22 recursion branches at the
current left-spine node, continues recursively on the left child, and fathoms the right child
after orbital fixing. -/
theorem exercise_9_22_complete_enumeration_tree_aux_eq_branch
    (m k : ℕ) :
    exercise_9_22_complete_enumeration_tree_aux m (k + 3) =
      .branch (.spine m)
        (exercise_9_22_complete_enumeration_tree_aux (m + 1) (k + 2))
        (.leaf (.rightLeaf m)) :=
  rfl

/-- Every recursive Exercise 9.22 subtree is rooted at the current left-spine node. -/
theorem exercise_9_22_complete_enumeration_tree_aux_root
    (m remaining : ℕ) :
    (exercise_9_22_complete_enumeration_tree_aux m remaining).rootLabel = .spine m := by
  cases remaining with
  | zero => rfl
  | succ remaining =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          cases remaining with
          | zero => rfl
          | succ k => rfl

/-- Once at least three variables remain unfixed, the recursive Exercise 9.22 subtree has the
expected left-spine size `2 * remaining - 3`. -/
theorem exercise_9_22_complete_enumeration_tree_aux_size
    (m k : ℕ) :
    (exercise_9_22_complete_enumeration_tree_aux m (k + 3)).size = 2 * k + 3 := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
      change (exercise_9_22_complete_enumeration_tree_aux (m + 1) (k + 3)).size + 1 + 1 =
        2 * (k + 1) + 3
      rw [ih (m + 1)]
      omega

/-- The root of the Exercise 9.22 tree is the node where no variable has yet been fixed to `0`. -/
theorem exercise_9_22_complete_enumeration_tree_root
    (n : ℕ) :
    (exercise_9_22_complete_enumeration_tree n).rootLabel = .spine 0 := by
  simpa [exercise_9_22_complete_enumeration_tree] using
    exercise_9_22_complete_enumeration_tree_aux_root 0 n

/-- The Exercise 9.22 complete enumeration tree has `2 * n - 3` nodes for `n ≥ 3`. -/
theorem exercise_9_22_complete_enumeration_tree_size
    (n : ℕ)
    (hn : 3 ≤ n) :
    (exercise_9_22_complete_enumeration_tree n).size = 2 * n - 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [exercise_9_22_complete_enumeration_tree, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Nat.mul_add] using exercise_9_22_complete_enumeration_tree_aux_size 0 k

end Exercise922
