import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Matrix.Mul

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Domain-style sampling for this file:
-- * primary domain: SOS2 branching for piecewise-linear approximations in branch-and-bound
-- * sampled owner abstractions:
--   - mathlib's `stdSimplex`, the canonical owner for nonnegative breakpoint weights summing to `1`
--   - the local `BreakpointApproximation`, which should own the interpolated point/value API
--     instead of exposing duplicate standalone wrappers
--   - the Chapter 9 branch-node namespace pattern from `SingleIntegerBranchNode` and
--     `SymmetricTspBranchNode`, where child-node constructions live on the node owner
-- * source/core/bridge triage:
--   - the SOS2 separation statements and the separable approximation node are source-facing
--   - `stdSimplex ℝ (Fin (K + 2))` is the core/canonical owner for breakpoint-weight feasibility
--   - interpolated-point/objective and child-node constructors are bridge/view API derived from
--     those source-facing owners
-- * primitive data: the breakpoint family, sampled values, SOS2 adjacency predicate, and node
--   branch list
-- * derived API: breakpoint interpolation, node reconstruction/objective/feasibility, and child
--   node constructors

section Exercise916

/-- Explicit breakpoint data `l = s₀ < s₁ < ... < s_{K+1} = u` together with the sampled values
`f(s_k)` used for the piecewise-linear approximation in Exercise 9.16. -/
structure BreakpointApproximation (K : ℕ) where
  breakpoints : Fin (K + 2) → ℝ
  values : Fin (K + 2) → ℝ
  strictMono : StrictMono breakpoints

namespace BreakpointApproximation

/-- The lower endpoint `l = s₀` of the breakpoint family. -/
def lower {K : ℕ} (data : BreakpointApproximation K) : ℝ :=
  data.breakpoints 0

/-- The upper endpoint `u = s_{K+1}` of the breakpoint family. -/
def upper {K : ℕ} (data : BreakpointApproximation K) : ℝ :=
  data.breakpoints (Fin.last (K + 1))

/-- The interpolated `x`-value recovered from the breakpoint convex combination `lam`. -/
def interpolatedPoint {K : ℕ} (data : BreakpointApproximation K) (lam : Fin (K + 2) → ℝ) : ℝ :=
  ∑ k, lam k * data.breakpoints k

/-- The interpolated objective value `g(x) = ∑ k λ_k f(s_k)` attached to the breakpoint weights
`lam`. -/
def interpolatedValue {K : ℕ} (data : BreakpointApproximation K) (lam : Fin (K + 2) → ℝ) : ℝ :=
  ∑ k, lam k * data.values k

end BreakpointApproximation

/-- `sos2_weights lam` means that any two positive weights occur at breakpoint indices of distance
at most `1`, so at most two adjacent `λ_k` can be positive. -/
def sos2_weights {K : ℕ} (lam : Fin (K + 2) → ℝ) : Prop :=
  ∀ ⦃i j : Fin (K + 2)⦄, 0 < lam i → 0 < lam j → Nat.dist i.1 j.1 ≤ 1

/-- For the interior breakpoint indexed by `p.succ`, this is the sum of all breakpoint weights
strictly to its left. The source notation is `∑_{k=1}^{p-1} λ_k = 0`, written in zero-based
`Fin` indexing. -/
def sos2_left_mass {K : ℕ} (p : Fin K) (lam : Fin (K + 2) → ℝ) : ℝ :=
  ∑ k, if k.1 < p.1.succ then lam k else 0

/-- For the interior breakpoint indexed by `p.succ`, this is the sum of all breakpoint weights
strictly to its right. The source notation is `∑_{k=p+1}^{n} λ_k = 0`, written in zero-based
`Fin` indexing. -/
def sos2_right_mass {K : ℕ} (p : Fin K) (lam : Fin (K + 2) → ℝ) : ℝ :=
  ∑ k, if p.1.succ < k.1 then lam k else 0

/-- The disjunctive separation obtained by branching at the interior breakpoint indexed by
`p.succ`: either all mass strictly to the left is zero or all mass strictly to the right is zero. -/
def sos2_branch_separation {K : ℕ} (p : Fin K) (lam : Fin (K + 2) → ℝ) : Prop :=
  sos2_left_mass p lam = 0 ∨ sos2_right_mass p lam = 0

/-- Helper for Exercise 9.16: indices strictly on opposite sides of the pivot `p.1.succ` differ
by at least `2`, so they cannot both support positive SOS2 weights. -/
lemma dist_ge_two_of_left_right_of_pivot
    {K : ℕ} (p : Fin K) (i j : Fin (K + 2))
    (hi : i.1 < p.1.succ) (hj : p.1.succ < j.1) :
    2 ≤ Nat.dist i.1 j.1 := by
  -- Rewrite the distance using the left-to-right order determined by the pivot inequalities.
  rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt (lt_trans hi hj))]
  omega

/-- Helper for Exercise 9.16: once one breakpoint weight is positive strictly to the left of the
pivot, the SOS2 adjacency rule forces every strictly right weight to vanish, so the right-side
mass is zero. -/
lemma sos2_right_mass_eq_zero_of_left_positive
    {K : ℕ} (lam : Fin (K + 2) → ℝ)
    (hlam : lam ∈ stdSimplex ℝ (Fin (K + 2)))
    (hsos2 : sos2_weights lam) (p : Fin K) (i : Fin (K + 2))
    (hi : i.1 < p.1.succ) (hi_pos : 0 < lam i) :
    sos2_right_mass p lam = 0 := by
  have hzero : ∀ k : Fin (K + 2), p.1.succ < k.1 → lam k = 0 := by
    intro k hk
    have hnot_pos : ¬ 0 < lam k := by
      intro hk_pos
      -- Positive weights on both sides of the pivot would be too far apart for an SOS2 vector.
      have hdist_ge : 2 ≤ Nat.dist i.1 k.1 :=
        dist_ge_two_of_left_right_of_pivot p i k hi hk
      have hdist_le : Nat.dist i.1 k.1 ≤ 1 := hsos2 hi_pos hk_pos
      have : 2 ≤ 1 := le_trans hdist_ge hdist_le
      omega
    exact le_antisymm (le_of_not_gt hnot_pos) (hlam.1 k)
  -- Collapse the guarded sum by proving that every strictly right term is zero.
  unfold sos2_right_mass
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hk : p.1.succ < k.1
  · simp [hk, hzero k hk]
  · simp [hk]

/-- Helper for Exercise 9.16: if no breakpoint weight is positive strictly to the left of the
pivot, then nonnegativity forces all left-side weights to vanish, so the left-side mass is zero. -/
lemma sos2_left_mass_eq_zero_of_no_left_positive
    {K : ℕ} (lam : Fin (K + 2) → ℝ)
    (hlam : lam ∈ stdSimplex ℝ (Fin (K + 2))) (p : Fin K)
    (hno_left : ∀ i : Fin (K + 2), i.1 < p.1.succ → ¬ 0 < lam i) :
    sos2_left_mass p lam = 0 := by
  have hzero : ∀ i : Fin (K + 2), i.1 < p.1.succ → lam i = 0 := by
    intro i hi
    -- On the left of the pivot, nonnegativity plus `¬ 0 < lam i` gives `lam i = 0`.
    exact le_antisymm (le_of_not_gt (hno_left i hi)) (hlam.1 i)
  -- Collapse the guarded sum by proving that every strictly left term is zero.
  unfold sos2_left_mass
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hk : k.1 < p.1.succ
  · simp [hk, hzero k hk]
  · simp [hk]

/-- Exercise 9.16 (1). For SOS2 breakpoint weights, every interior breakpoint yields a valid
branching disjunction: all positive mass lies on or to the left of that breakpoint, or all
positive mass lies on or to the right of it. -/
theorem exercise_9_16_valid_sos2_separation
    {K : ℕ} (lam : Fin (K + 2) → ℝ)
    (hlam : lam ∈ stdSimplex ℝ (Fin (K + 2)))
    (hsos2 : sos2_weights lam)
    (p : Fin K) :
    sos2_branch_separation p lam := by
  by_cases hleft_pos : ∃ i : Fin (K + 2), i.1 < p.1.succ ∧ 0 < lam i
  · rcases hleft_pos with ⟨i, hi, hi_pos⟩
    -- A positive left weight forces the entire right side to vanish.
    exact Or.inr (sos2_right_mass_eq_zero_of_left_positive lam hlam hsos2 p i hi hi_pos)
  · -- Otherwise every strictly left weight is nonpositive, hence zero by simplex nonnegativity.
    have hno_left : ∀ i : Fin (K + 2), i.1 < p.1.succ → ¬ 0 < lam i := by
      intro i hi hi_pos
      exact hleft_pos ⟨i, hi, hi_pos⟩
    exact Or.inl (sos2_left_mass_eq_zero_of_no_left_positive lam hlam p hno_left)

/-- The chosen side of an SOS2 branching disjunction. -/
inductive SOS2BranchSide where
  | left
  | right

/-- A branch choice for one coordinate of the separable nonlinear program, obtained by selecting
an interior breakpoint and deciding whether to keep only the left or only the right side of the
SOS2 disjunction. -/
structure SOS2BranchChoice {n : ℕ} (K : Fin n → ℕ) where
  coordinate : Fin n
  pivot : Fin (K coordinate)
  side : SOS2BranchSide

namespace SOS2BranchChoice

/-- The branch choice that keeps only the left side of the SOS2 disjunction at `(j, p)`. -/
def left {n : ℕ} {K : Fin n → ℕ} (j : Fin n) (p : Fin (K j)) : SOS2BranchChoice K where
  coordinate := j
  pivot := p
  side := .left

/-- The branch choice that keeps only the right side of the SOS2 disjunction at `(j, p)`. -/
def right {n : ℕ} {K : Fin n → ℕ} (j : Fin n) (p : Fin (K j)) : SOS2BranchChoice K where
  coordinate := j
  pivot := p
  side := .right

/-- A branch choice holds for `lam` when the weights on the excluded side of the chosen interior
breakpoint sum to zero. -/
def holds {n : ℕ} {K : Fin n → ℕ}
    (choice : SOS2BranchChoice K) (lam : (j : Fin n) → Fin (K j + 2) → ℝ) : Prop :=
  match choice.side with
  | .left => sos2_right_mass choice.pivot (lam choice.coordinate) = 0
  | .right => sos2_left_mass choice.pivot (lam choice.coordinate) = 0

@[simp] theorem holds_left {n : ℕ} {K : Fin n → ℕ} (j : Fin n) (p : Fin (K j))
    (lam : (i : Fin n) → Fin (K i + 2) → ℝ) :
    (left j p).holds lam ↔ sos2_right_mass p (lam j) = 0 := by
  rfl

@[simp] theorem holds_right {n : ℕ} {K : Fin n → ℕ} (j : Fin n) (p : Fin (K j))
    (lam : (i : Fin n) → Fin (K i + 2) → ℝ) :
    (right j p).holds lam ↔ sos2_left_mass p (lam j) = 0 := by
  rfl

end SOS2BranchChoice

/-- A branch-and-bound node for the piecewise-linear approximation of a separable nonlinear
program `max ∑ j f_j(x_j)` subject to `A x ≤ b` and `l ≤ x ≤ u`. The active branch list records
the SOS2 disjunction sides imposed so far. -/
structure SeparableNonlinearApproximationNode (m n : ℕ) (K : Fin n → ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  lower : Fin n → ℝ
  upper : Fin n → ℝ
  approximation : (j : Fin n) → BreakpointApproximation (K j)
  activeBranches : List (SOS2BranchChoice K)
  approximation_bounds :
    ∀ j, (approximation j).lower = lower j ∧ (approximation j).upper = upper j

namespace SeparableNonlinearApproximationNode

/-- The vector `x` reconstructed from the current breakpoint weights of every coordinate. -/
def reconstructedPoint
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (lam : (j : Fin n) → Fin (K j + 2) → ℝ) : Fin n → ℝ :=
  fun j ↦ (node.approximation j).interpolatedPoint (lam j)

/-- The separable piecewise-linear objective value attached to the current breakpoint weights. -/
def approximateObjective
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (lam : (j : Fin n) → Fin (K j + 2) → ℝ) : ℝ :=
  ∑ j, (node.approximation j).interpolatedValue (lam j)

/-- The active branching disjunctions of a node are satisfied by `lam` when each stored branch
choice holds for the corresponding coordinate weights. -/
def branchConstraintsSatisfied
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (lam : (j : Fin n) → Fin (K j + 2) → ℝ) : Prop :=
  ∀ choice ∈ node.activeBranches, choice.holds lam

/-- The LP relaxation at a branch-and-bound node is feasible when each coordinate uses convex
breakpoint weights, the reconstructed point satisfies `A x ≤ b` and `l ≤ x ≤ u`, and all active
SOS2 branch choices hold. -/
def relaxationFeasible
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (lam : (j : Fin n) → Fin (K j + 2) → ℝ) : Prop :=
  (∀ j, lam j ∈ stdSimplex ℝ (Fin (K j + 2))) ∧
    (∀ i, (node.A.mulVec (node.reconstructedPoint lam)) i ≤ node.b i) ∧
    (∀ j,
      node.lower j ≤ (node.reconstructedPoint lam) j ∧
        (node.reconstructedPoint lam) j ≤ node.upper j) ∧
    node.branchConstraintsSatisfied lam

/-- The child node obtained by adding the left side of the chosen SOS2 branching disjunction. -/
def leftChild
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (j : Fin n) (p : Fin (K j)) :
    SeparableNonlinearApproximationNode m n K :=
  { node with activeBranches := SOS2BranchChoice.left j p :: node.activeBranches }

/-- The child node obtained by adding the right side of the chosen SOS2 branching disjunction. -/
def rightChild
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (j : Fin n) (p : Fin (K j)) :
    SeparableNonlinearApproximationNode m n K :=
  { node with activeBranches := SOS2BranchChoice.right j p :: node.activeBranches }

/-- Exercise 9.16 (2). Branching on coordinate `j` at the interior breakpoint `p` replaces a
node by the two child nodes obtained by adding the left and right sides of the SOS2 separation. -/
def branchChildren
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (j : Fin n) (p : Fin (K j)) :
    SeparableNonlinearApproximationNode m n K × SeparableNonlinearApproximationNode m n K :=
  (node.leftChild j p, node.rightChild j p)

@[simp] theorem branchConstraintsSatisfied_leftChild
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (j : Fin n) (p : Fin (K j)) (lam : (i : Fin n) → Fin (K i + 2) → ℝ) :
    (node.leftChild j p).branchConstraintsSatisfied lam ↔
      (SOS2BranchChoice.left j p).holds lam ∧ node.branchConstraintsSatisfied lam := by
  simp [leftChild, branchConstraintsSatisfied]

@[simp] theorem branchConstraintsSatisfied_rightChild
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (j : Fin n) (p : Fin (K j)) (lam : (i : Fin n) → Fin (K i + 2) → ℝ) :
    (node.rightChild j p).branchConstraintsSatisfied lam ↔
      (SOS2BranchChoice.right j p).holds lam ∧ node.branchConstraintsSatisfied lam := by
  simp [rightChild, branchConstraintsSatisfied]

end SeparableNonlinearApproximationNode

/-- Any SOS2-feasible solution at a parent node satisfies the branch constraints of at least one
of the two child nodes created by branching on a chosen coordinate and interior breakpoint. -/
theorem exercise_9_16_branch_and_bound_children_spec
    {m n : ℕ} {K : Fin n → ℕ} (node : SeparableNonlinearApproximationNode m n K)
    (j : Fin n) (p : Fin (K j))
    (lam : (i : Fin n) → Fin (K i + 2) → ℝ)
    (hbranch : node.branchConstraintsSatisfied lam)
    (hweight : lam j ∈ stdSimplex ℝ (Fin (K j + 2)))
    (hsos2 : sos2_weights (lam j)) :
    (node.leftChild j p).branchConstraintsSatisfied lam ∨
      (node.rightChild j p).branchConstraintsSatisfied lam := by
  -- Branch on the coordinate-level SOS2 disjunction and send each side to the matching child.
  rcases exercise_9_16_valid_sos2_separation (lam := lam j) hweight hsos2 p with hleft | hright
  · right
    rw [SeparableNonlinearApproximationNode.branchConstraintsSatisfied_rightChild]
    constructor
    · simpa using hleft
    · exact hbranch
  · left
    rw [SeparableNonlinearApproximationNode.branchConstraintsSatisfied_leftChild]
    constructor
    · simpa using hright
    · exact hbranch

end Exercise916
