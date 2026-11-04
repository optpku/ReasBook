/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Domain-style sampling for this file:
-- * primary domain: branch-and-bound for a mixed-integer linear program with one integer variable
-- * sampled owner abstractions:
--   - Chapter 4's `rational_mixed_polyhedron`, `mixed_integer_points`, and
--     `mixed_linear_objective`, which are the canonical owners for the linear-programming data
--   - mathlib's `Int.fract`, whose zero/nonzero predicate is the canonical owner for a real
--     value being integral/fractional
--   - the local Chapter 9 `EnumerationTree`, which is reused downstream as the owner of explicit
--     binary branch-and-bound trees
--   - the local `SingleIntegerBranchNode`, which should own the canonical branch-node constructors
--     instead of duplicating them in downstream coordinate-specialized files
-- * source/core/bridge triage:
--   - `SingleIntegerBranchNode`, `OneIntegerVariableMILP`, and
--     `IsVariableBranchingWithLpLowerBoundsTree` are source-facing
--   - Chapter 4 mixed-space linear-programming owners and `Int.fract` are the core/canonical
--     owners reused here
--   - downstream coordinate-specialized branch nodes are bridge/view uses of
--     `SingleIntegerBranchNode`
-- * primitive data: node bounds, mixed-linear constraint matrices, linear objective
--   coefficients, and the recursive tree shape
-- * derived API: branch-node constructor abbreviations such as fixed/equality and split nodes

section Exercise913

universe u

/-- A branch-and-bound node for a problem with one integer variable records optional lower and
upper integer bounds on that variable. -/
structure SingleIntegerBranchNode where
  lowerBound : Option ℤ
  upperBound : Option ℤ

namespace SingleIntegerBranchNode

/-- The root node has no branching bounds on the unique integer variable. -/
def root : SingleIntegerBranchNode :=
  ⟨none, none⟩

/-- The node imposing the equality branch `z = t`. -/
def fixed (t : ℤ) : SingleIntegerBranchNode :=
  ⟨some t, some t⟩

/-- The node imposing the split branch `z ≤ t`. -/
def leftSplit (t : ℤ) : SingleIntegerBranchNode :=
  ⟨none, some t⟩

/-- The node imposing the split branch `t ≤ z`. -/
def rightSplit (t : ℤ) : SingleIntegerBranchNode :=
  ⟨some t, none⟩

/-- The real value `x` is feasible for the node bounds when it satisfies the recorded lower and
upper integer restrictions. -/
def Allows (N : SingleIntegerBranchNode) (x : ℝ) : Prop :=
  (match N.lowerBound with
    | some lb => (lb : ℝ) ≤ x
    | none => True) ∧
    (match N.upperBound with
      | some ub => x ≤ (ub : ℝ)
      | none => True)

/-- The left child created by variable branching at a fractional LP value `x` refines the
inherited interval by imposing the additional bound `z ≤ ⌊x⌋`. -/
noncomputable def leftChild (N : SingleIntegerBranchNode) (x : ℝ) : SingleIntegerBranchNode :=
  ⟨N.lowerBound,
    some <| match N.upperBound with
      | some ub => min ub (Int.floor x)
      | none => Int.floor x⟩

/-- The right child created by variable branching at a fractional LP value `x` refines the
inherited interval by imposing the additional bound `⌈x⌉ ≤ z`. -/
noncomputable def rightChild (N : SingleIntegerBranchNode) (x : ℝ) : SingleIntegerBranchNode :=
  ⟨some <| match N.lowerBound with
      | some lb => max lb (Int.ceil x)
      | none => Int.ceil x,
    N.upperBound⟩

@[simp] theorem allows_root (x : ℝ) : root.Allows x := by
  simp [root, Allows]

@[simp] theorem allows_fixed_iff (t : ℤ) (x : ℝ) : (fixed t).Allows x ↔ x = t := by
  constructor
  · rintro ⟨hl, hu⟩
    exact le_antisymm hu hl
  · intro hx
    simp [fixed, Allows, hx]

@[simp] theorem allows_leftSplit_iff (t : ℤ) (x : ℝ) : (leftSplit t).Allows x ↔ x ≤ t := by
  simp [leftSplit, Allows]

@[simp] theorem allows_rightSplit_iff (t : ℤ) (x : ℝ) : (rightSplit t).Allows x ↔ t ≤ x := by
  simp [rightSplit, Allows]

@[simp] theorem leftChild_lowerBound (N : SingleIntegerBranchNode) (x : ℝ) :
    (N.leftChild x).lowerBound = N.lowerBound :=
  rfl

@[simp] theorem leftChild_upperBound (N : SingleIntegerBranchNode) (x : ℝ) :
    (N.leftChild x).upperBound =
      some
        (match N.upperBound with
        | some ub => min ub (Int.floor x)
        | none => Int.floor x) :=
  rfl

@[simp] theorem rightChild_lowerBound (N : SingleIntegerBranchNode) (x : ℝ) :
    (N.rightChild x).lowerBound =
      some
        (match N.lowerBound with
        | some lb => max lb (Int.ceil x)
        | none => Int.ceil x) :=
  rfl

@[simp] theorem rightChild_upperBound (N : SingleIntegerBranchNode) (x : ℝ) :
    (N.rightChild x).upperBound = N.upperBound :=
  rfl

@[simp] theorem allows_leftChild_iff (N : SingleIntegerBranchNode) (x z : ℝ) :
    (N.leftChild x).Allows z ↔ N.Allows z ∧ z ≤ Int.floor x := by
  cases h : N.upperBound <;>
    simp [Allows, leftChild, h, and_assoc, and_left_comm, and_comm]

@[simp] theorem allows_rightChild_iff (N : SingleIntegerBranchNode) (x z : ℝ) :
    (N.rightChild x).Allows z ↔ N.Allows z ∧ Int.ceil x ≤ z := by
  cases h : N.lowerBound <;>
    simp [Allows, rightChild, h, and_assoc, and_left_comm, and_comm]

end SingleIntegerBranchNode

/-- A mixed integer linear program with one distinguished integer variable and `n` continuous
variables. Its LP relaxation is the mixed polyhedron
`{(x, y) | A x + G y ≤ b} ⊆ ℝ × ℝ^n`, and its mixed-integer feasible set is obtained by requiring
the unique integer coordinate `x` to lie in `ℤ`. -/
structure OneIntegerVariableMILP (m n : ℕ) where
  integerMatrix : Matrix (Fin m) (Fin 1) ℚ
  continuousMatrix : Matrix (Fin m) (Fin n) ℚ
  rhs : Fin m → ℚ
  integerObjective : Fin 1 → ℝ
  continuousObjective : Fin n → ℝ

namespace OneIntegerVariableMILP

variable {m n : ℕ}

/-- The LP relaxation feasible region of `P`. -/
def lpRelaxation (P : OneIntegerVariableMILP m n) : Set (MixedRealPoint 1 n) :=
  rational_mixed_polyhedron P.integerMatrix P.continuousMatrix P.rhs

/-- The mixed-integer feasible region of `P`, obtained by requiring the unique distinguished
integer coordinate to be integral. -/
def mipFeasibleSet (P : OneIntegerVariableMILP m n) : Set (MixedRealPoint 1 n) :=
  mixed_integer_points P.lpRelaxation

/-- The linear objective value of `P` at `(x, y)`. -/
def objectiveValue (P : OneIntegerVariableMILP m n) (xy : MixedRealPoint 1 n) : ℝ :=
  mixed_linear_objective P.integerObjective P.continuousObjective xy

/-- The unique distinguished coordinate of a point in `ℝ × ℝ^n`. -/
def integerValue (xy : MixedRealPoint 1 n) : ℝ :=
  xy.1 0

@[simp] theorem mem_lpRelaxation_iff (P : OneIntegerVariableMILP m n) (xy : MixedRealPoint 1 n) :
    xy ∈ P.lpRelaxation ↔
      (P.integerMatrix.map (Rat.castHom ℝ)) *ᵥ xy.1 +
          (P.continuousMatrix.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤
        fun i ↦ (P.rhs i : ℝ) :=
  Iff.rfl

@[simp] theorem objectiveValue_def (P : OneIntegerVariableMILP m n) (xy : MixedRealPoint 1 n) :
    P.objectiveValue xy =
      P.integerObjective ⬝ᵥ xy.1 + P.continuousObjective ⬝ᵥ xy.2 :=
  rfl

@[simp] theorem integerValue_mk (x : Fin 1 → ℝ) (y : Fin n → ℝ) :
    integerValue (x, y) = x 0 :=
  rfl

/-- Membership in the MIP feasible set is LP feasibility together with integrality of the unique
distinguished coordinate. -/
theorem mem_mipFeasibleSet_iff (P : OneIntegerVariableMILP m n) (xy : MixedRealPoint 1 n) :
    xy ∈ P.mipFeasibleSet ↔ xy ∈ P.lpRelaxation ∧ ∃ z : ℤ, integerValue xy = (z : ℝ) := by
  constructor
  · intro hxy
    rcases (mem_mixed_integer_points_iff.mp hxy) with ⟨hlp, hint⟩
    rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff] at hint
    rcases hint with ⟨z, hz⟩
    refine ⟨hlp, z 0, ?_⟩
    simpa [integerValue] using congrFun hz 0
  · rintro ⟨hlp, z, hz⟩
    refine (mem_mixed_integer_points_iff).2 ⟨hlp, ?_⟩
    rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff]
    refine ⟨fun _ ↦ z, ?_⟩
    funext j
    fin_cases j
    simpa [integerValue] using hz

/-- The LP relaxation of `P` restricted to the branch-and-bound node `N`. -/
def NodeLpFeasible (P : OneIntegerVariableMILP m n)
    (N : SingleIntegerBranchNode) (xy : MixedRealPoint 1 n) : Prop :=
  xy ∈ P.lpRelaxation ∧ N.Allows (integerValue xy)

/-- `xy` is an optimal solution of the node LP relaxation for the minimization problem `P`. -/
def IsNodeLpOptimalSolution (P : OneIntegerVariableMILP m n)
    (N : SingleIntegerBranchNode) (xy : MixedRealPoint 1 n) : Prop :=
  P.NodeLpFeasible N xy ∧
    ∀ xy', P.NodeLpFeasible N xy' → P.objectiveValue xy ≤ P.objectiveValue xy'

/-- The LP relaxation of `P` has a unique optimal solution at the root node. -/
def RootHasUniqueLpOptimalSolution (P : OneIntegerVariableMILP m n) : Prop :=
  ∃! xy : MixedRealPoint 1 n, P.IsNodeLpOptimalSolution SingleIntegerBranchNode.root xy

/-- The node `N` is fathomed by LP-relaxation lower bounds when an incumbent mixed-integer
solution has objective value no greater than the optimal value of the node LP relaxation. -/
def FathomedByLpLowerBound (P : OneIntegerVariableMILP m n) (N : SingleIntegerBranchNode) : Prop :=
  ∃ incumbent xy,
    incumbent ∈ P.mipFeasibleSet ∧
      P.IsNodeLpOptimalSolution N xy ∧
      P.objectiveValue incumbent ≤ P.objectiveValue xy

/-- An incumbent mixed-integer feasible point whose value is no greater than the optimal node LP
value certifies fathoming by LP-relaxation lower bounds. -/
theorem fathomedByLpLowerBound_of_le
    (P : OneIntegerVariableMILP m n)
    (N : SingleIntegerBranchNode)
    {incumbent xy : MixedRealPoint 1 n}
    (hincumbent : incumbent ∈ P.mipFeasibleSet)
    (hopt : P.IsNodeLpOptimalSolution N xy)
    (hle : P.objectiveValue incumbent ≤ P.objectiveValue xy) :
    P.FathomedByLpLowerBound N :=
  ⟨incumbent, xy, hincumbent, hopt, hle⟩

end OneIntegerVariableMILP

/-- A finite binary enumeration tree whose nodes are labeled by branch-and-bound subproblems. -/
inductive EnumerationTree (α : Type u) where
  /-- A fathomed subproblem. -/
  | leaf : α → EnumerationTree α
  /-- A branched subproblem with left and right child subtrees. -/
  | branch : α → EnumerationTree α → EnumerationTree α → EnumerationTree α

namespace EnumerationTree

variable {α : Type u}

/-- The label at the root of the enumeration tree. -/
def rootLabel : EnumerationTree α → α
  | leaf a => a
  | branch a _ _ => a

/-- The number of nodes in the enumeration tree. -/
def size : EnumerationTree α → ℕ
  | leaf _ => 1
  | branch _ left right => left.size + right.size + 1

@[simp] theorem rootLabel_leaf (a : α) : rootLabel (.leaf a : EnumerationTree α) = a :=
  rfl

@[simp] theorem rootLabel_branch (a : α) (left right : EnumerationTree α) :
    rootLabel (.branch a left right) = a :=
  rfl

@[simp] theorem size_leaf (a : α) : size (.leaf a : EnumerationTree α) = 1 :=
  rfl

@[simp] theorem size_branch (a : α) (left right : EnumerationTree α) :
    size (.branch a left right) = left.size + right.size + 1 :=
  rfl

end EnumerationTree

/-- `IsVariableBranchingWithLpLowerBoundsTree P T` means that `T` is an enumeration tree produced
by branch-and-bound on a mixed integer linear program with one integer variable, where every
branched node uses variable branching on the unique integer coordinate at a fractional optimal LP
solution and every leaf is fathomed by infeasibility, by an integral optimal LP solution, or by
comparing the node LP lower bound with an incumbent mixed-integer feasible solution. -/
inductive IsVariableBranchingWithLpLowerBoundsTree
    {m n : ℕ} (P : OneIntegerVariableMILP m n) :
    EnumerationTree SingleIntegerBranchNode → Prop
  /-- An infeasible LP relaxation gives a leaf. -/
  | leaf_infeasible {N : SingleIntegerBranchNode}
      (hinfeasible : ∀ xy, ¬ P.NodeLpFeasible N xy) :
      IsVariableBranchingWithLpLowerBoundsTree P (.leaf N)
  /-- An integral optimal LP solution gives a leaf. -/
  | leaf_integral {N : SingleIntegerBranchNode} {xy : MixedRealPoint 1 n}
      (hopt : P.IsNodeLpOptimalSolution N xy)
      (hintegral : Int.fract (OneIntegerVariableMILP.integerValue xy) = 0) :
      IsVariableBranchingWithLpLowerBoundsTree P (.leaf N)
  /-- An incumbent mixed-integer feasible value no greater than the node LP optimum also gives a
  leaf. -/
  | leaf_bounded {N : SingleIntegerBranchNode}
      (hbounded : P.FathomedByLpLowerBound N) :
      IsVariableBranchingWithLpLowerBoundsTree P (.leaf N)
  /-- A fractional optimal LP solution is branched by the standard left/right variable split. -/
  | branch {N : SingleIntegerBranchNode}
      {left right : EnumerationTree SingleIntegerBranchNode} {xy : MixedRealPoint 1 n}
      (hopt : P.IsNodeLpOptimalSolution N xy)
      (hfractional : Int.fract (OneIntegerVariableMILP.integerValue xy) ≠ 0)
      (hleft_root :
        left.rootLabel = N.leftChild (OneIntegerVariableMILP.integerValue xy))
      (hright_root :
        right.rootLabel = N.rightChild (OneIntegerVariableMILP.integerValue xy))
      (hleft :
        IsVariableBranchingWithLpLowerBoundsTree P left)
      (hright :
        IsVariableBranchingWithLpLowerBoundsTree P right) :
      IsVariableBranchingWithLpLowerBoundsTree P (.branch N left right)

namespace OneIntegerVariableMILP

/-- Helper for Exercise 9.13: the root LP relaxation is convex because each row inequality is
preserved under convex combinations. -/
lemma lpRelaxation_convex (P : OneIntegerVariableMILP m n) :
    Convex ℝ P.lpRelaxation := by
  intro x hx y hy a s ha hs has
  rw [P.mem_lpRelaxation_iff] at hx hy ⊢
  intro i
  -- Combine the two row inequalities with the same convex weights.
  have hax :
      a *
          (((P.integerMatrix.map (Rat.castHom ℝ)) *ᵥ x.1 +
              (P.continuousMatrix.map (Rat.castHom ℝ)) *ᵥ x.2) i) ≤
        a * (P.rhs i : ℝ) :=
    mul_le_mul_of_nonneg_left (hx i) ha
  have hsy :
      s *
          (((P.integerMatrix.map (Rat.castHom ℝ)) *ᵥ y.1 +
              (P.continuousMatrix.map (Rat.castHom ℝ)) *ᵥ y.2) i) ≤
        s * (P.rhs i : ℝ) :=
    mul_le_mul_of_nonneg_left (hy i) hs
  have hsum := add_le_add hax hsy
  calc
    (((P.integerMatrix.map (Rat.castHom ℝ)) *ᵥ (a • x.1 + s • y.1) +
          (P.continuousMatrix.map (Rat.castHom ℝ)) *ᵥ (a • x.2 + s • y.2)) i)
        = a *
              (((P.integerMatrix.map (Rat.castHom ℝ)) *ᵥ x.1 +
                  (P.continuousMatrix.map (Rat.castHom ℝ)) *ᵥ x.2) i) +
            s *
              (((P.integerMatrix.map (Rat.castHom ℝ)) *ᵥ y.1 +
                  (P.continuousMatrix.map (Rat.castHom ℝ)) *ᵥ y.2) i) := by
            simp [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              left_distrib, right_distrib, mul_add, add_mul, mul_assoc, add_assoc,
              add_left_comm, add_comm]
    _ ≤ a * (P.rhs i : ℝ) + s * (P.rhs i : ℝ) := hsum
    _ = (P.rhs i : ℝ) := by
      calc
        a * (P.rhs i : ℝ) + s * (P.rhs i : ℝ) = (a + s) * (P.rhs i : ℝ) := by ring
        _ = (P.rhs i : ℝ) := by rw [has, one_mul]

/-- Helper for Exercise 9.13: the linear objective is affine along convex combinations. -/
lemma objectiveValue_convexCombination
    (P : OneIntegerVariableMILP m n)
    (x y : MixedRealPoint 1 n)
    (t : ℝ) :
    P.objectiveValue ((1 - t) • x + t • y) =
      (1 - t) * P.objectiveValue x + t * P.objectiveValue y := by
  -- Expand the objective on each block and collect the weighted terms.
  simp [OneIntegerVariableMILP.objectiveValue_def, dotProduct_add, dotProduct_smul, smul_eq_mul,
    left_distrib, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 9.13: the unique root LP optimum has strictly smaller objective value than
every distinct root-feasible point. -/
lemma rootOptimalObjective_lt_of_ne
    (P : OneIntegerVariableMILP m n)
    {xRoot y : MixedRealPoint 1 n}
    (hxRoot : P.IsNodeLpOptimalSolution SingleIntegerBranchNode.root xRoot)
    (huniq : ∀ y', P.IsNodeLpOptimalSolution SingleIntegerBranchNode.root y' → y' = xRoot)
    (hy : P.NodeLpFeasible SingleIntegerBranchNode.root y)
    (hne : y ≠ xRoot) :
    P.objectiveValue xRoot < P.objectiveValue y := by
  have hroot_le : P.objectiveValue xRoot ≤ P.objectiveValue y := hxRoot.2 y hy
  by_contra hnotlt
  have hy_le : P.objectiveValue y ≤ P.objectiveValue xRoot := le_of_not_gt hnotlt
  have hEq : P.objectiveValue y = P.objectiveValue xRoot := le_antisymm hy_le hroot_le
  -- Equality of objective values upgrades `y` to another root optimum, contradicting uniqueness.
  have hy_opt : P.IsNodeLpOptimalSolution SingleIntegerBranchNode.root y := by
    refine ⟨hy, ?_⟩
    intro y' hy'
    calc
      P.objectiveValue y = P.objectiveValue xRoot := hEq
      _ ≤ P.objectiveValue y' := hxRoot.2 y' hy'
  exact hne (huniq y hy_opt)

/-- Helper for Exercise 9.13: every optimal solution of the left child already lies on the new
boundary `z = ⌊P.integerValue xRoot⌋`. -/
lemma integerValue_eq_floor_of_leftChildOptimal
    (P : OneIntegerVariableMILP m n)
    {xRoot y : MixedRealPoint 1 n}
    (hxRoot : P.IsNodeLpOptimalSolution SingleIntegerBranchNode.root xRoot)
    (huniq : ∀ y', P.IsNodeLpOptimalSolution SingleIntegerBranchNode.root y' → y' = xRoot)
    (hfractional : Int.fract (OneIntegerVariableMILP.integerValue xRoot) ≠ 0)
    (hy :
      P.IsNodeLpOptimalSolution
        (SingleIntegerBranchNode.root.leftChild (OneIntegerVariableMILP.integerValue xRoot)) y) :
    OneIntegerVariableMILP.integerValue y =
      Int.floor (OneIntegerVariableMILP.integerValue xRoot) := by
  have hy_lp : y ∈ P.lpRelaxation := hy.1.1
  have hy_bound :
      OneIntegerVariableMILP.integerValue y ≤
        Int.floor (OneIntegerVariableMILP.integerValue xRoot) := by
    exact (SingleIntegerBranchNode.allows_leftChild_iff _ _ _).1 hy.1.2 |>.2
  have hfloor_lt_root :
      (Int.floor (OneIntegerVariableMILP.integerValue xRoot) : ℝ) <
        OneIntegerVariableMILP.integerValue xRoot := by
    exact Int.floor_lt_self_iff.2 (Int.fract_ne_zero_iff.1 hfractional)
  have hy_root : P.NodeLpFeasible SingleIntegerBranchNode.root y := ⟨hy_lp, by simp⟩
  have hy_ne_root : y ≠ xRoot := by
    intro hEq
    subst hEq
    linarith
  by_cases hboundary :
      OneIntegerVariableMILP.integerValue y =
        Int.floor (OneIntegerVariableMILP.integerValue xRoot)
  · exact hboundary
  · have hy_lt :
        OneIntegerVariableMILP.integerValue y <
          Int.floor (OneIntegerVariableMILP.integerValue xRoot) :=
      lt_of_le_of_ne hy_bound hboundary
    let t : ℝ :=
      (OneIntegerVariableMILP.integerValue xRoot -
          Int.floor (OneIntegerVariableMILP.integerValue xRoot)) /
        (OneIntegerVariableMILP.integerValue xRoot -
          OneIntegerVariableMILP.integerValue y)
    let u : MixedRealPoint 1 n := (1 - t) • xRoot + t • y
    have hden_pos :
        0 <
          OneIntegerVariableMILP.integerValue xRoot -
            OneIntegerVariableMILP.integerValue y := by
      linarith
    have hnum_pos :
        0 <
          OneIntegerVariableMILP.integerValue xRoot -
            Int.floor (OneIntegerVariableMILP.integerValue xRoot) := by
      linarith
    have ht_pos : 0 < t := by
      exact div_pos hnum_pos hden_pos
    have ht_lt_one : t < 1 := by
      have hnum_lt_den :
          OneIntegerVariableMILP.integerValue xRoot -
              Int.floor (OneIntegerVariableMILP.integerValue xRoot) <
            OneIntegerVariableMILP.integerValue xRoot -
              OneIntegerVariableMILP.integerValue y := by
        linarith
      dsimp [t]
      exact (div_lt_one hden_pos).2 hnum_lt_den
    have h_one_sub_nonneg : 0 ≤ 1 - t := by
      linarith
    have hu_lp : u ∈ P.lpRelaxation := by
      -- The interpolated point stays in the root LP relaxation by convexity.
      exact P.lpRelaxation_convex hxRoot.1.1 hy_lp h_one_sub_nonneg ht_pos.le (by ring)
    have hden_ne :
        OneIntegerVariableMILP.integerValue xRoot -
            OneIntegerVariableMILP.integerValue y ≠ 0 := by
      linarith
    have hu_scalar :
        (1 - t) * OneIntegerVariableMILP.integerValue xRoot +
            t * OneIntegerVariableMILP.integerValue y =
          Int.floor (OneIntegerVariableMILP.integerValue xRoot) := by
      dsimp [t]
      field_simp [hden_ne]
      rw [Int.fract]
      ring_nf
    have hu_boundary :
        OneIntegerVariableMILP.integerValue u =
          Int.floor (OneIntegerVariableMILP.integerValue xRoot) := by
      -- The interpolation parameter was chosen so the distinguished coordinate lands on the floor.
      calc
        OneIntegerVariableMILP.integerValue u =
            (1 - t) * OneIntegerVariableMILP.integerValue xRoot +
              t * OneIntegerVariableMILP.integerValue y := by
                simp [u, OneIntegerVariableMILP.integerValue, Pi.add_apply, Pi.smul_apply,
                  smul_eq_mul]
        _ = Int.floor (OneIntegerVariableMILP.integerValue xRoot) := hu_scalar
    have hu_child :
        P.NodeLpFeasible
          (SingleIntegerBranchNode.root.leftChild (OneIntegerVariableMILP.integerValue xRoot)) u := by
      refine ⟨hu_lp, ?_⟩
      rw [SingleIntegerBranchNode.allows_leftChild_iff]
      constructor
      · simp
      · simpa [hu_boundary]
    have hroot_obj_lt :
        P.objectiveValue xRoot < P.objectiveValue y :=
      P.rootOptimalObjective_lt_of_ne hxRoot huniq hy_root hy_ne_root
    have hu_obj_lt : P.objectiveValue u < P.objectiveValue y := by
      have h_one_sub_pos : 0 < 1 - t := by
        linarith
      have hx_scaled :
          (1 - t) * P.objectiveValue xRoot < (1 - t) * P.objectiveValue y :=
        mul_lt_mul_of_pos_left hroot_obj_lt h_one_sub_pos
      calc
        P.objectiveValue u =
            (1 - t) * P.objectiveValue xRoot + t * P.objectiveValue y := by
              rw [P.objectiveValue_convexCombination]
        _ < (1 - t) * P.objectiveValue y + t * P.objectiveValue y := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_lt_add_right hx_scaled (t * P.objectiveValue y)
        _ = P.objectiveValue y := by ring
    have hy_u : P.objectiveValue y ≤ P.objectiveValue u := hy.2 u hu_child
    linarith

/-- Helper for Exercise 9.13: every optimal solution of the right child already lies on the new
boundary `z = ⌈P.integerValue xRoot⌉`. -/
lemma integerValue_eq_ceil_of_rightChildOptimal
    (P : OneIntegerVariableMILP m n)
    {xRoot y : MixedRealPoint 1 n}
    (hxRoot : P.IsNodeLpOptimalSolution SingleIntegerBranchNode.root xRoot)
    (huniq : ∀ y', P.IsNodeLpOptimalSolution SingleIntegerBranchNode.root y' → y' = xRoot)
    (hfractional : Int.fract (OneIntegerVariableMILP.integerValue xRoot) ≠ 0)
    (hy :
      P.IsNodeLpOptimalSolution
        (SingleIntegerBranchNode.root.rightChild (OneIntegerVariableMILP.integerValue xRoot)) y) :
    OneIntegerVariableMILP.integerValue y =
      Int.ceil (OneIntegerVariableMILP.integerValue xRoot) := by
  have hy_lp : y ∈ P.lpRelaxation := hy.1.1
  have hy_bound :
      (Int.ceil (OneIntegerVariableMILP.integerValue xRoot) : ℝ) ≤
        OneIntegerVariableMILP.integerValue y := by
    exact (SingleIntegerBranchNode.allows_rightChild_iff _ _ _).1 hy.1.2 |>.2
  have hroot_not_int : OneIntegerVariableMILP.integerValue xRoot ∉ Set.range Int.cast :=
    Int.fract_ne_zero_iff.1 hfractional
  have hceil_eq_int :
      Int.ceil (OneIntegerVariableMILP.integerValue xRoot) =
        Int.floor (OneIntegerVariableMILP.integerValue xRoot) + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem _).2 hroot_not_int
  have hroot_lt_ceil :
      OneIntegerVariableMILP.integerValue xRoot <
        Int.ceil (OneIntegerVariableMILP.integerValue xRoot) := by
    simpa [hceil_eq_int] using Int.lt_floor_add_one (OneIntegerVariableMILP.integerValue xRoot)
  have hy_root : P.NodeLpFeasible SingleIntegerBranchNode.root y := ⟨hy_lp, by simp⟩
  have hy_ne_root : y ≠ xRoot := by
    intro hEq
    subst hEq
    linarith
  by_cases hboundary :
      OneIntegerVariableMILP.integerValue y =
        Int.ceil (OneIntegerVariableMILP.integerValue xRoot)
  · exact hboundary
  · have hy_gt :
        (Int.ceil (OneIntegerVariableMILP.integerValue xRoot) : ℝ) <
          OneIntegerVariableMILP.integerValue y :=
      lt_of_le_of_ne hy_bound (by simpa [eq_comm] using hboundary)
    let t : ℝ :=
      (Int.ceil (OneIntegerVariableMILP.integerValue xRoot) -
          OneIntegerVariableMILP.integerValue xRoot) /
        (OneIntegerVariableMILP.integerValue y -
          OneIntegerVariableMILP.integerValue xRoot)
    let u : MixedRealPoint 1 n := (1 - t) • xRoot + t • y
    have hden_pos :
        0 <
          OneIntegerVariableMILP.integerValue y -
            OneIntegerVariableMILP.integerValue xRoot := by
      linarith
    have hnum_pos :
        0 <
          Int.ceil (OneIntegerVariableMILP.integerValue xRoot) -
            OneIntegerVariableMILP.integerValue xRoot := by
      linarith
    have ht_pos : 0 < t := by
      exact div_pos hnum_pos hden_pos
    have ht_lt_one : t < 1 := by
      have hnum_lt_den :
          Int.ceil (OneIntegerVariableMILP.integerValue xRoot) -
              OneIntegerVariableMILP.integerValue xRoot <
            OneIntegerVariableMILP.integerValue y -
              OneIntegerVariableMILP.integerValue xRoot := by
        linarith
      dsimp [t]
      exact (div_lt_one hden_pos).2 hnum_lt_den
    have h_one_sub_nonneg : 0 ≤ 1 - t := by
      linarith
    have hu_lp : u ∈ P.lpRelaxation := by
      -- The same convexity argument keeps the interpolation inside the root relaxation.
      exact P.lpRelaxation_convex hxRoot.1.1 hy_lp h_one_sub_nonneg ht_pos.le (by ring)
    have hden_ne :
        OneIntegerVariableMILP.integerValue y -
            OneIntegerVariableMILP.integerValue xRoot ≠ 0 := by
      linarith
    have hu_scalar :
        (1 - t) * OneIntegerVariableMILP.integerValue xRoot +
            t * OneIntegerVariableMILP.integerValue y =
          Int.ceil (OneIntegerVariableMILP.integerValue xRoot) := by
      have hceil_eq_real :
          ((Int.ceil (OneIntegerVariableMILP.integerValue xRoot) : ℤ) : ℝ) =
            Int.floor (OneIntegerVariableMILP.integerValue xRoot) + 1 := by
        exact_mod_cast hceil_eq_int
      dsimp [t]
      field_simp [hden_ne]
      rw [hceil_eq_real]
      simp [Int.fract]
      ring_nf
    have hu_boundary :
        OneIntegerVariableMILP.integerValue u =
          Int.ceil (OneIntegerVariableMILP.integerValue xRoot) := by
      -- The chosen interpolation parameter now lands on the ceiling boundary.
      calc
        OneIntegerVariableMILP.integerValue u =
            (1 - t) * OneIntegerVariableMILP.integerValue xRoot +
              t * OneIntegerVariableMILP.integerValue y := by
                simp [u, OneIntegerVariableMILP.integerValue, Pi.add_apply, Pi.smul_apply,
                  smul_eq_mul]
        _ = Int.ceil (OneIntegerVariableMILP.integerValue xRoot) := hu_scalar
    have hu_child :
        P.NodeLpFeasible
          (SingleIntegerBranchNode.root.rightChild (OneIntegerVariableMILP.integerValue xRoot)) u := by
      refine ⟨hu_lp, ?_⟩
      rw [SingleIntegerBranchNode.allows_rightChild_iff]
      constructor
      · simp
      · simpa [hu_boundary]
    have hroot_obj_lt :
        P.objectiveValue xRoot < P.objectiveValue y :=
      P.rootOptimalObjective_lt_of_ne hxRoot huniq hy_root hy_ne_root
    have hu_obj_lt : P.objectiveValue u < P.objectiveValue y := by
      have h_one_sub_pos : 0 < 1 - t := by
        linarith
      have hx_scaled :
          (1 - t) * P.objectiveValue xRoot < (1 - t) * P.objectiveValue y :=
        mul_lt_mul_of_pos_left hroot_obj_lt h_one_sub_pos
      calc
        P.objectiveValue u =
            (1 - t) * P.objectiveValue xRoot + t * P.objectiveValue y := by
              rw [P.objectiveValue_convexCombination]
        _ < (1 - t) * P.objectiveValue y + t * P.objectiveValue y := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_lt_add_right hx_scaled (t * P.objectiveValue y)
        _ = P.objectiveValue y := by ring
    have hy_u : P.objectiveValue y ≤ P.objectiveValue u := hy.2 u hu_child
    linarith

end OneIntegerVariableMILP

/-- Exercise 9.13. For a mixed integer linear program with one integer variable, if the root LP
relaxation has a unique optimal solution, then every branch-and-bound enumeration tree produced by
variable branching and LP-relaxation lower bounds has at most three nodes. -/
theorem exercise_9_13_enumeration_tree_size_le_three
    {m n : ℕ}
    (P : OneIntegerVariableMILP m n)
    (T : EnumerationTree SingleIntegerBranchNode)
    (hroot : P.RootHasUniqueLpOptimalSolution)
    (htree : IsVariableBranchingWithLpLowerBoundsTree P T)
    (hroot_label : T.rootLabel = SingleIntegerBranchNode.root) :
    T.size ≤ 3 := by
  obtain ⟨xRoot, hxRoot, huniq⟩ := hroot
  cases htree with
  | leaf_infeasible hinfeasible =>
      simp
  | leaf_integral hopt hintegral =>
      simp
  | leaf_bounded hbounded =>
      simp
  | @branch N left right xy hopt hfractional hleft_root hright_root hleft hright =>
      have hnode : N = SingleIntegerBranchNode.root := by
        simpa using hroot_label
      subst hnode
      -- Uniqueness identifies the branch witness with the unique root LP optimum.
      have hxy : xy = xRoot := huniq xy hopt
      subst xy
      have hleft_size : left.size = 1 := by
        cases hleft with
        | leaf_infeasible hinfeasible =>
            simp
        | leaf_integral hoptLeft hintegral =>
            simp
        | leaf_bounded hbounded =>
            simp
        | @branch Nleft leftleft leftright xyLeft hoptLeft hfractionalLeft
            hleftleft_root hleftright_root hleftleft hleftright =>
            have hleft_node :
                Nleft = SingleIntegerBranchNode.root.leftChild
                  (OneIntegerVariableMILP.integerValue xRoot) := by
              simpa using hleft_root
            subst hleft_node
            -- Route correction: a second left branch would force the child optimum onto the
            -- integer boundary, contradicting the child's fractional branching witness.
            have hboundary :=
              P.integerValue_eq_floor_of_leftChildOptimal hxRoot huniq hfractional hoptLeft
            have hfrac_zero :
                Int.fract (OneIntegerVariableMILP.integerValue xyLeft) = 0 := by
              simpa [hboundary]
            exact False.elim (hfractionalLeft hfrac_zero)
      have hright_size : right.size = 1 := by
        cases hright with
        | leaf_infeasible hinfeasible =>
            simp
        | leaf_integral hoptRight hintegral =>
            simp
        | leaf_bounded hbounded =>
            simp
        | @branch Nright rightleft rightright xyRight hoptRight hfractionalRight
            hrightleft_root hrightright_root hrightleft hrightright =>
            have hright_node :
                Nright = SingleIntegerBranchNode.root.rightChild
                  (OneIntegerVariableMILP.integerValue xRoot) := by
              simpa using hright_root
            subst hright_node
            -- The same boundary argument rules out branching on the right child as well.
            have hboundary :=
              P.integerValue_eq_ceil_of_rightChildOptimal hxRoot huniq hfractional hoptRight
            have hfrac_zero :
                Int.fract (OneIntegerVariableMILP.integerValue xyRight) = 0 := by
              simpa [hboundary]
            exact False.elim (hfractionalRight hfrac_zero)
      -- Once both children are leaves, the whole enumeration tree has exactly three nodes.
      simp [EnumerationTree.size_branch, hleft_size, hright_size]

end Exercise913
