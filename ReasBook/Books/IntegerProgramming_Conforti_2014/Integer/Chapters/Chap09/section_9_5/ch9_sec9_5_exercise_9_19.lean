import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Order.Minimal
import Mathlib.Tactic

open SimpleGraph
open scoped BigOperators
open scoped Matrix

-- Domain-style sampling for this exercise:
-- * primary domain: clique inequalities in conflict graphs of binary `0,1` programs
-- * sampled owner abstractions:
--   - `SimpleGraph.fromRel` / `SimpleGraph.fromRel_adj` for a source-facing conflict relation
--   - `SimpleGraph.fromEdgeSet` / `SimpleGraph.fromEdgeSet_adj` for a finite explicit edge list
--   - `SimpleGraph.IsClique` together with `Maximal G.IsClique` for clique statements
-- * primitive data: binary literals, their evaluation, the conflict relation, and the explicit
--   thirteen-edge family of Exercise 9.19 (3)
-- * derived API: the source-facing conflict graph and the explicit four-variable graph, each
--   built from the canonical `SimpleGraph` owners

universe u

section Exercise919

variable {B : Type u}

/-- A binary literal is either a binary variable `x_j` or its complement `1 - x_j`. -/
inductive BinaryLiteral (B : Type u)
  | var : B → BinaryLiteral B
  | neg : B → BinaryLiteral B
deriving DecidableEq

/-- Helper for Exercise 9.19: binary literals over a finite index set form a finite type. -/
private instance [Fintype B] : Fintype (BinaryLiteral B) :=
  Fintype.ofEquiv (B ⊕ B)
    { toFun := fun s =>
        match s with
        | Sum.inl j => BinaryLiteral.var j
        | Sum.inr j => BinaryLiteral.neg j
      invFun := fun l =>
        match l with
        | BinaryLiteral.var j => Sum.inl j
        | BinaryLiteral.neg j => Sum.inr j
      left_inv := by
        intro l
        cases l <;> rfl
      right_inv := by
        intro s
        cases s <;> rfl }

/-- The value of a binary literal at a real vector `x`. Positive literals evaluate to `x_j`,
while complemented literals evaluate to `1 - x_j`. -/
def binary_literal_value (x : B → ℝ) : BinaryLiteral B → ℝ
  | .var j => x j
  | .neg j => 1 - x j

@[simp] theorem binary_literal_value_var (x : B → ℝ) (j : B) :
    binary_literal_value x (.var j) = x j :=
  rfl

@[simp] theorem binary_literal_value_neg (x : B → ℝ) (j : B) :
    binary_literal_value x (.neg j) = 1 - x j :=
  rfl

/-- A binary literal is active at `x` when its value is `1`. -/
def binary_literal_is_one (x : B → ℝ) (l : BinaryLiteral B) : Prop :=
  binary_literal_value x l = 1

/-- The left-hand side of the clique inequality attached to a finite literal family. -/
def clique_inequality_lhs (C : Finset (BinaryLiteral B)) (x : B → ℝ) : ℝ :=
  Finset.sum C fun l ↦
    match l with
    | .var j => x j
    | .neg j => -x j

/-- The right-hand side of the clique inequality attached to a finite literal family. -/
def clique_inequality_rhs (C : Finset (BinaryLiteral B)) : ℝ :=
  1 - Finset.sum C (fun l ↦
    match l with
    | .var _ => (0 : ℝ)
    | .neg _ => 1)

/-- Two literals conflict when they are distinct and cannot both take the value `1` on any
feasible point. -/
def literal_conflict (feasible : Set (B → ℝ)) (u v : BinaryLiteral B) : Prop :=
  u ≠ v ∧ ∀ ⦃x : B → ℝ⦄, x ∈ feasible → ¬ (binary_literal_is_one x u ∧ binary_literal_is_one x v)

/-- The conflict relation on literals is symmetric. -/
theorem literal_conflict_symmetric (feasible : Set (B → ℝ)) :
    Symmetric (literal_conflict feasible) := by
  intro u v huv
  rcases huv with ⟨huv_ne, huv_conflict⟩
  -- Swap the active-literal witness to transfer infeasibility to the reversed pair.
  refine ⟨by simpa [ne_eq, eq_comm] using huv_ne, ?_⟩
  intro x hx hactive
  exact huv_conflict hx ⟨hactive.2, hactive.1⟩

/-- The conflict graph of a mixed `0,1` problem on the binary index set `B`. -/
def conflictGraph (feasible : Set (B → ℝ)) : SimpleGraph (BinaryLiteral B) :=
  SimpleGraph.fromRel (literal_conflict feasible)

/-- In the conflict graph, adjacency is exactly literal conflict. -/
@[simp] theorem conflictGraph_adj_iff
    (feasible : Set (B → ℝ)) (u v : BinaryLiteral B) :
    (conflictGraph feasible).Adj u v ↔ literal_conflict feasible u v := by
  constructor
  · intro huv
    rcases (SimpleGraph.fromRel_adj (literal_conflict feasible) u v).1 huv with
      ⟨_, hconflict | hconflict⟩
    · exact hconflict
    · exact literal_conflict_symmetric feasible hconflict
  · intro huv
    exact (SimpleGraph.fromRel_adj (literal_conflict feasible) u v).2 ⟨huv.1, Or.inl huv⟩

/-- Helper for Exercise 9.19: every literal on a feasible binary point evaluates to `0` or `1`. -/
private lemma binaryLiteralValue_eq_zero_or_one_of_feasible
    (feasible : Set (B → ℝ))
    (h_binary : ∀ ⦃x : B → ℝ⦄, x ∈ feasible → is_zero_one_family x)
    {x : B → ℝ} (hx : x ∈ feasible) (l : BinaryLiteral B) :
    binary_literal_value x l = 0 ∨ binary_literal_value x l = 1 := by
  cases l with
  | var j =>
      simpa [binary_literal_value] using is_zero_one_family.apply (h_binary hx) j
  | neg j =>
      rcases is_zero_one_family.apply (h_binary hx) j with hj | hj
      · right
        simp [binary_literal_value, hj]
      · left
        simp [binary_literal_value, hj]

/-- Helper for Exercise 9.19: adding back the complemented-literal count turns the clique
left-hand side into the sum of literal values. -/
private lemma cliqueInequalityLhs_add_negCount_eq_sum_binaryLiteralValue
    (C : Finset (BinaryLiteral B)) (x : B → ℝ) :
    clique_inequality_lhs C x +
        Finset.sum C (fun l ↦ match l with | .var _ => (0 : ℝ) | .neg _ => 1) =
      Finset.sum C (binary_literal_value x) := by
  -- Merge the two sums so each literal can be normalized separately.
  rw [clique_inequality_lhs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro l hl
  cases l with
  | var j =>
      simp [binary_literal_value]
  | neg j =>
      simp [binary_literal_value, sub_eq_add_neg, add_comm]

/-- Helper for Exercise 9.19: on a feasible binary point, summing literal values counts the
active literals in the finite family `C`. -/
private lemma sum_binaryLiteralValue_eq_card_filter_isOne
    (feasible : Set (B → ℝ))
    (h_binary : ∀ ⦃x : B → ℝ⦄, x ∈ feasible → is_zero_one_family x)
    (C : Finset (BinaryLiteral B)) (x : B → ℝ)
    [DecidablePred (binary_literal_is_one x)] (hx : x ∈ feasible) :
    Finset.sum C (binary_literal_value x) =
      ((C.filter fun l ↦ binary_literal_is_one x l).card : ℝ) := by
  classical
  induction C using Finset.induction_on with
  | empty =>
      simp
  | @insert l C hl ih =>
      -- Each new literal contributes either `0` or `1`, matching whether it survives the filter.
      rcases binaryLiteralValue_eq_zero_or_one_of_feasible feasible h_binary hx l with hzero | hone
      · have hnot : ¬ binary_literal_is_one x l := by
          simp [binary_literal_is_one, hzero]
        simp [Finset.filter_insert, hl, ih, hnot, hzero]
      · have hone' : binary_literal_is_one x l := by
          simp [binary_literal_is_one, hone]
        calc
          Finset.sum (insert l C) (binary_literal_value x)
              = binary_literal_value x l + Finset.sum C (binary_literal_value x) := by
                  simp [hl]
          _ = 1 + Finset.sum C (binary_literal_value x) := by rw [hone]
          _ = 1 + ((C.filter fun l ↦ binary_literal_is_one x l).card : ℝ) := by rw [ih]
          _ = ((insert l C).filter fun l ↦ binary_literal_is_one x l).card := by
                rw [Finset.filter_insert, if_pos hone', Finset.card_insert_of_notMem]
                · rw [Nat.cast_add, Nat.cast_one]
                  linarith
                · simp [hl]

/-- Helper for Exercise 9.19: a clique cannot contain two literals that are simultaneously active
at the same feasible point. -/
private lemma activeLiteralFilter_card_le_one_of_clique
    (feasible : Set (B → ℝ))
    {C : Finset (BinaryLiteral B)}
    (hC : (conflictGraph feasible).IsClique C)
    (x : B → ℝ) [DecidablePred (binary_literal_is_one x)] (hx : x ∈ feasible) :
    (C.filter fun l ↦ binary_literal_is_one x l).card ≤ 1 := by
  classical
  refine Finset.card_le_one_iff.2 ?_
  intro a b ha hb
  by_contra hab
  have haC : a ∈ C := (Finset.mem_filter.mp ha).1
  have hbC : b ∈ C := (Finset.mem_filter.mp hb).1
  have ha1 : binary_literal_is_one x a := (Finset.mem_filter.mp ha).2
  have hb1 : binary_literal_is_one x b := (Finset.mem_filter.mp hb).2
  -- Two active members of the clique would violate the conflict relation on feasible points.
  have hab_conflict : literal_conflict feasible a b := by
    exact (conflictGraph_adj_iff feasible a b).1 (hC haC hbC hab)
  exact hab_conflict.2 hx ⟨ha1, hb1⟩

/-- For Exercise 9.19, part (1) shows that any clique `C` of the conflict graph on the literals
`x_j` and `1 - x_j` yields the displayed
clique inequality is valid for every feasible binary point. -/
theorem exercise_9_19_clique_inequality_valid
    (feasible : Set (B → ℝ))
    (h_binary : ∀ ⦃x : B → ℝ⦄, x ∈ feasible → is_zero_one_family x)
    {C : Finset (BinaryLiteral B)}
    (hC : (conflictGraph feasible).IsClique C)
    (x : B → ℝ) (hx : x ∈ feasible) :
    clique_inequality_lhs C x ≤ clique_inequality_rhs C := by
  classical
  -- Rewrite the displayed inequality as a bound on the number of active literals in the clique.
  have hsum_le :
      clique_inequality_lhs C x +
          Finset.sum C (fun l ↦ match l with | .var _ => (0 : ℝ) | .neg _ => 1) ≤ 1 := by
    rw [cliqueInequalityLhs_add_negCount_eq_sum_binaryLiteralValue,
      sum_binaryLiteralValue_eq_card_filter_isOne feasible h_binary C x hx]
    exact_mod_cast activeLiteralFilter_card_le_one_of_clique feasible hC x hx
  -- Moving the complemented-literal count back to the right yields the clique inequality.
  simpa [clique_inequality_rhs] using (le_sub_iff_add_le).2 hsum_le

/-- For Exercise 9.19, part (2) shows that if a clique contains both `x_k` and `1 - x_k`, then
every other literal in the clique is forced to take the value `0` on every feasible binary
point. -/
theorem exercise_9_19_clique_with_complement_forces_other_literals_zero
    (feasible : Set (B → ℝ))
    (h_binary : ∀ ⦃x : B → ℝ⦄, x ∈ feasible → is_zero_one_family x)
    {C : Finset (BinaryLiteral B)}
    (hC : (conflictGraph feasible).IsClique C)
    {k : B}
    (hk_var : BinaryLiteral.var k ∈ C)
    (hk_neg : BinaryLiteral.neg k ∈ C)
    (l : BinaryLiteral B) (hl : l ∈ C)
    (hl_var : l ≠ BinaryLiteral.var k)
    (hl_neg : l ≠ BinaryLiteral.neg k)
    (x : B → ℝ) (hx : x ∈ feasible) :
    binary_literal_value x l = 0 := by
  -- One of `x_k` or `1 - x_k` is active, and its conflicts rule out `l` being active.
  rcases is_zero_one_family.apply (h_binary hx) k with hk0 | hk1
  · have hnot_active : ¬ binary_literal_is_one x l := by
      intro hl_one
      have hconflict : literal_conflict feasible (BinaryLiteral.neg k) l := by
        exact (conflictGraph_adj_iff feasible (BinaryLiteral.neg k) l).1 <|
          hC hk_neg hl (fun hEq ↦ hl_neg hEq.symm)
      have hk_neg_one : binary_literal_is_one x (BinaryLiteral.neg k) := by
        simp [binary_literal_is_one, binary_literal_value, hk0]
      exact hconflict.2 hx ⟨hk_neg_one, hl_one⟩
    rcases binaryLiteralValue_eq_zero_or_one_of_feasible feasible h_binary hx l with hzero | hone
    · exact hzero
    · exact False.elim <| hnot_active <| by simpa [binary_literal_is_one] using hone
  · have hnot_active : ¬ binary_literal_is_one x l := by
      intro hl_one
      have hconflict : literal_conflict feasible (BinaryLiteral.var k) l := by
        exact (conflictGraph_adj_iff feasible (BinaryLiteral.var k) l).1 <|
          hC hk_var hl (fun hEq ↦ hl_var hEq.symm)
      have hk_var_one : binary_literal_is_one x (BinaryLiteral.var k) := by
        simp [binary_literal_is_one, binary_literal_value, hk1]
      exact hconflict.2 hx ⟨hk_var_one, hl_one⟩
    rcases binaryLiteralValue_eq_zero_or_one_of_feasible feasible h_binary hx l with hzero | hone
    · exact hzero
    · exact False.elim <| hnot_active <| by simpa [binary_literal_is_one] using hone

/-- The feasible `0,1` set of Exercise 9.19 (3), in the coordinate order `(x1, x2, x3, x4)`. -/
def exercise_9_19_feasible_set : Set (Fin 4 → ℝ) :=
  {x : Fin 4 → ℝ |
    4 * x 0 + x 1 - 3 * x 3 ≤ 2 ∧
      3 * x 0 + 2 * x 1 + 5 * x 2 + 3 * x 3 ≤ 7 ∧
        x 1 + x 2 - x 3 ≤ 0 ∧
          is_zero_one_family x}

/-- The thirteen conflict edges listed explicitly in Exercise 9.19 (3). -/
def exercise_9_19_edges : Finset (Sym2 (BinaryLiteral (Fin 4))) :=
  {s(BinaryLiteral.var 0, BinaryLiteral.var 1),
    s(BinaryLiteral.var 0, BinaryLiteral.var 2),
    s(BinaryLiteral.var 0, BinaryLiteral.neg 0),
    s(BinaryLiteral.var 0, BinaryLiteral.neg 3),
    s(BinaryLiteral.var 1, BinaryLiteral.var 2),
    s(BinaryLiteral.var 1, BinaryLiteral.neg 1),
    s(BinaryLiteral.var 1, BinaryLiteral.neg 3),
    s(BinaryLiteral.var 2, BinaryLiteral.var 3),
    s(BinaryLiteral.var 2, BinaryLiteral.neg 0),
    s(BinaryLiteral.var 2, BinaryLiteral.neg 1),
    s(BinaryLiteral.var 2, BinaryLiteral.neg 2),
    s(BinaryLiteral.var 2, BinaryLiteral.neg 3),
    s(BinaryLiteral.var 3, BinaryLiteral.neg 3)}

/-- The graph listed explicitly for the four-variable `0,1` program of Exercise 9.19 (3). -/
def exercise_9_19_graph : SimpleGraph (BinaryLiteral (Fin 4)) :=
  SimpleGraph.fromEdgeSet (exercise_9_19_edges : Set (Sym2 (BinaryLiteral (Fin 4))))

@[simp] theorem exercise_9_19_graph_adj_iff (u v : BinaryLiteral (Fin 4)) :
    exercise_9_19_graph.Adj u v ↔ s(u, v) ∈ exercise_9_19_edges ∧ u ≠ v := by
  simp [exercise_9_19_graph]

/-- Helper for Exercise 9.19: the concrete feasible set consists of exactly four `0/1` points. -/
private lemma memExercise919FeasibleSet_iff (x : Fin 4 → ℝ) :
    x ∈ exercise_9_19_feasible_set ↔
      x = ![0, 0, 0, 0] ∨
        x = ![0, 0, 0, 1] ∨
          x = ![1, 0, 0, 1] ∨
            x = ![0, 1, 0, 1] := by
  constructor
  · intro hx
    rcases hx with ⟨hineq1, hineq2, hineq3, hbin⟩
    have hx2_zero : x 2 = 0 := by
      rcases is_zero_one_family.apply hbin 2 with hx2 | hx2
      · exact hx2
      · rcases is_zero_one_family.apply hbin 0 with hx0 | hx0 <;>
          rcases is_zero_one_family.apply hbin 1 with hx1 | hx1 <;>
          rcases is_zero_one_family.apply hbin 3 with hx3 | hx3 <;> exfalso <;>
          linarith
    rcases is_zero_one_family.apply hbin 1 with hx1 | hx1
    · rcases is_zero_one_family.apply hbin 3 with hx3 | hx3
      · have hx0_zero : x 0 = 0 := by
          rcases is_zero_one_family.apply hbin 0 with hx0 | hx0 <;>
            linarith
        left
        ext i
        fin_cases i <;> simp [hx0_zero, hx1, hx2_zero, hx3]
      · rcases is_zero_one_family.apply hbin 0 with hx0 | hx0
        · right
          left
          ext i
          fin_cases i <;> simp [hx0, hx1, hx2_zero, hx3]
        · right
          right
          left
          ext i
          fin_cases i <;> simp [hx0, hx1, hx2_zero, hx3]
    · have hx3_one : x 3 = 1 := by
        rcases is_zero_one_family.apply hbin 3 with hx3 | hx3 <;>
          linarith
      have hx0_zero : x 0 = 0 := by
        rcases is_zero_one_family.apply hbin 0 with hx0 | hx0 <;>
          linarith
      right
      right
      right
      ext i
      fin_cases i <;> simp [hx0_zero, hx1, hx2_zero, hx3_one]
  · intro hx
    rcases hx with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
      intro i
      fin_cases i <;> simp
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp
        norm_num
      · simp
        norm_num
      · simp
      intro i
      fin_cases i <;> simp
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp
        norm_num
      · simp
        norm_num
      · simp
      intro i
      fin_cases i <;> simp
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp
        norm_num
      · simp
        norm_num
      · simp
      intro i
      fin_cases i <;> simp

/-- Helper for Exercise 9.19: the four feasible points are indexed in the same order as
`memExercise919FeasibleSet_iff`. -/
private def exercise919Point : Fin 4 → Fin 4 → ℝ
  | 0 => ![0, 0, 0, 0]
  | 1 => ![0, 0, 0, 1]
  | 2 => ![1, 0, 0, 1]
  | _ => ![0, 1, 0, 1]

/-- Helper for Exercise 9.19: each feasible point carries an explicit finite family of active
literals. -/
private def exercise919ActiveLiterals : Fin 4 → Finset (BinaryLiteral (Fin 4))
  | 0 => {BinaryLiteral.neg 0, BinaryLiteral.neg 1, BinaryLiteral.neg 2, BinaryLiteral.neg 3}
  | 1 => {BinaryLiteral.neg 0, BinaryLiteral.neg 1, BinaryLiteral.neg 2, BinaryLiteral.var 3}
  | 2 => {BinaryLiteral.var 0, BinaryLiteral.neg 1, BinaryLiteral.neg 2, BinaryLiteral.var 3}
  | _ => {BinaryLiteral.neg 0, BinaryLiteral.var 1, BinaryLiteral.neg 2, BinaryLiteral.var 3}

/-- Helper for Exercise 9.19: each indexed feasible point really belongs to the feasible set. -/
private lemma exercise919Point_mem_feasibleSet (p : Fin 4) :
    exercise919Point p ∈ exercise_9_19_feasible_set := by
  -- Check each of the four classified points against the feasible-set characterization.
  fin_cases p <;> simp [exercise919Point, memExercise919FeasibleSet_iff]

/-- Helper for Exercise 9.19: active literals at the four feasible points are exactly the listed
finite literal families. -/
private lemma binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals
    (p : Fin 4) (l : BinaryLiteral (Fin 4)) :
    binary_literal_is_one (exercise919Point p) l ↔ l ∈ exercise919ActiveLiterals p := by
  -- Unfold each point and literal kind once, then let finite simplification finish.
  cases l with
  | var j =>
      fin_cases p <;> fin_cases j <;>
        simp [exercise919Point, exercise919ActiveLiterals,
          binary_literal_is_one, binary_literal_value]
  | neg j =>
      fin_cases p <;> fin_cases j <;>
        simp [exercise919Point, exercise919ActiveLiterals,
          binary_literal_is_one, binary_literal_value]

/-- Helper for Exercise 9.19: a pair witness can be searched for among the four classified
feasible points. -/
private lemma exercise919_pairHasFeasibleWitness_iff_existsPoint
    (u v : BinaryLiteral (Fin 4)) :
    (∃ x, x ∈ exercise_9_19_feasible_set ∧ binary_literal_is_one x u ∧ binary_literal_is_one x v) ↔
      ∃ p : Fin 4, u ∈ exercise919ActiveLiterals p ∧ v ∈ exercise919ActiveLiterals p := by
  constructor
  · rintro ⟨x, hx, hu, hv⟩
    -- Replace an arbitrary feasible witness by its index in the four-point classification.
    rcases (memExercise919FeasibleSet_iff x).1 hx with rfl | rfl | rfl | rfl
    · refine ⟨0, ?_, ?_⟩
      · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals 0 u).1 <|
          by simpa [exercise919Point] using hu
      · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals 0 v).1 <|
          by simpa [exercise919Point] using hv
    · refine ⟨1, ?_, ?_⟩
      · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals 1 u).1 <|
          by simpa [exercise919Point] using hu
      · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals 1 v).1 <|
          by simpa [exercise919Point] using hv
    · refine ⟨2, ?_, ?_⟩
      · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals 2 u).1 <|
          by simpa [exercise919Point] using hu
      · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals 2 v).1 <|
          by simpa [exercise919Point] using hv
    · refine ⟨3, ?_, ?_⟩
      · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals 3 u).1 <|
          by simpa [exercise919Point] using hu
      · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals 3 v).1 <|
          by simpa [exercise919Point] using hv
  · rintro ⟨p, hu, hv⟩
    -- Reconstruct a feasible witness from the indexed point and its active-literal data.
    refine ⟨exercise919Point p, exercise919Point_mem_feasibleSet p, ?_, ?_⟩
    · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals p u).2 hu
    · exact (binaryLiteral_is_one_exercise919Point_iff_mem_activeLiterals p v).2 hv

/-- Helper for Exercise 9.19: literal conflict is equivalent to distinctness together with the
absence of a feasible point activating both literals. -/
private lemma exercise919_literalConflict_iff_noPairWitness
    (u v : BinaryLiteral (Fin 4)) :
    literal_conflict exercise_9_19_feasible_set u v ↔
      u ≠ v ∧
        ¬ ∃ x, x ∈ exercise_9_19_feasible_set ∧
          binary_literal_is_one x u ∧ binary_literal_is_one x v := by
  constructor
  · rintro ⟨huv, hconflict⟩
    -- Repackage the universal infeasibility clause as the absence of a joint witness.
    refine ⟨huv, ?_⟩
    rintro ⟨x, hx, hu, hv⟩
    exact hconflict hx ⟨hu, hv⟩
  · rintro ⟨huv, hnowitness⟩
    -- Any hypothetical simultaneous activation would contradict the witness-free form.
    refine ⟨huv, ?_⟩
    intro x hx hactive
    exact hnowitness ⟨x, hx, hactive.1, hactive.2⟩

/-- Helper for Exercise 9.19: two distinct literals are jointly realizable exactly for the
nonedges of the explicit graph. -/
private lemma exercise919_pairHasFeasibleWitness_iff_nonedge
    (u v : BinaryLiteral (Fin 4)) (huv : u ≠ v) :
    (∃ x, x ∈ exercise_9_19_feasible_set ∧ binary_literal_is_one x u ∧ binary_literal_is_one x v) ↔
      s(u, v) ∉ exercise_9_19_edges := by
  -- After indexing the four feasible witnesses, the remaining check is purely finite.
  rw [exercise919_pairHasFeasibleWitness_iff_existsPoint]
  revert huv u v
  show ∀ u v : BinaryLiteral (Fin 4),
      u ≠ v →
        ((∃ p : Fin 4, u ∈ exercise919ActiveLiterals p ∧ v ∈ exercise919ActiveLiterals p) ↔
          s(u, v) ∉ exercise_9_19_edges
        )
  decide

/-- Helper for Exercise 9.19: cliquehood in the explicit graph is pairwise membership in the
listed edge family. -/
private lemma exercise919_isClique_iff_pairwiseEdge
    (S : Set (BinaryLiteral (Fin 4))) :
    exercise_9_19_graph.IsClique S ↔
      ∀ ⦃u v⦄, u ∈ S → v ∈ S → u ≠ v → s(u, v) ∈ exercise_9_19_edges := by
  constructor
  · intro hC u v hu hv huv
    -- Read each clique adjacency through the explicit graph's edge-set API.
    exact (exercise_9_19_graph_adj_iff u v).1 (hC hu hv huv) |>.1
  · intro hpair u hu v hv huv
    -- Pairwise edge membership reconstructs every adjacency required for cliquehood.
    exact (exercise_9_19_graph_adj_iff u v).2 ⟨hpair hu hv huv, huv⟩

/-- Helper for Exercise 9.19: in the four-variable example, literal conflict is exactly
membership in the explicit thirteen-edge list. -/
private lemma exercise919_literalConflict_iff_edgeMem
    (u v : BinaryLiteral (Fin 4)) :
    literal_conflict exercise_9_19_feasible_set u v ↔
      s(u, v) ∈ exercise_9_19_edges ∧ u ≠ v := by
  rw [exercise919_literalConflict_iff_noPairWitness]
  constructor
  · rintro ⟨huv, hnowitness⟩
    -- Convert the absence of a witness into explicit edge membership via the nonedge bridge.
    refine ⟨?_, huv⟩
    by_contra hedge
    exact hnowitness ((exercise919_pairHasFeasibleWitness_iff_nonedge u v huv).2 hedge)
  · rintro ⟨hedge, huv⟩
    -- Any feasible joint witness would exhibit a nonedge, contradicting the explicit edge list.
    refine ⟨huv, ?_⟩
    intro hwitness
    exact (exercise919_pairHasFeasibleWitness_iff_nonedge u v huv).1 hwitness hedge

/-- For Exercise 9.19, part (3) identifies the graph obtained from the four-variable `0,1`
program with the explicit graph `exercise_9_19_graph` having the thirteen listed conflict
edges. -/
theorem exercise_9_19_graph_eq_conflictGraph :
    exercise_9_19_graph = conflictGraph exercise_9_19_feasible_set := by
  ext u v
  -- Rewrite both graph adjacencies to the same explicit edge-membership criterion.
  rw [exercise_9_19_graph_adj_iff, conflictGraph_adj_iff, exercise919_literalConflict_iff_edgeMem]

/-- Helper for Exercise 9.19: maximal cliques in the explicit graph are exactly cliques that
cannot be enlarged by inserting one more literal. -/
private lemma exercise919_maximalClique_iff_forall_insert_finset
    {C : Finset (BinaryLiteral (Fin 4))} :
    Maximal exercise_9_19_graph.IsClique C ↔
      exercise_9_19_graph.IsClique C ∧
        ∀ x ∉ C, ¬ exercise_9_19_graph.IsClique (insert x C) := by
  -- Route correction: apply the set-level maximality API once, then immediately simplify back to
  -- `Finset.insert` so the later classification stays in a decidable finite normal form.
  simpa [Finset.mem_coe, Finset.coe_insert, Set.mem_insert_iff] using
    (Set.maximal_iff_forall_insert
      (P := exercise_9_19_graph.IsClique)
      (s := (↑C : Set (BinaryLiteral (Fin 4))))
      (hP := fun {_ _} hT hST => hT.subset hST))

/-- Helper for Exercise 9.19: inserted candidate cliques can be tested directly against the
explicit edge list. -/
private lemma exercise919_insertClique_iff_pairwiseEdge
    (C : Finset (BinaryLiteral (Fin 4))) (x : BinaryLiteral (Fin 4)) :
    exercise_9_19_graph.IsClique (insert x C) ↔
      ∀ ⦃u v⦄, u ∈ insert x C → v ∈ insert x C → u ≠ v → s(u, v) ∈ exercise_9_19_edges := by
  -- Reuse the explicit-edge clique criterion without leaving the `Finset.insert` spelling world.
  simpa [Finset.mem_coe] using
    (exercise919_isClique_iff_pairwiseEdge (S := (↑(insert x C) : Set (BinaryLiteral (Fin 4)))))

/-- Helper for Exercise 9.19: explicit edge membership is packaged as a Boolean test so the final
finite maximal-clique classification can be decided by computation. -/
private def exercise919EdgeMemBool
    (u v : BinaryLiteral (Fin 4)) : Bool :=
  decide (s(u, v) ∈ exercise_9_19_edges)

/-- Helper for Exercise 9.19: the Boolean edge test is equivalent to membership in the explicit
edge list. -/
private lemma exercise919EdgeMemBool_eq_true_iff
    (u v : BinaryLiteral (Fin 4)) :
    exercise919EdgeMemBool u v = true ↔ s(u, v) ∈ exercise_9_19_edges := by
  simp [exercise919EdgeMemBool]

/-- Helper for Exercise 9.19: the normalized clique-maximality predicate can be rewritten from the
implicit pairwise-edge binder form to an explicit finite quantifier form. -/
private lemma exercise919ImplicitPairwise_iff_explicit
    (C : Finset (BinaryLiteral (Fin 4))) :
    ((∀ ⦃u v : BinaryLiteral (Fin 4)⦄, u ∈ C → v ∈ C → u ≠ v → s(u, v) ∈ exercise_9_19_edges) ∧
        ∀ x ∉ C,
          ¬∀ ⦃u v : BinaryLiteral (Fin 4)⦄, u ∈ insert x C → v ∈ insert x C →
            u ≠ v → s(u, v) ∈ exercise_9_19_edges) ↔
      ((∀ u, u ∈ C → ∀ v, v ∈ C → u ≠ v → s(u, v) ∈ exercise_9_19_edges) ∧
        ∀ x, x ∉ C →
          ¬ ∀ u, u ∈ insert x C → ∀ v, v ∈ insert x C →
            u ≠ v → s(u, v) ∈ exercise_9_19_edges) := by
  -- Route correction: rewrite the remaining finite quantifiers to an explicit form before
  -- attempting any closed computation on the classifier.
  constructor
  · rintro ⟨hpair, hmax⟩
    refine ⟨?_, ?_⟩
    · intro u hu v hv huv
      exact hpair hu hv huv
    · intro x hx hinsert
      exact hmax x hx (fun {u v} hu hv huv ↦ hinsert u hu v hv huv)
  · rintro ⟨hpair, hmax⟩
    refine ⟨?_, ?_⟩
    · intro u v hu hv huv
      exact hpair u hu v hv huv
    · intro x hx hinsert
      exact hmax x hx (fun u hu v hv huv ↦ hinsert hu hv huv)

/-- Helper for Exercise 9.19: the explicit pairwise-edge predicate is equivalent to its Boolean
reflection, isolating the final computational classifier from proposition-valued edge tests. -/
private lemma exercise919ExplicitEdgeProp_iff_bool
    (C : Finset (BinaryLiteral (Fin 4))) :
    ((∀ u, u ∈ C → ∀ v, v ∈ C → u ≠ v → s(u, v) ∈ exercise_9_19_edges) ∧
        ∀ x, x ∉ C →
          ¬ ∀ u, u ∈ insert x C → ∀ v, v ∈ insert x C →
            u ≠ v → s(u, v) ∈ exercise_9_19_edges) ↔
      ((∀ u, u ∈ C → ∀ v, v ∈ C → u ≠ v → exercise919EdgeMemBool u v = true) ∧
        ∀ x, x ∉ C →
          ¬ ∀ u, u ∈ insert x C → ∀ v, v ∈ insert x C →
            u ≠ v → exercise919EdgeMemBool u v = true) := by
  -- Replace each atomic edge-membership test by its Boolean reflection so the remaining blocker
  -- is only the closed finite classification step.
  constructor
  · rintro ⟨hpair, hmax⟩
    refine ⟨?_, ?_⟩
    · intro u hu v hv huv
      exact (exercise919EdgeMemBool_eq_true_iff u v).2 (hpair u hu v hv huv)
    · intro x hx hxpair
      exact hmax x hx (fun u hu v hv huv ↦
        (exercise919EdgeMemBool_eq_true_iff u v).1 (hxpair u hu v hv huv))
  · rintro ⟨hpair, hmax⟩
    refine ⟨?_, ?_⟩
    · intro u hu v hv huv
      exact (exercise919EdgeMemBool_eq_true_iff u v).1 (hpair u hu v hv huv)
    · intro x hx hxpair
      exact hmax x hx (fun u hu v hv huv ↦
        (exercise919EdgeMemBool_eq_true_iff u v).2 (hxpair u hu v hv huv))

/-- Helper for Exercise 9.19: the candidate literal families form a finite type because the
underlying literal type is finite. -/
private instance : Fintype (Finset (BinaryLiteral (Fin 4))) :=
  Finset.fintype

/-- Helper for Exercise 9.19: the five maximal cliques are packaged as one explicit finite family
so the final classification theorem can be recovered from a membership statement. -/
private def exercise919ListedMaximalCliques : Finset (Finset (BinaryLiteral (Fin 4))) :=
  { ({BinaryLiteral.var 2, BinaryLiteral.neg 2} : Finset (BinaryLiteral (Fin 4))),
    ({BinaryLiteral.var 0, BinaryLiteral.neg 0, BinaryLiteral.var 2} :
      Finset (BinaryLiteral (Fin 4))),
    ({BinaryLiteral.var 1, BinaryLiteral.neg 1, BinaryLiteral.var 2} :
      Finset (BinaryLiteral (Fin 4))),
    ({BinaryLiteral.var 3, BinaryLiteral.neg 3, BinaryLiteral.var 2} :
      Finset (BinaryLiteral (Fin 4))),
    ({BinaryLiteral.var 0, BinaryLiteral.var 1, BinaryLiteral.var 2,
        BinaryLiteral.neg 3} : Finset (BinaryLiteral (Fin 4))) }

/-- Helper for Exercise 9.19: the normalized maximal-clique predicate is reflected into a Boolean
so the remaining finite classification can be computed on a closed object. -/
private def exercise919NormalizedMaximalCliqueBool
    (C : Finset (BinaryLiteral (Fin 4))) : Bool :=
  letI :
      DecidablePred fun u : BinaryLiteral (Fin 4) =>
        u ∈ C → ∀ v : BinaryLiteral (Fin 4), v ∈ C →
          u ≠ v → exercise919EdgeMemBool u v = true :=
    fun u =>
      letI :
          Decidable (∀ v : BinaryLiteral (Fin 4), v ∈ C →
            u ≠ v → exercise919EdgeMemBool u v = true) :=
        Fintype.decidableForallFintype
      inferInstance
  letI :
      DecidablePred fun x : BinaryLiteral (Fin 4) =>
        x ∉ C →
          ¬ ∀ u : BinaryLiteral (Fin 4), u ∈ insert x C →
              ∀ v : BinaryLiteral (Fin 4), v ∈ insert x C →
                u ≠ v → exercise919EdgeMemBool u v = true :=
    fun x =>
      letI :
          DecidablePred fun u : BinaryLiteral (Fin 4) =>
            u ∈ insert x C →
              ∀ v : BinaryLiteral (Fin 4), v ∈ insert x C →
                u ≠ v → exercise919EdgeMemBool u v = true :=
        fun u =>
          letI :
              Decidable (∀ v : BinaryLiteral (Fin 4), v ∈ insert x C →
                u ≠ v → exercise919EdgeMemBool u v = true) :=
            Fintype.decidableForallFintype
          inferInstance
      inferInstance
  letI :
      Decidable (∀ u : BinaryLiteral (Fin 4), u ∈ C → ∀ v : BinaryLiteral (Fin 4), v ∈ C →
        u ≠ v → exercise919EdgeMemBool u v = true) :=
    Fintype.decidableForallFintype
  letI :
      Decidable (∀ x : BinaryLiteral (Fin 4), x ∉ C →
        ¬ ∀ u : BinaryLiteral (Fin 4), u ∈ insert x C →
            ∀ v : BinaryLiteral (Fin 4), v ∈ insert x C →
              u ≠ v → exercise919EdgeMemBool u v = true) :=
    Fintype.decidableForallFintype
  decide
    ((∀ u : BinaryLiteral (Fin 4), u ∈ C → ∀ v : BinaryLiteral (Fin 4), v ∈ C →
        u ≠ v → exercise919EdgeMemBool u v = true) ∧
      ∀ x : BinaryLiteral (Fin 4), x ∉ C →
        ¬ ∀ u : BinaryLiteral (Fin 4), u ∈ insert x C →
            ∀ v : BinaryLiteral (Fin 4), v ∈ insert x C →
          u ≠ v → exercise919EdgeMemBool u v = true)

/-- Helper for Exercise 9.19: the computed maximal cliques are the subsets of the eight literals
whose Boolean classifier evaluates to `true`. -/
private def exercise919ComputedMaximalCliques : Finset (Finset (BinaryLiteral (Fin 4))) :=
  Finset.univ.powerset.filter fun S ↦ exercise919NormalizedMaximalCliqueBool S = true

/-- Helper for Exercise 9.19: the Boolean classifier is equivalent to the normalized explicit
maximal-clique predicate. -/
private lemma exercise919NormalizedMaximalCliqueBool_eq_true_iff
    (C : Finset (BinaryLiteral (Fin 4))) :
    exercise919NormalizedMaximalCliqueBool C = true ↔
      ((∀ u, u ∈ C → ∀ v, v ∈ C → u ≠ v → exercise919EdgeMemBool u v = true) ∧
        ∀ x, x ∉ C →
          ¬ ∀ u, u ∈ insert x C → ∀ v, v ∈ insert x C →
            u ≠ v → exercise919EdgeMemBool u v = true) := by
  -- Re-expand the Boolean reflection only once so later rewriting can stay proposition-free.
  simp [exercise919NormalizedMaximalCliqueBool]

/-- Helper for Exercise 9.19: the closed computed container records exactly the candidate families
whose Boolean maximal-clique classifier is true. -/
private lemma exercise919_memComputedMaximalCliques_iff
    (C : Finset (BinaryLiteral (Fin 4))) :
    C ∈ exercise919ComputedMaximalCliques ↔
      exercise919NormalizedMaximalCliqueBool C = true := by
  -- Membership in the filtered powerset reduces to the classifier because every finite family is
  -- automatically a subset of `Finset.univ`.
  simp [exercise919ComputedMaximalCliques, Finset.mem_filter]

/-- Helper for Exercise 9.19: the closed computed classifier evaluates to the five listed maximal
cliques of the explicit four-variable graph. -/
private lemma exercise919ComputedMaximalCliques_eq_listedCliques :
    exercise919ComputedMaximalCliques = exercise919ListedMaximalCliques := by
  -- The computation is now closed: both sides are concrete finsets of literal families.
  decide

/-- Helper for Exercise 9.19: membership in the explicit finite family is exactly the five-way
disjunction used by the theorem statement. -/
private lemma exercise919_memListedMaximalCliques_iff
    (C : Finset (BinaryLiteral (Fin 4))) :
    C ∈ exercise919ListedMaximalCliques ↔
      C = ({BinaryLiteral.var 2, BinaryLiteral.neg 2} : Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 0, BinaryLiteral.neg 0, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 1, BinaryLiteral.neg 1, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 3, BinaryLiteral.neg 3, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 0, BinaryLiteral.var 1, BinaryLiteral.var 2,
            BinaryLiteral.neg 3} : Finset (BinaryLiteral (Fin 4))) := by
  -- Normalize membership in the explicit finite family back to the theorem statement's shape.
  simp [exercise919ListedMaximalCliques]

/-- Helper for Exercise 9.19: after normalizing maximality to one-step insert tests, the maximal
cliques are exactly the five listed literal families. -/
private lemma exercise919_normalizedMaximalClique_iff_listed
    (C : Finset (BinaryLiteral (Fin 4))) :
    (exercise_9_19_graph.IsClique C ∧
        ∀ x ∉ C, ¬ exercise_9_19_graph.IsClique (insert x C)) ↔
      C = ({BinaryLiteral.var 2, BinaryLiteral.neg 2} : Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 0, BinaryLiteral.neg 0, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 1, BinaryLiteral.neg 1, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 3, BinaryLiteral.neg 3, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 0, BinaryLiteral.var 1, BinaryLiteral.var 2,
            BinaryLiteral.neg 3} : Finset (BinaryLiteral (Fin 4))) := by
  have hClique :
      exercise_9_19_graph.IsClique C ↔
        ∀ ⦃u v⦄, u ∈ C → v ∈ C → u ≠ v → s(u, v) ∈ exercise_9_19_edges := by
    -- Rewrite cliquehood for `C` itself to the explicit edge predicate.
    simpa [Finset.mem_coe] using
      (exercise919_isClique_iff_pairwiseEdge (S := (↑C : Set (BinaryLiteral (Fin 4)))))
  -- Every remaining quantifier now ranges over the finite eight-literal universe.
  rw [hClique]
  clear hClique
  simp_rw [exercise919_insertClique_iff_pairwiseEdge]
  rw [exercise919ImplicitPairwise_iff_explicit C, exercise919ExplicitEdgeProp_iff_bool C]
  -- Route correction: classify the normalized open predicate by first turning it into membership
  -- in a closed computed finset, and only then unfold the explicit five-way list.
  rw [(exercise919NormalizedMaximalCliqueBool_eq_true_iff C).symm]
  calc
    exercise919NormalizedMaximalCliqueBool C = true ↔
        C ∈ exercise919ComputedMaximalCliques := by
          exact (exercise919_memComputedMaximalCliques_iff C).symm
    _ ↔ C ∈ exercise919ListedMaximalCliques := by
      rw [exercise919ComputedMaximalCliques_eq_listedCliques]
    _ ↔
        C = ({BinaryLiteral.var 2, BinaryLiteral.neg 2} : Finset (BinaryLiteral (Fin 4))) ∨
          C = ({BinaryLiteral.var 0, BinaryLiteral.neg 0, BinaryLiteral.var 2} :
            Finset (BinaryLiteral (Fin 4))) ∨
          C = ({BinaryLiteral.var 1, BinaryLiteral.neg 1, BinaryLiteral.var 2} :
            Finset (BinaryLiteral (Fin 4))) ∨
          C = ({BinaryLiteral.var 3, BinaryLiteral.neg 3, BinaryLiteral.var 2} :
            Finset (BinaryLiteral (Fin 4))) ∨
          C = ({BinaryLiteral.var 0, BinaryLiteral.var 1, BinaryLiteral.var 2,
              BinaryLiteral.neg 3} : Finset (BinaryLiteral (Fin 4))) := by
          exact exercise919_memListedMaximalCliques_iff C

/-- Exercise 9.19 (4). The maximal cliques of the graph for the four-variable example are exactly
the five explicitly listed literal families. -/
theorem exercise_9_19_maximal_cliques
    {C : Finset (BinaryLiteral (Fin 4))} :
    Maximal exercise_9_19_graph.IsClique C ↔
      C = ({BinaryLiteral.var 2, BinaryLiteral.neg 2} : Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 0, BinaryLiteral.neg 0, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 1, BinaryLiteral.neg 1, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 3, BinaryLiteral.neg 3, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) ∨
        C = ({BinaryLiteral.var 0, BinaryLiteral.var 1, BinaryLiteral.var 2,
            BinaryLiteral.neg 3} : Finset (BinaryLiteral (Fin 4))) := by
  -- Route correction: normalize maximality directly in `Finset`, then classify the resulting
  -- explicit insert condition by finite computation on the eight literals.
  rw [exercise919_maximalClique_iff_forall_insert_finset,
    exercise919_normalizedMaximalClique_iff_listed]

/-- For Exercise 9.19, part (5) shows that the nontrivial maximal clique inequalities deduced
from the four-variable graph are `x3 ≤ 0` and `x1 + x2 + x3 - x4 ≤ 0`. -/
theorem exercise_9_19_nontrivial_maximal_clique_inequalities
    (x : Fin 4 → ℝ) (hx : x ∈ exercise_9_19_feasible_set) :
    x 2 ≤ 0 ∧ x 0 + x 1 + x 2 - x 3 ≤ 0 := by
  have h_binary :
      ∀ ⦃y : Fin 4 → ℝ⦄, y ∈ exercise_9_19_feasible_set → is_zero_one_family y := by
    intro y hy
    exact hy.2.2.2
  have hCliqueZero_graph :
      exercise_9_19_graph.IsClique
        ({BinaryLiteral.var 0, BinaryLiteral.neg 0, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) := by
    -- Check the three pairwise adjacencies directly in the explicit graph.
    intro u hu v hv huv
    have hu' :
        u = BinaryLiteral.var 0 ∨
          u = BinaryLiteral.neg 0 ∨
            u = BinaryLiteral.var 2 := by
      simpa using hu
    have hv' :
        v = BinaryLiteral.var 0 ∨
          v = BinaryLiteral.neg 0 ∨
            v = BinaryLiteral.var 2 := by
      simpa using hv
    rcases hu' with rfl | rfl | rfl <;>
      rcases hv' with rfl | rfl | rfl <;>
      simp [exercise_9_19_graph_adj_iff, exercise_9_19_edges] at huv ⊢
  have hCliqueMixed_graph :
      exercise_9_19_graph.IsClique
        ({BinaryLiteral.var 0, BinaryLiteral.var 1, BinaryLiteral.var 2, BinaryLiteral.neg 3} :
          Finset (BinaryLiteral (Fin 4))) := by
    -- Check the six relevant adjacencies directly in the explicit graph.
    intro u hu v hv huv
    have hu' :
        u = BinaryLiteral.var 0 ∨
          u = BinaryLiteral.var 1 ∨
            u = BinaryLiteral.var 2 ∨
              u = BinaryLiteral.neg 3 := by
      simpa using hu
    have hv' :
        v = BinaryLiteral.var 0 ∨
          v = BinaryLiteral.var 1 ∨
            v = BinaryLiteral.var 2 ∨
              v = BinaryLiteral.neg 3 := by
      simpa using hv
    rcases hu' with rfl | rfl | rfl | rfl <;>
      rcases hv' with rfl | rfl | rfl | rfl <;>
      simp [exercise_9_19_graph_adj_iff, exercise_9_19_edges] at huv ⊢
  have hCliqueZero :
      (conflictGraph exercise_9_19_feasible_set).IsClique
        ({BinaryLiteral.var 0, BinaryLiteral.neg 0, BinaryLiteral.var 2} :
          Finset (BinaryLiteral (Fin 4))) := by
    simpa [exercise_9_19_graph_eq_conflictGraph] using hCliqueZero_graph
  have hCliqueMixed :
      (conflictGraph exercise_9_19_feasible_set).IsClique
        ({BinaryLiteral.var 0, BinaryLiteral.var 1, BinaryLiteral.var 2, BinaryLiteral.neg 3} :
          Finset (BinaryLiteral (Fin 4))) := by
    simpa [exercise_9_19_graph_eq_conflictGraph] using hCliqueMixed_graph
  have hx2_zero : x 2 = 0 := by
    -- A clique containing both `x₁` and `1 - x₁` forces the remaining literal `x₃` to vanish.
    simpa [binary_literal_value] using
      exercise_9_19_clique_with_complement_forces_other_literals_zero
        exercise_9_19_feasible_set h_binary hCliqueZero
        (k := 0)
        (hk_var := by simp) (hk_neg := by simp)
        (l := BinaryLiteral.var 2) (hl := by simp)
        (hl_var := by decide) (hl_neg := by decide)
        x hx
  have hmixed :
      x 0 + x 1 + x 2 - x 3 ≤ 0 := by
    -- The abstract clique inequality specializes directly to the four-literal clique.
    simpa [clique_inequality_lhs, clique_inequality_rhs, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using
      exercise_9_19_clique_inequality_valid
        exercise_9_19_feasible_set h_binary
        (C := {BinaryLiteral.var 0, BinaryLiteral.var 1, BinaryLiteral.var 2, BinaryLiteral.neg 3})
        hCliqueMixed x hx
  refine ⟨?_, hmixed⟩
  linarith

/-- The first nontrivial maximal clique inequality of Exercise 9.19 (5) gives `x3 ≤ 0`. -/
theorem exercise_9_19_x3_nonpos {x : Fin 4 → ℝ} (hx : x ∈ exercise_9_19_feasible_set) :
    x 2 ≤ 0 :=
  (exercise_9_19_nontrivial_maximal_clique_inequalities x hx).1

/-- The second nontrivial maximal clique inequality of Exercise 9.19 (5) gives
`x1 + x2 + x3 - x4 ≤ 0`. -/
theorem exercise_9_19_x1_add_x2_add_x3_sub_x4_nonpos
    {x : Fin 4 → ℝ} (hx : x ∈ exercise_9_19_feasible_set) :
    x 0 + x 1 + x 2 - x 3 ≤ 0 :=
  (exercise_9_19_nontrivial_maximal_clique_inequalities x hx).2

/-- For Exercise 9.19, part (6) shows that maximal cliques containing both a variable and its
complement force the fixing `x3 = 0` in the four-variable example. -/
theorem exercise_9_19_fix_x3_to_zero
    {x : Fin 4 → ℝ} (hx : x ∈ exercise_9_19_feasible_set) :
    x 2 = 0 := by
  rcases is_zero_one_family.apply hx.2.2.2 2 with hx2 | hx2
  · exact hx2
  · exact False.elim <| (not_le_of_gt zero_lt_one) <| by
      simpa [hx2] using exercise_9_19_x3_nonpos hx

end Exercise919
