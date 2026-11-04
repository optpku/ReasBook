/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.YesSet

open scoped BigOperators

public section

namespace SAT

/-- A SAT literal in the variables `x_1, ..., x_n` is either a positive occurrence `x_j` or a
negative occurrence `¬x_j`. -/
inductive Literal (n : ℕ)
  | pos : Fin n → Literal n
  | neg : Fin n → Literal n
deriving DecidableEq, Repr

/-- A SAT clause in `n` variables is a finite family of literals. -/
abbrev Clause (n : ℕ) := Finset (Literal n)

/-- A SAT instance consists of a finite family of clauses in finitely many variables. -/
structure Instance where
  n : ℕ
  m : ℕ
  clauses : Fin m → Clause n

namespace Instance

/-- Build a SAT instance from an explicit row-indexed clause family. -/
def ofClauses {n m : ℕ} (clauses : Fin m → Clause n) : SAT.Instance where
  n := n
  m := m
  clauses := clauses

/-- The variable count of `SAT.Instance.ofClauses clauses` is the ambient `n`. -/
theorem ofClauses_n {n m : ℕ} (clauses : Fin m → Clause n) :
    (SAT.Instance.ofClauses clauses).n = n := by
  -- Unfolding `ofClauses` exposes the stored variable count directly.
  rfl

/-- The clause count of `SAT.Instance.ofClauses clauses` is the ambient `m`. -/
theorem ofClauses_m {n m : ℕ} (clauses : Fin m → Clause n) :
    (SAT.Instance.ofClauses clauses).m = m := by
  -- Unfolding `ofClauses` exposes the stored clause count directly.
  rfl

end Instance

namespace Literal

/-- A literal is satisfied by a Boolean assignment when the corresponding truth value matches the
literal sign. -/
def satisfiedBy {n : ℕ} (l : Literal n) (τ : Fin n → Bool) : Prop :=
  match l with
  | .pos j => τ j = true
  | .neg j => τ j = false

/-- A positive literal is satisfied exactly when the underlying variable is assigned `true`. -/
theorem satisfiedBy_pos_iff {n : ℕ} (τ : Fin n → Bool) (j : Fin n) :
    (Literal.pos j).satisfiedBy τ ↔ τ j = true := by
  -- The positive case is exactly the defining branch of `Literal.satisfiedBy`.
  rfl

/-- A negative literal is satisfied exactly when the underlying variable is assigned `false`. -/
theorem satisfiedBy_neg_iff {n : ℕ} (τ : Fin n → Bool) (j : Fin n) :
    (Literal.neg j).satisfiedBy τ ↔ τ j = false := by
  -- The negative case is exactly the defining branch of `Literal.satisfiedBy`.
  rfl

end Literal

namespace Clause

/-- A clause is satisfied by a Boolean assignment when one of its literals is satisfied. -/
def satisfiedBy {n : ℕ} (C : Clause n) (τ : Fin n → Bool) : Prop :=
  ∃ l ∈ C, l.satisfiedBy τ

/-- Expanding `C.satisfiedBy τ` yields the existential over satisfied literals in `C`. -/
theorem satisfiedBy_iff_exists_mem {n : ℕ} (C : Clause n) (τ : Fin n → Bool) :
    C.satisfiedBy τ ↔ ∃ l ∈ C, l.satisfiedBy τ := by
  -- This theorem is the definitional expansion of clause satisfaction.
  rfl

/-- The number of negative literals in the clause `C`. -/
def negativeCount {n : ℕ} (C : Clause n) : ℕ :=
  Finset.sum C fun l ↦
    match l with
    | .pos _ => 0
    | .neg _ => 1

/-- The signed clause objective on an integer vector `x`. -/
def objective {n : ℕ} (C : Clause n) (x : Fin n → ℤ) : ℤ :=
  Finset.sum C fun l ↦
    match l with
    | .pos j => x j
    | .neg j => -x j

/-- The integer vector `x` falsifies `C` when every positive literal is `0` and every negative
literal is `1`. -/
def falsifiedBy {n : ℕ} (C : Clause n) (x : Fin n → ℤ) : Prop :=
  ∀ l ∈ C,
    match l with
    | .pos j => x j = 0
    | .neg j => x j = 1

/-- Expanding `C.falsifiedBy x` gives the literalwise falsity conditions. -/
theorem falsifiedBy_iff {n : ℕ} {C : Clause n} {x : Fin n → ℤ} :
    C.falsifiedBy x ↔
      ∀ l ∈ C,
        match l with
        | .pos j => x j = 0
        | .neg j => x j = 1 :=
  Iff.rfl

/-- Helper for Definition 2.29: the normalized slack contributed by a single literal under the
integer assignment `x`. -/
def literalSlack {n : ℕ} (x : Fin n → ℤ) (l : Literal n) : ℤ :=
  match l with
  | .pos j => x j
  | .neg j => 1 - x j

/-- Helper for Definition 2.29: adding `C.negativeCount` to the clause objective rewrites it as
the sum of the literalwise slack terms. -/
theorem objective_add_negativeCount_eq_sumLiteralSlack
    {n : ℕ} (C : Clause n) (x : Fin n → ℤ) :
    C.objective x + (C.negativeCount : ℤ) = Finset.sum C (literalSlack x) := by
  -- Rewrite both clause statistics as sums so the literal contributions can be combined.
  rw [objective, negativeCount, Nat.cast_sum, ← Finset.sum_add_distrib]
  -- Each literal then simplifies to its normalized slack contribution.
  refine Finset.sum_congr rfl ?_
  intro l hl
  cases l with
  | pos j =>
      simp [literalSlack]
  | neg j =>
      simp [literalSlack, sub_eq_add_neg, add_comm]

/-- Helper for Definition 2.29: every normalized literal slack is nonnegative for a binary
integer assignment. -/
theorem literalSlack_nonneg_of_binary
    {n : ℕ} {x : Fin n → ℤ} (hx : ∀ j, x j = 0 ∨ x j = 1) (l : Literal n) :
    0 ≤ literalSlack x l := by
  -- Binary coordinates force each slack to be either `0` or `1`.
  cases l with
  | pos j =>
      rcases hx j with h0 | h1
      · simp [literalSlack, h0]
      · simp [literalSlack, h1]
  | neg j =>
      rcases hx j with h0 | h1
      · simp [literalSlack, h0]
      · simp [literalSlack, h1]

/-- Helper for Definition 2.29: for a binary assignment, a normalized literal slack vanishes
exactly when that literal is falsified. -/
theorem literalSlack_eq_zero_iff_of_binary
    {n : ℕ} {x : Fin n → ℤ} (hx : ∀ j, x j = 0 ∨ x j = 1) (l : Literal n) :
    literalSlack x l = 0 ↔
      match l with
      | .pos j => x j = 0
      | .neg j => x j = 1 := by
  -- Binary coordinates reduce the slack computation to the two possible cases.
  cases l with
  | pos j =>
      rcases hx j with h0 | h1
      · simp [literalSlack, h0]
      · simp [literalSlack, h1]
  | neg j =>
      rcases hx j with h0 | h1
      · simp [literalSlack, h0]
      · simp [literalSlack, h1]

/-- For a binary integer vector, the clause objective attains `-(C.negativeCount : ℤ)` exactly
when `x` falsifies the clause `C`. -/
theorem objective_eq_neg_negativeCount_iff_falsifiedBy_of_binary
    {n : ℕ} (C : Clause n) {x : Fin n → ℤ} (hx : ∀ j, x j = 0 ∨ x j = 1) :
    C.objective x = -(C.negativeCount : ℤ) ↔ C.falsifiedBy x := by
  -- Move the target value to a zero-sum statement over normalized literal slacks.
  rw [eq_neg_iff_add_eq_zero, objective_add_negativeCount_eq_sumLiteralSlack]
  -- A sum of nonnegative slacks vanishes exactly when every literal slack vanishes.
  rw [Finset.sum_eq_zero_iff_of_nonneg fun l _hl ↦ literalSlack_nonneg_of_binary hx l]
  -- The pointwise zero condition is exactly the clause falsity predicate.
  rw [falsifiedBy_iff]
  constructor
  · intro h l hl
    exact (literalSlack_eq_zero_iff_of_binary hx l).mp (h l hl)
  · intro h l hl
    exact (literalSlack_eq_zero_iff_of_binary hx l).mpr (h l hl)

end Clause

namespace Instance

/-- A SAT instance has a satisfying assignment when some Boolean valuation satisfies every clause.
-/
def hasSatisfyingAssignment (I : SAT.Instance) : Prop :=
  ∃ τ : Fin I.n → Bool, ∀ i : Fin I.m, (I.clauses i).satisfiedBy τ

/-- Expanding `I.hasSatisfyingAssignment` yields the textbook existential over truth assignments
that satisfy all clauses of `I`. -/
theorem hasSatisfyingAssignment_iff (I : SAT.Instance) :
    I.hasSatisfyingAssignment ↔
      ∃ τ : Fin I.n → Bool, ∀ i : Fin I.m, (I.clauses i).satisfiedBy τ := by
  -- This is the definitional expansion of the SAT satisfiability predicate.
  rfl

/-- The encoding size of a SAT instance counts variables, clauses, and literal occurrences. -/
def encodingSize (I : SAT.Instance) : ℕ :=
  I.n + I.m + ∑ i : Fin I.m, (I.clauses i).card

/-- Expanding `I.encodingSize` yields the variable count, clause count, and total literal count.
-/
theorem encodingSize_eq (I : SAT.Instance) :
    I.encodingSize = I.n + I.m + ∑ i : Fin I.m, (I.clauses i).card := by
  -- The encoding size theorem just unfolds the stored formula.
  rfl

/-- The canonical decision problem attached to SAT uses `SAT.Instance` as instances, the encoding
size `SAT.Instance.encodingSize`, and the yes-instances consisting of satisfiable formulas. -/
noncomputable abbrev decisionProblem : DecisionProblem :=
  DecisionProblem.ofYesSet SAT.Instance.encodingSize { I | I.hasSatisfyingAssignment }

/-- The Boolean answer of `SAT.Instance.decisionProblem` is true exactly when the SAT instance has
a satisfying assignment. -/
theorem decisionProblem_answer_eq_true_iff (I : SAT.Instance) :
    SAT.Instance.decisionProblem.answer I = true ↔ I.hasSatisfyingAssignment := by
  simp [decisionProblem]

end Instance

end SAT
