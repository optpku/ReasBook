/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_proposition_1_10.ZeroOneILP
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_29.SAT
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace SAT

namespace Instance

/-- The clause matrix `A` of a SAT instance has entry `1` for a positive occurrence, `-1` for a
negative occurrence, and `0` when the variable does not contribute to the clause row. -/
def constraintMatrix (I : SAT.Instance) : Matrix (Fin I.m) (Fin I.n) ℤ :=
  fun i j ↦
    (if Literal.pos j ∈ I.clauses i then (1 : ℤ) else 0) -
      (if Literal.neg j ∈ I.clauses i then (1 : ℤ) else 0)

/-- Expanding `I.constraintMatrix` yields the row/column entry used in the SAT inequality
translation. -/
theorem constraintMatrix_apply (I : SAT.Instance) (i : Fin I.m) (j : Fin I.n) :
    I.constraintMatrix i j =
      (if Literal.pos j ∈ I.clauses i then (1 : ℤ) else 0) -
        (if Literal.neg j ∈ I.clauses i then (1 : ℤ) else 0) := by
  -- Evaluating the matrix exposes the two signed occurrence indicators.
  rfl

/-- The function `I.negativeCount` records how many negative literals occur in each clause. -/
def negativeCount (I : SAT.Instance) : Fin I.m → ℤ :=
  fun i ↦ (I.clauses i).negativeCount

/-- Expanding `I.negativeCount i` yields the sum of the negative-literal indicators in the
`i`-th clause. -/
theorem negativeCount_eq_sum (I : SAT.Instance) (i : Fin I.m) :
    I.negativeCount i =
      Finset.sum (I.clauses i) fun l ↦
        match l with
        | Literal.pos _ => (0 : ℤ)
        | Literal.neg _ => 1 := by
  -- Unfold the instance statistic and cast the defining natural-number sum to `ℤ`.
  rw [negativeCount, SAT.Clause.negativeCount, Nat.cast_sum]
  -- Each literal's `0` or `1` contribution is unchanged by the cast.
  refine Finset.sum_congr rfl ?_
  intro l _hl
  cases l <;> rfl

/-- The source right-hand side `1 - n(A)` of the SAT inequality system. -/
def rhs (I : SAT.Instance) : Fin I.m → ℤ :=
  fun i ↦ 1 - I.negativeCount i

/-- Expanding `I.rhs i` yields the source term `1 - n(A)` for the `i`-th clause row. -/
theorem rhs_eq (I : SAT.Instance) (i : Fin I.m) :
    I.rhs i = 1 - I.negativeCount i := by
  -- Evaluating the right-hand side exposes its defining subtraction.
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_definition_2_31/ZeroOneILP.lean`:
the signed occurrence sum of a clause is its objective. -/
private theorem signedMembershipSum_eq_objective
    {n : ℕ} (C : SAT.Clause n) (x : Fin n → ℤ) :
    (∑ j : Fin n,
        ((if Literal.pos j ∈ C then (1 : ℤ) else 0) -
          (if Literal.neg j ∈ C then (1 : ℤ) else 0)) * x j) = C.objective x := by
  classical
  -- Induct over the literals; inserting one literal changes exactly its signed coordinate.
  unfold SAT.Clause.objective
  induction C using Finset.induction_on with
  | empty => simp
  | @insert l C hl ih =>
      cases l with
      | pos j =>
          rw [Finset.sum_insert hl]
          calc
            (∑ k,
                ((if Literal.pos k ∈ insert (Literal.pos j) C then (1 : ℤ) else 0) -
                  (if Literal.neg k ∈ insert (Literal.pos j) C then (1 : ℤ) else 0)) *
                    x k) =
                ∑ k, ((if k = j then x k else 0) +
                  ((if Literal.pos k ∈ C then (1 : ℤ) else 0) -
                    (if Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _hk
                  by_cases hkj : k = j
                  · subst k
                    by_cases hneg : Literal.neg j ∈ C
                    · simp [hl, hneg]
                    · simp [hl, hneg]
                  · simp [hkj]
            _ = (∑ k, if k = j then x k else 0) +
                  ∑ k,
                    ((if Literal.pos k ∈ C then (1 : ℤ) else 0) -
                      (if Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k :=
                Finset.sum_add_distrib
            _ = x j +
                  ∑ k,
                    ((if Literal.pos k ∈ C then (1 : ℤ) else 0) -
                      (if Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k := by
                rw [Fintype.sum_ite_eq']
            _ = x j + ∑ l ∈ C,
                  match l with
                  | Literal.pos k => x k
                  | Literal.neg k => -x k := congrArg (fun z : ℤ ↦ x j + z) ih
      | neg j =>
          rw [Finset.sum_insert hl]
          calc
            (∑ k,
                ((if Literal.pos k ∈ insert (Literal.neg j) C then (1 : ℤ) else 0) -
                  (if Literal.neg k ∈ insert (Literal.neg j) C then (1 : ℤ) else 0)) *
                    x k) =
                ∑ k, ((if k = j then -x k else 0) +
                  ((if Literal.pos k ∈ C then (1 : ℤ) else 0) -
                    (if Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _hk
                  by_cases hkj : k = j
                  · subst k
                    by_cases hpos : Literal.pos j ∈ C
                    · simp [hl, hpos]
                    · simp [hl, hpos]
                  · simp [hkj]
            _ = (∑ k, if k = j then -x k else 0) +
                  ∑ k,
                    ((if Literal.pos k ∈ C then (1 : ℤ) else 0) -
                      (if Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k :=
                Finset.sum_add_distrib
            _ = -x j +
                  ∑ k,
                    ((if Literal.pos k ∈ C then (1 : ℤ) else 0) -
                      (if Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k := by
                rw [Fintype.sum_ite_eq']
            _ = -x j + ∑ l ∈ C,
                  match l with
                  | Literal.pos k => x k
                  | Literal.neg k => -x k := congrArg (fun z : ℤ ↦ -x j + z) ih

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_definition_2_31/ZeroOneILP.lean`:
matrix multiplication by a clause row agrees with the clause objective. -/
private theorem constraintMatrix_mulVec_eq_objective
    (I : SAT.Instance) (i : Fin I.m) (x : Fin I.n → ℤ) :
    Matrix.mulVec I.constraintMatrix x i = (I.clauses i).objective x := by
  -- Expose matrix multiplication and invoke the signed-occurrence normalization.
  simpa [Matrix.mulVec, dotProduct, constraintMatrix] using
    signedMembershipSum_eq_objective (I.clauses i) x

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_definition_2_31/ZeroOneILP.lean`:
the integer vector associated with a Boolean assignment is binary. -/
private theorem boolVector_isBinary {n : ℕ} (tau : Fin n → Bool) :
    ∀ j, (if tau j then (1 : ℤ) else 0) = 0 ∨ (if tau j then (1 : ℤ) else 0) = 1 := by
  -- Split on each Boolean coordinate to obtain the corresponding endpoint.
  intro j
  cases tau j <;> simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_definition_2_31/ZeroOneILP.lean`:
a Boolean assignment satisfies a clause exactly when its integer vector does not falsify it. -/
private theorem satisfiedBy_iff_not_falsifiedBy_bool
    {n : ℕ} (C : SAT.Clause n) (tau : Fin n → Bool) :
    C.satisfiedBy tau ↔
      ¬ C.falsifiedBy (fun j ↦ if tau j then (1 : ℤ) else 0) := by
  constructor
  · rintro ⟨l, hl, hsatisfied⟩ hfalsified
    -- A satisfied literal cannot obey its corresponding falsity equation.
    have hfalsifiedLiteral := hfalsified l hl
    cases l with
    | pos j =>
        change tau j = true at hsatisfied
        change (if tau j then (1 : ℤ) else 0) = 0 at hfalsifiedLiteral
        simp [hsatisfied] at hfalsifiedLiteral
    | neg j =>
        change tau j = false at hsatisfied
        change (if tau j then (1 : ℤ) else 0) = 1 at hfalsifiedLiteral
        simp [hsatisfied] at hfalsifiedLiteral
  · intro hnotFalsified
    by_contra hnotSatisfied
    apply hnotFalsified
    intro l hl
    -- If no member literal is satisfied, each Boolean coordinate has the falsifying value.
    cases l with
    | pos j =>
        cases htau : tau j with
        | false => simp [htau]
        | true =>
            have hsatisfiedLiteral : (Literal.pos j).satisfiedBy tau := by
              simp [Literal.satisfiedBy, htau]
            exact (hnotSatisfied ⟨Literal.pos j, hl, hsatisfiedLiteral⟩).elim
    | neg j =>
        cases htau : tau j with
        | false =>
            have hsatisfiedLiteral : (Literal.neg j).satisfiedBy tau := by
              simp [Literal.satisfiedBy, htau]
            exact (hnotSatisfied ⟨Literal.neg j, hl, hsatisfiedLiteral⟩).elim
        | true => simp [htau]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_definition_2_31/ZeroOneILP.lean`:
the objective of a clause on a binary vector is bounded below by minus its negative count. -/
private theorem neg_negativeCount_le_objective_of_binary
    {n : ℕ} (C : SAT.Clause n) {x : Fin n → ℤ}
    (hx : ∀ j, x j = 0 ∨ x j = 1) :
    -(C.negativeCount : ℤ) ≤ C.objective x := by
  -- Rewrite the shifted objective as a sum of nonnegative literal slacks.
  have hsum : 0 ≤ ∑ l ∈ C, SAT.Clause.literalSlack x l := by
    exact Finset.sum_nonneg fun l _hl ↦ SAT.Clause.literalSlack_nonneg_of_binary hx l
  rw [← C.objective_add_negativeCount_eq_sumLiteralSlack] at hsum
  omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_definition_2_31/ZeroOneILP.lean`:
clause satisfaction is equivalent to its integral objective inequality. -/
private theorem satisfiedBy_iff_rhs_le_objective
    {n : ℕ} (C : SAT.Clause n) (tau : Fin n → Bool) :
    C.satisfiedBy tau ↔
      1 - (C.negativeCount : ℤ) ≤
        C.objective (fun j ↦ if tau j then (1 : ℤ) else 0) := by
  have hbinary := boolVector_isBinary tau
  have hlower := neg_negativeCount_le_objective_of_binary C hbinary
  constructor
  · intro hsatisfied
    -- Satisfaction excludes the unique minimal objective value, so integrality raises the bound.
    have hne :
        C.objective (fun j ↦ if tau j then (1 : ℤ) else 0) ≠
          -(C.negativeCount : ℤ) := by
      intro heq
      have hfalsified :=
        (C.objective_eq_neg_negativeCount_iff_falsifiedBy_of_binary hbinary).mp heq
      exact (satisfiedBy_iff_not_falsifiedBy_bool C tau).mp hsatisfied hfalsified
    omega
  · intro hobjective
    -- Conversely, the stronger integral bound rules out clause falsification.
    apply (satisfiedBy_iff_not_falsifiedBy_bool C tau).mpr
    intro hfalsified
    have heq :=
      (C.objective_eq_neg_negativeCount_iff_falsifiedBy_of_binary hbinary).mpr hfalsified
    omega

/-- The SAT-to-`0/1`-ILP translation packages the equivalent `≤` system obtained by negating the
source inequalities `A x ≥ 1 - n(A)`. -/
def toZeroOneILP (I : SAT.Instance) : ZeroOneILPInstance :=
  ZeroOneILPInstance.ofSystem (-I.constraintMatrix) (fun i ↦ - I.rhs i)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_definition_2_31/ZeroOneILP.lean:
A Boolean assignment satisfies `I` exactly when it gives a feasible `0/1` point for
`I.toZeroOneILP`. -/
theorem satisfiable_iff_zeroOneILP_feasible (I : SAT.Instance) :
    I.hasSatisfyingAssignment ↔ I.toZeroOneILP.hasFeasibleAssignment := by
  unfold hasSatisfyingAssignment ZeroOneILPInstance.hasFeasibleAssignment toZeroOneILP
    ZeroOneILPInstance.ofSystem
  constructor
  · rintro ⟨tau, hsatisfies⟩
    refine ⟨tau, ?_⟩
    intro i
    dsimp only
    -- Translate clause satisfaction to the corresponding unnegated row inequality.
    have hobjective :=
      (satisfiedBy_iff_rhs_le_objective (I.clauses i) tau).mp (hsatisfies i)
    -- Negating both sides puts that inequality in the stored `≤` orientation.
    rw [Matrix.neg_mulVec, Pi.neg_apply,
      constraintMatrix_mulVec_eq_objective I i]
    unfold rhs negativeCount
    omega
  · rintro ⟨tau, hfeasible⟩
    refine ⟨tau, ?_⟩
    intro i
    -- Normalize the feasible translated row back to the clause objective inequality.
    have hrow := hfeasible i
    dsimp only at hrow
    rw [Matrix.neg_mulVec, Pi.neg_apply,
      constraintMatrix_mulVec_eq_objective I i] at hrow
    unfold rhs negativeCount at hrow
    -- The sharp objective characterization recovers satisfaction of this clause.
    apply (satisfiedBy_iff_rhs_le_objective (I.clauses i) tau).mpr
    omega

end Instance

end SAT
