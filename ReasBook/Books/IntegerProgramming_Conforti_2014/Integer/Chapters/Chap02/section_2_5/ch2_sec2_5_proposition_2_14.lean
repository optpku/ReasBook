/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_31.ZeroOneILP
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_proposition_2_14.Clause

open scoped BigOperators

namespace SAT.Instance

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14.lean`: the signed occurrence
sum of a clause is its objective. -/
theorem signedOccurrenceSum_eq_objective
    {n : ℕ} (C : SAT.Clause n) (x : Fin n → ℤ) :
    (∑ j : Fin n,
        ((if SAT.Literal.pos j ∈ C then (1 : ℤ) else 0) -
          (if SAT.Literal.neg j ∈ C then (1 : ℤ) else 0)) * x j) = C.objective x := by
  classical
  -- Induct over the literals, recording the signed contribution of the inserted literal.
  unfold SAT.Clause.objective
  induction C using Finset.induction_on with
  | empty => simp
  | @insert l C hl ih =>
      cases l with
      | pos j =>
          rw [Finset.sum_insert hl]
          calc
            (∑ k,
                ((if SAT.Literal.pos k ∈ insert (SAT.Literal.pos j) C then (1 : ℤ) else 0) -
                  (if SAT.Literal.neg k ∈ insert (SAT.Literal.pos j) C then (1 : ℤ) else 0)) *
                    x k) =
                ∑ k, ((if k = j then x k else 0) +
                  ((if SAT.Literal.pos k ∈ C then (1 : ℤ) else 0) -
                    (if SAT.Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _hk
                  by_cases hkj : k = j
                  · subst k
                    by_cases hneg : SAT.Literal.neg j ∈ C
                    · simp [hl, hneg]
                    · simp [hl, hneg]
                  · simp [hkj]
            _ = (∑ k, if k = j then x k else 0) +
                  ∑ k,
                    ((if SAT.Literal.pos k ∈ C then (1 : ℤ) else 0) -
                      (if SAT.Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k :=
                Finset.sum_add_distrib
            _ = x j +
                  ∑ k,
                    ((if SAT.Literal.pos k ∈ C then (1 : ℤ) else 0) -
                      (if SAT.Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k := by
                rw [Fintype.sum_ite_eq']
            _ = x j + ∑ l ∈ C,
                  match l with
                  | SAT.Literal.pos k => x k
                  | SAT.Literal.neg k => -x k := congrArg (fun z : ℤ ↦ x j + z) ih
      | neg j =>
          rw [Finset.sum_insert hl]
          calc
            (∑ k,
                ((if SAT.Literal.pos k ∈ insert (SAT.Literal.neg j) C then (1 : ℤ) else 0) -
                  (if SAT.Literal.neg k ∈ insert (SAT.Literal.neg j) C then (1 : ℤ) else 0)) *
                    x k) =
                ∑ k, ((if k = j then -x k else 0) +
                  ((if SAT.Literal.pos k ∈ C then (1 : ℤ) else 0) -
                    (if SAT.Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _hk
                  by_cases hkj : k = j
                  · subst k
                    by_cases hpos : SAT.Literal.pos j ∈ C
                    · simp [hl, hpos]
                    · simp [hl, hpos]
                  · simp [hkj]
            _ = (∑ k, if k = j then -x k else 0) +
                  ∑ k,
                    ((if SAT.Literal.pos k ∈ C then (1 : ℤ) else 0) -
                      (if SAT.Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k :=
                Finset.sum_add_distrib
            _ = -x j +
                  ∑ k,
                    ((if SAT.Literal.pos k ∈ C then (1 : ℤ) else 0) -
                      (if SAT.Literal.neg k ∈ C then (1 : ℤ) else 0)) * x k := by
                rw [Fintype.sum_ite_eq']
            _ = -x j + ∑ l ∈ C,
                  match l with
                  | SAT.Literal.pos k => x k
                  | SAT.Literal.neg k => -x k := congrArg (fun z : ℤ ↦ -x j + z) ih

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14.lean`: multiplying by a row of
the translated constraint matrix evaluates the corresponding clause objective. -/
theorem constraintMatrix_mulVec_eq_clauseObjective
    (I : SAT.Instance) (i : Fin I.m) (x : Fin I.n → ℤ) :
    Matrix.mulVec I.constraintMatrix x i = (I.clauses i).objective x := by
  -- Unfold one matrix row and apply the signed-occurrence normalization.
  simpa [Matrix.mulVec, dotProduct, constraintMatrix] using
    signedOccurrenceSum_eq_objective (I.clauses i) x

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14.lean`: a Boolean assignment
satisfies a clause exactly when its canonical integer vector meets the clause bound. -/
theorem satisfiedByIffRhsLeObjectiveOfBoolVector
    {n : ℕ} (C : SAT.Clause n) (τ : Fin n → Bool) :
    C.satisfiedBy τ ↔
      1 - (C.negativeCount : ℤ) ≤
        C.objective (fun j ↦ if τ j then (1 : ℤ) else 0) := by
  constructor
  · intro hsatisfied
    -- Satisfaction excludes the complementary strict-violation condition.
    apply le_of_not_gt
    intro hlt
    exact ((C.notSatisfiedByIffObjectiveLtRhsOfBoolVector τ).mpr hlt) hsatisfied
  · intro hobjective
    -- The non-strict bound contradicts every strict violation of the clause inequality.
    by_contra hnotSatisfied
    have hlt := (C.notSatisfiedByIffObjectiveLtRhsOfBoolVector τ).mp hnotSatisfied
    exact (not_lt_of_ge hobjective) hlt

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14.lean`: the canonical integer
encoding of an assignment is feasible exactly when the assignment satisfies every clause. -/
theorem boolVector_mem_toZeroOneILP_feasibleSet_iff
    (I : SAT.Instance) (τ : Fin I.n → Bool) :
    (fun j ↦ if τ j then (1 : ℤ) else 0) ∈ I.toZeroOneILP.feasibleSet ↔
      ∀ i : Fin I.m, (I.clauses i).satisfiedBy τ := by
  constructor
  · intro hfeasible
    rcases (ZeroOneILPInstance.mem_feasibleSet_iff I.toZeroOneILP _).mp hfeasible with
      ⟨_hbinary, hrows⟩
    intro i
    -- Normalize the stored negated row inequality back to the source clause bound.
    have hrow := hrows i
    dsimp only [toZeroOneILP, ZeroOneILPInstance.ofSystem] at hrow
    rw [Matrix.neg_mulVec, Pi.neg_apply] at hrow
    have hmatrix :
        I.constraintMatrix.mulVec (fun j : Fin I.n ↦ if τ j then (1 : ℤ) else 0) i =
          (I.clauses i).objective (fun j ↦ if τ j then (1 : ℤ) else 0) :=
      constraintMatrix_mulVec_eq_clauseObjective I i _
    have hunnegated :
        I.rhs i ≤
          I.constraintMatrix.mulVec (fun j : Fin I.n ↦ if τ j then (1 : ℤ) else 0) i :=
      neg_le_neg_iff.mp hrow
    rw [hmatrix] at hunnegated
    unfold rhs negativeCount at hunnegated
    exact (satisfiedByIffRhsLeObjectiveOfBoolVector (I.clauses i) τ).mpr hunnegated
  · intro hsatisfies
    apply (ZeroOneILPInstance.mem_feasibleSet_iff I.toZeroOneILP _).mpr
    refine ⟨?_, ?_⟩
    · -- Every coordinate of the canonical encoding is an integer endpoint.
      intro j
      cases τ j <;> simp
    · intro i
      -- Negate the semantic clause bound to obtain the translated row inequality.
      have hobjective :=
        (satisfiedByIffRhsLeObjectiveOfBoolVector (I.clauses i) τ).mp (hsatisfies i)
      dsimp only [toZeroOneILP, ZeroOneILPInstance.ofSystem]
      rw [Matrix.neg_mulVec, Pi.neg_apply]
      have hmatrix :
          I.constraintMatrix.mulVec (fun j : Fin I.n ↦ if τ j then (1 : ℤ) else 0) i =
            (I.clauses i).objective (fun j ↦ if τ j then (1 : ℤ) else 0) :=
        constraintMatrix_mulVec_eq_clauseObjective I i _
      have hunnegated :
          I.rhs i ≤
            I.constraintMatrix.mulVec (fun j : Fin I.n ↦ if τ j then (1 : ℤ) else 0) i := by
        rw [hmatrix]
        unfold rhs negativeCount
        exact hobjective
      exact neg_le_neg hunnegated

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14.lean`: every binary integer vector
is the canonical integer encoding of a Boolean vector, and conversely. -/
theorem binaryIntVector_iff_exists_boolVector
    {n : ℕ} (x : Fin n → ℤ) :
    (∀ j, x j = 0 ∨ x j = 1) ↔
      ∃ τ : Fin n → Bool, (fun j ↦ if τ j then (1 : ℤ) else 0) = x := by
  constructor
  · intro hbinary
    let τ : Fin n → Bool := fun j ↦ if x j = 1 then true else false
    refine ⟨τ, ?_⟩
    -- Decode each binary coordinate and verify that re-encoding returns it.
    funext j
    dsimp only [τ]
    rcases hbinary j with hzero | hone
    · simp [hzero]
    · simp [hone]
  · rintro ⟨τ, hτ⟩
    intro j
    -- Transport the evident binary alternative along the encoding equality.
    rw [← congrFun hτ j]
    cases τ j <;> simp

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14.lean

Proposition 2.14 [Inference as existence of a counterexample]. A clause `C` is not deducible
from the clause family `I` exactly when there exists a Boolean assignment satisfying every clause
of `I` but not `C`, equivalently when the translated `0/1` integer program `I.toZeroOneILP` has a
feasible binary point whose clause objective for `C` is strictly less than
`1 - (C.negativeCount : ℤ)`. -/
theorem counterexampleIffExistsFeasibleViolation
    (I : SAT.Instance) (C : SAT.Clause I.n) :
    (∃ τ : Fin I.n → Bool, (∀ i : Fin I.m, (I.clauses i).satisfiedBy τ) ∧ ¬ C.satisfiedBy τ) ↔
      ∃ x : Fin I.n → ℤ, x ∈ I.toZeroOneILP.feasibleSet ∧
        C.objective x < 1 - (C.negativeCount : ℤ) := by
  constructor
  · rintro ⟨τ, hsatisfies, hnotSatisfied⟩
    let x : Fin I.n → ℤ := fun j ↦ if τ j then 1 else 0
    refine ⟨x, ?_, ?_⟩
    · -- The witness-preserving bridge turns all satisfied clauses into feasibility.
      exact (boolVector_mem_toZeroOneILP_feasibleSet_iff I τ).mpr hsatisfies
    · -- The same encoded witness strictly violates the distinguished clause.
      exact (C.notSatisfiedByIffObjectiveLtRhsOfBoolVector τ).mp hnotSatisfied
  · rintro ⟨x, hx, hviolation⟩
    have hbinary := (ZeroOneILPInstance.mem_feasibleSet_iff I.toZeroOneILP x).mp hx |>.1
    obtain ⟨τ, hτ⟩ := (binaryIntVector_iff_exists_boolVector x).mp hbinary
    refine ⟨τ, ?_, ?_⟩
    · -- Re-encode the binary point and transport its feasibility to clause satisfaction.
      apply (boolVector_mem_toZeroOneILP_feasibleSet_iff I τ).mp
      rw [hτ]
      exact hx
    · -- Transport the strict violation to the decoded assignment.
      apply (C.notSatisfiedByIffObjectiveLtRhsOfBoolVector τ).mpr
      rw [hτ]
      exact hviolation

#print axioms counterexampleIffExistsFeasibleViolation

end SAT.Instance
