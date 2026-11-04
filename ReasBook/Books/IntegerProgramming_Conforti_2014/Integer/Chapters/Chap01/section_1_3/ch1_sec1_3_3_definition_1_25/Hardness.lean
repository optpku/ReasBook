/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_20.NP
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_24.AnswerReduction

@[expose] public section

/-- A computational problem `Q` is NP-hard if every decision problem in `NP` admits a
polynomial-time answer reduction to `Q`. -/
def ComputationalProblem.isNPHard (Q : ComputationalProblem) : Prop :=
  ∀ D : DecisionProblem, D.inNP → Nonempty (PolynomialTimeAnswerReduction D Q)

namespace ComputationalProblem

/-- `Q.isNPHard` means that every decision problem in `NP` admits a polynomial-time answer
reduction to `Q`. -/
theorem isNPHard_iff
    (Q : ComputationalProblem) :
    Q.isNPHard ↔
      ∀ D : DecisionProblem, D.inNP → Nonempty (PolynomialTimeAnswerReduction D Q) :=
  Iff.rfl

end ComputationalProblem
