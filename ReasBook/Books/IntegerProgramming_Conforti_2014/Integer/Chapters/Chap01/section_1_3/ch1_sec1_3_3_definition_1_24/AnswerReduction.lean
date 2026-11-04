/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.Problem
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_18.PolynomialTime

@[expose] public section

/-- A polynomial-time answer reduction from a decision problem `D` to a computational problem `Q`
translates instances of `D` to instances of `Q` and recovers the correct answer from any solution
of the translated instance in polynomial time. -/
structure PolynomialTimeAnswerReduction
    (D : DecisionProblem)
    (Q : ComputationalProblem) where
  translate : PolynomialTimeMap D.Instance Q.Instance D.encodingSize Q.encodingSize
  recover :
    PolynomialTimeMap
      (Sigma fun i : D.Instance ↦ Q.Solution (translate.toFun i))
      Bool
      (fun x ↦ D.encodingSize x.1 + Q.solutionEncodingSize (translate.toFun x.1) x.2)
      (fun _ ↦ (1 : ℕ))
  recoverCorrect :
    ∀ i : D.Instance, ∀ s : Q.Solution (translate.toFun i),
      recover.toFun ⟨i, s⟩ = D.answer i
