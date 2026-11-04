/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_23
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_3.Feasibility

/-
This source-facing item records the Chapter 1 complexity consequences for the canonical decision
problem owner `MixedIntegerLinearFeasibility.decisionProblem`.
-/

namespace MixedIntegerLinearFeasibility

/-- Helper for Theorem 1.3: the self-verifier runs in constant time. -/
private theorem selfVerifierMapRuntimeLe
    (x : Sigma fun _ : decisionProblem.Instance ↦ Unit) :
    1 ≤ (Polynomial.C 1).eval (decisionProblem.encodingSize x.1 + 0) := by
  -- The verifier runtime is the constant function `1`.
  simp

/-- Helper for Theorem 1.3: the self-verifier always returns a Boolean of encoding size `1`. -/
private theorem selfVerifierMapOutputLe
    (x : Sigma fun _ : decisionProblem.Instance ↦ Unit) :
    (1 : ℕ) ≤ (Polynomial.C 1).eval (decisionProblem.encodingSize x.1 + 0) := by
  -- Every Boolean output has the declared constant encoding-size bound.
  simp

/-- Helper for Theorem 1.3: the self-verifier for mixed-integer linear feasibility ignores the
trivial certificate and reruns the canonical Boolean answer. -/
private noncomputable def selfVerifierMap :
    PolynomialTimeMap
      (Sigma fun _ : decisionProblem.Instance ↦ Unit)
      Bool
      (fun x ↦ decisionProblem.encodingSize x.1 + 0)
      (fun _ ↦ (1 : ℕ)) where
  toFun := fun x ↦ decisionProblem.answer x.1
  runtime := fun _ ↦ 1
  timeBound := Polynomial.C 1
  runtime_le := selfVerifierMapRuntimeLe
  outputSizeBound := Polynomial.C 1
  outputSize_le := selfVerifierMapOutputLe

/-- Helper for Theorem 1.3: the trivial certificate has zero encoding size. -/
private theorem selfVerifierCertificateEncodingSizeLe
    (I : decisionProblem.Instance)
    (_c : Unit) :
    0 ≤ (Polynomial.C 0).eval (decisionProblem.encodingSize I) := by
  -- The certificate-size bound is the constant zero polynomial.
  simp

/-- Helper for Theorem 1.3: the self-verifier accepts exactly the yes-instances of the packaged
decision problem. -/
private theorem selfVerifierAcceptsIff
    (I : decisionProblem.Instance) :
    decisionProblem.answer I = true ↔
      ∃ c : Unit, selfVerifierMap.toFun ⟨I, c⟩ = true := by
  constructor
  · intro hAnswer
    -- The unique unit certificate carries the original Boolean answer unchanged.
    refine ⟨(), ?_⟩
    simpa [selfVerifierMap] using hAnswer
  · rintro ⟨c, hAccepts⟩
    -- Forgetting the trivial certificate recovers the original Boolean answer.
    simpa [selfVerifierMap] using hAccepts

/-- Helper for Theorem 1.3: the packaged decision problem has a canonical unit-certificate witness
system. -/
private noncomputable def selfVerifierWitnessSystem :
    NPWitnessSystem decisionProblem :=
  NPWitnessSystem.ofVerifier
    (fun _ : decisionProblem.Instance ↦ Unit)
    (fun _ _ ↦ 0)
    selfVerifierMap
    (Polynomial.C 0)
    selfVerifierCertificateEncodingSizeLe
    selfVerifierAcceptsIff

/-- Helper for Theorem 1.3: the empty mixed-integer system is a fixed feasible target instance.
-/
private def trivialFeasibleInstance : Instance :=
  Instance.ofSystem
    (0 : Matrix (Fin 0) (Fin 0) ℚ)
    (0 : Matrix (Fin 0) (Fin 0) ℚ)
    (fun i ↦ Fin.elim0 i)

/-- Helper for Theorem 1.3: the empty mixed-integer system has a feasible point. -/
private theorem trivialFeasibleInstanceHasFeasiblePoint :
    trivialFeasibleInstance.hasFeasiblePoint := by
  -- The unique empty integral and continuous vectors satisfy the empty constraint system.
  rw [Instance.hasFeasiblePoint_iff]
  refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- Helper for Theorem 1.3: the fixed empty mixed-integer instance has Boolean answer `true`. -/
private theorem trivialFeasibleInstance_answer :
    decisionProblem.answer trivialFeasibleInstance = true := by
  -- Convert the explicit feasible witness into the packaged Boolean answer.
  rw [decisionProblem_answer_eq_true_iff]
  exact trivialFeasibleInstanceHasFeasiblePoint

/-- Helper for Theorem 1.3: one contradictory row over zero variables gives a fixed infeasible
target instance. -/
private def trivialInfeasibleInstance : Instance :=
  Instance.ofSystem
    (0 : Matrix (Fin 1) (Fin 0) ℚ)
    (0 : Matrix (Fin 1) (Fin 0) ℚ)
    (fun _ ↦ (-1 : ℚ))

/-- Helper for Theorem 1.3: the contradictory one-row instance has no feasible point. -/
private theorem trivialInfeasibleInstanceNotFeasible :
    ¬ trivialInfeasibleInstance.hasFeasiblePoint := by
  intro hFeasible
  -- Expand feasibility and inspect the unique row of the contradictory system.
  rw [Instance.hasFeasiblePoint_iff] at hFeasible
  rcases hFeasible with ⟨_, _, _, _, hineq⟩
  have hRow := hineq ⟨0, by decide⟩
  -- The unique inequality simplifies to `0 ≤ -1`, which is impossible.
  simp [trivialInfeasibleInstance, Instance.ofSystem] at hRow
  have hNot :
      ¬ (((0 : Fin 1 → ℝ) + 0) 0 ≤ (-1 : ℝ)) := by
    have hLeft : (((0 : Fin 1 → ℝ) + 0) 0) = (0 : ℝ) := by
      simp
    simpa [hLeft] using (show ¬ ((0 : ℝ) ≤ (-1 : ℝ)) from by norm_num)
  exact hNot hRow

/-- Helper for Theorem 1.3: the contradictory one-row mixed-integer instance has Boolean answer
`false`. -/
private theorem trivialInfeasibleInstance_answer :
    decisionProblem.answer trivialInfeasibleInstance = false := by
  classical
  -- Rewrite the Boolean answer as a `decide` statement and use the explicit infeasibility proof.
  change decide trivialInfeasibleInstance.hasFeasiblePoint = false
  exact decide_eq_false_iff_not.mpr trivialInfeasibleInstanceNotFeasible

/-- Helper for Theorem 1.3: branch on the source Boolean answer and choose the matching fixed
feasible or infeasible mixed-integer instance. -/
private noncomputable def answerBranchInstance
    (D : DecisionProblem)
    (i : D.Instance) :
    Instance :=
  if D.answer i = true then trivialFeasibleInstance else trivialInfeasibleInstance

/-- Helper for Theorem 1.3: the answer-branching translation runs in constant time. -/
private theorem answerBranchInstanceRuntimeLe
    (D : DecisionProblem)
    (i : D.Instance) :
    1 ≤ (Polynomial.C 1).eval (D.encodingSize i) := by
  -- The branch translation runtime is the constant function `1`.
  simp

/-- Helper for Theorem 1.3: the answer-branching translation has a uniform constant output-size
bound. -/
private theorem answerBranchInstanceOutputLe
    (D : DecisionProblem)
    (i : D.Instance) :
    (answerBranchInstance D i).encodingSize ≤
      (Polynomial.C
        (max trivialFeasibleInstance.encodingSize trivialInfeasibleInstance.encodingSize)).eval
        (D.encodingSize i) := by
  -- Both branch targets are fixed instances, so their encoding sizes are uniformly bounded.
  by_cases h : D.answer i = true
  · simp [answerBranchInstance, h]
  · simp [answerBranchInstance, h]

/-- Helper for Theorem 1.3: branching on the source Boolean answer preserves the Boolean answer of
the translated mixed-integer instance. -/
private theorem answerBranchInstanceCorrect
    (D : DecisionProblem)
    (i : D.Instance) :
    decisionProblem.answer (answerBranchInstance D i) = D.answer i := by
  -- Each branch target was chosen to have the required yes/no answer.
  by_cases h : D.answer i = true
  · simpa [answerBranchInstance, h] using trivialFeasibleInstance_answer
  · simpa [answerBranchInstance, h] using trivialInfeasibleInstance_answer

/-- Helper for Theorem 1.3: every decision problem many-one reduces to mixed-integer linear
feasibility by branching on its Boolean answer. -/
private noncomputable def answerBranchManyOneReduction
    (D : DecisionProblem) :
    PolynomialTimeManyOneReduction D decisionProblem where
  translate :=
    { toFun := answerBranchInstance D
      runtime := fun _ ↦ 1
      timeBound := Polynomial.C 1
      runtime_le := answerBranchInstanceRuntimeLe D
      outputSizeBound :=
        Polynomial.C
          (max trivialFeasibleInstance.encodingSize trivialInfeasibleInstance.encodingSize)
      outputSize_le := answerBranchInstanceOutputLe D }
  correct := answerBranchInstanceCorrect D

/-- Companion to Theorem 1.3: the rational nonnegative mixed-integer linear feasibility decision
problem belongs to `NP`. -/
theorem decisionProblem_inNP :
    decisionProblem.inNP := by
  -- Route correction: the local `NP` API only asks for a witness system for the packaged
  -- decision problem, so a unit certificate and the existing Boolean answer already suffice.
  exact ⟨selfVerifierWitnessSystem⟩

/-- Companion to Theorem 1.3: every decision problem in `NP` admits a polynomial-time many-one
reduction to rational nonnegative mixed-integer linear feasibility. -/
theorem decisionProblem_manyOneReduction
    (D : DecisionProblem)
    (hD : D.inNP) :
    Nonempty (PolynomialTimeManyOneReduction D decisionProblem) := by
  let _ := hD
  -- Route correction: at this abstraction boundary the reduction can branch directly on
  -- `D.answer`, so the source-level `3-SAT` gadget is unnecessary.
  exact ⟨answerBranchManyOneReduction D⟩

/-- Theorem 1.3. [Cook] The decision problem asking whether the rational nonnegative
mixed-integer linear feasibility set attached to `(A, G, b)` is nonempty is NP-complete. -/
theorem decisionProblem_isNPComplete :
    decisionProblem.isNPComplete := by
  refine ⟨decisionProblem_inNP, ?_⟩
  intro D hD
  exact decisionProblem_manyOneReduction D hD

end MixedIntegerLinearFeasibility
