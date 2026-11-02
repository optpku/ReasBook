module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_24.AnswerReduction

@[expose] public section

namespace PolynomialTimeAnswerReduction

/-- Helper for composing answer reductions: the second-stage recovery returns the correct answer
for the intermediate `E`-instance. -/
theorem transIntermediateRecoverCorrect
    {D E : DecisionProblem}
    {Q : ComputationalProblem}
    (first : PolynomialTimeAnswerReduction D E.toProblem)
    (second : PolynomialTimeAnswerReduction E Q)
    (i : D.Instance)
    (s : Q.Solution ((PolynomialTimeMap.comp second.translate first.translate).toFun i)) :
    second.recover.toFun ⟨first.translate.toFun i, s⟩ = E.answer (first.translate.toFun i) := by
  simpa using second.recoverCorrect (first.translate.toFun i) s

/-- Helper for composing answer reductions: a solution of the composed `Q`-instance induces a
solution of the intermediate decision problem `E`. -/
def transIntermediateSolution
    {D E : DecisionProblem}
    {Q : ComputationalProblem}
    (first : PolynomialTimeAnswerReduction D E.toProblem)
    (second : PolynomialTimeAnswerReduction E Q)
    (i : D.Instance)
    (s : Q.Solution ((PolynomialTimeMap.comp second.translate first.translate).toFun i)) :
    E.toProblem.Solution (first.translate.toFun i) :=
  ⟨second.recover.toFun ⟨first.translate.toFun i, s⟩,
    transIntermediateRecoverCorrect first second i s⟩

/-- Helper for composing answer reductions: evaluation of a natural-coefficient polynomial is
monotone on `ℕ`. -/
private lemma polynomialEvalNatMono (p : Polynomial ℕ) :
    Monotone p.eval := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro q r hq hr x y hxy
    simpa [Polynomial.eval_add] using add_le_add (hq hxy) (hr hxy)
  · intro n a x y hxy
    simpa [Polynomial.eval_monomial, Nat.mul_comm] using
      mul_le_mul_left (pow_le_pow_left' hxy n) a

/-- Helper for composing answer reductions: the composed recovery runtime is bounded by the
advertised polynomial. -/
theorem transRecoverRuntimeLe
    {D E : DecisionProblem}
    {Q : ComputationalProblem}
    (first : PolynomialTimeAnswerReduction D E.toProblem)
    (second : PolynomialTimeAnswerReduction E Q) :
    ∀ x : Sigma fun i : D.Instance ↦
        Q.Solution ((PolynomialTimeMap.comp second.translate first.translate).toFun i),
      second.recover.runtime ⟨first.translate.toFun x.1, x.2⟩ +
          first.recover.runtime ⟨x.1, transIntermediateSolution first second x.1 x.2⟩ ≤
        ((second.recover.timeBound.comp (first.translate.outputSizeBound + Polynomial.X)) +
          first.recover.timeBound.comp (Polynomial.X + Polynomial.C 1)).eval
          (D.encodingSize x.1 +
            Q.solutionEncodingSize
              ((PolynomialTimeMap.comp second.translate first.translate).toFun x.1) x.2) := by
  intro x
  -- Record the composed input size once so the two monotonicity arguments share the same target.
  let n :=
    D.encodingSize x.1 +
      Q.solutionEncodingSize
        ((PolynomialTimeMap.comp second.translate first.translate).toFun x.1) x.2
  have hSourceLe : D.encodingSize x.1 ≤ n := by
    -- The original instance size is one summand of the composed input size.
    dsimp [n]
    exact Nat.le_add_right _ _
  have hSolutionLe :
      Q.solutionEncodingSize
          ((PolynomialTimeMap.comp second.translate first.translate).toFun x.1) x.2 ≤ n := by
    -- The solution size is the other summand of the composed input size.
    dsimp [n]
    exact Nat.le_add_left _ _
  have hTranslateOutput :
      E.encodingSize (first.translate.toFun x.1) ≤
        first.translate.outputSizeBound.eval (D.encodingSize x.1) := by
    -- The first translation already controls the encoding size of the intermediate instance.
    simpa using first.translate.outputSize_le x.1
  have hTranslateOutput' :
      E.encodingSize (first.translate.toFun x.1) ≤ first.translate.outputSizeBound.eval n := by
    -- Monotonicity lets us enlarge the first-stage output bound to the composed input size.
    exact le_trans hTranslateOutput
      (polynomialEvalNatMono first.translate.outputSizeBound hSourceLe)
  have hSecondInputLeRaw :
      E.encodingSize (first.translate.toFun x.1) +
          Q.solutionEncodingSize
            ((PolynomialTimeMap.comp second.translate first.translate).toFun x.1) x.2 ≤
        first.translate.outputSizeBound.eval n + n := by
    -- The second recovery sees the intermediate instance plus the final solution.
    exact add_le_add hTranslateOutput' hSolutionLe
  have hSecondInputLe :
      E.encodingSize (first.translate.toFun x.1) +
          Q.solutionEncodingSize
            ((PolynomialTimeMap.comp second.translate first.translate).toFun x.1) x.2 ≤
        (first.translate.outputSizeBound + Polynomial.X).eval n := by
    -- Normalize the arithmetic bound to the advertised polynomial expression.
    simpa [Polynomial.eval_add] using hSecondInputLeRaw
  have hSecondRuntime :
      second.recover.runtime ⟨first.translate.toFun x.1, x.2⟩ ≤
        (second.recover.timeBound.comp
          (first.translate.outputSizeBound + Polynomial.X)).eval n := by
    -- First bound the second recovery at its native input size, then enlarge that input.
    calc
      second.recover.runtime ⟨first.translate.toFun x.1, x.2⟩ ≤
          second.recover.timeBound.eval
            (E.encodingSize (first.translate.toFun x.1) +
              Q.solutionEncodingSize
                ((PolynomialTimeMap.comp second.translate first.translate).toFun x.1) x.2) := by
        simpa [PolynomialTimeMap.comp_apply] using
          second.recover.runtime_le ⟨first.translate.toFun x.1, x.2⟩
      _ ≤ second.recover.timeBound.eval
            ((first.translate.outputSizeBound + Polynomial.X).eval n) := by
        exact polynomialEvalNatMono second.recover.timeBound hSecondInputLe
      _ = (second.recover.timeBound.comp
            (first.translate.outputSizeBound + Polynomial.X)).eval n := by
        rw [Polynomial.eval_comp]
  have hFirstInputLeRaw :
      D.encodingSize x.1 +
          E.toProblem.solutionEncodingSize
            (first.translate.toFun x.1) (transIntermediateSolution first second x.1 x.2) ≤
        n + 1 := by
    -- Solving the intermediate decision problem contributes constant Boolean encoding size `1`.
    calc
      D.encodingSize x.1 +
          E.toProblem.solutionEncodingSize
            (first.translate.toFun x.1) (transIntermediateSolution first second x.1 x.2) =
          D.encodingSize x.1 + 1 := by
        simp [DecisionProblem.toProblem]
      _ ≤ n + 1 := by
        exact Nat.add_le_add_right hSourceLe 1
  have hFirstInputLe :
      D.encodingSize x.1 +
          E.toProblem.solutionEncodingSize
            (first.translate.toFun x.1) (transIntermediateSolution first second x.1 x.2) ≤
        (Polynomial.X + Polynomial.C 1).eval n := by
    -- Normalize the constant-size bound to the input polynomial used by the first recovery.
    simpa [Polynomial.eval_add] using hFirstInputLeRaw
  have hFirstRuntime :
      first.recover.runtime ⟨x.1, transIntermediateSolution first second x.1 x.2⟩ ≤
        (first.recover.timeBound.comp (Polynomial.X + Polynomial.C 1)).eval n := by
    -- The first recovery only needs the original instance together with a Boolean witness.
    calc
      first.recover.runtime ⟨x.1, transIntermediateSolution first second x.1 x.2⟩ ≤
          first.recover.timeBound.eval
            (D.encodingSize x.1 +
              E.toProblem.solutionEncodingSize
                (first.translate.toFun x.1) (transIntermediateSolution first second x.1 x.2)) := by
        exact first.recover.runtime_le ⟨x.1, transIntermediateSolution first second x.1 x.2⟩
      _ ≤ first.recover.timeBound.eval ((Polynomial.X + Polynomial.C 1).eval n) := by
        exact polynomialEvalNatMono first.recover.timeBound hFirstInputLe
      _ = (first.recover.timeBound.comp (Polynomial.X + Polynomial.C 1)).eval n := by
        rw [Polynomial.eval_comp]
  -- Add the two component runtime bounds and normalize the sum of polynomials.
  calc
    second.recover.runtime ⟨first.translate.toFun x.1, x.2⟩ +
        first.recover.runtime ⟨x.1, transIntermediateSolution first second x.1 x.2⟩ ≤
      (second.recover.timeBound.comp (first.translate.outputSizeBound + Polynomial.X)).eval n +
        (first.recover.timeBound.comp (Polynomial.X + Polynomial.C 1)).eval n := by
      exact add_le_add hSecondRuntime hFirstRuntime
    _ =
        ((second.recover.timeBound.comp (first.translate.outputSizeBound + Polynomial.X)) +
          first.recover.timeBound.comp (Polynomial.X + Polynomial.C 1)).eval n := by
      rw [Polynomial.eval_add]
    _ =
        ((second.recover.timeBound.comp (first.translate.outputSizeBound + Polynomial.X)) +
          first.recover.timeBound.comp (Polynomial.X + Polynomial.C 1)).eval
          (D.encodingSize x.1 +
            Q.solutionEncodingSize
              ((PolynomialTimeMap.comp second.translate first.translate).toFun x.1) x.2) := by
      rfl

/-- Helper for composing answer reductions: the composed recovery output has constant Boolean
encoding size. -/
theorem transRecoverOutputSizeLe
    {D E : DecisionProblem}
    {Q : ComputationalProblem}
    (first : PolynomialTimeAnswerReduction D E.toProblem)
    (second : PolynomialTimeAnswerReduction E Q) :
    ∀ x : Sigma fun i : D.Instance ↦
        Q.Solution ((PolynomialTimeMap.comp second.translate first.translate).toFun i),
      (1 : ℕ) ≤
        (Polynomial.C 1).eval
          (D.encodingSize x.1 +
            Q.solutionEncodingSize
              ((PolynomialTimeMap.comp second.translate first.translate).toFun x.1) x.2) := by
  intro x
  simp

/-- Helper for composing answer reductions: the composed recovery still returns the correct answer
for the original instance. -/
theorem transRecoverCorrect
    {D E : DecisionProblem}
    {Q : ComputationalProblem}
    (first : PolynomialTimeAnswerReduction D E.toProblem)
    (second : PolynomialTimeAnswerReduction E Q)
    (i : D.Instance)
    (s : Q.Solution ((PolynomialTimeMap.comp second.translate first.translate).toFun i)) :
    first.recover.toFun ⟨i, transIntermediateSolution first second i s⟩ = D.answer i := by
  exact first.recoverCorrect i (transIntermediateSolution first second i s)

/-- Compose a reduction to `E.toProblem` with a reduction from `E` to `Q`. -/
noncomputable def trans
    {D E : DecisionProblem}
    {Q : ComputationalProblem}
    (first : PolynomialTimeAnswerReduction D E.toProblem)
    (second : PolynomialTimeAnswerReduction E Q) :
    PolynomialTimeAnswerReduction D Q :=
  let translate := PolynomialTimeMap.comp second.translate first.translate
  { translate := translate
    recover :=
      { toFun := fun x : Sigma fun i : D.Instance ↦ Q.Solution (translate.toFun i) ↦
          first.recover.toFun ⟨x.1, transIntermediateSolution first second x.1 x.2⟩
        runtime := fun x : Sigma fun i : D.Instance ↦ Q.Solution (translate.toFun i) ↦
          second.recover.runtime ⟨first.translate.toFun x.1, x.2⟩ +
            first.recover.runtime ⟨x.1, transIntermediateSolution first second x.1 x.2⟩
        timeBound :=
          (second.recover.timeBound.comp (first.translate.outputSizeBound + Polynomial.X)) +
            first.recover.timeBound.comp (Polynomial.X + Polynomial.C 1)
        runtime_le := transRecoverRuntimeLe first second
        outputSizeBound := Polynomial.C 1
        outputSize_le := transRecoverOutputSizeLe first second }
    recoverCorrect := transRecoverCorrect first second }

/-- The translation map of `trans first second` is the composition of the two translation maps. -/
theorem trans_translate_apply
    {D E : DecisionProblem}
    {Q : ComputationalProblem}
    (first : PolynomialTimeAnswerReduction D E.toProblem)
    (second : PolynomialTimeAnswerReduction E Q)
    (i : D.Instance) :
    (PolynomialTimeAnswerReduction.trans first second).translate.toFun i =
      second.translate.toFun (first.translate.toFun i) := by
  simpa [PolynomialTimeAnswerReduction.trans] using
    PolynomialTimeMap.comp_apply second.translate first.translate i

end PolynomialTimeAnswerReduction

/-- A polynomial-time many-one reduction from `D` to `Q` translates instances of `D` to instances
of `Q` in polynomial time and preserves the Boolean answer on each instance. -/
structure PolynomialTimeManyOneReduction
    (D Q : DecisionProblem) where
  translate : PolynomialTimeMap D.Instance Q.Instance D.encodingSize Q.encodingSize
  correct : ∀ i : D.Instance, Q.answer (translate.toFun i) = D.answer i

namespace PolynomialTimeManyOneReduction

variable {D E Q : DecisionProblem}

/-- A many-one reduction preserves the yes-instances of the source and target decision problems.
-/
theorem answer_eq_true_iff
    (f : PolynomialTimeManyOneReduction D Q)
    (i : D.Instance) :
    D.answer i = true ↔ Q.answer (f.translate.toFun i) = true := by
  -- The reduction correctness identifies the source answer with the translated answer.
  rw [← f.correct i]

/-- Helper for Definition 1.24: the correctness field for the composition of many-one reductions.
-/
theorem compCorrect
    (f : PolynomialTimeManyOneReduction E Q)
    (g : PolynomialTimeManyOneReduction D E) :
    ∀ i : D.Instance,
      Q.answer ((PolynomialTimeMap.comp f.translate g.translate).toFun i) = D.answer i := by
  intro i
  -- Compose the two correctness statements along the translated intermediate instance.
  calc
    Q.answer ((PolynomialTimeMap.comp f.translate g.translate).toFun i) =
        E.answer (g.translate.toFun i) := by
      simpa [PolynomialTimeMap.comp_apply] using f.correct (g.translate.toFun i)
    _ = D.answer i := by
      exact g.correct i

/-- Compose two polynomial-time many-one reductions by composing their translation maps. -/
noncomputable def comp
    (f : PolynomialTimeManyOneReduction E Q)
    (g : PolynomialTimeManyOneReduction D E) :
    PolynomialTimeManyOneReduction D Q where
  translate := PolynomialTimeMap.comp f.translate g.translate
  correct := compCorrect f g

/-- The translation map of `comp f g` is the composition of the underlying translation maps. -/
theorem comp_apply
    (f : PolynomialTimeManyOneReduction E Q)
    (g : PolynomialTimeManyOneReduction D E)
    (i : D.Instance) :
    (comp f g).translate.toFun i = f.translate.toFun (g.translate.toFun i) := by
  -- The composed reduction reuses the composed translation map verbatim.
  simpa [comp] using PolynomialTimeMap.comp_apply f.translate g.translate i

/-- Helper for Definition 1.24: the induced answer-reduction recovery has constant unit runtime
and output-size bounds. -/
theorem toAnswerReductionRecoverBound
    (f : PolynomialTimeManyOneReduction D Q) :
    ∀ x : Sigma fun i : D.Instance ↦ Q.toProblem.Solution (f.translate.toFun i),
      (1 : ℕ) ≤
        (Polynomial.C 1).eval
          (D.encodingSize x.1 + Q.toProblem.solutionEncodingSize (f.translate.toFun x.1) x.2) := by
  intro x
  -- The associated decision problem encodes every Boolean witness with constant size `1`.
  simp [DecisionProblem.toProblem]

/-- Helper for Definition 1.24: recovering from a translated `Q.toProblem` solution returns the
original Boolean answer. -/
theorem toAnswerReductionRecoverCorrect
    (f : PolynomialTimeManyOneReduction D Q)
    (i : D.Instance)
    (s : Q.toProblem.Solution (f.translate.toFun i)) :
    s.1 = D.answer i := by
  -- Unpack the canonical Boolean witness for `Q.toProblem` and then use the reduction correctness.
  calc
    s.1 = Q.answer (f.translate.toFun i) := by
      exact DecisionProblem.toProblem_solution_value Q (f.translate.toFun i) s
    _ = D.answer i := by
      exact f.correct i

/-- Any many-one reduction to a decision problem induces an answer reduction to the associated
computational problem. -/
noncomputable def toAnswerReduction
    (f : PolynomialTimeManyOneReduction D Q) :
    PolynomialTimeAnswerReduction D Q.toProblem where
  translate := f.translate
  recover :=
    { toFun := fun x ↦ x.2.1
      runtime := fun _ ↦ 1
      timeBound := Polynomial.C 1
      runtime_le := toAnswerReductionRecoverBound f
      outputSizeBound := Polynomial.C 1
      outputSize_le := toAnswerReductionRecoverBound f }
  recoverCorrect := toAnswerReductionRecoverCorrect f

/-- The translation map of `f.toAnswerReduction` agrees with the translation map of `f`. -/
theorem toAnswerReduction_translate_apply
    (f : PolynomialTimeManyOneReduction D Q)
    (i : D.Instance) :
    f.toAnswerReduction.translate.toFun i = f.translate.toFun i := by
  -- The induced answer reduction keeps the original translation map unchanged.
  rfl

end PolynomialTimeManyOneReduction
