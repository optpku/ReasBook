module

public import Mathlib.Computability.TuringMachine.Computable
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_18.PolynomialTime
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.Problem

@[expose] public section

open Computability Turing

/-- Relative to a chosen finite encoding of `D.Instance`, a polynomial-time decider for `D`
consists of a TM2 machine computing `D.answer` in polynomial time together with a proof that the
chosen encoding has the declared input length `D.encodingSize`. -/
structure PolynomialTimeDecider
    (D : DecisionProblem)
    (instanceEncoding : FinEncoding D.Instance) where
  inputLength_eq : ∀ i : D.Instance, (instanceEncoding.encode i).length = D.encodingSize i
  machine : TM2ComputableInPolyTime instanceEncoding.encode encodeBool D.answer

namespace PolynomialTimeDecider

variable {D : DecisionProblem} {instanceEncoding : FinEncoding D.Instance}

/-- Build a polynomial-time decider from an explicit finite input encoding compatible with
`D.encodingSize` and a TM2 machine computing `D.answer` in polynomial time for that encoding. -/
def ofTM2
    (inputLength_eq :
      ∀ i : D.Instance, (instanceEncoding.encode i).length = D.encodingSize i)
    (machine : TM2ComputableInPolyTime instanceEncoding.encode encodeBool D.answer) :
    PolynomialTimeDecider D instanceEncoding where
  inputLength_eq := inputLength_eq
  machine := machine

/-- A polynomial-time decider computes the correct Boolean answer of `D` on every encoded input.
-/
def outputsAnswer
    (A : PolynomialTimeDecider D instanceEncoding)
    (i : D.Instance) :
    TM2Outputs
      A.machine.tm
      (List.map A.machine.inputAlphabet.invFun (instanceEncoding.encode i))
      (some (List.map A.machine.outputAlphabet.invFun (encodeBool (D.answer i)))) :=
  TM2OutputsInTime.toTM2Outputs (A.machine.outputsFun i)

/-- The polynomial runtime of a decider can be re-expressed using the declared encoding-size
function of the underlying decision problem. -/
def outputsAnswerWithinBound
    (A : PolynomialTimeDecider D instanceEncoding)
    (i : D.Instance) :
    TM2OutputsInTime
      A.machine.tm
      (List.map A.machine.inputAlphabet.invFun (instanceEncoding.encode i))
      (some (List.map A.machine.outputAlphabet.invFun (encodeBool (D.answer i))))
      (A.machine.time.eval (D.encodingSize i)) := by
  simpa [A.inputLength_eq i] using A.machine.outputsFun i

/-- Forget a polynomial-time decider to the induced polynomial-time Boolean map on instances. -/
noncomputable def toPolynomialTimeMap
    (A : PolynomialTimeDecider D instanceEncoding) :
    PolynomialTimeMap D.Instance Bool D.encodingSize (fun _ ↦ (1 : ℕ)) where
  toFun := D.answer
  runtime := fun i ↦ A.machine.time.eval (D.encodingSize i)
  timeBound := A.machine.time
  runtime_le := fun _ ↦ le_rfl
  outputSizeBound := Polynomial.C 1
  outputSize_le := fun _ ↦ by simp

/-- The polynomial-time map induced by a decider computes the Boolean answer of the underlying
decision problem. -/
theorem toPolynomialTimeMap_apply
    (A : PolynomialTimeDecider D instanceEncoding)
    (i : D.Instance) :
    A.toPolynomialTimeMap.toFun i = D.answer i :=
  rfl

/-- A polynomial-time decider carries a TM2 realizer for its induced polynomial-time map. -/
theorem toPolynomialTimeMap_hasTM2Realizer
    (A : PolynomialTimeDecider D instanceEncoding) :
    Nonempty
      (TM2ComputableInPolyTime
        instanceEncoding.encode
        encodeBool
        A.toPolynomialTimeMap.toFun) := by
  exact ⟨by simpa [toPolynomialTimeMap] using A.machine⟩

end PolynomialTimeDecider

namespace DecisionProblem

/-- A decision problem lies in `P` when, for the chosen finite encoding of its instances, there is
a deterministic TM2 machine deciding `D.answer` in time polynomial in `D.encodingSize`. -/
def inP (D : DecisionProblem) (instanceEncoding : FinEncoding D.Instance) : Prop :=
  Nonempty (PolynomialTimeDecider D instanceEncoding)

/-- Expanding `D.inP` recalls the canonical polynomial-time decider owner. -/
theorem inP_iff
    (D : DecisionProblem)
    (instanceEncoding : FinEncoding D.Instance) :
    D.inP instanceEncoding ↔ Nonempty (PolynomialTimeDecider D instanceEncoding) :=
  Iff.rfl

/-- A decision problem lies in `P` exactly when the chosen finite input encoding has length
`D.encodingSize` and `D.answer` is computed by a TM2 machine in polynomial time for that
encoding. -/
theorem inP_iff_exists_tm2Decider
    (D : DecisionProblem)
    (instanceEncoding : FinEncoding D.Instance) :
    D.inP instanceEncoding ↔
      (∀ i : D.Instance, (instanceEncoding.encode i).length = D.encodingSize i) ∧
        Nonempty (TM2ComputableInPolyTime instanceEncoding.encode encodeBool D.answer) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.inputLength_eq, ⟨A.machine⟩⟩
  · rintro ⟨inputLength_eq, ⟨machine⟩⟩
    exact ⟨PolynomialTimeDecider.ofTM2 inputLength_eq machine⟩

/-- A decision problem lies in `P` exactly when the chosen encoding has length `D.encodingSize`
and `D.answer` is realized by a polynomial-time Boolean map together with a TM2 machine computing
that map on the chosen encoding. -/
theorem inP_iff_exists_polynomialTimeMap
    (D : DecisionProblem)
    (instanceEncoding : FinEncoding D.Instance) :
    D.inP instanceEncoding ↔
      (∀ i : D.Instance, (instanceEncoding.encode i).length = D.encodingSize i) ∧
        ∃ f : PolynomialTimeMap D.Instance Bool D.encodingSize (fun _ ↦ (1 : ℕ)),
          (∀ i : D.Instance, f.toFun i = D.answer i) ∧
            Nonempty
              (TM2ComputableInPolyTime instanceEncoding.encode encodeBool f.toFun) := by
  constructor
  · rintro ⟨A⟩
    exact
      ⟨A.inputLength_eq, A.toPolynomialTimeMap, A.toPolynomialTimeMap_apply,
        A.toPolynomialTimeMap_hasTM2Realizer⟩
  · rintro ⟨inputLength_eq, f, hf, ⟨machine⟩⟩
    have hfun : f.toFun = D.answer := funext hf
    exact ⟨PolynomialTimeDecider.ofTM2 inputLength_eq (by simpa [hfun] using machine)⟩

end DecisionProblem
