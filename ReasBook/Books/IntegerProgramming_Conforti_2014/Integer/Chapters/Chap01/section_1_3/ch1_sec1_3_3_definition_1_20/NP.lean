/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.Problem
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_18.PolynomialTime

@[expose] public section

/-- An NP witness system for a decision problem `D` consists of certificates, a certificate-size
function, a polynomial-time verifier, a polynomial bound on certificate sizes, and the usual
acceptance characterization of positive instances. -/
structure NPWitnessSystem (D : DecisionProblem) where
  Certificate : D.Instance → Type
  certificateEncodingSize : (i : D.Instance) → Certificate i → ℕ
  verify :
    PolynomialTimeMap
      (Sigma Certificate)
      Bool
      (fun x ↦ D.encodingSize x.1 + certificateEncodingSize x.1 x.2)
      (fun _ ↦ (1 : ℕ))
  certificateBound : Polynomial ℕ
  certificateEncodingSize_le :
    ∀ i : D.Instance, ∀ c : Certificate i,
      certificateEncodingSize i c ≤ certificateBound.eval (D.encodingSize i)
  accepts_iff :
    ∀ i : D.Instance,
      D.answer i = true ↔ ∃ c : Certificate i, verify.toFun ⟨i, c⟩ = true

namespace NPWitnessSystem

variable {D : DecisionProblem}

/-- Build an NP witness system from explicit certificate data, a polynomial-time verifier, a
polynomial certificate-size bound, and the usual positive-instance correctness equivalence. -/
def ofVerifier
    (Certificate : D.Instance → Type)
    (certificateEncodingSize : (i : D.Instance) → Certificate i → ℕ)
    (verify :
      PolynomialTimeMap
        (Sigma Certificate)
        Bool
        (fun x ↦ D.encodingSize x.1 + certificateEncodingSize x.1 x.2)
        (fun _ ↦ (1 : ℕ)))
    (certificateBound : Polynomial ℕ)
    (certificateEncodingSize_le :
      ∀ i : D.Instance, ∀ c : Certificate i,
        certificateEncodingSize i c ≤ certificateBound.eval (D.encodingSize i))
    (accepts_iff :
      ∀ i : D.Instance,
        D.answer i = true ↔ ∃ c : Certificate i, verify.toFun ⟨i, c⟩ = true) :
    NPWitnessSystem D where
  Certificate := Certificate
  certificateEncodingSize := certificateEncodingSize
  verify := verify
  certificateBound := certificateBound
  certificateEncodingSize_le := certificateEncodingSize_le
  accepts_iff := accepts_iff

/-- Evaluating the verifier of an NP witness system characterizes the positive instances of the
underlying decision problem. -/
theorem verify_iff
    (A : NPWitnessSystem D)
    (i : D.Instance) :
    D.answer i = true ↔ ∃ c : A.Certificate i, A.verify.toFun ⟨i, c⟩ = true :=
  A.accepts_iff i

/-- The certificate-size control of an NP witness system is given by its declared polynomial
bound. -/
theorem certificateEncodingSize_le_bound
    (A : NPWitnessSystem D)
    (i : D.Instance)
    (c : A.Certificate i) :
    A.certificateEncodingSize i c ≤ A.certificateBound.eval (D.encodingSize i) :=
  A.certificateEncodingSize_le i c

/-- An NP witness system packages both the polynomial certificate-size bound and the verifier
characterization of positive instances. -/
theorem spec
    (A : NPWitnessSystem D) :
    (∀ i : D.Instance, ∀ c : A.Certificate i,
      A.certificateEncodingSize i c ≤ A.certificateBound.eval (D.encodingSize i)) ∧
      ∀ i : D.Instance,
        D.answer i = true ↔ ∃ c : A.Certificate i, A.verify.toFun ⟨i, c⟩ = true :=
  ⟨A.certificateEncodingSize_le, A.accepts_iff⟩

end NPWitnessSystem

namespace DecisionProblem

/-- A decision problem belongs to `NP` when it admits a polynomially bounded witness system with a
polynomial-time verifier. -/
def inNP (D : DecisionProblem) : Prop :=
  Nonempty (NPWitnessSystem D)

/-- Expanding `D.inNP` recalls the canonical NP witness-system owner. -/
theorem inNP_iff
    (D : DecisionProblem) :
    D.inNP ↔ Nonempty (NPWitnessSystem D) :=
  Iff.rfl

/-- A decision problem lies in `NP` exactly when there are certificates with polynomially bounded
encoding size and a polynomial-time verifier recognizing the positive instances. -/
theorem inNP_iff_exists_verifier
    (D : DecisionProblem) :
    D.inNP ↔
      ∃ Certificate : D.Instance → Type,
        ∃ certificateEncodingSize : (i : D.Instance) → Certificate i → ℕ,
          ∃ verify :
            PolynomialTimeMap
              (Sigma Certificate)
              Bool
              (fun x ↦ D.encodingSize x.1 + certificateEncodingSize x.1 x.2)
              (fun _ ↦ (1 : ℕ)),
            ∃ certificateBound : Polynomial ℕ,
              (∀ i : D.Instance, ∀ c : Certificate i,
                certificateEncodingSize i c ≤ certificateBound.eval (D.encodingSize i)) ∧
                (∀ i : D.Instance,
                  D.answer i = true ↔ ∃ c : Certificate i, verify.toFun ⟨i, c⟩ = true) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.Certificate, A.certificateEncodingSize, A.verify, A.certificateBound,
      A.certificateEncodingSize_le, A.accepts_iff⟩
  · rintro ⟨Certificate, certificateEncodingSize, verify, certificateBound,
      certificateEncodingSize_le, accepts_iff⟩
    exact
      ⟨NPWitnessSystem.ofVerifier
        Certificate
        certificateEncodingSize
        verify
        certificateBound
        certificateEncodingSize_le
        accepts_iff⟩

end DecisionProblem
