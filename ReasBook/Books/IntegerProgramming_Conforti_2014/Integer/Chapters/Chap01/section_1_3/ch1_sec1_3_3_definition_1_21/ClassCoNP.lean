module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.Problem
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_18.PolynomialTime

@[expose] public section

/-- A co-NP witness system for a decision problem `D` consists of certificates, a
certificate-size function, a polynomial-time verifier, a polynomial bound on certificate sizes,
and the usual acceptance characterization of negative instances. -/
structure CoNPWitnessSystem (D : DecisionProblem) where
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
  accepts_iff_no :
    ∀ i : D.Instance,
      D.answer i = false ↔ ∃ c : Certificate i, verify.toFun ⟨i, c⟩ = true

namespace CoNPWitnessSystem

variable {D : DecisionProblem}

/-- Build a co-NP witness system from explicit certificate data, a polynomial-time verifier, a
polynomial certificate-size bound, and the usual negative-instance correctness equivalence. -/
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
    (accepts_iff_no :
      ∀ i : D.Instance,
        D.answer i = false ↔ ∃ c : Certificate i, verify.toFun ⟨i, c⟩ = true) :
    CoNPWitnessSystem D where
  Certificate := Certificate
  certificateEncodingSize := certificateEncodingSize
  verify := verify
  certificateBound := certificateBound
  certificateEncodingSize_le := certificateEncodingSize_le
  accepts_iff_no := accepts_iff_no

/-- Evaluating the verifier of a co-NP witness system characterizes the negative instances of the
underlying decision problem. -/
theorem verify_iff_no
    (A : CoNPWitnessSystem D)
    (i : D.Instance) :
    D.answer i = false ↔ ∃ c : A.Certificate i, A.verify.toFun ⟨i, c⟩ = true :=
  A.accepts_iff_no i

end CoNPWitnessSystem

namespace DecisionProblem

/-- A decision problem belongs to `co-NP` when it admits a polynomially bounded witness system
with a polynomial-time verifier for negative instances. -/
def inCoNP (D : DecisionProblem) : Prop :=
  Nonempty (CoNPWitnessSystem D)

/-- Expanding `D.inCoNP` recalls the canonical co-NP witness-system owner. -/
theorem inCoNP_iff
    (D : DecisionProblem) :
    D.inCoNP ↔ Nonempty (CoNPWitnessSystem D) :=
  Iff.rfl

end DecisionProblem
