module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCases

@[expose] public section

open ADMM.FiniteMemory ADMM.FiniteMemory.Reconstruction

namespace ADMM.ConvergenceProof

/-- The four adjoining exact certificates cover the entire nonclassical
parameter range, including every shared endpoint. -/
theorem parameter_has_certificate {γ : ℝ}
    (hlower : (3 : ℝ) / 2 ≤ γ) (hupper : γ ≤ (377 : ℝ) / 200) :
    ∃ ℓ, Nonempty (Certificate ℓ γ) := by
  by_cases h₁ : γ ≤ (17 : ℝ) / 10
  · refine ⟨2, ⟨toIntervalCertificate caseOneValid γ ?_ ?_⟩⟩
    · simpa [caseOne, RationalCase.ofNumerators] using hlower
    · simpa [caseOne, RationalCase.ofNumerators] using h₁
  · by_cases h₂ : γ ≤ (187 : ℝ) / 100
    · refine ⟨6, ⟨toIntervalCertificate caseTwoValid γ ?_ ?_⟩⟩
      · have h : (17 : ℝ) / 10 ≤ γ := le_of_not_ge h₁
        simpa [caseTwo, RationalCase.ofNumerators] using h
      · simpa [caseTwo, RationalCase.ofNumerators] using h₂
    · by_cases h₃ : γ ≤ (47 : ℝ) / 25
      · refine ⟨8, ⟨toIntervalCertificate caseThreeValid γ ?_ ?_⟩⟩
        · have h : (187 : ℝ) / 100 ≤ γ := le_of_not_ge h₂
          simpa [caseThree, RationalCase.ofNumerators] using h
        · simpa [caseThree, RationalCase.ofNumerators] using h₃
      · refine ⟨8, ⟨toIntervalCertificate caseFourValid γ ?_ ?_⟩⟩
        · have h : (47 : ℝ) / 25 ≤ γ := le_of_not_ge h₃
          simpa [caseFour, RationalCase.ofNumerators] using h
        · simpa [caseFour, RationalCase.ofNumerators] using hupper

end ADMM.ConvergenceProof
