/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.RefinedEndpoint.Data

@[expose] public section

set_option maxRecDepth 8192

namespace ADMM.RefinedEndpoint.Data

/-- The normalization checked by the rational verifier, now checked by the kernel. -/
theorem weights_normalized : omega + (lagWeights.map LagWeight.coefficient).sum = 1 := by
  decide +kernel

/-- Signed lag moment in one block. The paper's first moment is its negative. -/
def signedMoment (b : ADMM.FiniteMemory.Block) : ℚ :=
  ((lagWeights.filter (fun e ↦ decide (e.block = b))).map
    (fun e ↦ (e.lag : ℚ) * e.coefficient)).sum

/-- Equality of the two signed moments is exactly the manuscript's balanced-moment test. -/
theorem balanced_signed_moments : signedMoment .F = signedMoment .J := by
  decide +kernel

theorem omega_pos : 0 < omega := by decide +kernel

theorem epsilon_pos : 0 < epsilon := by decide +kernel

theorem kappa_pos : 0 < kappa := by decide +kernel

/-- Extract the actual rational inequality from the finite Boolean sign certificate. -/
theorem coefficient_nonnegative (e : LagWeight) (he : e ∈ lagWeights) :
    0 ≤ e.coefficient := by
  exact of_decide_eq_true ((List.all_eq_true.mp lagWeights_nonnegative) e he)

/-- The Nyquist mode contributes a real coordinate, as required by the Fourier realization. -/
theorem fourierFactors_nyquist_real :
    fourierFactors.all (fun e ↦ decide
      (e.mode = period / 2 → e.etaIm = 0 ∧ e.wIm = 0)) = true := by
  decide +kernel

end ADMM.RefinedEndpoint.Data
