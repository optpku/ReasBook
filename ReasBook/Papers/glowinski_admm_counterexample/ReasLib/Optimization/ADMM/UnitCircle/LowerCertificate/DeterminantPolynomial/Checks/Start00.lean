/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.TargetContext
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Checks.StartZero

@[expose] public section

set_option maxRecDepth 8192

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

set_option maxHeartbeats 5000000 in
-- Seven new source coefficients; the already verified constant is reused below.
theorem startChunk00Tail : ∀ i : Fin 7,
    startLeftCoefficient (i.val + 1) = startRightCoefficient (i.val + 1) := by
  decide +kernel

theorem startChunk00 : ∀ i : Fin 8,
    startLeftCoefficient i = startRightCoefficient i := by
  intro i
  by_cases hz : i.val = 0
  · simpa only [hz] using startCoefficientZero
  · have h := startChunk00Tail ⟨i.val - 1, by omega⟩
    simpa only [Nat.sub_add_cancel (show 1 ≤ i.val by omega)] using h

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
