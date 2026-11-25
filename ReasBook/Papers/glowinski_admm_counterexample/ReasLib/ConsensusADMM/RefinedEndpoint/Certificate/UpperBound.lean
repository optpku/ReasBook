/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.SparseGeometry
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.ActualChecks

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open ADMM.RefinedEndpoint
open Period1024
open scoped RealInnerProductSpace

/-- A positive integer lower numerator on the shared positive denominator
certifies strict positivity of the enclosed real quantity. -/
theorem positive_of_numerator {I : IntInterval} {x : ℝ}
    (hx : (I.toRat gramDenominator).Contains x) (hI : 0 < I.lower) : 0 < x := by
  apply hx.positive
  change 0 < (I.lower : ℚ) / (gramDenominator : ℚ)
  exact div_pos (by exact_mod_cast hI) (by exact_mod_cast gramDenominator_pos)

/-- All first-block phase-zero products are strictly positive for the actual orbit. -/
theorem first_zeroPhase_supports :
    ZeroPhaseStrictSupports (imageVertex eta scaledMultiplier)
      (firstSupportNormal ADMM.RefinedEndpoint.upper eta scaledMultiplier) := by
  have hq : (0 : ℝ) < upperDenominator := by exact_mod_cast upperDenominator_pos
  constructor
  · have hp := positive_of_numerator
      (pairNumerator_contains firstNormalNumerator (firstTarget 0))
      (first_supports_positive ⟨0, by decide⟩)
    rw [firstNormal_sparseValue, firstTarget_zero, real_inner_smul_left] at hp
    exact (mul_pos_iff_of_pos_left hq).mp hp
  · intro j hj
    have hjval : 0 < j.val := by
      by_contra h
      have hz : j.val = 0 := by omega
      apply hj
      exact (ZMod.val_eq_zero j).mp hz
    have hN : j.val < 1024 := j.val_lt
    have hp := positive_of_numerator
      (pairNumerator_contains firstNormalNumerator (firstTarget j.val))
      (first_supports_positive ⟨j.val, hN⟩)
    rw [firstNormal_sparseValue, firstTarget_pos j.val hjval hN,
      real_inner_smul_left, ZMod.natCast_zmod_val] at hp
    exact (mul_pos_iff_of_pos_left hq).mp hp

/-- All second-block phase-zero products are strictly positive for the actual orbit. -/
theorem second_zeroPhase_supports :
    ZeroPhaseStrictSupports eta
      (secondSupportNormal ADMM.RefinedEndpoint.upper scaledMultiplier) := by
  have hq : (0 : ℝ) < upperDenominator := by exact_mod_cast upperDenominator_pos
  constructor
  · have hp := positive_of_numerator
      (pairNumerator_contains secondNormalNumerator (secondTarget 0))
      (second_supports_positive ⟨0, by decide⟩)
    rw [secondNormal_sparseValue, secondTarget_zero, real_inner_smul_left] at hp
    exact (mul_pos_iff_of_pos_left hq).mp hp
  · intro j hj
    have hjval : 0 < j.val := by
      by_contra h
      have hz : j.val = 0 := by omega
      apply hj
      exact (ZMod.val_eq_zero j).mp hz
    have hN : j.val < 1024 := j.val_lt
    have hp := positive_of_numerator
      (pairNumerator_contains secondNormalNumerator (secondTarget j.val))
      (second_supports_positive ⟨j.val, hN⟩)
    rw [secondNormal_sparseValue, secondTarget_pos j.val hjval hN,
      real_inner_smul_left, ZMod.natCast_zmod_val] at hp
    exact (mul_pos_iff_of_pos_left hq).mp hp

/-- The same checked integer evaluator certifies a nonzero primal residual. -/
theorem residual_norm_pos : 0 < ‖displacement scaledMultiplier 0‖ ^ 2 := by
  have hp := positive_of_numerator (pairNumerator_contains residualVector residualVector)
    residual_positive
  rw [residual_sparseValue, real_inner_self_eq_norm_sq] at hp
  exact hp

/-- Appendix C.3: the exact 1024-phase Fourier certificate proves the strict
refined upper endpoint bound without unproved certificate hypotheses. -/
theorem endpoint_lt_upper : ADMM.uniformConvergenceEndpoint < ADMM.RefinedEndpoint.upper := by
  exact endpoint_lt_upper_of_supports first_zeroPhase_supports second_zeroPhase_supports
    residual_norm_pos

end ConsensusADMM.RefinedEndpoint.Certificate
