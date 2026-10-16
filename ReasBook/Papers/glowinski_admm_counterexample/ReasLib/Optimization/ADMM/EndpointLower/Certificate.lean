module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.MatrixComparison
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.Descent.Local
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower.Lower.Local
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.IntervalCertificate

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.EndpointLower

/-- The paper's unchanged weights and affine storage satisfy every certificate
condition at the explicitly checked extension point. -/
noncomputable def certificate : Certificate 8 gamma where
  lagMinus := lagMinusNNReal caseFourValid
  lagPlus := lagPlusNNReal caseFourValid
  omega := caseFour.omega
  epsilon := caseFour.epsilon
  zeta := caseFour.zeta
  P := intervalStorage caseFour gamma
  μ := muNNReal caseFourValid
  memory_pos := caseFourValid.memory_pos
  gamma_pos := by norm_num [gamma]
  omega_pos := omega_cast_pos caseFourValid
  epsilon_pos := epsilon_cast_pos caseFourValid
  zeta_pos := zeta_cast_pos caseFourValid
  P_symm := intervalStorage_isSymm caseFourValid gamma
  μ_diag := muNNReal_diag caseFourValid
  value_balance := muNNReal_balance caseFourValid
  descent_psd := by
    rw [descent_cast]
    apply castMatrix_posSemidef_of_kernel_and_principalPivots
      descentQ_symm descentQ_kernel (threshold := 1 / 10000000) (by norm_num)
    rw [descentPrincipal_eq_candidate]
    exact Descent.candidatePositive
  lower_psd := by
    rw [lower_cast]
    apply castMatrix_posSemidef_of_positivePivots lowerQ_symm
      (threshold := 1 / 10000000) (by norm_num)
    rw [lower_eq_candidate]
    exact Lower.candidatePositive

/-- Interpolation fills the entire new interval, with all six scalar and weight
fields shared with the original upper endpoint certificate. -/
noncomputable def certificateOnExtension (t : ℝ)
    (hLower : (377 : ℝ) / 200 ≤ t) (hUpper : t ≤ gamma) : Certificate 8 t := by
  apply Certificate.interpolate (toEndpointCertificate caseFourValid .upper) certificate
  · norm_num [endpointGamma, caseFour, RationalCase.ofNumerators, gamma]
  · simpa [endpointGamma, caseFour, RationalCase.ofNumerators] using hLower
  · exact hUpper
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end ADMM.FiniteMemory.Reconstruction.EndpointLower
