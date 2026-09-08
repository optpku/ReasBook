module

public import ReasLib.Optimization.DFP.SpectralRecovery

public section

#check (CycleBoundaryState.recoveryRadius : ℝ → ℝ → ℝ → ℝ → ℝ)

#check (CycleBoundaryState.recoveryShape : ℝ → ℝ → ℝ → ℝ → ℝ)

#check (CycleBoundaryState.ofSpectral :
  (e : EuclideanSpace ℝ (Fin 2)) →
  (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) →
  ‖e‖ = 1 →
  0 < lambdaMinus →
  lambdaMinus < lambdaPlus →
  0 < gammaMinus →
  0 < gammaPlus →
  CycleBoundaryState)

#check (CycleBoundaryState.ofSpectral_spec :
  ∀ (e : EuclideanSpace ℝ (Fin 2))
      (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) (e_norm : ‖e‖ = 1)
      (lambdaMinus_pos : 0 < lambdaMinus) (lambda_order : lambdaMinus < lambdaPlus)
      (gammaMinus_pos : 0 < gammaMinus) (gammaPlus_pos : 0 < gammaPlus),
    let s := CycleBoundaryState.ofSpectral e lambdaMinus lambdaPlus gammaMinus gammaPlus e_norm
      lambdaMinus_pos lambda_order gammaMinus_pos gammaPlus_pos
    0 < s.amplitude ∧ 0 < s.h ∧ 0 < s.r ∧ 0 < s.p ∧
      s.amplitude = gammaMinus ∧ s.h = lambdaPlus ∧
      s.r = CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus ∧
      s.p = CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus ∧
      s.metric = s.frame * Matrix.diagonal ![lambdaMinus, lambdaPlus] * s.frame.transpose ∧
      s.gradient =
        (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
            !₂[gammaMinus, gammaPlus])
