/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Lemma_A_4_Canonical_recovery_formulas_Recovery.lean
-/

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
