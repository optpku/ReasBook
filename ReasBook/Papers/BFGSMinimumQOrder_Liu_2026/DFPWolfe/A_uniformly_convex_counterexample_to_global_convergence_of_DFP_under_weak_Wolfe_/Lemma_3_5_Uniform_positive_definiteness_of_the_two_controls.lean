/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_5_Uniform_positive_definiteness_of_the_two_controls.lean
-/

module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_3_4_Two_phase_controls_Controls

/- Lemma 3.5 (Uniform positive-definiteness of the two controls) (1) -/
#check (TwoPhaseControls.matrix_posDef :
  ∀ (ε ε₀ : ℝ) (i : Fin 2), 0 < ε → ε ≤ ε₀ → ε₀ < 1 / 4 →
    Matrix.PosDef (TwoPhaseControls.phase ε i).matrix)

/- Lemma 3.5 (Uniform positive-definiteness of the two controls) (2) -/
#check (TwoPhaseControls.spectrum_mem :
  ∀ (ε ε₀ : ℝ) (i j : Fin 2), 0 < ε → ε ≤ ε₀ → ε₀ < 1 / 4 →
    (TwoPhaseControls.matrix_isHermitian ε i).eigenvalues j ∈ Set.Icc (1 / 2) (3 / 2))
