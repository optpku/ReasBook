/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_3_4_Two_phase_controls_Controls.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls

public section

open scoped Matrix

/- The legacy control module remains a typed compatibility surface. -/
#check (PlanarDFPControl : Type)
#check (TwoPhaseControls.radius : ℝ → ℝ)
#check (TwoPhaseControls.radius_def : ∀ ε : ℝ, TwoPhaseControls.radius ε = ε ^ 2)
#check (TwoPhaseControls.first : ℝ → PlanarDFPControl)
#check (TwoPhaseControls.first_matrix : ∀ ε : ℝ,
  (TwoPhaseControls.first ε).matrix = !![1, ε; ε, 1])
#check (TwoPhaseControls.first_tau : ∀ ε : ℝ,
  (TwoPhaseControls.first ε).tau = 2 / 3)
#check (TwoPhaseControls.second : ℝ → PlanarDFPControl)
#check (TwoPhaseControls.second_matrix : ∀ ε : ℝ,
  (TwoPhaseControls.second ε).matrix = !![1, -2 * ε; -2 * ε, 1])
#check (TwoPhaseControls.second_tau : ∀ ε : ℝ,
  (TwoPhaseControls.second ε).tau = 1 / 3)
#check (TwoPhaseControls.phase : ℝ → Fin 2 → PlanarDFPControl)
#check (TwoPhaseControls.phase_zero : ∀ ε : ℝ,
  TwoPhaseControls.phase ε 0 = TwoPhaseControls.first ε)
#check (TwoPhaseControls.phase_one : ∀ ε : ℝ,
  TwoPhaseControls.phase ε 1 = TwoPhaseControls.second ε)
#check (TwoPhaseControls.matrix_isHermitian : ∀ (ε : ℝ) (i : Fin 2),
  ((TwoPhaseControls.phase ε i).matrix).IsHermitian)
#check (TwoPhaseControls.matrix_posDef : ∀ (ε ε₀ : ℝ) (i : Fin 2),
  0 < ε → ε ≤ ε₀ → ε₀ < 1 / 4 → Matrix.PosDef (TwoPhaseControls.phase ε i).matrix)
#check (TwoPhaseControls.tau_pos : ∀ (ε : ℝ) (i : Fin 2),
  0 < (TwoPhaseControls.phase ε i).tau)
#check (TwoPhaseControls.spectrum_mem : ∀ (ε ε₀ : ℝ) (i j : Fin 2),
  0 < ε → ε ≤ ε₀ → ε₀ < 1 / 4 →
    (TwoPhaseControls.matrix_isHermitian ε i).eigenvalues j ∈ Set.Icc (1 / 2) (3 / 2))
