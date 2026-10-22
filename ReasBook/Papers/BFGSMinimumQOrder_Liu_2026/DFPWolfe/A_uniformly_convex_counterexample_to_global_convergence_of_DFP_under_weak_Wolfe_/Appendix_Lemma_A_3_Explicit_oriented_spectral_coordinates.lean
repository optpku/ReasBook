/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Lemma_A_3_Explicit_oriented_spectral_coordinates.lean
-/

module

import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_4_Analytic_oriented_eigenframe_near_a_simple_spectrum
import Mathlib.Analysis.Normed.Module.Connected

/- Appendix Lemma A.3 (Explicit oriented spectral coordinates): the explicit ordered
eigenvalues and normalized low eigenvector, together with its positive perpendicular, give
a fixed real-analytic positively oriented diagonalizing frame near `matrix 0 0 1`. A positive
base-point pairing with an analytic field persists on a connected ball for this same branch. -/
#check RealSymmetric2.gap
#check RealSymmetric2.low
#check RealSymmetric2.high
#check RealSymmetric2.lowVector
#check RealSymmetric2.highVector
#check RealSymmetric2.norm_lowVector
#check RealSymmetric2.lowVector_eigen
#check RealSymmetric2.highVector_eigen
#check RealSymmetric2.diag_mem_lowChart
#check RealSymmetric2.analyticOnNhd_low
#check RealSymmetric2.analyticOnNhd_high
#check RealSymmetric2.analyticOnNhd_lowVector
#check RealSymmetric2.analyticOnNhd_highVector
#check RealSymmetric2.highVector_eq_perp_lowVector
#check RealSymmetric2.analyticOnNhd_frame
#check RealSymmetric2.frame_mem_specialOrthogonalGroup
#check RealSymmetric2.frame_diag
#check RealSymmetric2.frame_diagonalizes
#check RealSymmetric2.exists_ball_inner_lowVector_pos
#check Metric.isConnected_ball
