/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe.lean
-/

module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Theorem_2_3_Uniformly_convex_weak_Wolfe_DFP_counterexample_in_dimension_two
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Theorem_2_4_Counterexample_in_every_dimension_n_ge2
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Theorem_Main_theorem
public import ReasLib.Optimization.DFP.GlobalConvergence
public import ReasLib.Optimization.DFP.LevelSetGlobalConvergence
public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedTransport
public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedIdentityInitialization
public import ReasLib.Optimization.DFP.WolfeCounterexample.AutomaticIdentityFactor
public import ReasLib.Optimization.DFP.WolfeCounterexample.SemanticProjections
public import ReasLib.Optimization.DFP.WolfeCounterexample.MatrixIdentityInitialization
public import ReasLib.Optimization.DFP.WolfeCounterexample.MatrixIdentityLiminfCertificate
public import ReasLib.Optimization.DFP.WolfeCounterexample.AutomaticMatrixIdentityLiminf

/-!
# DFPWolfe

The top-level module exposes the fixed and paper-range strong-Wolfe
counterexamples, their all-dimensional transport, the identity-initialization
operator and matrix interfaces, the level-set semantics, and the resulting
global-convergence negations.
-/
