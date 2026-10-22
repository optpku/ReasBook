/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_8b_Coefficient_comparison_and_vanishing_derivative_extraction.lean
-/

module

public import ReasLib.Analysis.Calculus.ContDiff.Taylor
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.CoefficientComparison

/- Infrastructure I.8b (Coefficient comparison and vanishing-derivative extraction) (1) -/
#check FiniteTaylorJet.scalarCoeff_eq_of_eval_sub_isLittleO

/- Infrastructure I.8b (Coefficient comparison and vanishing-derivative extraction) (2) -/
#check ContDiffAt.taylor_isLittleO_of_iteratedDeriv_eq_zero
