/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_8_Finite_Taylor_jets_and_coefficient_extraction_UniformRemainder.lean
-/

module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder

/- Infrastructure I.8 (Finite Taylor jets and coefficient extraction):
finite Taylor jets have compact-parameter uniform remainder estimates for
families jointly smooth or analytic near every point of the compact parameter
fiber. -/
#check FiniteTaylorJet.uniformRemainderOn_of_contDiffAt
#check FiniteTaylorJet.uniformRemainderOn_of_analyticAt
