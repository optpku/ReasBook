/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_8_Finite_Taylor_jets_and_coefficient_extraction_TaylorJet.lean
-/

module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet

/- Infrastructure I.8 (Finite Taylor jets and coefficient extraction):
finite Taylor coefficients are bundled as continuous multilinear maps through
a fixed order. -/
#check FiniteTaylorJet
