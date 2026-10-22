/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_8_Finite_Taylor_jets_and_coefficient_extraction.lean
-/

module

public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_8_Finite_Taylor_jets_and_coefficient_extraction_TaylorJet
public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_8_Finite_Taylor_jets_and_coefficient_extraction_UniformRemainder

/- Infrastructure I.8 (Finite Taylor jets and coefficient extraction) (1):
finite Taylor coefficients are bundled as continuous multilinear maps and can
be constructed from factorial-normalized iterated Fréchet derivatives. -/
#check FiniteTaylorJet
#check FiniteTaylorJet.ofFunction

/- Infrastructure I.8 (Finite Taylor jets and coefficient extraction) (2):
finite jets expose coefficient extraction, polynomial evaluation, zero extension
to a formal multilinear series, and an explicit remainder. -/
#check FiniteTaylorJet.scalarCoeff
#check FiniteTaylorJet.eval
#check FiniteTaylorJet.toFormalMultilinearSeries
#check FiniteTaylorJet.remainder

/- Infrastructure I.8 (Finite Taylor jets and coefficient extraction) (3):
families jointly `C^m` near every point of a fixed compact parameter fiber
have order-`m` Peano remainder estimates uniform on that fiber. -/
#check FiniteTaylorJet.uniformRemainderOn_of_contDiffAt

/- Infrastructure I.8 (Finite Taylor jets and coefficient extraction) (4):
families jointly analytic near every point of a fixed compact parameter fiber
have the compact-uniform finite-jet estimate at every finite order. -/
#check FiniteTaylorJet.uniformRemainderOn_of_analyticAt

/- Infrastructure I.8 (Finite Taylor jets and coefficient extraction) (5):
multivariable uniform jet remainders restrict along bounded directions to the
existing scalar-path uniform remainder predicate. -/
#check FiniteTaylorJet.IsUniformRemainderOn.along
