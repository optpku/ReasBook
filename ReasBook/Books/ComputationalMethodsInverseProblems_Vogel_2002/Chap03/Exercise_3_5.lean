/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Cor_3_8

public section

/- Exercise 3.5. Prove Corollary 3.8.

This exercise is a check-only reuse surface: Corollary 3.8 is already
formalized in `Book.Ch3.Cor_3_8` as
`ConjugateGradient.terminates_at_exact_solution_from_any_initial_guess`, the
finite-step exact-termination statement for conjugate gradient with a
positive-definite matrix `A`, arbitrary right-hand side `b`, and arbitrary
initial guess `f₀`.

The already-formalized companion consequence
`ConjugateGradient.solves_system_from_any_initial_guess` remains available in
`Book.Ch3.Cor_3_8`, but it is not repeated here as a second labeled entry.
-/
#check ConjugateGradient.terminates_at_exact_solution_from_any_initial_guess
