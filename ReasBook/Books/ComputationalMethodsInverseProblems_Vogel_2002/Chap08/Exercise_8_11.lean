/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_14
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_1.Fredholm
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_16

public section

/-!
Exercise 8.11.

The source asks for an empirical numerical study for the one-dimensional test
problem of Section 8.3.1, comparing the effect of varying `α` and `β` on the
performance of each of the four algorithms used there, and asking in
particular what happens when `β` is taken very small.

In the current repository snapshot, the four relevant Chapter 8 algorithms are
already tracked as chapter items by `Book.Ch8.Algorithm_8_2_1`,
`Book.Ch8.Algorithm_8_2_2`, `Book.Ch8.Algorithm_8_2_3`, and
`Book.Ch8.Algorithm_8_2_4`. Among those files, `Algorithm_8_2_1`,
`Algorithm_8_2_2`, and `Algorithm_8_2_4` expose conservative check-only
source-facing clause skeletons, while `Algorithm_8_2_3` records that no
source-facing Lean declaration is yet available because the book's pseudocode
is internally inconsistent. The analytic small-`β` approximation bridge is
already tracked by `Book.Ch8.Exercise_8_16`.

What is still missing is the exact Section 8.3.1 one-dimensional benchmark as
a checked Lean owner, together with a benchmark-specific numerical
performance/comparison surface and a faithful source-facing Lean owner for the
lagged-diffusivity algorithm itself. Since those missing pieces are the
semantic payload of the exercise, this file remains a labeled `#check`-only
blocker entry rather than inventing a benchmark package, a synthetic
performance theorem, or a guessed method wrapper.
-/

/- Exercise 8.11. Main labeled source-facing blocker entry.

The imported Chapter 8 method files already track all four relevant algorithms,
but only `Algorithm_8_2_1`, `Algorithm_8_2_2`, and `Algorithm_8_2_4` currently
provide check-only source-facing clause skeletons. `Algorithm_8_2_3` instead
records the present absence of a faithful Lean declaration because of the
source pseudocode inconsistency, and `Book.Ch8.Exercise_8_16` provides the
checked small-`β` convergence anchor for `J_β`. The `#check` commands below
therefore record only the one-dimensional benchmark ingredients and the
Chapter 8 approximation bridge that a later faithful formalization of this
exercise should reuse directly. -/

#check Fredholm1D.figure11TrueSolution
#check Fredholm1D.midpointMatrix
#check VariationalRegularization.smoothNormApproxTotalVariation
#check VariationalRegularization.smoothNormApproxTotalVariation_tendstoUniformlyOn
