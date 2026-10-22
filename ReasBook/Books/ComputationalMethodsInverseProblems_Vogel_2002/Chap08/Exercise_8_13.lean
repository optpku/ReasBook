/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4_1.Approximation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Remark_8_3

public section

/-!
Exercise 8.13.

The source exercise concerns the Section 8.3.1 one-dimensional benchmark
together with the Chapter 8 steepest-descent, primal Newton,
lagged-diffusivity, and primal-dual Newton procedures. In the current
repository snapshot, those source-facing procedural blocker surfaces are
already owned by `Book.Ch8.Algorithm_8_2_1`, `Book.Ch8.Algorithm_8_2_2`,
`Book.Ch8.Algorithm_8_2_3`, `Book.Ch8.Algorithm_8_2_4`, and
`Book.Ch8.Remark_8_3`.

What is still missing is the exact Section 8.3.1 one-dimensional benchmark as
a checked Lean owner, together with any benchmark-specific implementation or
comparison surface needed to state the exercise itself. Accordingly this item
remains a labeled blocker/check-only surface, but it reuses the Chapter 8
source-facing method files instead of falling back to generic backend
iteration APIs.
-/

/- Exercise 8.13. Main labeled source-facing blocker entry.

The Chapter 8 method surfaces relevant to this exercise are already tracked by
the imported algorithm and remark files. The `#check` commands below therefore
record only the approximation owners that modify the total-variation term in
the one-dimensional benchmark, while the exact benchmark and the
exercise-specific implementation/comparison surface remain upstream blockers.
-/

#check VariationalRegularization.smoothNormApproxTotalVariation
#check VariationalRegularization.huberApproxTotalVariation
