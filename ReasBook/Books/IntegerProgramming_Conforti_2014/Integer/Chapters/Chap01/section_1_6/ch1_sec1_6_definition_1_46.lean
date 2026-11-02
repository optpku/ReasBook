import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_1.Problem
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped Matrix

/- Definition 1.46: a pure integer linear program is the optimization problem
`max cᵀ x` subject to `A *ᵥ x ≤ b`, `x ∈ ℤ^n`, and `0 ≤ x`, formalized by the reusable owner
`PureIntegerLinearProgram`. The displayed two-variable example is the explicit coefficient package
below. -/
#check PureIntegerLinearProgram
#check
  (PureIntegerLinearProgram.ofCoefficients
    ![2, 1]
    ![![-1, 1], ![6, 2]]
    ![(0 : ℝ), 21] : PureIntegerLinearProgram 2 2)
