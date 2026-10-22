/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.ConditionNumber
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.QuadraticFunctional

public section

/- Definition 3.4 (1). The matrix condition number is formalized by
`Matrix.conditionNumber`. -/
#check Matrix.conditionNumber

/- Definition 3.4 (2). For a positive-definite matrix, the specialized
condition number `Matrix.posDefConditionNumber` reduces to the ratio of the
largest and smallest spectral values. -/
#check Matrix.posDefConditionNumber_eq_spectralExtrema

/- Definition 3.4 (3). The predicate that a map
`J : EuclideanSpace ℝ n → ℝ` is quadratic is formalized by
`QuadraticOptimization.IsQuadraticFunctional`; its explicit source-facing
expansion is `QuadraticOptimization.isQuadraticFunctional_iff`. -/
#check QuadraticOptimization.IsQuadraticFunctional

/- Definition 3.4 (4). The gradient of a quadratic functional with symmetric
matrix part is `f ↦ b + A.toEuclideanLin f`. -/
#check QuadraticOptimization.gradient_quadraticFunctional

/- Definition 3.4 (5). The Hessian of a quadratic functional with symmetric
matrix part acts by `A.toEuclideanLin`. -/
#check QuadraticOptimization.hessian_quadraticFunctional

/- Definition 3.4 (6). The source hypothesis that a quadratic functional is
positive is represented by the explicit assumption `hspd : A.PosDef`, under
which the functional is strictly convex. -/
#check QuadraticOptimization.strictConvexOn_quadraticFunctional_of_posDef

/- Definition 3.4 (7). A positive-definite quadratic functional attains its
minimum at `-(A⁻¹).toEuclideanLin b`. -/
#check QuadraticOptimization.isMinOn_quadraticFunctional_of_posDef

/- Definition 3.4 (8). A positive-definite quadratic functional has
`-(A⁻¹).toEuclideanLin b` as its unique minimizer. -/
#check QuadraticOptimization.eq_minimizer_of_isMinOn_quadraticFunctional_of_posDef

/- Definition 3.4 (9). The exact steepest-descent line-search step is formalized
by `QuadraticOptimization.exactLineSearchStep_quadraticFunctional`. -/
#check QuadraticOptimization.exactLineSearchStep_quadraticFunctional
