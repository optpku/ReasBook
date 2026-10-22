/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3.EnergyNorm
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.QuadraticFunctional

public section

noncomputable section

open scoped Matrix.Energy

namespace QuadraticOptimization

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The error of an approximate solution `f` from the exact solution
`quadraticFunctionalMinimizer b A` of `A x = -b`. -/
@[expose]
def error (A : Matrix n n ℝ) (b f : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  f - quadraticFunctionalMinimizer b A

/-- The `A`-energy norm of `QuadraticOptimization.error A b f`. -/
@[expose]
def energyNormError
    (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) : ℝ :=
  ‖error A b f‖_[A, hA]

/-- Unfolding lemma for `QuadraticOptimization.error`. -/
theorem error_eq_sub
    (A : Matrix n n ℝ) (b f : EuclideanSpace ℝ n) :
    error A b f = f - quadraticFunctionalMinimizer b A :=
  rfl

/-- Unfolding lemma for `QuadraticOptimization.energyNormError`. -/
theorem energyNormError_eq
    (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    energyNormError A b hA f = ‖error A b f‖_[A, hA] :=
  rfl

end QuadraticOptimization
