/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

noncomputable section

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u}
variable {n : Type v} [Fintype n]
variable {m : Type w} [Fintype m] [DecidableEq m]

/-- The estimator obtained by applying the coefficient matrix `B` to the observed random vector
`Z`. -/
def linearEstimator (B : Matrix n m ℝ) (Z : Ω → EuclideanSpace ℝ m) :
    Ω → EuclideanSpace ℝ n :=
  fun ω ↦ B.toEuclideanLin (Z ω)

section

omit [Fintype n] in
/-- The defining formula for `linearEstimator`. -/
theorem linearEstimator_apply (B : Matrix n m ℝ) (Z : Ω → EuclideanSpace ℝ m) (ω : Ω) :
    (linearEstimator B Z ω : EuclideanSpace ℝ n) = B.toEuclideanLin (Z ω) := by
  simp [linearEstimator]

end

end

end ProbabilityTheory
