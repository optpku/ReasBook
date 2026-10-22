/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Lemma_11_5_4

noncomputable section

section Chapter11Theorem1155Comparison

variable {n m : ℕ}

/-- The linear equality-constrained problem with objective `f` and the constraint data recorded by
`method`. -/
def LinearlyConstrainedQuarteringSearchMethod.toLinearEqualityConstrainedProblem
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    LinearEqualityConstrainedProblem n m where
  objective := f
  constraintMatrix := method.constraintMatrix
  constraintTarget := method.constraintTarget

/-- The feasible set of `method.toLinearEqualityConstrainedProblem f` is exactly the linear
equality-constrained feasible set recorded by `method`. -/
theorem LinearlyConstrainedQuarteringSearchMethod.toLinearEqualityConstrainedProblem_feasibleSet_eq
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (method.toLinearEqualityConstrainedProblem f).feasibleSet =
      method.feasibleSet :=
  rfl

/-- A point is feasible for `method.toLinearEqualityConstrainedProblem f` exactly when it belongs
to the feasible set recorded by `method`. -/
@[simp] theorem LinearlyConstrainedQuarteringSearchMethod.mem_toLinearEqualityConstrainedProblem_iff
    (method : LinearlyConstrainedQuarteringSearchMethod n m)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ method.toLinearEqualityConstrainedProblem f ↔ x ∈ method.feasibleSet := by
  rfl

end Chapter11Theorem1155Comparison
