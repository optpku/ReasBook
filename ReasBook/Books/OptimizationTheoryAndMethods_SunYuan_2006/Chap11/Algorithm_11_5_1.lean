/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Algorithm_11_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Algorithm_11_5_2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall hits verified for this item: `linearlyConstrainedFeasibleSet` is already the
-- Chapter 11 owner for the equality-constrained feasible set in `Algorithm_11_5_2`, while
-- `projectedGradientReducedGradient` and `projectedGradientDirection` in
-- `Algorithm_11_4_1` already own the null-space projected-gradient construction
-- `-Z (Zᵀ ∇f(x))`. The stagewise Algorithm 11.5.1 data therefore stays explicit here, but the
-- duplicate local direction owner is removed.

/-- Chapter11 Algorithm 11.5.1: the null-space projected-gradient method for the linearly
constrained problem `Aᵀ x = b` starts from a feasible point `x₁`, fixes a matrix `Z` satisfying
`Aᵀ Z = 0` and `rank Z = n - m` under the dimension side condition `m ≤ n`, assumes that
the objective has the genuine gradient `∇f(x_k)` at each stage `k ≥ 1`, sets
`d_k = -Z Zᵀ ∇f(x_k)`, stops exactly when `‖d_k‖ ≤ ε`, and otherwise updates
`x_(k + 1) = x_k + α_k • d_k` with a positive line-search step size `α_k`. -/
structure NullSpaceProjectedGradientMethod (n m : ℕ) where
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  constraintMatrix : Matrix (Fin n) (Fin m) ℝ
  constraintTarget : EuclideanSpace ℝ (Fin m)
  nullMatrix : Matrix (Fin n) (Fin (n - m)) ℝ
  tolerance : ℝ
  initialPoint : EuclideanSpace ℝ (Fin n)
  active : ℕ → Prop
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  stepSize : ℕ → ℝ
  hmn : m ≤ n
  tolerance_nonneg : 0 ≤ tolerance
  initialPoint_mem : initialPoint ∈ linearlyConstrainedFeasibleSet constraintMatrix constraintTarget
  nullMatrix_spec : constraintMatrix.transpose * nullMatrix = 0 ∧ Matrix.rank nullMatrix = n - m
  iterate_one : iterate 1 = initialPoint
  objective_hasGradientAt (k : ℕ) (_ : 1 ≤ k) :
    HasGradientAt objective (gradient objective (iterate k)) (iterate k)
  feasible (k : ℕ) (_ : 1 ≤ k) :
    active k → iterate k ∈ linearlyConstrainedFeasibleSet constraintMatrix constraintTarget
  active_iff (k : ℕ) (_ : 1 ≤ k) :
    active k ↔
      tolerance <
        ‖projectedGradientDirection nullMatrix
            (projectedGradientReducedGradient nullMatrix (gradient objective (iterate k)))‖
  stepSize_pos (k : ℕ) (_ : 1 ≤ k) : active k → 0 < stepSize k
  iterate_succ (k : ℕ) (_ : 1 ≤ k) :
    active k →
      iterate (k + 1) =
        iterate k + stepSize k •
          projectedGradientDirection nullMatrix
            (projectedGradientReducedGradient nullMatrix (gradient objective (iterate k)))

namespace NullSpaceProjectedGradientMethod

/-- A null-space projected-gradient method can be evaluated at stage `k` as its iterate `x_k`. -/
instance : CoeFun (_root_.NullSpaceProjectedGradientMethod n m) (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply
    (method : _root_.NullSpaceProjectedGradientMethod n m) (k : ℕ) :
    method k = method.iterate k := rfl

/-- The Step-2 search direction computed from the current iterate `x_k`. -/
def directionAt (method : NullSpaceProjectedGradientMethod n m) (k : ℕ) : Point :=
  projectedGradientDirection method.nullMatrix
    (projectedGradientReducedGradient method.nullMatrix
      (gradient method.objective (method k)))

/-- Unfolding `method.directionAt k` gives the Step-2 formula `-Z Zᵀ ∇f(x_k)`. -/
theorem directionAt_eq
    (method : NullSpaceProjectedGradientMethod n m) (k : ℕ) :
    method.directionAt k =
      projectedGradientDirection method.nullMatrix
        (projectedGradientReducedGradient method.nullMatrix
          (gradient method.objective (method k))) := rfl

/-- Algorithm 11.5.1 terminates at stage `k` exactly when `‖d_k‖ ≤ ε`. -/
def terminatedAt (method : NullSpaceProjectedGradientMethod n m) (k : ℕ) : Prop :=
  ‖method.directionAt k‖ ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` gives the source stopping test `‖d_k‖ ≤ ε`. -/
theorem terminatedAt_iff
    (method : NullSpaceProjectedGradientMethod n m) (k : ℕ) :
    method.terminatedAt k ↔ ‖method.directionAt k‖ ≤ method.tolerance := Iff.rfl

/-- The initial iterate of `method` is feasible for the equality constraints `Aᵀ x = b`. -/
theorem initialPoint_mem_feasibleSet
    (method : NullSpaceProjectedGradientMethod n m) :
    method.initialPoint ∈
      linearlyConstrainedFeasibleSet method.constraintMatrix method.constraintTarget :=
  method.initialPoint_mem

/-- The first iterate of `method` is the recorded feasible starting point `x₁`. -/
theorem iterate_one_eq_initialPoint
    (method : NullSpaceProjectedGradientMethod n m) :
    method.iterate 1 = method.initialPoint :=
  method.iterate_one

/-- The initial iterate of `method` is feasible for the equality constraints `Aᵀ x = b`. -/
theorem iterate_one_mem_feasibleSet
    (method : NullSpaceProjectedGradientMethod n m) :
    method.iterate 1 ∈
      linearlyConstrainedFeasibleSet method.constraintMatrix method.constraintTarget := by
  simpa [method.iterate_one_eq_initialPoint] using method.initialPoint_mem_feasibleSet

/-- For every stage `k ≥ 1`, the algorithm continues exactly when the Step-2 stopping test fails. -/
theorem active_iff_not_terminatedAt
    (method : NullSpaceProjectedGradientMethod n m) {k : ℕ} (hk : 1 ≤ k) :
    method.active k ↔ ¬ method.terminatedAt k := by
  have hactive : method.active k ↔ method.tolerance < ‖method.directionAt k‖ := by
    simpa [directionAt] using (method.active_iff k hk)
  simpa [terminatedAt, not_le] using hactive

/-- If stage `k` is active, then the next iterate is obtained by moving along the Step-2
projected-gradient direction by the recorded positive step size `α_k`. -/
theorem iterate_succ_eq_add_direction
    (method : NullSpaceProjectedGradientMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hactive : method.active k) :
    method.iterate (k + 1) = method.iterate k + method.stepSize k • method.directionAt k := by
  simpa [directionAt] using method.iterate_succ k hk hactive

end NullSpaceProjectedGradientMethod

#print axioms NullSpaceProjectedGradientMethod.directionAt
#print axioms NullSpaceProjectedGradientMethod.terminatedAt

end
