/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Order.Filter.Extr

noncomputable section

section

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Chapter 6 already treats `TrustRegionSubproblem` as the owner of the step-space quadratic
-- model, feasible set, and predicted reduction. This file keeps that owner shape and treats the
-- current iterate `x_k` only as bridge data for the translated trust region and actual reduction.

/-- Chapter06 Definition 6.1-extra-1: a trust-region subproblem at iteration `k` is the
quadratic model `q^(k) (s) = f(x_k) + g_kᵀ s + (1 / 2) sᵀ B_k s` together with a symmetric
matrix `B_k` and a positive trust-region radius `Δ_k`. The iterate `x_k` itself is ambient data
for the translated trust region and the actual-reduction formula, not primitive step-space data
of the subproblem owner. -/
structure TrustRegionSubproblem (n : ℕ) where
  fAtCenter : ℝ
  gradient : EuclideanSpace ℝ (Fin n)
  hessianApprox : Matrix (Fin n) (Fin n) ℝ
  hessianApprox_symm : hessianApprox.IsSymm
  radius : ℝ
  radius_pos : 0 < radius

/-- The quadratic model attached to a trust-region subproblem. -/
def TrustRegionSubproblem.quadraticModel (P : TrustRegionSubproblem n) (s : Point) : ℝ :=
  P.fAtCenter + dotProduct P.gradient s +
    (1 / 2 : ℝ) * dotProduct s (P.hessianApprox.mulVec s)

/-- A trust-region subproblem coerces to its quadratic model. -/
instance : CoeFun (TrustRegionSubproblem n) (fun _ ↦ Point → ℝ) where
  coe P := P.quadraticModel

/-- Evaluating a trust-region subproblem as a function agrees with its quadratic model. -/
theorem TrustRegionSubproblem.coeFn_apply (P : TrustRegionSubproblem n) (s : Point) :
    P s = P.quadraticModel s := rfl

/-- Expanding the quadratic model gives the usual `f(x_k) + g_kᵀ s + (1 / 2) sᵀ B_k s`
formula. -/
theorem TrustRegionSubproblem.quadraticModel_eq (P : TrustRegionSubproblem n) (s : Point) :
    P.quadraticModel s =
      P.fAtCenter + dotProduct P.gradient s +
        (1 / 2 : ℝ) * dotProduct s (P.hessianApprox.mulVec s) := rfl

/-- Evaluating the trust-region quadratic model at the zero step returns `f(x_k)`. -/
theorem TrustRegionSubproblem.quadraticModel_zero (P : TrustRegionSubproblem n) :
    P.quadraticModel 0 = P.fAtCenter := by
  simp [TrustRegionSubproblem.quadraticModel]

/-- The feasible set of the trust-region subproblem is the closed ball `‖s‖ ≤ Δ_k` in step
space. -/
def TrustRegionSubproblem.feasibleSet (P : TrustRegionSubproblem n) : Set Point :=
  Metric.closedBall 0 P.radius

/-- Membership in the feasible set is exactly the trust-region norm constraint. -/
theorem TrustRegionSubproblem.mem_feasibleSet_iff (P : TrustRegionSubproblem n) (s : Point) :
    s ∈ P.feasibleSet ↔ ‖s‖ ≤ P.radius := by
  simp [TrustRegionSubproblem.feasibleSet]

/-- A step solves the trust-region subproblem when it is feasible and minimizes the quadratic
model on the trust region. This keeps the source-facing owner on `TrustRegionSubproblem` while
reusing mathlib's canonical minimizer predicate `IsMinOn` for the actual optimality condition. -/
def TrustRegionSubproblem.IsSolution
    (P : TrustRegionSubproblem n) (sStar : Point) : Prop :=
  sStar ∈ P.feasibleSet ∧ IsMinOn P P.feasibleSet sStar

/-- Unfolding `P.IsSolution sStar` gives feasibility together with minimization of the quadratic
model on the trust region. -/
theorem TrustRegionSubproblem.isSolution_iff_mem_feasibleSet_and_isMinOn
    (P : TrustRegionSubproblem n) (sStar : Point) :
    P.IsSolution sStar ↔ sStar ∈ P.feasibleSet ∧ IsMinOn P P.feasibleSet sStar :=
  Iff.rfl

/-- Membership in the translated trust region `closedBall x_k Δ_k` is exactly the centered norm
constraint `‖x - x_k‖ ≤ Δ_k`. -/
theorem TrustRegionSubproblem.mem_closedBall_iff (P : TrustRegionSubproblem n)
    (center x : Point) :
    x ∈ Metric.closedBall center P.radius ↔ ‖x - center‖ ≤ P.radius := by
  simp [Metric.mem_closedBall, dist_eq_norm]

/-- Translating the feasible set by the current iterate `x_k` gives the trust region
`closedBall x_k Δ_k`. -/
theorem TrustRegionSubproblem.center_add_mem_closedBall_iff
    (P : TrustRegionSubproblem n) (center s : Point) :
    center + s ∈ Metric.closedBall center P.radius ↔ s ∈ P.feasibleSet := by
  rw [TrustRegionSubproblem.mem_closedBall_iff, TrustRegionSubproblem.mem_feasibleSet_iff]
  simp

/-- The actual reduction is `f(x_k) - f(x_k + s_k)`. -/
def TrustRegionSubproblem.actualReduction
    (center : Point) (f : Point → ℝ) (sk : Point) : ℝ :=
  f center - f (center + sk)

/-- Expanding `actualReduction` gives `f(x_k) - f(x_k + s_k)`. -/
theorem TrustRegionSubproblem.actualReduction_eq_sub
    (center : Point) (f : Point → ℝ) (sk : Point) :
    TrustRegionSubproblem.actualReduction center f sk = f center - f (center + sk) := rfl

/-- The predicted reduction is `q^(k) (0) - q^(k) (s_k)`. -/
def TrustRegionSubproblem.predictedReduction (P : TrustRegionSubproblem n) (sk : Point) : ℝ :=
  P 0 - P sk

/-- Expanding `predictedReduction` gives `q^(k) (0) - q^(k) (s_k)`. -/
theorem TrustRegionSubproblem.predictedReduction_eq (P : TrustRegionSubproblem n) (sk : Point) :
    P.predictedReduction sk = P 0 - P sk := rfl

/-- The Euclidean operator norm `‖B_k‖₂` of the Hessian approximation. -/
def TrustRegionSubproblem.hessianOperatorNorm (P : TrustRegionSubproblem n) : ℝ :=
  ‖P.hessianApprox‖

/-- Expanding `hessianOperatorNorm` gives the matrix operator norm of `B_k`. -/
theorem TrustRegionSubproblem.hessianOperatorNorm_eq (P : TrustRegionSubproblem n) :
    P.hessianOperatorNorm = ‖P.hessianApprox‖ :=
  rfl

/-- The trust-region agreement ratio is the quotient of actual and predicted reductions. -/
def TrustRegionSubproblem.reductionRatio
    (P : TrustRegionSubproblem n) (center : Point) (f : Point → ℝ) (sk : Point) : ℝ :=
  TrustRegionSubproblem.actualReduction center f sk / P.predictedReduction sk

/-- Expanding `reductionRatio` gives the usual ratio `Ared_k / Pred_k`. -/
theorem TrustRegionSubproblem.reductionRatio_eq
    (P : TrustRegionSubproblem n) (center : Point) (f : Point → ℝ) (sk : Point) :
    P.reductionRatio center f sk =
      TrustRegionSubproblem.actualReduction center f sk / P.predictedReduction sk := rfl

end
