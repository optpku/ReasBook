/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Remark_13_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.EuclideanSubgradient
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_6_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_6_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_6_2

noncomputable section

open scoped BigOperators CompositeNonsmooth

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * source-facing owners in this file: the trust-region model, its chosen-norm subproblem solver
--   predicate, the accepted-step multiplier relation, and the method structure;
-- * core/canonical owner reused from `Definition_14_6_extra_1`:
--   `CompositeNonsmoothOptimizationProblem`;
-- * chosen trust-region-norm owners reused from Chapter 01/13:
--   `IsVectorNorm` and `trustRegionPenaltyFeasibleSet`;
-- * core/canonical Hessian owner reused from Chapter 3:
--   `hessianAt`;
-- * reused matrix bridge from Chapter 3:
--   `hessianMatrixAt`;
-- * reused Euclidean bridge from `EuclideanSubgradient`:
--   `Chapter14.IsSubgradientAt`.
-- Primitive data here are the composite problem, the `C²` regularity of the scalar components
-- `x ↦ problem.smoothMap x i`, the chosen trust-region norm `ρ`, and the stage records; the
-- Euclidean Hessian matrices
-- `∇² f_i(x)` and the trust-region matrices `B_k` are derived from the Chapter 3 owners rather
-- than stored as extra representative data. The Section 14.6 directional quantity is reused
-- directly from the owner-specialized surface `problem.firstOrderModel`, written as
-- `DF[problem](x, d)`.

/-- The matrix `∑ i, λ i • ∇² f_i(x)` from `(14.7.7)` attached to a point `x` and multipliers
`λ : ℝ^m`. -/
def trustRegionHessianApproximation
    (componentHessian : Fin m → Point → MatrixN) (x : Point) (weights : ValuePoint) : MatrixN :=
  ∑ i : Fin m, weights i • componentHessian i x

/-- Unfolding `trustRegionHessianApproximation componentHessian x weights` gives the source matrix
`∑ i, λ i • ∇² f_i(x)`. -/
theorem trustRegionHessianApproximation_eq
    (componentHessian : Fin m → Point → MatrixN) (x : Point) (weights : ValuePoint) :
    trustRegionHessianApproximation componentHessian x weights =
      ∑ i : Fin m, weights i • componentHessian i x :=
  rfl

/-- The predicted reduction `φ(0) - φ(d)` used in `(14.7.8)`. -/
def trustRegionPredictedReduction (φ : Point → ℝ) (d : Point) : ℝ :=
  φ 0 - φ d

/-- Unfolding `trustRegionPredictedReduction φ d` gives the source denominator
`φ(0) - φ(d)`. -/
theorem trustRegionPredictedReduction_eq (φ : Point → ℝ) (d : Point) :
    trustRegionPredictedReduction φ d = φ 0 - φ d :=
  rfl

/-- The trust-region model `φ_k(d) = h (f(x_k) + A(x_k)ᵀ d) + (1 / 2) dᵀ B_k d` used in
`(14.7.1)`. -/
def compositeNonsmoothTrustRegionModel
    (problem : CompositeNonsmoothOptimizationProblem n m) (xk : Point) (Bk : MatrixN)
    (d : Point) : ℝ :=
  problem.outerFunction
      (problem.smoothMap xk +
        WithLp.toLp 2
          ((compositeNonsmoothJacobianTranspose problem.smoothMap xk).transpose.mulVec d.ofLp)) +
    (1 / 2 : ℝ) * dotProduct d (Bk.mulVec d)

/-- Unfolding `compositeNonsmoothTrustRegionModel problem xk Bk d` gives the
source formula for `φ_k(d)`. -/
theorem compositeNonsmoothTrustRegionModel_apply
    (problem : CompositeNonsmoothOptimizationProblem n m) (xk : Point) (Bk : MatrixN) (d : Point) :
    compositeNonsmoothTrustRegionModel problem xk Bk d =
      problem.outerFunction
        (problem.smoothMap xk +
          WithLp.toLp 2
            ((compositeNonsmoothJacobianTranspose problem.smoothMap xk).transpose.mulVec
              d.ofLp)) +
        (1 / 2 : ℝ) * dotProduct d (Bk.mulVec d) :=
  rfl

/-- `IsCompositeNonsmoothTrustRegionSolution ρ problem xk Bk Δk dk` means that `dk` solves the
chosen-norm trust-region subproblem built from `(14.7.1)`-`(14.7.2)`: it is feasible for the
ball cut out by the Chapter 13 owner `trustRegionPenaltyFeasibleSet ρ Δk`, and minimizes the
model `φ_k` on that ball. The source Algorithm `14.7.1` is recovered by the Euclidean choice
`ρ = l2Norm`. -/
def IsCompositeNonsmoothTrustRegionSolution
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ]
    (problem : CompositeNonsmoothOptimizationProblem n m) (xk : Point) (Bk : MatrixN)
    (Δk : ℝ) (dk : Point) : Prop :=
  dk ∈ trustRegionPenaltyFeasibleSet ρ Δk ∧
    IsMinOn
      (compositeNonsmoothTrustRegionModel problem xk Bk)
      (trustRegionPenaltyFeasibleSet ρ Δk)
      dk

/-- Expanding `IsCompositeNonsmoothTrustRegionSolution` gives feasibility together with global
minimality of the trust-region model on the chosen trust-region ball. -/
theorem isCompositeNonsmoothTrustRegionSolution_iff
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ]
    (problem : CompositeNonsmoothOptimizationProblem n m) (xk : Point) (Bk : MatrixN)
    (Δk : ℝ) (dk : Point) :
    IsCompositeNonsmoothTrustRegionSolution ρ problem xk Bk Δk dk ↔
      ρ dk.ofLp ≤ Δk ∧
        ∀ d : Point, ρ d.ofLp ≤ Δk →
          compositeNonsmoothTrustRegionModel problem xk Bk dk ≤
            compositeNonsmoothTrustRegionModel problem xk Bk d := by
  rw [IsCompositeNonsmoothTrustRegionSolution, isMinOn_iff]
  constructor
  · rintro ⟨hdk, hmin⟩
    refine ⟨(mem_trustRegionPenaltyFeasibleSet_iff ρ Δk dk).1 hdk, ?_⟩
    intro d hd
    exact hmin d ((mem_trustRegionPenaltyFeasibleSet_iff ρ Δk d).2 hd)
  · rintro ⟨hdk, hmin⟩
    refine ⟨(mem_trustRegionPenaltyFeasibleSet_iff ρ Δk dk).2 hdk, ?_⟩
    intro d hd
    exact hmin d ((mem_trustRegionPenaltyFeasibleSet_iff ρ Δk d).1 hd)

/-- `IsCompositeNonsmoothAcceptedStepMultiplier problem x d lam` means that `lam` is the Step-5
multiplier from `(14.7.5)`: it is a codomain Euclidean subgradient at `problem.smoothMap x`
whose directional value along `d` attains the canonical Section 14.6 owner quantity
`DF[problem](x, d)`. -/
def IsCompositeNonsmoothAcceptedStepMultiplier
    (problem : CompositeNonsmoothOptimizationProblem n m) (x d : Point) (lam : ValuePoint) : Prop :=
  Chapter14.IsSubgradientAt problem.outerFunction (problem.smoothMap x) lam ∧
    inner ℝ d
      (WithLp.toLp 2
        ((compositeNonsmoothJacobianTranspose problem.smoothMap x).mulVec lam.ofLp)) =
      DF[problem](x, d)

/-- Unfolding `IsCompositeNonsmoothAcceptedStepMultiplier problem x d lam`
gives the Step-5 multiplier condition from `(14.7.5)`. -/
theorem isCompositeNonsmoothAcceptedStepMultiplier_iff
    (problem : CompositeNonsmoothOptimizationProblem n m) (x d : Point) (lam : ValuePoint) :
    IsCompositeNonsmoothAcceptedStepMultiplier problem x d lam ↔
      Chapter14.IsSubgradientAt problem.outerFunction (problem.smoothMap x) lam ∧
        inner ℝ d
          (WithLp.toLp 2
            ((compositeNonsmoothJacobianTranspose problem.smoothMap x).mulVec lam.ofLp)) =
          DF[problem](x, d) :=
  Iff.rfl

private abbrev componentHessianMatrix
    (problem : CompositeNonsmoothOptimizationProblem n m) :
    Fin m → Point → MatrixN :=
  fun i x ↦ hessianMatrixAt (fun y : Point ↦ problem.smoothMap y i) x

namespace CompositeNonsmoothTrustRegion

/-- The stage Hessian approximation `B_k = ∑ i, λ_(k - 1, i) ∇² f_i(x_k)` attached to the
recorded iterate and multiplier data. -/
def hessianApproximationAt
    (problem : CompositeNonsmoothOptimizationProblem n m)
    (iterate : ℕ → Point) (multiplier : ℕ → ValuePoint) (k : ℕ) : MatrixN :=
  trustRegionHessianApproximation
    (componentHessianMatrix problem)
    (iterate k)
    (multiplier (k - 1))

/-- The trust-region model `φ_k` attached to the stage data `(x_k, λ_(k - 1))`. -/
def modelAt
    (problem : CompositeNonsmoothOptimizationProblem n m)
    (iterate : ℕ → Point) (multiplier : ℕ → ValuePoint) (k : ℕ) : Point → ℝ :=
  compositeNonsmoothTrustRegionModel problem (iterate k)
    (hessianApproximationAt problem iterate multiplier k)

/-- The trial point `x_k + d_k` attached to the iterate and direction data. -/
def trialPoint
    (iterate direction : ℕ → Point) (k : ℕ) : Point :=
  iterate k + direction k

/-- The monotone trust-region ratio `r_k` from `(14.7.8)`, formed from the stage data of
Algorithm 14.7.1. -/
def reductionRatioAt
    (problem : CompositeNonsmoothOptimizationProblem n m)
    (iterate : ℕ → Point) (multiplier : ℕ → ValuePoint)
    (direction : ℕ → Point) (k : ℕ) : ℝ :=
  (problem (iterate k) - problem (trialPoint iterate direction k)) /
    (modelAt problem iterate multiplier k 0 -
      modelAt problem iterate multiplier k (direction k))

end CompositeNonsmoothTrustRegion

/-- Chapter14 Algorithm 14.7.1, refined to the chosen trust-region norm `ρ`: a trust-region run
for a composite nonsmooth optimization problem records an initial point `x₁`, an initial
multiplier vector `λ₀`, an initial trust-region radius `Δ₁ > 0`, a tolerance `ε ≥ 0`, the
iterate sequence `x_k`, the multiplier sequence `λ_k`, the directions `d_k`, and the
trust-region radii `Δ_k`. The source hypothesis that each scalar component `f_i` is twice
continuously differentiable is recorded directly through `componentContDiff`; the Hessian
matrices `∇² f_i(x)` and the Step-1 approximation
`B_k = ∑ i, λ_(k - 1, i) ∇² f_i(x_k)` from `(14.7.7)` are then derived canonically through the
Chapter 3 Hessian-matrix bridge. The Jacobian-transpose field `A(x) = ∇ f(x)ᵀ` and the model
functions `φ_k` are likewise derived from the composite problem and the stage data. At each
stage `k ≥ 1`, the recorded direction solves the trust-region subproblem built from that
canonical Jacobian data, the current Hessian approximation, and the chosen norm `ρ`; the source
Algorithm `14.7.1` is the specialization `ρ = l2Norm`. The stopping case
`ρ (d_k.ofLp) ≤ ε` is allowed; only continuing stages with `ε < ρ (d_k.ofLp)` satisfy the Step-3
radius update and the Step-4/Step-5 iterate and multiplier rules. On accepted steps
`x_(k + 1) = x_k + d_k`, and the new multiplier `λ_k` satisfies the Step-5 relation `(14.7.5)`.
-/
structure CompositeNonsmoothTrustRegionMethod
    (n m : ℕ) (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] where
  problem : CompositeNonsmoothOptimizationProblem n m
  componentContDiff :
    ∀ i : Fin m, ContDiff ℝ 2 (fun y : Chapter14.Point n ↦ problem.smoothMap y i)
  initialPoint : Chapter14.Point n
  initialMultiplier : Chapter14.Point m
  initialRadius : ℝ
  epsilon : ℝ
  iterate : ℕ → Chapter14.Point n
  multiplier : ℕ → Chapter14.Point m
  direction : ℕ → Chapter14.Point n
  trustRegionRadius : ℕ → ℝ
  initialRadius_pos : 0 < initialRadius
  epsilon_nonneg : 0 ≤ epsilon
  iterate_one : iterate 1 = initialPoint
  multiplier_zero : multiplier 0 = initialMultiplier
  trustRegionRadius_one : trustRegionRadius 1 = initialRadius
  direction_subproblem_solution
      (k : ℕ) (_hk : 1 ≤ k) :
      IsCompositeNonsmoothTrustRegionSolution
        ρ
        problem
        (iterate k)
        (CompositeNonsmoothTrustRegion.hessianApproximationAt problem iterate multiplier k)
        (trustRegionRadius k)
        (direction k)
  predictedReduction_pos
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp) :
      0 <
        trustRegionPredictedReduction
          (CompositeNonsmoothTrustRegion.modelAt problem iterate multiplier k)
          (direction k)
  trustRegionRadius_succ
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp) :
      trustRegionRadius (k + 1) =
        if CompositeNonsmoothTrustRegion.reductionRatioAt
              problem
              iterate
              multiplier
              direction
              k <
            (1 / 4 : ℝ) then
          ρ (direction k).ofLp / 4
        else if (3 / 4 : ℝ) <
              CompositeNonsmoothTrustRegion.reductionRatioAt
                problem
                iterate
                multiplier
                direction
                k ∧
              ρ (direction k).ofLp = trustRegionRadius k then
          2 * trustRegionRadius k
        else
          trustRegionRadius k
  iterate_succ_of_positive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        0 <
          CompositeNonsmoothTrustRegion.reductionRatioAt
            problem
            iterate
            multiplier
            direction
            k) :
      iterate (k + 1) = CompositeNonsmoothTrustRegion.trialPoint iterate direction k
  multiplier_of_positive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        0 <
          CompositeNonsmoothTrustRegion.reductionRatioAt
            problem
            iterate
            multiplier
            direction
            k) :
      IsCompositeNonsmoothAcceptedStepMultiplier
        problem
        (CompositeNonsmoothTrustRegion.trialPoint iterate direction k)
        (direction k)
        (multiplier k)
  iterate_succ_of_nonpositive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        CompositeNonsmoothTrustRegion.reductionRatioAt
            problem
            iterate
            multiplier
            direction
            k ≤
          0) :
      iterate (k + 1) = iterate k
  multiplier_of_nonpositive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        CompositeNonsmoothTrustRegion.reductionRatioAt
            problem
            iterate
            multiplier
            direction
            k ≤
          0) :
      multiplier k = multiplier (k - 1)

namespace CompositeNonsmoothTrustRegionMethod

variable {ρ : (Fin n → ℝ) → ℝ} [IsVectorNorm ρ]

local notation "Method" => @_root_.CompositeNonsmoothTrustRegionMethod n m ρ _

/-- A composite nonsmooth trust-region method can be evaluated at stage `k` as its iterate
`x_k`. -/
instance : CoeFun Method (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply (method : Method) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The matrix `B_k` from `(14.7.7)`, built from the current iterate `x_k` and the previous
multiplier vector `λ_(k - 1)`. -/
def hessianApproximationAt
    (method : Method) (k : ℕ) : MatrixN :=
  CompositeNonsmoothTrustRegion.hessianApproximationAt
    method.problem
    method.iterate
    method.multiplier
    k

/-- Unfolding `method.hessianApproximationAt k` gives the source matrix `B_k` from `(14.7.7)`. -/
theorem hessianApproximationAt_eq
    (method : Method) (k : ℕ) :
    method.hessianApproximationAt k =
      ∑ i : Fin m,
        (method.multiplier (k - 1)) i •
          hessianMatrixAt (fun y : Point ↦ method.problem.smoothMap y i) (method.iterate k) :=
  trustRegionHessianApproximation_eq
    (componentHessianMatrix method.problem)
    (method.iterate k)
    (method.multiplier (k - 1))

/-- Each scalar component `x ↦ f_i(x)` of the smooth map in Algorithm 14.7.1 is globally `C²`. -/
theorem component_contDiff
    (method : Method) (i : Fin m) :
    ContDiff ℝ 2 (fun y : Point ↦ method.problem.smoothMap y i) :=
  method.componentContDiff i

/-- The canonical Chapter 3 Hessian matrix bridge for the scalar component `x ↦ f_i(x)` agrees
with the actual derivative of `gradient (fun y ↦ f_i(y))`. -/
theorem componentHessianAt_eq_hessian
    (method : Method) (i : Fin m) (x : Point) :
    Matrix.toEuclideanLin (hessianMatrixAt (fun y : Point ↦ method.problem.smoothMap y i) x) =
      fderiv ℝ (gradient fun y : Point ↦ method.problem.smoothMap y i) x :=
  by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact
      congrArg
        (fun T : Point →L[ℝ] Point ↦ (T : Point →ₗ[ℝ] Point))
        (by
          simpa [hessianAt] using
            toEuclideanCLM_hessianMatrixAt (fun y : Point ↦ method.problem.smoothMap y i) x)

/-- The stage model `φ_k` is derived from the problem data, iterate `x_k`, previous multiplier
`λ_(k - 1)`, and the resulting Hessian approximation `B_k`. -/
def modelFunction
    (method : Method) (k : ℕ) : Point → ℝ :=
  CompositeNonsmoothTrustRegion.modelAt
    method.problem
    method.iterate
    method.multiplier
    k

/-- The trial point `x_k + d_k` used in Steps 3 and 5. -/
def trialPointAt (method : Method) (k : ℕ) : Point :=
  CompositeNonsmoothTrustRegion.trialPoint method.iterate method.direction k

/-- Unfolding `method.trialPointAt k` gives the Step-5 trial point `x_k + d_k`. -/
theorem trialPointAt_eq
    (method : Method) (k : ℕ) :
    method.trialPointAt k = method.iterate k + method.direction k :=
  rfl

/-- The actual reduction `h(f(x_k)) - h(f(x_k + d_k))` at stage `k`. -/
def actualReductionAt (method : Method) (k : ℕ) : ℝ :=
  method.problem (method.iterate k) - method.problem (method.trialPointAt k)

/-- Unfolding `method.actualReductionAt k` gives the source numerator from `(14.7.8)`. -/
theorem actualReductionAt_eq
    (method : Method) (k : ℕ) :
    method.actualReductionAt k =
      method.problem (method.iterate k) - method.problem (method.trialPointAt k) :=
  rfl

/-- The predicted reduction `φ_k(0) - φ_k(d_k)` at stage `k`. -/
def predictedReductionAt
    (method : Method) (k : ℕ) : ℝ :=
  trustRegionPredictedReduction (method.modelFunction k) (method.direction k)

/-- Unfolding `method.predictedReductionAt k` gives the denominator from `(14.7.8)`. -/
theorem predictedReductionAt_eq
    (method : Method) (k : ℕ) :
    method.predictedReductionAt k =
      method.modelFunction k 0 - method.modelFunction k (method.direction k) :=
  rfl

/-- At each stage `k ≥ 1`, the recorded model function `φ_k` is the trust-region model from
`(14.7.1)` built from `A(x_k)` and `B_k`. -/
theorem modelFunction_eq_stageModel
    (method : Method) (k : ℕ) :
    method.modelFunction k =
      compositeNonsmoothTrustRegionModel method.problem (method.iterate k)
        (method.hessianApproximationAt k) :=
  rfl

/-- The ratio `r_k` from `(14.7.8)`. -/
def reductionRatioAt
    (method : Method) (k : ℕ) : ℝ :=
  CompositeNonsmoothTrustRegion.reductionRatioAt
    method.problem
    method.iterate
    method.multiplier
    method.direction
    k

/-- Unfolding `method.reductionRatioAt k` gives the source ratio `r_k` from `(14.7.8)`. -/
theorem reductionRatioAt_eq
    (method : Method) (k : ℕ) :
    method.reductionRatioAt k =
      (method.problem (method.iterate k) - method.problem (method.trialPointAt k)) /
        (method.modelFunction k 0 - method.modelFunction k (method.direction k)) :=
  rfl

/-- `method.stopsAt k` is the Step-2 stopping test `‖d_k‖ ≤ ε`. -/
def stopsAt (method : Method) (k : ℕ) : Prop :=
  ρ (method.direction k).ofLp ≤ method.epsilon

/-- Unfolding `method.stopsAt k` gives the Step-2 stopping condition `‖d_k‖ ≤ ε`. -/
theorem stopsAt_iff
    (method : Method) (k : ℕ) :
    method.stopsAt k ↔ ρ (method.direction k).ofLp ≤ method.epsilon :=
  Iff.rfl

/-- `method.continuesAt k` is the Step-2 continuation branch `ε < ‖d_k‖`. -/
def continuesAt (method : Method) (k : ℕ) : Prop :=
  method.epsilon < ρ (method.direction k).ofLp

/-- Unfolding `method.continuesAt k` gives the Step-2 continuation condition `ε < ‖d_k‖`. -/
theorem continuesAt_iff
    (method : Method) (k : ℕ) :
    method.continuesAt k ↔ method.epsilon < ρ (method.direction k).ofLp :=
  Iff.rfl

/-- Every stage either stops or continues after the Step-2 norm test. -/
theorem stop_or_continue
    (method : Method) (k : ℕ) :
    method.stopsAt k ∨ method.continuesAt k := by
  rcases lt_or_ge method.epsilon (ρ (method.direction k).ofLp) with hContinue | hStop
  · exact Or.inr hContinue
  · exact Or.inl hStop

/-- The recorded iterate sequence starts from the given initial point `x₁`. -/
theorem iterate_one_eq_initialPoint (method : Method) :
    method.iterate 1 = method.initialPoint :=
  method.iterate_one

/-- The recorded multiplier sequence starts from the given initial value `λ₀`. -/
theorem multiplier_zero_eq_initialMultiplier
    (method : Method) :
    method.multiplier 0 = method.initialMultiplier :=
  method.multiplier_zero

/-- The recorded trust-region radii start from the given initial radius `Δ₁`. -/
theorem trustRegionRadius_one_eq_initialRadius
    (method : Method) :
    method.trustRegionRadius 1 = method.initialRadius :=
  method.trustRegionRadius_one

/-- At each recorded stage `k ≥ 1`, the direction `d_k` solves the source subproblem
`(14.7.1)`-`(14.7.2)` built from `A(x_k)` and `B_k`. -/
theorem direction_subproblem_solution_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k) :
    IsCompositeNonsmoothTrustRegionSolution
      ρ
      method.problem
      (method.iterate k)
      (method.hessianApproximationAt k)
      (method.trustRegionRadius k)
      (method.direction k) := by
  simpa [hessianApproximationAt, CompositeNonsmoothTrustRegion.hessianApproximationAt] using
    method.direction_subproblem_solution k hk

/-- Every continuing stage `k ≥ 1` has strictly positive predicted reduction
`φ_k(0) - φ_k(d_k)`. -/
theorem predictedReduction_pos_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hContinue : method.continuesAt k) :
    0 < method.predictedReductionAt k := by
  simpa [continuesAt, predictedReductionAt, modelFunction, CompositeNonsmoothTrustRegion.modelAt,
    trustRegionPredictedReduction] using
    method.predictedReduction_pos k hk hContinue

/-- At each continuing stage `k ≥ 1`, the next trust-region radius is updated by the Step-3
branching rule based on `r_k`. -/
theorem trustRegionRadius_succ_eq
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hContinue : method.continuesAt k) :
    method.trustRegionRadius (k + 1) =
      if method.reductionRatioAt k < (1 / 4 : ℝ) then
        ρ (method.direction k).ofLp / 4
      else if (3 / 4 : ℝ) < method.reductionRatioAt k ∧
            ρ (method.direction k).ofLp = method.trustRegionRadius k then
        2 * method.trustRegionRadius k
      else
        method.trustRegionRadius k := by
  have hContinue' : method.epsilon < ρ (method.direction k).ofLp := by
    simpa [continuesAt] using hContinue
  change method.trustRegionRadius (k + 1) =
    if CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k <
        (1 / 4 : ℝ) then
      ρ (method.direction k).ofLp / 4
    else if (3 / 4 : ℝ) < CompositeNonsmoothTrustRegion.reductionRatioAt
            method.problem
            method.iterate
            method.multiplier
            method.direction
            k ∧
          ρ (method.direction k).ofLp = method.trustRegionRadius k then
      2 * method.trustRegionRadius k
    else
      method.trustRegionRadius k
  exact method.trustRegionRadius_succ k hk hContinue'

/-- If a continuing stage has `r_k > 0`, Step 5 accepts the trial point as the next iterate. -/
theorem iterate_succ_eq_trialPointAt_of_positive_ratio
    (method : Method) {k : ℕ}
    (hk : 1 ≤ k) (hContinue : method.continuesAt k) (hrk : 0 < method.reductionRatioAt k) :
    method.iterate (k + 1) = method.trialPointAt k := by
  have hContinue' : method.epsilon < ρ (method.direction k).ofLp := by
    simpa [continuesAt] using hContinue
  have hrk' :
      0 <
        CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k := by
    simpa [reductionRatioAt] using hrk
  change method.iterate (k + 1) =
    CompositeNonsmoothTrustRegion.trialPoint method.iterate method.direction k
  exact method.iterate_succ_of_positive_ratio k hk hContinue' hrk'

/-- If a continuing stage has `r_k > 0`, the accepted multiplier satisfies `(14.7.5)` at the
accepted point `x_k + d_k`. -/
theorem acceptedStepMultiplier_at
    (method : Method) {k : ℕ}
    (hk : 1 ≤ k) (hContinue : method.continuesAt k) (hrk : 0 < method.reductionRatioAt k) :
    IsCompositeNonsmoothAcceptedStepMultiplier
      method.problem
      (method.trialPointAt k)
      (method.direction k)
      (method.multiplier k) := by
  have hContinue' : method.epsilon < ρ (method.direction k).ofLp := by
    simpa [continuesAt] using hContinue
  have hrk' :
      0 <
        CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k := by
    simpa [reductionRatioAt] using hrk
  change IsCompositeNonsmoothAcceptedStepMultiplier
    method.problem
    (CompositeNonsmoothTrustRegion.trialPoint method.iterate method.direction k)
    (method.direction k)
    (method.multiplier k)
  exact method.multiplier_of_positive_ratio k hk hContinue' hrk'

/-- If a continuing stage has `r_k ≤ 0`, Step 4 keeps the current iterate unchanged. -/
theorem iterate_succ_eq_self_of_nonpositive_ratio
    (method : Method) {k : ℕ}
    (hk : 1 ≤ k) (hContinue : method.continuesAt k) (hrk : method.reductionRatioAt k ≤ 0) :
    method.iterate (k + 1) = method.iterate k := by
  have hContinue' : method.epsilon < ρ (method.direction k).ofLp := by
    simpa [continuesAt] using hContinue
  have hrk' :
      CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k ≤
        0 := by
    simpa [reductionRatioAt] using hrk
  exact method.iterate_succ_of_nonpositive_ratio k hk hContinue' hrk'

/-- If a continuing stage has `r_k ≤ 0`, Step 4 also keeps the multiplier vector unchanged. -/
theorem multiplier_eq_prev_of_nonpositive_ratio
    (method : Method) {k : ℕ}
    (hk : 1 ≤ k) (hContinue : method.continuesAt k) (hrk : method.reductionRatioAt k ≤ 0) :
    method.multiplier k = method.multiplier (k - 1) := by
  have hContinue' : method.epsilon < ρ (method.direction k).ofLp := by
    simpa [continuesAt] using hContinue
  have hrk' :
      CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k ≤
        0 := by
    simpa [reductionRatioAt] using hrk
  exact method.multiplier_of_nonpositive_ratio k hk hContinue' hrk'

end CompositeNonsmoothTrustRegionMethod

#print axioms trustRegionHessianApproximation
#print axioms trustRegionPredictedReduction
#print axioms compositeNonsmoothDF
#print axioms compositeNonsmoothTrustRegionModel
#print axioms CompositeNonsmoothTrustRegionMethod.hessianApproximationAt
#print axioms CompositeNonsmoothTrustRegionMethod.trialPointAt
#print axioms CompositeNonsmoothTrustRegionMethod.actualReductionAt
#print axioms CompositeNonsmoothTrustRegionMethod.predictedReductionAt
#print axioms CompositeNonsmoothTrustRegionMethod.reductionRatioAt

end
