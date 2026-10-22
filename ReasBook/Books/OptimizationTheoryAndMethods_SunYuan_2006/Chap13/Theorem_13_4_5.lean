/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Sequences
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Algorithm_13_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Lemma_13_4_3

noncomputable section

open Filter
open scoped BigOperators Matrix.Norms.L2Operator

section

variable {ambientDim constraintDim tangentDim : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin ambientDim)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin constraintDim)
local notation "Method" =>
  NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim

-- Semantic recall: `Algorithm_13_4_1` owns the null-space trust-region method and its Step-2/3/4
-- surfaces, while `Lemma_13_4_3` owns the source denominator `method.hessianNormEnvelope`.
-- This file keeps only the Theorem 13.4.5 boundedness and partial-sum layer built on that API.

namespace NullSpaceTrustRegionMethod

/-- The partial sums in `(13.4.63)`, written from the source denominator
`M_(k+1) = method.hessianNormEnvelope (k + 1)` with the book indices shifted by `k ↦ k + 1`
so the Lean sum starts at `0`. -/
def hessianApproximationReciprocalEnvelopePartialSum
    (method : Method)
    (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 0 N) fun k ↦ 1 / method.hessianNormEnvelope (k + 1)

/-- Unfolding `method.hessianApproximationReciprocalEnvelopePartialSum N` gives the source sum
`∑_{k = 0}^N 1 / M_(k+1)`. -/
theorem hessianApproximationReciprocalEnvelopePartialSum_eq
    (method : Method) (N : ℕ) :
    method.hessianApproximationReciprocalEnvelopePartialSum N =
      Finset.sum (Finset.Icc 0 N) (fun k ↦ 1 / method.hessianNormEnvelope (k + 1)) :=
  rfl

/-- The continuous linear map represented by the recorded Jacobian matrix at `x`. -/
def constraintJacobianLinearization
    (method : Method)
    (x : Point) : Point →L[ℝ] ConstraintPoint :=
  (Matrix.toEuclideanLin (method.constraintJacobianAt x).transpose).toContinuousLinearMap

/-- Unfolding `method.constraintJacobianLinearization x` gives the recorded Jacobian
linearization as a continuous linear map. -/
theorem constraintJacobianLinearization_eq (method : Method) (x : Point) :
    method.constraintJacobianLinearization x =
      (Matrix.toEuclideanLin (method.constraintJacobianAt x).transpose).toContinuousLinearMap :=
  rfl

/-- The Step-2 residual `‖c_k‖₂ + ‖Z_kᵀ g_k‖₂` at stage `k`. -/
def stoppingResidual (method : Method) (k : ℕ) : ℝ :=
  nullSpaceStoppingResidual
    (method.constraintResidual k)
    (method.nullSpaceBasis k)
    (method.gradient k)

/-- Unfolding `method.stoppingResidual k` gives the Step-2 residual formula at stage `k`. -/
theorem stoppingResidual_eq (method : Method) (k : ℕ) :
    method.stoppingResidual k =
      nullSpaceStoppingResidual
        (method.constraintResidual k)
        (method.nullSpaceBasis k)
        (method.gradient k) :=
  rfl

section ConvergenceTheorems

variable
    (f : Point → ℝ)
    (S : Set Point)
    (method : Method)
    (h_objective_contDiff : ContDiffOn ℝ 2 f S)
    (h_gradient_eq : ∀ x : Point, x ∈ S → _root_.gradient f x = method.gradientAt x)
    (h_constraint_contDiff : ContDiffOn ℝ 2 method.constraintResidualAt S)
    (h_constraintJacobian_is_fderiv :
      ∀ x : Point, x ∈ S →
        fderiv ℝ method.constraintResidualAt x = method.constraintJacobianLinearization x)
    (hS_open : IsOpen S)
    (h_iterates_mem : ∀ k : ℕ, 1 ≤ k → method.iterate k ∈ S)
    (h_gradient_bounded : Bornology.IsBounded (method.gradientAt '' S))
    (h_hessian_bounded : Bornology.IsBounded ((fun x : Point ↦ fderiv ℝ method.gradientAt x) '' S))
    (h_jacobian_bounded : Bornology.IsBounded (method.constraintJacobianAt '' S))
    (h_jacobianDerivative_bounded :
      Bornology.IsBounded
        ((fun x : Point ↦ fderiv ℝ method.constraintJacobianLinearization x) '' S))
    (h_stageSigma_eventually_constant :
      ∃ σBar : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → method.stageSigma k = σBar)
    (h_penalty_bounded_below :
      ∃ pLower : ℝ, ∀ k : ℕ, 1 ≤ k → pLower ≤ method.penaltyFunction (method.iterate k))
    (h_jacobian_stages_bounded :
      Bornology.IsBounded (Set.range fun k : ℕ ↦ method.constraintJacobian (k + 1)))
    (h_pseudoinverse_stages_bounded :
      Bornology.IsBounded (Set.range fun k : ℕ ↦ method.aPseudoInverse (k + 1)))
    (h_hessianApproximation_reciprocalEnvelopePartialSum_diverges :
      Tendsto method.hessianApproximationReciprocalEnvelopePartialSum atTop atTop)

/-- Chapter13 Theorem 13.4.5 (1): assume the objective `f` and the recorded constraint map of
`method` are `C²` on an open set `S` containing every book-index iterate `x_k` with `k ≥ 1`,
the recorded gradient map `method.gradientAt`, its derivative, the recorded Jacobian map
`method.constraintJacobianAt`, and its derivative are uniformly bounded on `S`, and the gradient
and Jacobian-identification hypotheses hold for `x ∈ S`; the stagewise penalty parameters `σ_k`
recorded as `method.stageSigma k` eventually stabilize, the recorded penalty function is bounded
below along the iterates, the stagewise Jacobians `A_k` and pseudoinverses `A_k⁺` are uniformly
bounded, and the source partial sums `(13.4.63)` `∑ 1 / M_k` diverge via
`method.hessianApproximationReciprocalEnvelopePartialSum`. Then the shifted Step-2 residual
sequence `k ↦ method.stoppingResidual (k + 1)` has `liminf` equal to `0`. -/
theorem liminf_stoppingResidual_eq_zero_of_eventually_constant_stageSigma
    : liminf (fun k : ℕ ↦ method.stoppingResidual (k + 1)) atTop = 0 := by
  sorry

/-- Chapter13 Theorem 13.4.5 (2): under the hypotheses of
`liminf_stoppingResidual_eq_zero_of_eventually_constant_stageSigma`, if in addition the Hessian
approximations `B_k` are uniformly bounded and `β₀ > 0`, then the same Step-2 residual sequence
converges to `0`. -/
theorem tendsto_stoppingResidual_zero_of_bounded_hessianApproximation
    (h_hessianApproximation_stages_bounded :
      Bornology.IsBounded (Set.range fun k : ℕ ↦ method.hessianApproximation (k + 1)))
    (h_beta0_pos : 0 < method.β₀) :
    Tendsto (fun k : ℕ ↦ method.stoppingResidual (k + 1)) atTop (nhds 0) := by
  sorry

end ConvergenceTheorems

end NullSpaceTrustRegionMethod

end
