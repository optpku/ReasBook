/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_1_extra_1

open Matrix

noncomputable section

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ResidualVector" => EuclideanSpace ℝ (Fin m)
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Domain-style sampling for this refine pass:
-- * primary domain: trust-region Levenberg-Marquardt subproblems for nonlinear least squares on
--   Euclidean spaces;
-- * sampled owner declarations in the minimal closure:
--   `nonlinearLeastSquaresObjective`,
--   `TrustRegionSubproblem`,
--   `TrustRegionSubproblem.feasibleSet`,
--   `TrustRegionSubproblem.reductionRatio`;
-- * best owner abstraction: Chapter 6 already owns the canonical trust-region quadratic-model
--   package `TrustRegionSubproblem`, while Chapter 7 already owns the nonlinear least-squares
--   objective `nonlinearLeastSquaresObjective`;
-- * source/core/bridge triage:
--   - source-facing: the explicit least-squares gradient and model `s ↦ (1 / 2) * ‖J s + r‖²`;
--   - core/canonical: `TrustRegionSubproblem`;
--   - bridge/view: the Step-3 least-squares data determine a canonical `TrustRegionSubproblem`,
--     and the algorithm records that owner rather than a parallel local wrapper.

/-- The Gauss-Newton gradient `g_k = J_kᵀ r_k`. -/
def trustRegionLevenbergMarquardtGradient
    (J : JacobianMatrix) (rk : ResidualVector) : Point :=
  Matrix.toEuclideanLin (Jᵀ : Matrix (Fin n) (Fin m) ℝ) rk

/-- The stopping-test norm `‖g_k‖ = ‖J_kᵀ r_k‖` at the iterate `x_k`. -/
def trustRegionLevenbergMarquardtGradientNorm
    (r : Point → ResidualVector) (J : Point → JacobianMatrix) (xk : Point) : ℝ :=
  ‖trustRegionLevenbergMarquardtGradient (J xk) (r xk)‖

/-- The quadratic model `q_k(s) = (1 / 2) * ‖J_k s + r_k‖²` used in the trust-region
Levenberg-Marquardt subproblem. -/
def trustRegionLevenbergMarquardtModel
    (J : JacobianMatrix) (rk : ResidualVector) (s : Point) : ℝ :=
  ((1 : ℝ) / 2) * ‖J.mulVec s + rk‖ ^ (2 : ℕ)

/-- The least-squares Step-3 data canonically determine the Chapter 6 trust-region subproblem
whose quadratic model is `s ↦ (1 / 2) * ‖J s + r‖²` with radius `Δ`. This is a bridge/view from
the Levenberg-Marquardt data to the owner `TrustRegionSubproblem`, not a second owner. -/
def leastSquaresTrustRegionSubproblem
    (J : JacobianMatrix) (rk : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) : TrustRegionSubproblem n where
  fAtCenter := ((1 : ℝ) / 2) * ‖rk‖ ^ (2 : ℕ)
  gradient := trustRegionLevenbergMarquardtGradient J rk
  hessianApprox := Jᵀ * J
  hessianApprox_symm := by
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  radius := Δ
  radius_pos := hΔ

/-- Chapter07 Algorithm 7.3.9: a trust-region type Levenberg-Marquardt algorithm for the
nonlinear least-squares objective attached to `r` and matrix field `J` consists of an initial
point `x₀`, an outer radius bound `ΔBar`, an initial trust-region radius `Δ₀ ∈ (0, ΔBar)`,
parameters `ε ≥ 0`, `0 < η₁ ≤ η₂ < 1`, `0 < γ₁ < 1 < γ₂`, and an approximate-solution fraction
`β₂ ∈ (0, 1]`, together with a sequence of accepted iterates `x k`, outer trust-region radii
`Δ k`, inner retry radii `trialRadius k j`, trial steps `step k j`, and acceptance indices
`acceptIndex k`. At every active outer iteration with `ε < ‖J(x_k)ᵀ r(x_k)‖`, the inner
attempt `j = 0` starts with radius `Δ_k`, and Step 3 is recorded directly on the canonical
Chapter 6 trust-region subproblem built from `J (x k)`, `r (x k)`, and `trialRadius k j`. The
source gradient `J(x_k)ᵀ r(x_k)` and the trial radius belong to that owner by construction, so
feasibility and strict positivity of the predicted reduction become owner-level derived
consequences instead of primitive packaged data. Rejected trials satisfy `ρ_(k,j) < η₁` and
update the next retry radius by `γ₁ * trialRadius k j`, the accepted trial `j = acceptIndex k`
satisfies `η₁ ≤ ρ_(k,j)`, the next iterate is `x_(k + 1) = x_k + s_(k,j)`, and the next outer
radius is `min (γ₂ * trialRadius k j) ΔBar` exactly in the source branch
`η₂ ≤ ρ_(k,j)` with `‖s_(k,j)‖ = trialRadius k j`, otherwise `trialRadius k j`. -/
structure TrustRegionLevenbergMarquardtAlgorithm
    (r : Point → ResidualVector) (J : Point → JacobianMatrix) where
  ε : ℝ
  η1 : ℝ
  η2 : ℝ
  γ1 : ℝ
  γ2 : ℝ
  β₂ : ℝ
  x0 : Point
  ΔBar : ℝ
  Δ0 : ℝ
  x : ℕ → Point
  Δ : ℕ → ℝ
  acceptIndex : ℕ → ℕ
  trialRadius : ℕ → ℕ → ℝ
  step : ℕ → ℕ → Point
  epsilon_nonneg : 0 ≤ ε
  eta1_pos : 0 < η1
  eta1_le_eta2 : η1 ≤ η2
  eta2_lt_one : η2 < 1
  gamma1_mem : γ1 ∈ Set.Ioo (0 : ℝ) 1
  gamma2_gt_one : 1 < γ2
  beta2_mem : β₂ ∈ Set.Ioc (0 : ℝ) 1
  deltaBar_pos : 0 < ΔBar
  delta0_mem : Δ0 ∈ Set.Ioo (0 : ℝ) ΔBar
  x_zero : x 0 = x0
  delta_zero : Δ 0 = Δ0
  delta_mem (k : ℕ) : Δ k ∈ Set.Ioc (0 : ℝ) ΔBar
  trialRadius_initial (k : ℕ)
      (_ : ε < trustRegionLevenbergMarquardtGradientNorm r J (x k)) :
      trialRadius k 0 = Δ k
  attempt_radius_mem (k j : ℕ)
      (_ : ε < trustRegionLevenbergMarquardtGradientNorm r J (x k))
      (_ : j ≤ acceptIndex k) :
      trialRadius k j ∈ Set.Ioc (0 : ℝ) ΔBar
  attempt_isApproximateSolution (k j : ℕ)
      (hk : ε < trustRegionLevenbergMarquardtGradientNorm r J (x k))
      (hj : j ≤ acceptIndex k) :
      (leastSquaresTrustRegionSubproblem
          (J (x k)) (r (x k)) (trialRadius k j)
          (attempt_radius_mem k j hk hj).1).isApproximateSolution
        β₂ (step k j)
  rejected_ratio_lt_eta1 (k j : ℕ)
      (hk : ε < trustRegionLevenbergMarquardtGradientNorm r J (x k))
      (hj : j < acceptIndex k) :
      (leastSquaresTrustRegionSubproblem
          (J (x k)) (r (x k)) (trialRadius k j)
          (attempt_radius_mem k j hk (Nat.le_of_lt hj)).1).reductionRatio
          (x k) (nonlinearLeastSquaresObjective r) (step k j) <
        η1
  rejected_radius_update (k j : ℕ)
      (_ : ε < trustRegionLevenbergMarquardtGradientNorm r J (x k))
      (_ : j < acceptIndex k) :
      trialRadius k (j + 1) = γ1 * trialRadius k j
  accepted_ratio_ge_eta1 (k : ℕ)
      (hk : ε < trustRegionLevenbergMarquardtGradientNorm r J (x k)) :
      η1 ≤
        (leastSquaresTrustRegionSubproblem
            (J (x k)) (r (x k)) (trialRadius k (acceptIndex k))
            (attempt_radius_mem k (acceptIndex k) hk (le_rfl)).1).reductionRatio
          (x k) (nonlinearLeastSquaresObjective r) (step k (acceptIndex k))
  iterate_update (k : ℕ)
      (_ : ε < trustRegionLevenbergMarquardtGradientNorm r J (x k)) :
      x (k + 1) = x k + step k (acceptIndex k)
  radius_update (k : ℕ) (hk : ε < trustRegionLevenbergMarquardtGradientNorm r J (x k)) :
      Δ (k + 1) =
        if
          η2 ≤
              (leastSquaresTrustRegionSubproblem
                  (J (x k)) (r (x k)) (trialRadius k (acceptIndex k))
                  (attempt_radius_mem k (acceptIndex k) hk (le_rfl)).1).reductionRatio
                (x k) (nonlinearLeastSquaresObjective r) (step k (acceptIndex k)) ∧
            ‖step k (acceptIndex k)‖ = trialRadius k (acceptIndex k)
        then
          min (γ2 * trialRadius k (acceptIndex k)) ΔBar
        else
          trialRadius k (acceptIndex k)

/-- A trust-region type Levenberg-Marquardt algorithm can be used as its accepted iterate
sequence `x`. -/
instance {r : Point → ResidualVector} {J : Point → JacobianMatrix} :
    CoeFun (TrustRegionLevenbergMarquardtAlgorithm r J) (fun _ ↦ ℕ → Point) where
  coe A := A.x

namespace TrustRegionLevenbergMarquardtAlgorithm

/-- The algorithm has terminated at iteration `k` when the source stopping test
`‖J(x_k)ᵀ r(x_k)‖ ≤ ε` holds. -/
def terminatedAt
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k : ℕ) : Prop :=
  trustRegionLevenbergMarquardtGradientNorm r J (A.x k) ≤ A.ε

/-- The outer iteration `k` is active exactly when the source stopping test has not fired. -/
def activeAt
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k : ℕ) : Prop :=
  A.ε < trustRegionLevenbergMarquardtGradientNorm r J (A.x k)

/-- The active-attempt Step-3 subproblem canonically determined by `J (x k)`, `r (x k)`, and the
retry radius `trialRadius k j`. -/
def subproblem
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k j : ℕ)
    (hk : A.activeAt k) (hj : j ≤ A.acceptIndex k) : TrustRegionSubproblem n :=
  leastSquaresTrustRegionSubproblem
    (J (A.x k)) (r (A.x k)) (A.trialRadius k j) (A.attempt_radius_mem k j hk hj).1

/-- The active-attempt canonical Step-3 subproblem has radius `trialRadius k j`. -/
theorem subproblem_radius
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k j : ℕ)
    (hk : A.activeAt k) (hj : j ≤ A.acceptIndex k) :
    (A.subproblem k j hk hj).radius = A.trialRadius k j :=
  by simp [subproblem, leastSquaresTrustRegionSubproblem]

/-- The active-attempt canonical Step-3 subproblem has gradient `J(x_k)ᵀ r(x_k)`. -/
theorem subproblem_gradient
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k j : ℕ)
    (hk : A.activeAt k) (hj : j ≤ A.acceptIndex k) :
    (A.subproblem k j hk hj).gradient =
      trustRegionLevenbergMarquardtGradient (J (A.x k)) (r (A.x k)) :=
  by simp [subproblem, leastSquaresTrustRegionSubproblem]

/-- Expanding `terminatedAt` gives the Step 2 inequality `‖J_kᵀ r_k‖ ≤ ε`. -/
theorem terminatedAt_iff
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k : ℕ) :
    A.terminatedAt k ↔
      trustRegionLevenbergMarquardtGradientNorm r J (A.x k) ≤ A.ε :=
  Iff.rfl

/-- Expanding `activeAt` gives the active-iteration inequality `ε < ‖J_kᵀ r_k‖`. -/
theorem activeAt_iff
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k : ℕ) :
    A.activeAt k ↔
      A.ε < trustRegionLevenbergMarquardtGradientNorm r J (A.x k) :=
  Iff.rfl

/-- Every active inner attempt recorded by the algorithm satisfies the canonical Chapter 6
approximate-solution predicate on the packaged Step-3 subproblem. -/
theorem step_isApproximateSolution_of_activeAt
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k j : ℕ)
    (hk : A.activeAt k) (hj : j ≤ A.acceptIndex k) :
    (A.subproblem k j hk hj).isApproximateSolution A.β₂ (A.step k j) :=
  A.attempt_isApproximateSolution k j hk hj

/-- The canonical Step-3 approximate-solution predicate implies feasibility for the packaged
trust-region subproblem. -/
theorem step_mem_feasibleSet_of_activeAt
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k j : ℕ)
    (hk : A.activeAt k) (hj : j ≤ A.acceptIndex k) :
    A.step k j ∈ (A.subproblem k j hk hj).feasibleSet :=
  (TrustRegionSubproblem.isApproximateSolution_iff
      (A.subproblem k j hk hj) A.β₂ (A.step k j)).1
    (A.step_isApproximateSolution_of_activeAt k j hk hj) |>.1

/-- Rewriting owner-level feasibility with the source radius gives `‖s_(k,j)‖ ≤ trialRadius k j`.
-/
theorem step_norm_le_trialRadius_of_activeAt
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k j : ℕ)
    (hk : A.activeAt k) (hj : j ≤ A.acceptIndex k) :
    ‖A.step k j‖ ≤ A.trialRadius k j := by
  have hfeasible := A.step_mem_feasibleSet_of_activeAt k j hk hj
  have hnorm :
      ‖A.step k j‖ ≤ (A.subproblem k j hk hj).radius :=
    (TrustRegionSubproblem.mem_feasibleSet_iff (A.subproblem k j hk hj) (A.step k j)).1 hfeasible
  simpa [A.subproblem_radius k j hk hj] using hnorm

/-- The Chapter 6 predicted-reduction lemma transfers to each active Step-3 attempt via the
packaged subproblem and the source gradient bridge `J(x_k)ᵀ r(x_k)`. -/
theorem predictedReduction_pos_of_activeAt
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) (k j : ℕ)
    (hk : A.activeAt k) (hj : j ≤ A.acceptIndex k) :
    0 < (A.subproblem k j hk hj).predictedReduction (A.step k j) := by
  have hgrad :
      0 <
        ‖trustRegionLevenbergMarquardtGradient (J (A.x k)) (r (A.x k))‖ :=
    lt_of_le_of_lt A.epsilon_nonneg hk
  have hsubgrad : 0 < ‖(A.subproblem k j hk hj).gradient‖ := by
    simpa [A.subproblem_gradient k j hk hj] using hgrad
  exact (A.subproblem k j hk hj).predictedReduction_pos_of_isApproximateSolution
    A.β₂ (A.step k j) A.beta2_mem hsubgrad
    (A.step_isApproximateSolution_of_activeAt k j hk hj)

end TrustRegionLevenbergMarquardtAlgorithm

end
