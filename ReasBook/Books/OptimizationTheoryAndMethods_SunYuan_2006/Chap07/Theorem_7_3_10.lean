/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.InitialSublevelSet
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Algorithm_7_3_9
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

noncomputable section

open Filter Matrix
open scoped Matrix.Norms.Frobenius Matrix.Norms.L2Operator
open scoped LeastSquares

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ResidualVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Domain sampling for this theorem file:
-- * primary domain: exact-stopping trust-region Levenberg-Marquardt asymptotics for nonlinear
--   least-squares on Euclidean spaces;
-- * sampled owner declarations in the minimal Chapter 7 closure:
--   `TrustRegionLevenbergMarquardtAlgorithm`,
--   `leastSquaresGradient`,
--   `gaussNewtonNormalMatrix`,
--   `nonlinearLeastSquaresObjective`,
--   `initialSublevelSet`,
--   `hessianMatrixAt`;
-- * source/core/bridge triage:
--   - source-facing owner here: the exact-stopping/stuttering infinite-run reading used by the
--     source convergence statement;
--   - core/canonical owners reused here: the Chapter 7 trust-region algorithm owner from
--     `Algorithm_7_3_9`, the Chapter 7 least-squares gradient owner `leastSquaresGradient`,
--     the canonical Gauss-Newton normal-matrix owner `gaussNewtonNormalMatrix`, and the
--     canonical least-squares initial sublevel-set owner `initialSublevelSet`.

namespace TrustRegionLevenbergMarquardtAlgorithm

/-- A source-faithful exact-stopping trust-region Levenberg-Marquardt run is a Chapter 7
trust-region Levenberg-Marquardt algorithm with zero stopping tolerance and stationary
continuation after the stopping test fires. The iterate, radius, and trial-step data stay owned
by `TrustRegionLevenbergMarquardtAlgorithm`; this predicate adds only the theorem-level source
semantics used by the convergence statement. -/
structure IsExactStoppingRun
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    (A : TrustRegionLevenbergMarquardtAlgorithm r J) : Prop where
  epsilon_eq_zero : A.ε = 0
  stationaryContinuation (k : ℕ) : A.terminatedAt k → A (k + 1) = A k

attribute [simp] IsExactStoppingRun.epsilon_eq_zero

namespace IsExactStoppingRun

/-- After the stopping test fires, an exact-stopping trust-region Levenberg-Marquardt run stays
at the same iterate. -/
theorem x_eq_succ_of_terminatedAt
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    {A : TrustRegionLevenbergMarquardtAlgorithm r J} (hA : A.IsExactStoppingRun) {k : ℕ}
    (hk : A.terminatedAt k) :
    A (k + 1) = A k :=
  hA.stationaryContinuation k hk

end IsExactStoppingRun

end TrustRegionLevenbergMarquardtAlgorithm

/-- The predicted reduction `Pred_k = q_k(0) - q_k(s_k)` for the trust-region least-squares
model `trustRegionLevenbergMarquardtModel`. -/
def trustRegionLevenbergMarquardtPredictedReduction
    (J : JacobianMatrix) (rk : ResidualVector) (step : Point) : ℝ :=
  trustRegionLevenbergMarquardtModel J rk 0 -
    trustRegionLevenbergMarquardtModel J rk step

/-- The actual-to-predicted reduction ratio `ρ_k = Ared_k / Pred_k`. -/
def trustRegionLevenbergMarquardtReductionRatio
    (r : Point → ResidualVector) (J : JacobianMatrix) (xk step : Point) : ℝ :=
  TrustRegionSubproblem.actualReduction xk (nonlinearLeastSquaresObjective r) step /
    trustRegionLevenbergMarquardtPredictedReduction J (r xk) step

/-- Chapter07 Theorem 7.3.10 (1): let `run` be an exact-stopping trust-region type
Levenberg-Marquardt Algorithm 7.3.9 run for `f(x) = (1 / 2) * ‖r(x)‖²` on the
canonical Jacobian field `residualJacobianMatrix r`. Assume `r` is continuously
differentiable, `f` is twice continuously differentiable, the initial sublevel set
`initialSublevelSet (nonlinearLeastSquaresObjective r) x₀` is bounded, and there exist
constants `M₁` and `M₂` such that `‖∇² f(x)‖ ≤ M₁` and
`‖gaussNewtonNormalMatrix r x‖ ≤ M₂` for every point in that initial sublevel set. Then the
canonical least-squares gradient sequence `g[r](run k)` tends to `0`. -/
theorem trustRegionLevenbergMarquardt_gaussNewtonGradient_tendsto_zero
    (r : Point → ResidualVector)
    (run : TrustRegionLevenbergMarquardtAlgorithm r (residualJacobianMatrix r))
    (hRun : run.IsExactStoppingRun)
    (hCr : ContDiff ℝ 1 r)
    (hC2 : ContDiff ℝ 2 (nonlinearLeastSquaresObjective r))
    (M1 M2 : ℝ)
    (hLevelSetBounded :
      Bornology.IsBounded (initialSublevelSet (nonlinearLeastSquaresObjective r) run.x0))
    (hHessianBound :
      ∀ x ∈ initialSublevelSet (nonlinearLeastSquaresObjective r) run.x0,
        ‖hessianMatrixAt (nonlinearLeastSquaresObjective r) x‖ ≤ M1)
    (hGramBound :
      ∀ x ∈ initialSublevelSet (nonlinearLeastSquaresObjective r) run.x0,
        ‖gaussNewtonNormalMatrix r x‖ ≤ M2) :
    Tendsto (fun k : ℕ ↦ g[r](run k)) atTop (nhds 0) := sorry

/-- Chapter07 Theorem 7.3.10 (2): under the same hypotheses, including
`ContDiff ℝ 1 r` so that `residualJacobianMatrix r` is the source Jacobian field,
the objective gradients satisfy `∇ f(x_k) ⟶ 0`. -/
theorem trustRegionLevenbergMarquardt_objectiveGradient_tendsto_zero
    (r : Point → ResidualVector)
    (run : TrustRegionLevenbergMarquardtAlgorithm r (residualJacobianMatrix r))
    (hRun : run.IsExactStoppingRun)
    (hCr : ContDiff ℝ 1 r)
    (hC2 : ContDiff ℝ 2 (nonlinearLeastSquaresObjective r))
    (M1 M2 : ℝ)
    (hLevelSetBounded :
      Bornology.IsBounded (initialSublevelSet (nonlinearLeastSquaresObjective r) run.x0))
    (hHessianBound :
      ∀ x ∈ initialSublevelSet (nonlinearLeastSquaresObjective r) run.x0,
        ‖hessianMatrixAt (nonlinearLeastSquaresObjective r) x‖ ≤ M1)
    (hGramBound :
      ∀ x ∈ initialSublevelSet (nonlinearLeastSquaresObjective r) run.x0,
        ‖gaussNewtonNormalMatrix r x‖ ≤ M2) :
    Tendsto
      (fun k : ℕ ↦ gradient (nonlinearLeastSquaresObjective r) (run k))
      atTop
      (nhds 0) := sorry

end
