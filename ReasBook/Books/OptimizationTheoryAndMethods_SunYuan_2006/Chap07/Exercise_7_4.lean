/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_10

noncomputable section

open Filter
open scoped LeastSquares

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ResidualVector" => EuclideanSpace ℝ (Fin m)

-- Domain sampling for this refine pass:
-- * primary domain: trust-region Levenberg-Marquardt local quadratic convergence for nonlinear
--   least squares on Euclidean spaces;
-- * sampled owner declarations in the minimal Chapter 7 closure:
--   `TrustRegionLevenbergMarquardtAlgorithm`,
--   `TrustRegionLevenbergMarquardtAlgorithm.IsExactStoppingRun`,
--   `initialSublevelSet`,
--   `G[_](_)`,
--   `S[_](_)`,
--   `HasQuadraticConvergenceTo`;
-- * best owner abstraction: the canonical Chapter 7 trust-region algorithm object together with
--   the exact-stopping/stuttering Chapter 7 trust-region run owner together with the Chapter 3
--   quadratic-convergence owner;
-- * primitive data: the residual map `r` and the recorded algorithm run `run`;
-- * derived API removed here: the duplicate local trust-region objective/model/feasible-set
--   wrappers, the duplicate local algorithm record, the ad hoc Hessian alias, and the parallel
--   `qQuadraticConvergenceTo` rate predicate.

/-- Chapter07 Exercise 7.4: let `run` be the exact-stopping/stuttering infinite-run reading of a
trust-region type Levenberg-Marquardt Algorithm 7.3.9 run for
`f(x) = (1 / 2) * ∑ i, (r_i(x))^2`. Assume `r` is twice continuously differentiable, so
`residualJacobianMatrix r` is the source Jacobian field and the source least-squares correction
and Hessian owners `S[r](xStar)` and `G[r](xStar)` retain their intended meaning, and the
nonlinear least-squares objective `f` is also twice continuously differentiable. If the level set
`L(x₀) = {x | f x ≤ f x₀}` is bounded, the iterate sequence `run` converges to `xStar`, the
least-squares Hessian `G(xStar)` is positive definite, and
`S(xStar) = ∑ i, r_i(xStar) • ∇² r_i(xStar) = 0`, then `run` converges to `xStar` with
quadratic rate, encoded by the canonical owner `HasQuadraticConvergenceTo run xStar`. -/
theorem trustRegionLevenbergMarquardt_qQuadraticConvergence_of_tendsto
    (r : Point → ResidualVector)
    (run : TrustRegionLevenbergMarquardtAlgorithm r (residualJacobianMatrix r))
    (hRun : run.IsExactStoppingRun)
    (xStar : Point)
    (hResidualC2 : ContDiff ℝ 2 r)
    (hLevelSetBounded :
      Bornology.IsBounded (initialSublevelSet (nonlinearLeastSquaresObjective r) run.x0))
    (hTendsto : Tendsto run atTop (nhds xStar))
    (hHessianPosDef : (G[r](xStar)).PosDef)
    (hCorrectionVanishes : S[r](xStar) = 0) :
    HasQuadraticConvergenceTo run xStar := by
  sorry

end
