/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Exercise_3_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_1_7

open Filter

/-- Chapter03 Exercise 3.5 (1): the `diag(1, 10000)` quadratic from Exercise 3.2 yields the
explicit `G`-energy decay factor `1 - 2 / 10001`, which is very close to `1`. -/
theorem steepestDescent_diagQuadraticOneTenThousand_energyLinearRate_close_to_one
    (A :
      GeneralUnconstrainedOptimizationMethod 2
        (quadraticObjective diagMatrixOneTenThousand 0 0))
    (h_direction :
      ∀ k : ℕ,
        A.d k =
          steepestDescentDirection
            (quadraticObjective diagMatrixOneTenThousand 0 0)
            (A k)) :
    ∀ k : ℕ,
      ellipsoidNorm diagMatrixOneTenThousand (A k) ≤
        (((1 : ℝ) - 2 / 10001) ^ k) * ellipsoidNorm diagMatrixOneTenThousand (A 0) := by
  have hrate : ((9999 : ℝ) / 10001) = 1 - 2 / 10001 := by
    norm_num
  simpa [hrate] using steepestDescent_diagQuadraticOneTenThousand_energyLinearRate A h_direction

/-- If the curvature ratio `m / M` is at most `ε`, then the Chapter 3 contraction-factor bound
`(M - m) / M` is at least `1 - ε`, so the asymptotic decrease can still be close to `1`. -/
theorem one_sub_le_steepestDescentContractionFactorBound_of_curvatureRatio_le
    {m M ε : ℝ} (hM : 0 < M) (hε : m / M ≤ ε) :
    1 - ε ≤ (M - m) / M := by
  calc
    1 - ε ≤ 1 - m / M := by
      simpa using sub_le_sub_left hε 1
    _ = M / M - m / M := by
      rw [div_self hM.ne']
    _ = (M - m) / M := by
      rw [sub_div]

/-- Chapter03 Exercise 3.5 (2): under the source hypotheses of Theorem 3.1.7, the asymptotic
steepest-descent contraction factor is bounded above by `(M - m) / M`, and if the curvature
ratio `m / M` is at most `ε`, then that same bound is at least `1 - ε`. -/
theorem steepestDescentContractionFactor_limsup_bound_ge_one_sub_of_sourceHypotheses
    {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xStar : EuclideanSpace ℝ (Fin n)}
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (α : ℕ → ℝ)
    {m lambdaMin lambdaMax M ε : ℝ}
    (hC2 : ∃ s ∈ nhds xStar, ContDiffOn ℝ 2 f s)
    (hStationary : IsStationaryPoint f xStar)
    (hLambdaMin :
      IsLeast
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMin)
    (hLambdaMax :
      IsGreatest
        {μ : ℝ | Module.End.HasEigenvalue (hessianAt f xStar).toLinearMap μ}
        lambdaMax)
    (hm : 0 < m)
    (hmMin : m ≤ lambdaMin)
    (hMaxM : lambdaMax ≤ M)
    (hSeq : IsSteepestDescentSequence f x α)
    (hx : Tendsto x atTop (nhds xStar))
    (hGapNe : ∀ k : ℕ, f (x k) ≠ f xStar)
    (hε : m / M ≤ ε) :
    Filter.limsup (steepestDescentContractionFactor f xStar x) atTop ≤ (M - m) / M ∧
      1 - ε ≤ (M - m) / M := by
  have hLambdaMin_le_lambdaMax : lambdaMin ≤ lambdaMax := hLambdaMin.2 hLambdaMax.1
  have hM : 0 < M := lt_of_lt_of_le hm (le_trans hmMin (le_trans hLambdaMin_le_lambdaMax hMaxM))
  constructor
  · exact
      limsup_steepestDescentContractionFactor_le_of_sourceHypotheses
        x α hC2 hStationary hLambdaMin hLambdaMax hm hmMin hMaxM hSeq hx hGapNe
  · exact one_sub_le_steepestDescentContractionFactorBound_of_curvatureRatio_le hM hε
