/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_3

noncomputable section

open Filter Matrix
open scoped LeastSquares
open scoped Matrix.Norms.Elementwise

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)
variable (r : Point → Residual)

-- Semantic recall: the canonical project owner for `Q`-quadratic convergence is
-- `HasQuadraticConvergenceTo` from Chapter 3. The Chapter 7 least-squares objective, Jacobian,
-- correction, Hessian, normal matrix, and step-equation owners already live in `Theorem_7_2_2`,
-- so this file reuses both the Chapter 3 convergence owner and the Chapter 7 Gauss-Newton owners
-- rather than keeping a parallel local rate predicate.

/-- Under the quantitative hypotheses of Theorem 7.2.2, if `r xStar = 0`, then any Gauss-Newton
sequence `x` for `r` satisfying the Theorem 7.2.2 step and convergence hypotheses converges to
`xStar` with `Q`-quadratic rate, encoded by the canonical owner
`HasQuadraticConvergenceTo x xStar`. The zero-residual hypothesis is consumed through the Chapter 7
owner facts that `xStar` globally minimizes `nonlinearLeastSquaresObjective r` on `Set.univ` and
that the source linear coefficient vanishes, while the neighborhood positive-definiteness
hypothesis already supplies the pointwise positive definiteness of
`gaussNewtonNormalMatrix r xStar`. -/
theorem gaussNewton_qQuadraticConvergence_of_zeroResidual
    (x : ℕ → Point) (xStar : Point)
    (hResidualC2 : ContDiff ℝ 2 r)
    (hStep : ∀ k : ℕ, solvesGaussNewtonNormalEquation r (x k) (x (k + 1)))
    (hTendsto : Tendsto x atTop (nhds xStar))
    (hNormalMatrixPosDef :
      ∃ δ > 0, ∀ y : Point,
        y ∈ Metric.ball xStar δ →
          (gaussNewtonNormalMatrix r y).PosDef)
    (hHessianLipschitz :
      ∃ δ > 0, ∃ L > 0, ∀ x y : Point,
        x ∈ Metric.ball xStar δ →
        y ∈ Metric.ball xStar δ →
          ‖G[r](x) - G[r](y)‖ ≤ L * ‖x - y‖)
    (hInverseLipschitz :
      ∃ δ > 0, ∃ L > 0, ∀ x y : Point,
        x ∈ Metric.ball xStar δ →
        y ∈ Metric.ball xStar δ →
          ‖(gaussNewtonNormalMatrix r x)⁻¹ - (gaussNewtonNormalMatrix r y)⁻¹‖ ≤
            L * ‖x - y‖)
    (hResidualZero : r xStar = 0) :
    HasQuadraticConvergenceTo x xStar := by
  rcases hNormalMatrixPosDef with ⟨δ, hδ, hNormalMatrixPosDef⟩
  have hGramPosDef : (gaussNewtonNormalMatrix r xStar).PosDef :=
    hNormalMatrixPosDef xStar <| by
      simpa [Metric.mem_ball] using hδ
  have hNormalMatrixPosDef' :
      ∃ δ > 0, ∀ y : Point,
        y ∈ Metric.ball xStar δ →
          (gaussNewtonNormalMatrix r y).PosDef :=
    ⟨δ, hδ, hNormalMatrixPosDef⟩
  have hMinOn :
      IsMinOn (nonlinearLeastSquaresObjective r) Set.univ xStar :=
    nonlinearLeastSquaresObjective_isMinOn_univ_of_residual_eq_zero r xStar hResidualZero
  have hLocalMin : IsLocalMin (nonlinearLeastSquaresObjective r) xStar :=
    hMinOn.isLocalMin (by simp)
  have hLinearCoeffZero :
      gaussNewtonLinearErrorCoefficient r xStar = 0 :=
    gaussNewtonLinearErrorCoefficient_eq_zero_of_residual_eq_zero r xStar hResidualZero
  have hEventualEstimate :
      ∃ C > 0, ∀ᶠ k : ℕ in atTop,
        ‖x (k + 1) - xStar‖ ≤
          gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ +
            C * ‖x k - xStar‖ ^ (2 : ℕ) :=
    gaussNewton_errorNorm_eventually_le_linear_plus_quadratic r x xStar hResidualC2 hLocalMin hStep
      hGramPosDef hTendsto hNormalMatrixPosDef' hHessianLipschitz hInverseLipschitz
  have hEventualQuadraticEstimate :
      ∃ C > 0, ∀ᶠ k : ℕ in atTop,
        ‖x (k + 1) - xStar‖ ≤ C * ‖x k - xStar‖ ^ (2 : ℕ) := by
    simpa [hLinearCoeffZero] using hEventualEstimate
  rcases hEventualQuadraticEstimate with ⟨C, hC, hEventually⟩
  -- Package the eventual one-step quadratic estimate into the canonical Chapter 3 owner.
  refine ⟨hTendsto, ?_⟩
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hEventually] with k hk
  simpa [Real.norm_eq_abs, abs_of_nonneg hC.le, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)] using hk

/-- Helper for Chapter07 Theorem 7.2.4: when `Fin n` is nonempty, positive definiteness of the
Gauss-Newton normal matrix forces the real spectrum to attain a positive least element. -/
private theorem gaussNewtonNormalMatrix_exists_positive_smallestSpectrum
    (r : Point → Residual) (xStar : Point)
    (hNonempty : Nonempty (Fin n))
    (hPosDef : (gaussNewtonNormalMatrix r xStar).PosDef) :
    ∃ lam > 0, IsLeast (spectrum ℝ (gaussNewtonNormalMatrix r xStar)) lam := by
  classical
  let s : Set ℝ := Set.range (posDefEigenvalues (gaussNewtonNormalMatrix r xStar) hPosDef)
  have hFinite : s.Finite := by
    simpa [s] using
      (Set.finite_range (posDefEigenvalues (gaussNewtonNormalMatrix r xStar) hPosDef))
  have hRangeNonempty : s.Nonempty := by
    let i0 : Fin n := Classical.choice hNonempty
    exact ⟨posDefEigenvalues (gaussNewtonNormalMatrix r xStar) hPosDef i0, ⟨i0, rfl⟩⟩
  obtain ⟨lam, hLeast⟩ := hFinite.isCompact.exists_isLeast hRangeNonempty
  have hLamPos : 0 < lam := by
    rcases (show lam ∈ s from hLeast.1) with ⟨i, hi⟩
    rw [← hi]
    simpa [posDefEigenvalues_def] using hPosDef.eigenvalues_pos i
  have hSpectrum :
      spectrum ℝ (gaussNewtonNormalMatrix r xStar) =
        Set.range (posDefEigenvalues (gaussNewtonNormalMatrix r xStar) hPosDef) := by
    simpa [posDefEigenvalues_def] using hPosDef.isHermitian.spectrum_eq_image_range
  refine ⟨lam, hLamPos, ?_⟩
  rw [hSpectrum]
  simpa [s] using hLeast

/-- Chapter07 Theorem 7.2.4: keep the geometric and regularity hypotheses from Theorem 7.2.3.
If `r xStar = 0`, then the residual-linearization condition is automatic with coefficient `0`, so
the only remaining spectral hypothesis is positive definiteness of the canonical Gauss-Newton
normal matrix at `xStar`. Under these assumptions there exists `ε > 0` such that every
`x0 ∈ Metric.ball xStar ε` admits a Gauss-Newton iterate family `x_k` which stays in `D`,
solves the canonical normal equation at each step, converges to `xStar`, and does so with
`Q`-quadratic convergence rate in the canonical sense `HasQuadraticConvergenceTo x xStar`. -/
theorem gaussNewton_exists_qQuadraticConvergence_of_zeroResidual
    (D : Set Point) (xStar : Point) (α γ : ℝ)
    (hOpen : IsOpen D)
    (hConvex : Convex ℝ D)
    (hxStar : xStar ∈ D)
    (hResidualC2 : ContDiffOn ℝ 2 r D)
    (hJLipschitz :
      ∀ x ∈ D, ∀ y ∈ D,
        ‖(Matrix.toEuclideanLin
            (J[r](x) - J[r](y))).toContinuousLinearMap‖ ≤
          γ * ‖x - y‖)
    (hJBound :
      ∀ x : Point, x ∈ D →
        ‖(Matrix.toEuclideanLin (J[r](x))).toContinuousLinearMap‖ ≤ α)
    (hGramPosDef : (gaussNewtonNormalMatrix r xStar).PosDef)
    (hResidualZero : r xStar = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x0 : Point, x0 ∈ Metric.ball xStar ε →
        ∃ x : ℕ → Point,
          x 0 = x0 ∧
            (∀ k : ℕ, x k ∈ D) ∧
            (∀ k : ℕ, solvesGaussNewtonNormalEquation r (x k) (x (k + 1))) ∧
            HasQuadraticConvergenceTo x xStar := by
  have hStationary : g[r](xStar) = 0 :=
    leastSquaresGradient_eq_zero_of_residual_eq_zero r xStar hResidualZero
  have hResidualLinearization :
      ∀ x : Point, x ∈ D →
        ‖Matrix.toEuclideanLin
            ((J[r](x) - J[r](xStar))ᵀ) (r xStar)‖ ≤
          0 * ‖x - xStar‖ := by
    intro x hx
    simp [hResidualZero]
  -- Route correction: reuse Theorem 7.2.3 at `σ = 0` instead of rebuilding the local analysis.
  by_cases hNonempty : Nonempty (Fin n)
  · classical
    let s : Set ℝ := Set.range (posDefEigenvalues (gaussNewtonNormalMatrix r xStar) hGramPosDef)
    have hFinite : s.Finite := by
      simpa [s] using
        (Set.finite_range (posDefEigenvalues (gaussNewtonNormalMatrix r xStar) hGramPosDef))
    have hRangeNonempty : s.Nonempty := by
      let i0 : Fin n := Classical.choice hNonempty
      exact ⟨posDefEigenvalues (gaussNewtonNormalMatrix r xStar) hGramPosDef i0, ⟨i0, rfl⟩⟩
    obtain ⟨lam, hLeastRange⟩ := hFinite.isCompact.exists_isLeast hRangeNonempty
    have hLamPos : 0 < lam := by
      rcases (show lam ∈ s from hLeastRange.1) with ⟨i, hi⟩
      rw [← hi]
      simpa [posDefEigenvalues_def] using hGramPosDef.eigenvalues_pos i
    have hLeast :
        IsLeast (spectrum ℝ (gaussNewtonNormalMatrix r xStar)) lam := by
      have hSpectrum :
          spectrum ℝ (gaussNewtonNormalMatrix r xStar) =
            Set.range (posDefEigenvalues (gaussNewtonNormalMatrix r xStar) hGramPosDef) := by
        simpa [posDefEigenvalues_def] using hGramPosDef.isHermitian.spectrum_eq_image_range
      rw [hSpectrum]
      simpa [s] using hLeastRange
    have hStrong :
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x0 : Point, x0 ∈ Metric.ball xStar ε →
            ∃ x : ℕ → Point,
              x 0 = x0 ∧
                (∀ k : ℕ, x k ∈ D) ∧
                (∀ k : ℕ, solvesGaussNewtonNormalEquation r (x k) (x (k + 1))) ∧
                HasLinearConvergenceTo x xStar ∧
                (∀ k : ℕ,
                  ‖x (k + 1) - xStar‖ ≤
                    (2 * 0 / lam) * ‖x k - xStar‖ +
                      (2 * α * γ / (2 * lam)) * ‖x k - xStar‖ ^ (2 : ℕ)) ∧
                (∀ k : ℕ,
                  ‖x (k + 1) - xStar‖ ≤
                    ((2 * 0 + lam) / (2 * lam)) * ‖x k - xStar‖) ∧
                ∀ k : ℕ, x k ≠ xStar → ‖x (k + 1) - xStar‖ < ‖x k - xStar‖ := by
      exact gaussNewtonLocalConvergence_of_smallestEigenvalueGap
        D r xStar lam 0 α γ 2
        hOpen hConvex hxStar hResidualC2 hJLipschitz hJBound
        (by norm_num) hStationary hLeast hResidualLinearization
        (by norm_num) (by simpa using hLamPos)
    rcases hStrong with ⟨ε, hε_pos, hLocal⟩
    exact ⟨ε, hε_pos, fun x0 hx0 ↦ by
      rcases hLocal x0 hx0 with
        ⟨x, hxInit, hxD, hxStep, hLinear, hBound1, _hBound2, _hStrict⟩
      have hQuadraticBound :
          ∀ k : ℕ,
            ‖x (k + 1) - xStar‖ ≤
              |2 * α * γ / (2 * lam)| * ‖x k - xStar‖ ^ (2 : ℕ) := by
        intro k
        have hk :
            ‖x (k + 1) - xStar‖ ≤
              (2 * α * γ / (2 * lam)) * ‖x k - xStar‖ ^ (2 : ℕ) := by
          -- The `σ = 0` specialization collapses the mixed linear-plus-quadratic estimate.
          simpa using hBound1 k
        have hPowNonneg : 0 ≤ ‖x k - xStar‖ ^ (2 : ℕ) := by
          positivity
        calc
          ‖x (k + 1) - xStar‖
              ≤ (2 * α * γ / (2 * lam)) * ‖x k - xStar‖ ^ (2 : ℕ) := hk
          _ ≤ |2 * α * γ / (2 * lam)| * ‖x k - xStar‖ ^ (2 : ℕ) := by
                exact mul_le_mul_of_nonneg_right (le_abs_self _) hPowNonneg
      have hQuadratic : HasQuadraticConvergenceTo x xStar :=
        hasQuadraticConvergenceTo_of_tendsto_and_bound
          hLinear.tendsto (abs_nonneg _) hQuadraticBound
      -- Keep the Gauss-Newton orbit data from Theorem 7.2.3 and only upgrade the rate owner.
      exact ⟨x, hxInit, hxD, hxStep, hQuadratic⟩⟩
  · letI : IsEmpty (Fin n) := not_nonempty_iff.mp hNonempty
    exact ⟨1, by norm_num, fun x0 _hx0 ↦ by
      have hx0_eq : x0 = xStar := Subsingleton.elim _ _
      refine ⟨fun _ : ℕ ↦ xStar, ?_, ?_, ?_, ?_⟩
      · simpa [hx0_eq]
      · intro k
        simpa using hxStar
      · intro k
        -- In the zero-dimensional branch the orbit is constant, so the normal equation is trivial.
        rw [solvesGaussNewtonNormalEquation_iff, hStationary]
        simp
      · have hQuadraticConst :
            ∀ k : ℕ,
              ‖(fun _ : ℕ ↦ xStar) (k + 1) - xStar‖ ≤
                (0 : ℝ) * ‖(fun _ : ℕ ↦ xStar) k - xStar‖ ^ (2 : ℕ) := by
          intro k
          simp
        exact
          hasQuadraticConvergenceTo_of_tendsto_and_bound
            tendsto_const_nhds (by norm_num) hQuadraticConst⟩

end
