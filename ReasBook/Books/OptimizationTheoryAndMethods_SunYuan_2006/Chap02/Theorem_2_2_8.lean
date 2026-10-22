/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Lemma_2_2_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_4

noncomputable section

open Filter
open scoped Gradient

section

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [CompleteSpace Point]

-- Domain sampling:
-- * primary domain: local linear convergence for exact line-search iterates near a local
--   minimizer;
-- * owner declarations inspected in this domain:
--   `IsExactLineSearchStepOnNonnegativeRay` from Chapter 2,
--   the local minimizer owner `IsLocalMin` used by `Lemma_2_2_7`,
--   the Chapter 3 convergence owners `HasEventuallyLinearConvergenceTo`,
--   `HasLinearConvergenceTo`,
--   and the Chapter 1 rate owners `rAtLeastLinearConvergenceTo`,
--   `IsNonnegErrorMajorant`, `HasQLinearConvergenceTo`,
--   `rLinearConvergenceTo`, `rLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant`;
-- * triage:
--   * source-facing data: the iterate, direction, and step sequences with the local minimizer,
--     uniform angle bound, and local regularity/Hessian hypotheses;
--   * core/canonical owner for the source conclusion "at least linearly": the Chapter 1 owner
--     `rAtLeastLinearConvergenceTo`;
--   * stricter derived companions only: the global contraction owner
--     `HasLinearConvergenceTo`, and the Chapter 1 rate owner `rLinearConvergenceTo` together
--     with its equivalent nonnegative `Q`-linear majorant witness; these require stronger
--     data than the source-facing local hypotheses alone;
-- * primitive data are the iterate, direction, and step sequences together with the local
--   minimizer, uniform angle bound, and local regularity/Hessian hypotheses. The scalar majorant
--   witness and the strict `R`-linear rate are derived API beyond the source-facing
--   at-least-`R`-linear owner and should not be the primary public theorem surface here.

variable (f : Point → ℝ) (x d : ℕ → Point) (α : ℕ → ℝ) (xStar : Point) (ε m M μ : ℝ)
variable
  (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
  (h_exactLineSearch : ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
  (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
  (h_hasGradientAt : ∀ k : ℕ, HasGradientAt f (∇ f (x k)) (x k))
  (h_tendsto : Tendsto x atTop (nhds xStar))
  (h_localMin : IsLocalMin f xStar)
  (hμ : 0 < μ)
  (h_angle :
    ∀ k : ℕ, ∇ f (x k) ≠ 0 →
      InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
  (hε : 0 < ε)
  (hC2 : ContDiffOn ℝ 2 f (Metric.ball xStar ε))
  (hm : 0 < m)
  (h_hessianLower :
    ∀ ⦃z : Point⦄, z ∈ Metric.ball xStar ε → ∀ y : Point,
      m * ‖y‖ ^ (2 : ℕ) ≤ inner ℝ y ((fderiv ℝ (∇ f) z) y))
  (h_hessianUpper :
    ∀ ⦃z : Point⦄, z ∈ Metric.ball xStar ε → ∀ y : Point,
      inner ℝ y ((fderiv ℝ (∇ f) z) y) ≤ M * ‖y‖ ^ (2 : ℕ))

include f x d α xStar ε m M μ h_descent h_exactLineSearch h_update h_hasGradientAt h_tendsto
  h_localMin hμ h_angle hε hC2 hm h_hessianLower h_hessianUpper

omit [NormedAddCommGroup Point] [InnerProductSpace ℝ Point] [CompleteSpace Point]
  f x d α xStar ε m M μ h_descent h_exactLineSearch h_update h_hasGradientAt h_tendsto
  h_localMin hμ h_angle hε hC2 hm h_hessianLower h_hessianUpper in
/-- Helper for Chapter02 Theorem 2.2.8: a positive multiple of a geometric sequence with
ratio `β ∈ (0, 1)` is `Q`-linearly convergent to `0`. -/
lemma scaledGeometric_hasQLinearConvergenceTo_zero
    {C β : ℝ} (hC : 0 < C) (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasQLinearConvergenceTo (fun k : ℕ ↦ C * β ^ (k + 1)) 0 := by
  -- Use the geometric ratio `β` as the textbook `Q`-linear witness.
  refine ⟨β, hβ1, ?_⟩
  refine
    { one_le := by norm_num
      beta_pos := hβ0
      tendsto := ?_
      ratio_tendsto := ?_ }
  · -- The geometric factor tends to `0`, and the positive scalar multiple preserves that limit.
    have hpow : Tendsto (fun n : ℕ ↦ β ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hpow.const_mul (C * β)
  · -- The first-order quotient is identically `β` on this geometric sequence.
    have hratio :
        qErrorRatio (fun k : ℕ ↦ C * β ^ (k + 1)) 0 1 = fun _ : ℕ ↦ β := by
      funext k
      have hkpow : C * β ^ (k + 1) ≠ 0 := by positivity
      calc
        qErrorRatio (fun k : ℕ ↦ C * β ^ (k + 1)) 0 1 k
            = (C * β ^ (k + 2)) / (C * β ^ (k + 1)) := by
                rw [qErrorRatio_apply]
                simp [abs_of_nonneg, hC.le, hβ0.le]
        _ = β := by
          rw [pow_succ']
          field_simp [hkpow]
    rw [hratio]
    simp

omit [InnerProductSpace ℝ Point] [CompleteSpace Point] f d α ε m M μ h_descent
  h_exactLineSearch h_update h_hasGradientAt h_tendsto h_localMin hμ h_angle hε hC2 hm
  h_hessianLower h_hessianUpper in
/-- Helper for Chapter02 Theorem 2.2.8: eventual linear contraction yields a global
nonnegative geometric majorant after padding the finite prefix by one constant. -/
lemma existsNonnegQLinearMajorant_of_hasEventuallyLinearConvergenceTo
    (hLinear : HasEventuallyLinearConvergenceTo x xStar) :
    ∃ q : ℕ → ℝ, IsNonnegErrorMajorant x xStar q ∧ HasQLinearConvergenceTo q 0 := by
  rcases hLinear.eventualContraction with ⟨c, hc, hcontract⟩
  rcases eventually_atTop.1 hcontract with ⟨N, hN⟩
  let C0 : ℝ := (Finset.range (N + 1)).sup' (by simp) (fun j ↦ ‖x j - xStar‖ / c ^ (j + 1))
  let C : ℝ := max 1 C0
  let q : ℕ → ℝ := fun k ↦ C * c ^ (k + 1)
  have hc0 : 0 < c := hc.1
  have hC : 0 < C := by
    -- The padded prefix constant is kept strictly positive so the `Q`-ratio witness is genuine.
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 C0)
  have htail :
      ∀ n : ℕ, ‖x (N + n) - xStar‖ ≤ ‖x N - xStar‖ * c ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        have hstep :
            ‖x (N + n + 1) - xStar‖ ≤ c * ‖x (N + n) - xStar‖ := by
          simpa [Nat.add_assoc] using hN (N + n) (Nat.le_add_right N n)
        calc
          ‖x (N + n + 1) - xStar‖ ≤ c * ‖x (N + n) - xStar‖ := hstep
          _ ≤ c * (‖x N - xStar‖ * c ^ n) := by
                gcongr
          _ = ‖x N - xStar‖ * c ^ (n + 1) := by
                rw [pow_succ']
                ring
  have hprefix_bound :
      ∀ k : ℕ, k ≤ N → ‖x k - xStar‖ ≤ C * c ^ (k + 1) := by
    intro k hk
    have hk_mem : k ∈ Finset.range (N + 1) := by
      simpa using Nat.lt_succ_of_le hk
    have hk_sup :
        ‖x k - xStar‖ / c ^ (k + 1) ≤ C0 := by
      exact Finset.le_sup' (f := fun j ↦ ‖x j - xStar‖ / c ^ (j + 1)) hk_mem
    have hk_pow_pos : 0 < c ^ (k + 1) := pow_pos hc0 _
    have hkC0 : ‖x k - xStar‖ ≤ C0 * c ^ (k + 1) := by
      exact (div_le_iff₀ hk_pow_pos).mp hk_sup
    calc
      ‖x k - xStar‖ ≤ C0 * c ^ (k + 1) := hkC0
      _ ≤ C * c ^ (k + 1) := by
            gcongr
            exact le_max_right 1 C0
  have hmajorant : IsNonnegErrorMajorant x xStar q := by
    refine ⟨?_, ?_⟩
    · -- The geometric majorant is pointwise nonnegative.
      intro k
      exact mul_nonneg hC.le (pow_nonneg hc0.le _)
    · intro k
      by_cases hk : k ≤ N
      · -- The padded prefix constant dominates every iterate before the contraction tail starts.
        exact hprefix_bound k hk
      · have hNk : N ≤ k := le_of_not_ge hk
        have hk_tail :
            ‖x k - xStar‖ ≤ ‖x N - xStar‖ * c ^ (k - N) := by
          simpa [Nat.add_sub_of_le hNk] using htail (k - N)
        have hN_bound : ‖x N - xStar‖ ≤ C * c ^ (N + 1) :=
          hprefix_bound N le_rfl
        calc
          ‖x k - xStar‖ ≤ ‖x N - xStar‖ * c ^ (k - N) := hk_tail
          _ ≤ (C * c ^ (N + 1)) * c ^ (k - N) := by
                gcongr
          _ = C * c ^ (k + 1) := by
                calc
                  (C * c ^ (N + 1)) * c ^ (k - N)
                      = C * (c ^ (N + 1) * c ^ (k - N)) := by ring
                  _ = C * c ^ (N + 1 + (k - N)) := by rw [← pow_add]
                  _ = C * c ^ (k + 1) := by
                      congr 2
                      calc
                        N + 1 + (k - N) = N + (k - N) + 1 := by omega
                        _ = k + 1 := by rw [Nat.add_sub_of_le hNk]
    -- Package the explicit geometric witness as the Chapter 1 `Q`-linear majorant.
  exact
    ⟨q, hmajorant,
      scaledGeometric_hasQLinearConvergenceTo_zero hC hc0 hc.2⟩

omit [InnerProductSpace ℝ Point] [CompleteSpace Point] f d α ε m M μ h_descent
  h_exactLineSearch h_update h_hasGradientAt h_tendsto h_localMin hμ h_angle hε hC2 hm
  h_hessianLower h_hessianUpper in
/-- Helper for Chapter02 Theorem 2.2.8: a geometric tail bound
`‖x (N + n) - xStar‖ ≤ K * β ^ n` with `β ∈ (0, 1)` extends to a global nonnegative
`Q`-linear majorant after padding the finite prefix by one constant. -/
lemma existsNonnegQLinearMajorant_of_tailGeometricBound
    {N : ℕ} {K β : ℝ}
    (_hK : 0 ≤ K)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (htail : ∀ n : ℕ, ‖x (N + n) - xStar‖ ≤ K * β ^ n) :
    ∃ q : ℕ → ℝ, IsNonnegErrorMajorant x xStar q ∧ HasQLinearConvergenceTo q 0 := by
  let A : ℝ := K / β ^ (N + 1)
  let C0 : ℝ := (Finset.range (N + 1)).sup' (by simp) (fun j ↦ ‖x j - xStar‖ / β ^ (j + 1))
  let C : ℝ := max 1 (max A C0)
  let q : ℕ → ℝ := fun k ↦ C * β ^ (k + 1)
  have hC : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (max A C0))
  have hA_le : A ≤ C := by
    exact le_trans (le_max_left A C0) (le_max_right 1 (max A C0))
  have hC0_le : C0 ≤ C := by
    exact le_trans (le_max_right A C0) (le_max_right 1 (max A C0))
  have hprefix_bound :
      ∀ k : ℕ, k ≤ N → ‖x k - xStar‖ ≤ C * β ^ (k + 1) := by
    intro k hk
    have hk_mem : k ∈ Finset.range (N + 1) := by
      simpa using Nat.lt_succ_of_le hk
    have hk_sup :
        ‖x k - xStar‖ / β ^ (k + 1) ≤ C0 := by
      exact Finset.le_sup' (f := fun j ↦ ‖x j - xStar‖ / β ^ (j + 1)) hk_mem
    have hk_pow_pos : 0 < β ^ (k + 1) := by
      exact pow_pos hβ0 _
    have hkC0 :
        ‖x k - xStar‖ ≤ C0 * β ^ (k + 1) := by
      exact (div_le_iff₀ hk_pow_pos).mp hk_sup
    calc
      ‖x k - xStar‖ ≤ C0 * β ^ (k + 1) := hkC0
      _ ≤ C * β ^ (k + 1) := by
            gcongr
  have htail_bound :
      ∀ k : ℕ, N ≤ k → ‖x k - xStar‖ ≤ A * β ^ (k + 1) := by
    intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hβpow_pos : 0 < β ^ (N + 1) := by
      exact pow_pos hβ0 _
    have hAeq :
        A * β ^ (N + n + 1) = K * β ^ n := by
      dsimp [A]
      rw [show N + n + 1 = (N + 1) + n by omega, pow_add]
      field_simp [hβpow_pos.ne']
      ring
    calc
      ‖x (N + n) - xStar‖ ≤ K * β ^ n := htail n
      _ = A * β ^ (N + n + 1) := hAeq.symm
  have hmajorant : IsNonnegErrorMajorant x xStar q := by
    refine ⟨?_, ?_⟩
    · -- The padded geometric witness is pointwise nonnegative.
      intro k
      exact mul_nonneg hC.le (pow_nonneg hβ0.le _)
    · intro k
      by_cases hk : k ≤ N
      · -- The finite prefix is absorbed into the padding constant `C`.
        exact hprefix_bound k hk
      · -- The explicit tail estimate is rescaled to the global geometric template.
        have hNk : N ≤ k := le_of_not_ge hk
        calc
          ‖x k - xStar‖ ≤ A * β ^ (k + 1) := htail_bound k hNk
          _ ≤ C * β ^ (k + 1) := by
                gcongr
  exact
    ⟨q, hmajorant,
      scaledGeometric_hasQLinearConvergenceTo_zero hC hβ0 hβ1⟩

omit x d α m μ h_descent h_exactLineSearch h_update h_hasGradientAt h_tendsto h_localMin
  hμ h_angle hε hm h_hessianLower in
/-- Helper for Chapter02 Theorem 2.2.8: on a ball-contained exact-step segment, every trial
step `a ∈ [0, αk]` satisfies the quadratic upper model coming from the local Hessian quadratic
upper bound. -/
lemma lineSearchObjective_le_base_add_linear_add_quadratic_onIcc_of_hessianQuadraticBound
    {xk dk : Point} {αk a : ℝ}
    (hαk : 0 < αk)
    (ha : a ∈ Set.Icc (0 : ℝ) αk)
    (h_segment : segment ℝ xk (xk + αk • dk) ⊆ Metric.ball xStar ε) :
    lineSearchObjective f xk dk a ≤
      lineSearchObjective f xk dk 0 + a * inner ℝ (∇ f xk) dk +
        (M / 2) * a ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) := by
  -- Restrict the ball-contained exact-step segment to the shorter trial segment.
  have h_segmenta : segment ℝ xk (xk + a • dk) ⊆ Metric.ball xStar ε := by
    intro z hz
    exact h_segment (searchRay_segment_subset_of_nonneg_le_step xk dk hαk ha.1 ha.2 hz)
  let φ : ℝ → ℝ := lineSearchObjective f xk (a • dk)
  have hφC2 : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) 1) := by
    simpa [φ] using unitIntervalTraceContDiffOn f xk dk a h_segmenta hC2
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := φ) (x := 1) (x₀ := 0) (n := 1) zero_ne_one hφC2
  have hξu : ξ ∈ Set.uIcc (0 : ℝ) 1 := by
    exact ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hξBall : xk + ξ • (a • dk) ∈ Metric.ball xStar ε :=
    unitIntervalTraceMapsToDomain xk dk a h_segmenta hξu
  have hsecond_bound :
      iteratedDeriv 2 φ ξ ≤ a ^ (2 : ℕ) * (M * ‖dk‖ ^ (2 : ℕ)) := by
    calc
      iteratedDeriv 2 φ ξ =
          iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) ξ := by
            symm
            exact iteratedDerivWithin_eq_iteratedDeriv
              (by
                simpa [Set.uIcc_of_le zero_le_one] using
                  uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
              (by
                change ContDiffAt ℝ 2 (f ∘ fun s : ℝ ↦ xk + s • (a • dk)) ξ
                exact (hC2.contDiffAt (Metric.isOpen_ball.mem_nhds hξBall)).comp ξ
                  (unitIntervalTraceContDiff xk dk a).contDiffAt)
              hξu
      _ = a ^ (2 : ℕ) * inner ℝ dk
            ((fderiv ℝ (fun z ↦ (InnerProductSpace.toDual ℝ Point).symm (fderiv ℝ f z))
                (xk + ξ • (a • dk))) dk) := by
            simpa [φ] using
              unitIntervalTraceSecondIteratedDeriv f xk dk a ξ Metric.isOpen_ball
                h_segmenta hC2 hξu
      _ = a ^ (2 : ℕ) * inner ℝ dk ((fderiv ℝ (∇ f) (xk + ξ • (a • dk))) dk) := by
            rw [show
              fderiv ℝ (fun z ↦ (InnerProductSpace.toDual ℝ Point).symm (fderiv ℝ f z))
                  (xk + ξ • (a • dk)) =
                fderiv ℝ (∇ f) (xk + ξ • (a • dk)) by rfl]
      _ ≤ a ^ (2 : ℕ) * (M * ‖dk‖ ^ (2 : ℕ)) := by
            gcongr
            exact h_hessianUpper hξBall dk
  have hfirst :
      iteratedDerivWithin 1 φ (Set.uIcc (0 : ℝ) 1) 0 =
        a * inner ℝ (∇ f xk) dk :=
    unitIntervalTraceFirstIteratedDerivZero f xk dk a Metric.isOpen_ball h_segmenta hC2
  have hTaylor' :
      φ 1 =
        φ 0 + a * inner ℝ (∇ f xk) dk + iteratedDeriv 2 φ ξ / 2 := by
    -- Expand the order-one Taylor polynomial and keep the Lagrange remainder explicit.
    have hbase :
        φ 1 - taylorWithinEval φ 1 (Set.uIcc (0 : ℝ) 1) 0 1 = iteratedDeriv 2 φ ξ / 2 := by
      simpa [pow_two] using hTaylor
    rw [taylorWithinEval_succ, taylor_within_zero_eval] at hbase
    rw [hfirst] at hbase
    norm_num at hbase
    have hbase' :
        φ 1 - (φ 0 + a * inner ℝ (∇ f xk) dk) = iteratedDeriv 2 φ ξ / 2 := by
      simpa [gradient] using hbase
    calc
      φ 1 = (φ 1 - (φ 0 + a * inner ℝ (∇ f xk) dk)) + (φ 0 + a * inner ℝ (∇ f xk) dk) := by
              ring
      _ = iteratedDeriv 2 φ ξ / 2 + (φ 0 + a * inner ℝ (∇ f xk) dk) := by
            rw [hbase']
      _ = φ 0 + a * inner ℝ (∇ f xk) dk + iteratedDeriv 2 φ ξ / 2 := by
            ring
  -- Evaluate the Taylor remainder at the trial step and insert the Hessian quadratic bound.
  calc
    lineSearchObjective f xk dk a = φ 1 := by
      simp [φ, lineSearchObjective_apply, smul_smul]
    _ = φ 0 + a * inner ℝ (∇ f xk) dk + iteratedDeriv 2 φ ξ / 2 := hTaylor'
    _ ≤ φ 0 + a * inner ℝ (∇ f xk) dk +
          (a ^ (2 : ℕ) * (M * ‖dk‖ ^ (2 : ℕ))) / 2 := by
            gcongr
    _ = lineSearchObjective f xk dk 0 + a * inner ℝ (∇ f xk) dk +
          (M / 2) * a ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) := by
            simp [φ, lineSearchObjective_zero]
            ring

omit h_tendsto h_localMin hε in
/-- Helper for Chapter02 Theorem 2.2.8: once two consecutive iterates lie in the local ball,
exact line search yields the textbook decrease
`((sin μ)^2 / (2 * M)) * ‖∇ f (x k)‖^2 ≤ f (x k) - f (x (k + 1))`. -/
lemma exactLineSearch_drop_ge_sinSq_mul_gradientNormSq_div_twoMulM
    {k : ℕ}
    (hxk : x k ∈ Metric.ball xStar ε)
    (hxk1 : x (k + 1) ∈ Metric.ball xStar ε) :
    ((Real.sin μ) ^ (2 : ℕ) / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) ≤
      f (x k) - f (x (k + 1)) := by
  by_cases hgrad : ∇ f (x k) = 0
  · -- The stationary case reduces to plain objective monotonicity.
    have hopt :
        lineSearchObjective f (x k) (d k) (α k) ≤
          lineSearchObjective f (x k) (d k) 0 :=
      (h_exactLineSearch k).optimal (by simp)
    have hstep : f (x (k + 1)) ≤ f (x k) := by
      simpa [lineSearchObjective_apply, lineSearchObjective_zero, h_update k] using hopt
    simp [hgrad]
    linarith
  · have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k hgrad
    have hdk_ne : d k ≠ 0 := hdesc.direction_ne
    have hnorm_sq_pos : 0 < ‖d k‖ ^ (2 : ℕ) := by
      exact pow_pos (norm_pos_iff.mpr hdk_ne) 2
    have hm_le_M : m ≤ M := by
      have hcompare :
          m * ‖d k‖ ^ (2 : ℕ) ≤ M * ‖d k‖ ^ (2 : ℕ) := by
        exact le_trans (h_hessianLower hxk (d k)) (h_hessianUpper hxk (d k))
      exact le_of_mul_le_mul_right (by simpa [mul_comm] using hcompare) hnorm_sq_pos
    have hMpos : 0 < M := lt_of_lt_of_le hm hm_le_M
    have hαk : 0 < α k :=
      exactLineSearchStep_pos_of_descent f (x k) (d k) (α k) hdesc (h_exactLineSearch k)
    have hsegment :
        segment ℝ (x k) (x k + α k • d k) ⊆ Metric.ball xStar ε := by
      simpa [h_update k] using (convex_ball xStar ε).segment_subset hxk hxk1
    have hDiff0 : DifferentiableAt ℝ f (x k) := (h_hasGradientAt k).differentiableAt
    have hDiffStep : DifferentiableAt ℝ f (x (k + 1)) :=
      (h_hasGradientAt (k + 1)).differentiableAt
    have hstationary : inner ℝ (∇ f (x (k + 1))) (d k) = 0 := by
      -- Exact optimality at the positive step forces the directional derivative to vanish.
      have hnhds : Set.Ici 0 ∈ nhds (α k) := Ici_mem_nhds hαk
      have hlocal : IsLocalMin (lineSearchObjective f (x k) (d k)) (α k) :=
        (h_exactLineSearch k).isMinOn.isLocalMin hnhds
      have hderivzero : deriv (lineSearchObjective f (x k) (d k)) (α k) = 0 :=
        hlocal.deriv_eq_zero
      have hderiv :
          deriv (lineSearchObjective f (x k) (d k)) (α k) =
            inner ℝ (∇ f (x (k + 1))) (d k) := by
        simpa [h_update k] using
          deriv_lineSearchObjective_apply f (x k) (d k) (α k)
            (by simpa [h_update k] using hDiffStep)
      rw [hderivzero] at hderiv
      simpa [eq_comm] using hderiv
    let ψ : ℝ → ℝ := lineSearchObjective f (x k) (α k • d k)
    have hψC2 : ContDiffOn ℝ 2 ψ (Set.uIcc (0 : ℝ) 1) := by
      simpa [ψ] using unitIntervalTraceContDiffOn f (x k) (d k) (α k) hsegment hC2
    have hψDiff1 : DifferentiableAt ℝ ψ 1 := by
      -- The endpoint `1` of the rescaled profile is the exact step.
      have hDiffStep' : DifferentiableAt ℝ f (x k + (1 : ℝ) • (α k • d k)) := by
        simpa [h_update k, one_smul] using hDiffStep
      change DifferentiableAt ℝ (f ∘ fun t : ℝ ↦ x k + t • (α k • d k)) 1
      simpa [one_smul] using
        hDiffStep'.comp 1 (unitIntervalTraceHasDerivAt (x k) (d k) (α k) 1).differentiableAt
    have hψDeriv0 : deriv ψ 0 = α k * inner ℝ (∇ f (x k)) (d k) := by
      -- Differentiate the rescaled line-search profile at the base point.
      calc
        deriv ψ 0 = inner ℝ (∇ f (x k)) (α k • d k) := by
          simpa [ψ, zero_smul] using
            deriv_lineSearchObjective_apply f (x k) (α k • d k) 0
              (by simpa [zero_smul] using hDiff0)
        _ = α k * inner ℝ (∇ f (x k)) (d k) := by
          rw [inner_smul_right, mul_comm]
    have hψDeriv0neg : deriv ψ 0 < 0 := by
      rw [hψDeriv0]
      nlinarith [hdesc.inner_gradient_neg, hαk]
    have hψDeriv1 : deriv ψ 1 = 0 := by
      -- The rescaled endpoint derivative is the exact-step stationarity equation.
      calc
        deriv ψ 1 = inner ℝ (∇ f (x k + 1 • (α k • d k))) (α k • d k) := by
          simpa [ψ, one_smul] using
            deriv_lineSearchObjective_apply f (x k) (α k • d k) 1
              (by simpa [h_update k, one_smul] using hDiffStep)
        _ = α k * inner ℝ (∇ f (x (k + 1))) (d k) := by
          simp [h_update k, inner_smul_right]
        _ = 0 := by simp [hstationary]
    have hψSecond :
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          iteratedDeriv 2 ψ t ≤ M * α k ^ (2 : ℕ) * ‖d k‖ ^ (2 : ℕ) := by
      intro t ht
      have htu : t ∈ Set.uIcc (0 : ℝ) 1 := Set.mem_uIcc_of_le ht.1 ht.2
      have hz : x k + t • (α k • d k) ∈ Metric.ball xStar ε :=
        unitIntervalTraceMapsToDomain (x k) (d k) (α k) hsegment htu
      calc
        iteratedDeriv 2 ψ t =
            iteratedDerivWithin 2 ψ (Set.uIcc (0 : ℝ) 1) t := by
              symm
              exact iteratedDerivWithin_eq_iteratedDeriv
                (by
                  simpa [Set.uIcc_of_le zero_le_one] using
                    uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
                (by
                  change ContDiffAt ℝ 2 (f ∘ fun s : ℝ ↦ x k + s • (α k • d k)) t
                  exact (hC2.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).comp t
                    (unitIntervalTraceContDiff (x k) (d k) (α k)).contDiffAt)
                htu
      _ = α k ^ (2 : ℕ) * inner ℝ (d k)
              ((fderiv ℝ (fun z ↦ (InnerProductSpace.toDual ℝ Point).symm (fderiv ℝ f z))
                  (x k + t • (α k • d k))) (d k)) := by
                simpa [ψ] using
                  unitIntervalTraceSecondIteratedDeriv f (x k) (d k) (α k) t Metric.isOpen_ball
                    hsegment hC2 htu
        _ = α k ^ (2 : ℕ) * inner ℝ (d k) ((fderiv ℝ (∇ f) (x k + t • (α k • d k))) (d k)) := by
              rw [show
                fderiv ℝ (fun z ↦ (InnerProductSpace.toDual ℝ Point).symm (fderiv ℝ f z))
                    (x k + t • (α k • d k)) =
                  fderiv ℝ (∇ f) (x k + t • (α k • d k)) by rfl]
        _ ≤ α k ^ (2 : ℕ) * (M * ‖d k‖ ^ (2 : ℕ)) := by
              gcongr
              exact h_hessianUpper hz (d k)
        _ = M * α k ^ (2 : ℕ) * ‖d k‖ ^ (2 : ℕ) := by
              ring
    have htrial_le_unit :
        -(deriv ψ 0) / (M * α k ^ (2 : ℕ) * ‖d k‖ ^ (2 : ℕ)) ≤ (1 : ℝ) := by
      have hψC2_Icc : ContDiffOn ℝ 2 ψ (Set.Icc (0 : ℝ) 1) := by
        simpa [Set.uIcc_of_le zero_le_one] using hψC2
      exact endpoint_ge_negDeriv_div_secondDerivBound
        (a := 1) (M := M * α k ^ (2 : ℕ) * ‖d k‖ ^ (2 : ℕ))
        (by norm_num) hψC2_Icc hψDiff1 hψDeriv0neg hψDeriv1
        (by positivity)
        hψSecond
    let αbar : ℝ := -(inner ℝ (∇ f (x k)) (d k)) / (M * ‖d k‖ ^ (2 : ℕ))
    have hαbar_nonneg : 0 ≤ αbar := by
      -- The descent-direction hypothesis makes the textbook trial step nonnegative.
      refine div_nonneg ?_ ?_
      · linarith [hdesc.inner_gradient_neg]
      · positivity
    have htrial_clear :
        -(inner ℝ (∇ f (x k)) (d k)) ≤ M * α k * ‖d k‖ ^ (2 : ℕ) := by
      have htrial_le_unit' := htrial_le_unit
      rw [hψDeriv0] at htrial_le_unit'
      have hnorm_sq_ne : ‖d k‖ ^ (2 : ℕ) ≠ 0 := by
        exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hdk_ne)
      have hαk_sq_ne : α k ^ (2 : ℕ) ≠ 0 := by
        exact pow_ne_zero 2 hαk.ne'
      field_simp [hMpos.ne', hαk_sq_ne, hnorm_sq_ne] at htrial_le_unit'
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using htrial_le_unit'
    have hαbar_le : αbar ≤ α k := by
      have hdenom_pos : 0 < M * ‖d k‖ ^ (2 : ℕ) := by
        positivity
      refine (div_le_iff₀ hdenom_pos).2 ?_
      simpa [αbar, mul_assoc, mul_left_comm, mul_comm] using htrial_clear
    have hαbar_mem : αbar ∈ Set.Icc (0 : ℝ) (α k) := ⟨hαbar_nonneg, hαbar_le⟩
    have htrial_model :
        lineSearchObjective f (x k) (d k) αbar ≤
          lineSearchObjective f (x k) (d k) 0 +
            αbar * inner ℝ (∇ f (x k)) (d k) +
              (M / 2) * αbar ^ (2 : ℕ) * ‖d k‖ ^ (2 : ℕ) :=
      lineSearchObjective_le_base_add_linear_add_quadratic_onIcc_of_hessianQuadraticBound
        (f := f) (xStar := xStar) (ε := ε) (M := M) (hC2 := hC2)
        (h_hessianUpper := h_hessianUpper)
        hαk hαbar_mem hsegment
    have hexact_compare :
        f (x k) - f (x (k + 1)) ≥ f (x k) - f (x k + αbar • d k) := by
      -- Exact line search compares the true step with the textbook trial step `αbar`.
      have hopt :
          lineSearchObjective f (x k) (d k) (α k) ≤ lineSearchObjective f (x k) (d k) αbar :=
        (h_exactLineSearch k).optimal hαbar_nonneg
      simpa [lineSearchObjective_apply, h_update k] using sub_le_sub_left hopt (f (x k))
    have htrial_decrease :
        f (x k) - f (x k + αbar • d k) ≥
          (inner ℝ (∇ f (x k)) (d k)) ^ (2 : ℕ) /
            (2 * M * ‖d k‖ ^ (2 : ℕ)) := by
      -- Evaluate the quadratic model at the minimizing trial step.
      have hmodel :
          f (x k + αbar • d k) ≤
            f (x k) + αbar * inner ℝ (∇ f (x k)) (d k) +
              (M / 2) * αbar ^ (2 : ℕ) * ‖d k‖ ^ (2 : ℕ) := by
        simpa [lineSearchObjective_apply, lineSearchObjective_zero] using htrial_model
      have hmodel' :
          f (x k) - f (x k + αbar • d k) ≥
            -(αbar * inner ℝ (∇ f (x k)) (d k)) -
              (M / 2) * αbar ^ (2 : ℕ) * ‖d k‖ ^ (2 : ℕ) := by
        nlinarith [hmodel]
      have hnorm_sq_ne : ‖d k‖ ^ (2 : ℕ) ≠ 0 := by
        exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hdk_ne)
      have hαbar_eval :
          -(αbar * inner ℝ (∇ f (x k)) (d k)) -
              (M / 2) * αbar ^ (2 : ℕ) * ‖d k‖ ^ (2 : ℕ) =
            (inner ℝ (∇ f (x k)) (d k)) ^ (2 : ℕ) /
              (2 * M * ‖d k‖ ^ (2 : ℕ)) := by
        unfold αbar
        field_simp [hMpos.ne', hnorm_sq_ne]
        ring
      rw [hαbar_eval] at hmodel'
      exact hmodel'
    have hangle_nonneg :
        0 ≤ InnerProductGeometry.angle (d k) (-(∇ f (x k))) :=
      InnerProductGeometry.angle_nonneg _ _
    have hhalf_pi_minus_mu_nonneg : 0 ≤ Real.pi / 2 - μ := by
      linarith [hangle_nonneg, h_angle k hgrad]
    have hcos_lower :
        Real.sin μ ≤ Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) := by
      have hcos :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          hangle_nonneg
          (by linarith [Real.pi_pos])
          (h_angle k hgrad)
      simpa [Real.cos_pi_div_two_sub] using hcos
    have hsin_nonneg : 0 ≤ Real.sin μ := by
      exact Real.sin_nonneg_of_nonneg_of_le_pi hμ.le (by linarith [Real.pi_pos])
    have hcos_nonneg :
        0 ≤ Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) := by
      refine Real.cos_nonneg_of_mem_Icc ?_
      constructor
      · linarith [hangle_nonneg, Real.pi_pos]
      · linarith [h_angle k hgrad, hμ, Real.pi_pos]
    have hcos_sq_lower :
        (Real.sin μ) ^ (2 : ℕ) ≤
          (Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k))))) ^ (2 : ℕ) := by
      nlinarith
    have hcos_rewrite :
        (1 / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) *
            (Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k))))) ^ (2 : ℕ) =
          (inner ℝ (∇ f (x k)) (d k)) ^ (2 : ℕ) /
            (2 * M * ‖d k‖ ^ (2 : ℕ)) := by
      calc
        (1 / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) *
            (Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k))))) ^ (2 : ℕ)
            =
          (1 / (2 * M)) *
            (‖∇ f (x k)‖ *
              Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k))))) ^ (2 : ℕ) := by
                rw [pow_two, pow_two]
                ring
        _ =
          (1 / (2 * M)) *
            (-(inner ℝ (∇ f (x k)) (d k) / ‖d k‖)) ^ (2 : ℕ) := by
              have hcosAngleRewrite :
                  ‖∇ f (x k)‖ *
                      Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) =
                    -(inner ℝ (∇ f (x k)) (d k) / ‖d k‖) :=
                gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm
                  f (x k) (d k)
              rw [hcosAngleRewrite]
        _ =
          (inner ℝ (∇ f (x k)) (d k)) ^ (2 : ℕ) /
            (2 * M * ‖d k‖ ^ (2 : ℕ)) := by
              have hnorm_sq_ne : ‖d k‖ ^ (2 : ℕ) ≠ 0 := by
                exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hdk_ne)
              field_simp [pow_two, hMpos.ne', hnorm_sq_ne]
    have hdrop_cos :
        (1 / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) *
            (Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k))))) ^ (2 : ℕ) ≤
          f (x k) - f (x (k + 1)) := by
      calc
        (1 / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) *
            (Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k))))) ^ (2 : ℕ)
            =
          (inner ℝ (∇ f (x k)) (d k)) ^ (2 : ℕ) /
            (2 * M * ‖d k‖ ^ (2 : ℕ)) := hcos_rewrite
        _ ≤ f (x k) - f (x (k + 1)) := le_trans htrial_decrease hexact_compare
    have hpref_nonneg :
        0 ≤ (1 / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) := by
      positivity
    have htarget_le :
        ((Real.sin μ) ^ (2 : ℕ) / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) ≤
          (1 / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) *
            (Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k))))) ^ (2 : ℕ) := by
      have hsq_scaled :
          ((1 / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ)) * (Real.sin μ) ^ (2 : ℕ) ≤
            ((1 / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ)) *
              (Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k))))) ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hcos_sq_lower hpref_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsq_scaled
    exact le_trans htarget_le hdrop_cos

/-- Helper for Chapter02 Theorem 2.2.8: the eventual ball-tail together with the exact
line-search decrease estimate yields a Chapter 1 nonnegative `Q`-linear majorant witness. -/
lemma existsNonnegQLinearMajorant_of_localExactLineSearchTail :
    ∃ q : ℕ → ℝ, IsNonnegErrorMajorant x xStar q ∧ HasQLinearConvergenceTo q 0 := by
  by_cases hPoint : Subsingleton Point
  · -- In the degenerate one-point space every error is already zero.
    have htail :
        ∀ n : ℕ, ‖x (0 + n) - xStar‖ ≤ (0 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
      intro n
      have hxeq : x n = xStar := Subsingleton.elim _ _
      simp [hxeq]
    exact
      existsNonnegQLinearMajorant_of_tailGeometricBound
        (x := x) (xStar := xStar)
        (N := 0) (K := 0) (β := 1 / 2) (by norm_num) (by norm_num) (by norm_num) htail
  · haveI : Nontrivial Point := not_subsingleton_iff_nontrivial.mp hPoint
    have hballEvent : ∀ᶠ k in atTop, x k ∈ Metric.ball xStar ε :=
      h_tendsto.eventually (Metric.ball_mem_nhds xStar hε)
    rcases eventually_atTop.1 hballEvent with ⟨N, hNball⟩
    by_cases hstationaryTail : ∀ k ≥ N, ∇ f (x k) = 0
    · -- If the tail gradients vanish in the ball, the tail is exactly `xStar`.
      have htail :
          ∀ n : ℕ, ‖x (N + n) - xStar‖ ≤ (0 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
        intro n
        have hxBall : x (N + n) ∈ Metric.ball xStar ε :=
          hNball (N + n) (Nat.le_add_right N n)
        have hgrad0 : ∇ f (x (N + n)) = 0 :=
          hstationaryTail (N + n) (Nat.le_add_right N n)
        have hgradLower :
            m * ‖x (N + n) - xStar‖ ≤ ‖∇ f (x (N + n))‖ :=
          minimizerGradientNorm_lowerBound_of_hessianQuadratic_bounds
            (f := f) (xStar := xStar) (ε := ε) h_localMin hC2 (x (N + n)) m
            (fun z hz y ↦ h_hessianLower hz y) hxBall
        have hnorm_zero : ‖x (N + n) - xStar‖ = 0 := by
          have : m * ‖x (N + n) - xStar‖ ≤ 0 := by
            simpa [hgrad0] using hgradLower
          have hnorm_nonneg : 0 ≤ ‖x (N + n) - xStar‖ := norm_nonneg _
          nlinarith [hm, hnorm_nonneg]
        simp [hnorm_zero]
      exact
        existsNonnegQLinearMajorant_of_tailGeometricBound
          (x := x) (xStar := xStar)
          (N := N) (K := 0) (β := 1 / 2) (by norm_num) (by norm_num) (by norm_num) htail
    · -- Otherwise one nonstationary tail index fixes the global contraction constants.
      have hnonstationaryTail : ∃ k, N ≤ k ∧ ∇ f (x k) ≠ 0 := by
        simpa using hstationaryTail
      rcases hnonstationaryTail with ⟨k0, hk0N, hk0grad⟩
      have hxk0 : x k0 ∈ Metric.ball xStar ε := hNball k0 hk0N
      have hdesc0 : IsDescentDirectionAt f (x k0) (d k0) := h_descent k0 hk0grad
      have hdk0_ne : d k0 ≠ 0 := hdesc0.direction_ne
      have hm_le_M : m ≤ M := by
        have hcompare :
            m * ‖d k0‖ ^ (2 : ℕ) ≤ M * ‖d k0‖ ^ (2 : ℕ) := by
          exact le_trans (h_hessianLower hxk0 (d k0)) (h_hessianUpper hxk0 (d k0))
        exact
          le_of_mul_le_mul_right
            (by simpa [mul_comm] using hcompare)
            (pow_pos (norm_pos_iff.mpr hdk0_ne) 2)
      have hMpos : 0 < M := lt_of_lt_of_le hm hm_le_M
      have hangle_nonneg0 :
          0 ≤ InnerProductGeometry.angle (d k0) (-(∇ f (x k0))) :=
        InnerProductGeometry.angle_nonneg _ _
      have hmu_le_halfPi : μ ≤ Real.pi / 2 := by
        linarith [hangle_nonneg0, h_angle k0 hk0grad]
      have hsin_pos : 0 < Real.sin μ := by
        exact Real.sin_pos_of_pos_of_lt_pi hμ (by linarith [hmu_le_halfPi, Real.pi_pos])
      let γ : ℝ := 1 - (m * Real.sin μ / M) ^ (2 : ℕ)
      have hratio_nonneg : 0 ≤ m * Real.sin μ / M := by
        positivity
      have hratio_le_one : m * Real.sin μ / M ≤ 1 := by
        refine (div_le_iff₀ hMpos).2 ?_
        calc
          m * Real.sin μ ≤ m * 1 := by
            gcongr
            exact Real.sin_le_one μ
          _ = m := by ring
          _ ≤ 1 * M := by simpa using hm_le_M
      have hγ_nonneg : 0 ≤ γ := by
        dsimp [γ]
        nlinarith
      have hγ_lt_one : γ < 1 := by
        dsimp [γ]
        have hratio_pos : 0 < m * Real.sin μ / M := by positivity
        nlinarith
      let β : ℝ := (γ + 1) / 2
      have hβ0 : 0 < β := by
        dsimp [β]
        nlinarith [hγ_nonneg]
      have hβ1 : β < 1 := by
        dsimp [β]
        nlinarith [hγ_lt_one]
      let δ : ℝ := Real.sqrt β
      have hδ0 : 0 < δ := Real.sqrt_pos.mpr hβ0
      have hδ_nonneg : 0 ≤ δ := hδ0.le
      have hδ_sq : δ ^ (2 : ℕ) = β := by
        dsimp [δ]
        simpa [pow_two] using Real.sq_sqrt hβ0.le
      have hδ1 : δ < 1 := by
        have hδsq_lt : δ ^ (2 : ℕ) < 1 := by
          simpa [hδ_sq] using hβ1
        nlinarith
      have hγ_le_β : γ ≤ β := by
        dsimp [β]
        nlinarith
      have hgap_nonneg :
          ∀ k : ℕ, N ≤ k → 0 ≤ f (x k) - f xStar := by
        intro k hk
        have hxk : x k ∈ Metric.ball xStar ε := hNball k hk
        have hlower :
            (1 / 2 : ℝ) * m * ‖x k - xStar‖ ^ (2 : ℕ) ≤ f (x k) - f xStar :=
          minimizerValue_lowerBound_of_hessianQuadratic_bounds
            (f := f) (xStar := xStar) (ε := ε) h_localMin hC2 (x k) m
            (fun z hz y ↦ h_hessianLower hz y) hxk
        nlinarith [hlower, hm]
      have hgap_rec :
          ∀ k : ℕ, N ≤ k →
            f (x (k + 1)) - f xStar ≤ γ * (f (x k) - f xStar) := by
        intro k hk
        have hxk : x k ∈ Metric.ball xStar ε := hNball k hk
        have hxk1 : x (k + 1) ∈ Metric.ball xStar ε :=
          hNball (k + 1) (le_trans hk (Nat.le_succ _))
        have hdrop :
            ((Real.sin μ) ^ (2 : ℕ) / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) ≤
              f (x k) - f (x (k + 1)) :=
          exactLineSearch_drop_ge_sinSq_mul_gradientNormSq_div_twoMulM
            (f := f) (x := x) (d := d) (α := α) (xStar := xStar) (ε := ε) (m := m) (M := M)
            (μ := μ) (h_descent := h_descent) (h_exactLineSearch := h_exactLineSearch)
            (h_update := h_update) (h_hasGradientAt := h_hasGradientAt) (hμ := hμ)
            (h_angle := h_angle) (hC2 := hC2)
            (hm := hm) (h_hessianLower := h_hessianLower) (h_hessianUpper := h_hessianUpper)
            hxk hxk1
        have hupper :
            f (x k) - f xStar ≤ (1 / 2 : ℝ) * M * ‖x k - xStar‖ ^ (2 : ℕ) :=
          minimizerValue_upperBound_of_hessianQuadratic_bounds
            (f := f) (xStar := xStar) (ε := ε) h_localMin hC2 (x k) M
            (fun z hz y ↦ h_hessianUpper hz y) hxk
        have hgradLower :
            m * ‖x k - xStar‖ ≤ ‖∇ f (x k)‖ :=
          minimizerGradientNorm_lowerBound_of_hessianQuadratic_bounds
            (f := f) (xStar := xStar) (ε := ε) h_localMin hC2 (x k) m
            (fun z hz y ↦ h_hessianLower hz y) hxk
        have hgrad_sq :
            m ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) ≤ ‖∇ f (x k)‖ ^ (2 : ℕ) := by
          have hgrad_nonneg : 0 ≤ ‖∇ f (x k)‖ := norm_nonneg _
          have hmul_nonneg : 0 ≤ m * ‖x k - xStar‖ := by positivity
          nlinarith [hgradLower, hgrad_nonneg, hmul_nonneg]
        have hgap_to_grad :
            (2 * m ^ (2 : ℕ) / M) * (f (x k) - f xStar) ≤ ‖∇ f (x k)‖ ^ (2 : ℕ) := by
          have hgap_to_norm :
              (2 * m ^ (2 : ℕ) / M) * (f (x k) - f xStar) ≤
                m ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) := by
            have htwice_gap :
                2 * (f (x k) - f xStar) ≤ M * ‖x k - xStar‖ ^ (2 : ℕ) := by
              nlinarith [hupper]
            have hscale_nonneg : 0 ≤ m ^ (2 : ℕ) / M := by
              positivity
            have hscaled :
                (m ^ (2 : ℕ) / M) * (2 * (f (x k) - f xStar)) ≤
                  (m ^ (2 : ℕ) / M) * (M * ‖x k - xStar‖ ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left htwice_gap hscale_nonneg
            calc
              (2 * m ^ (2 : ℕ) / M) * (f (x k) - f xStar)
                  = (m ^ (2 : ℕ) / M) * (2 * (f (x k) - f xStar)) := by
                      field_simp [hMpos.ne']
              _ ≤ (m ^ (2 : ℕ) / M) * (M * ‖x k - xStar‖ ^ (2 : ℕ)) := hscaled
              _ = m ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) := by
                    field_simp [hMpos.ne']
          exact le_trans hgap_to_norm hgrad_sq
        have hdrop_gap :
            (m * Real.sin μ / M) ^ (2 : ℕ) * (f (x k) - f xStar) ≤
              f (x k) - f (x (k + 1)) := by
          have hpref_nonneg : 0 ≤ (Real.sin μ) ^ (2 : ℕ) / (2 * M) := by
            positivity
          have hscaled :
              ((Real.sin μ) ^ (2 : ℕ) / (2 * M)) *
                  ((2 * m ^ (2 : ℕ) / M) * (f (x k) - f xStar)) ≤
                ((Real.sin μ) ^ (2 : ℕ) / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hgap_to_grad hpref_nonneg
          calc
            (m * Real.sin μ / M) ^ (2 : ℕ) * (f (x k) - f xStar)
                =
              ((Real.sin μ) ^ (2 : ℕ) / (2 * M)) *
                ((2 * m ^ (2 : ℕ) / M) * (f (x k) - f xStar)) := by
                  field_simp [hMpos.ne']
            _ ≤ ((Real.sin μ) ^ (2 : ℕ) / (2 * M)) * ‖∇ f (x k)‖ ^ (2 : ℕ) := hscaled
            _ ≤ f (x k) - f (x (k + 1)) := hdrop
        dsimp [γ]
        nlinarith [hdrop_gap]
      have hgap_tail :
          ∀ n : ℕ, f (x (N + n)) - f xStar ≤ (f (x N) - f xStar) * β ^ n := by
        intro n
        induction n with
        | zero =>
            simp
        | succ n ihn =>
            have hrec :
                f (x (N + n + 1)) - f xStar ≤ γ * (f (x (N + n)) - f xStar) := by
              simpa [Nat.add_assoc] using hgap_rec (N + n) (Nat.le_add_right N n)
            have hgap_nonneg_n :
                0 ≤ f (x (N + n)) - f xStar :=
              hgap_nonneg (N + n) (Nat.le_add_right N n)
            calc
              f (x (N + n + 1)) - f xStar ≤ γ * (f (x (N + n)) - f xStar) := hrec
              _ ≤ β * ((f (x N) - f xStar) * β ^ n) := by
                    gcongr
              _ = (f (x N) - f xStar) * β ^ (n + 1) := by
                    rw [pow_succ']
                    ring
      let K : ℝ := Real.sqrt ((2 / m) * (f (x N) - f xStar))
      have hK_nonneg : 0 ≤ K := by
        exact Real.sqrt_nonneg _
      have hK_sq_nonneg : 0 ≤ (2 / m) * (f (x N) - f xStar) := by
        have hgapN : 0 ≤ f (x N) - f xStar := hgap_nonneg N le_rfl
        positivity
      have hnorm_tail :
          ∀ n : ℕ, ‖x (N + n) - xStar‖ ≤ K * δ ^ n := by
        intro n
        have hxBall : x (N + n) ∈ Metric.ball xStar ε := hNball (N + n) (Nat.le_add_right N n)
        have hlower :
            (1 / 2 : ℝ) * m * ‖x (N + n) - xStar‖ ^ (2 : ℕ) ≤
              f (x (N + n)) - f xStar :=
          minimizerValue_lowerBound_of_hessianQuadratic_bounds
            (f := f) (xStar := xStar) (ε := ε) h_localMin hC2 (x (N + n)) m
            (fun z hz y ↦ h_hessianLower hz y) hxBall
        have hsq_bound :
            ‖x (N + n) - xStar‖ ^ (2 : ℕ) ≤
              ((2 / m) * (f (x N) - f xStar)) * β ^ n := by
          have hnorm_to_gap :
              ‖x (N + n) - xStar‖ ^ (2 : ℕ) ≤
                (2 / m) * (f (x (N + n)) - f xStar) := by
            have hscale_nonneg : 0 ≤ 2 / m := by positivity
            have hscaled :
                (2 / m) * ((1 / 2 : ℝ) * m * ‖x (N + n) - xStar‖ ^ (2 : ℕ)) ≤
                  (2 / m) * (f (x (N + n)) - f xStar) := by
              exact mul_le_mul_of_nonneg_left hlower hscale_nonneg
            calc
              ‖x (N + n) - xStar‖ ^ (2 : ℕ)
                  = (2 / m) * ((1 / 2 : ℝ) * m * ‖x (N + n) - xStar‖ ^ (2 : ℕ)) := by
                      field_simp [hm.ne']
              _ ≤ (2 / m) * (f (x (N + n)) - f xStar) := hscaled
          calc
            ‖x (N + n) - xStar‖ ^ (2 : ℕ) ≤ (2 / m) * (f (x (N + n)) - f xStar) := hnorm_to_gap
            _ ≤ (2 / m) * ((f (x N) - f xStar) * β ^ n) := by
                  gcongr
                  exact hgap_tail n
            _ = ((2 / m) * (f (x N) - f xStar)) * β ^ n := by
                  ring
        have hK_sq :
            K ^ (2 : ℕ) = (2 / m) * (f (x N) - f xStar) := by
          dsimp [K]
          simpa [pow_two] using Real.sq_sqrt hK_sq_nonneg
        have hδn_sq : (δ ^ n) ^ (2 : ℕ) = β ^ n := by
          calc
            (δ ^ n) ^ (2 : ℕ) = δ ^ (n * 2) := by rw [pow_mul]
            _ = δ ^ (2 * n) := by simp [Nat.mul_comm]
            _ = (δ ^ (2 : ℕ)) ^ n := by rw [pow_mul]
            _ = β ^ n := by rw [hδ_sq]
        have hright_sq :
            (K * δ ^ n) ^ (2 : ℕ) =
              ((2 / m) * (f (x N) - f xStar)) * β ^ n := by
          have hK_mul : K * K = (2 / m) * (f (x N) - f xStar) := by
            simpa [pow_two] using hK_sq
          have hδn_mul : δ ^ n * δ ^ n = β ^ n := by
            simpa [pow_two] using hδn_sq
          calc
            (K * δ ^ n) ^ (2 : ℕ) = (K * K) * (δ ^ n * δ ^ n) := by
              ring
            _ = ((2 / m) * (f (x N) - f xStar)) * β ^ n := by
              rw [hK_mul, hδn_mul]
        have hright_nonneg : 0 ≤ K * δ ^ n := by
          exact mul_nonneg hK_nonneg (pow_nonneg hδ_nonneg _)
        have hsq :
            ‖x (N + n) - xStar‖ ^ (2 : ℕ) ≤ (K * δ ^ n) ^ (2 : ℕ) := by
          simpa [hright_sq] using hsq_bound
        have habs := (sq_le_sq).1 hsq
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hright_nonneg] using habs
      exact
        existsNonnegQLinearMajorant_of_tailGeometricBound
          (x := x) (xStar := xStar)
          (N := N) (K := K) (β := δ) hK_nonneg hδ0 hδ1 hnorm_tail

/-- Chapter02 Theorem 2.2.8: let `x` be an iterate sequence generated by the exact-line-search
scheme of Chapter02 Algorithm 2.2.1 for `f : Point → ℝ`, with search directions `d` and exact
line-search steps `α` on the nonnegative ray, updates `x (k + 1) = x k + α k • d k`, and
`HasGradientAt f (∇ f (x k)) (x k)` along the iterates. Assume `x ⟶ xStar`, where `xStar` is a
local minimizer of `f`, and suppose the angle between `d k` and `-∇ f (x k)` is uniformly bounded
away from `π / 2` on every nonstationary iterate. If `f` is `C²` on `Metric.ball xStar ε`, and
the Hessian quadratic form is bounded below by `m > 0` and above by `M` on that ball, then the
iterates converge to `xStar` at least linearly, expressed by the Chapter 1 owner
`rAtLeastLinearConvergenceTo`. This matches the source proof's geometric-majorant conclusion and
still allows the finite-termination and superlinear-tail cases that the stricter Chapter 1
`R`-linear predicate excludes. The Chapter 3 contraction owners are stronger derived API and are
not the source-facing main conclusion here. -/
theorem exactLineSearch_atLeastLinearConvergenceTo_of_tendsto_isLocalMin_of_angleBound
    : rAtLeastLinearConvergenceTo x xStar := by
  -- Use the Chapter 1 majorant characterization with the tail witness built above.
  exact
    (rAtLeastLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant x xStar).2
      (existsNonnegQLinearMajorant_of_localExactLineSearchTail
        (f := f) (x := x) (d := d) (α := α) (xStar := xStar) (ε := ε) (m := m) (M := M)
        (μ := μ) (h_descent := h_descent) (h_exactLineSearch := h_exactLineSearch)
        (h_update := h_update) (h_hasGradientAt := h_hasGradientAt) (h_tendsto := h_tendsto)
        (h_localMin := h_localMin) (hμ := hμ) (h_angle := h_angle) (hε := hε) (hC2 := hC2)
        (hm := hm) (h_hessianLower := h_hessianLower) (h_hessianUpper := h_hessianUpper))

/-- Companion bridge: if the first `R`-rate is strictly positive, so the source-facing
at-least-linear conclusion is neither finite termination nor a superlinear tail, then
Theorem 2.2.8 strengthens to the strict Chapter 1 `R`-linear owner. -/
theorem exactLineSearch_rLinearConvergenceTo_of_tendsto_isLocalMin_of_angleBound_of_rRate_pos
    (hRpos : 0 < R[1] x xStar) :
    rLinearConvergenceTo x xStar := by
  have hAtLeast :
      rAtLeastLinearConvergenceTo x xStar :=
    exactLineSearch_atLeastLinearConvergenceTo_of_tendsto_isLocalMin_of_angleBound
      f x d α xStar ε m M μ h_descent h_exactLineSearch h_update h_hasGradientAt h_tendsto
      h_localMin hμ h_angle hε hC2 hm h_hessianLower h_hessianUpper
  exact ⟨hAtLeast.1, hRpos, hAtLeast.2⟩

/-- Companion bridge: under the additional hypothesis `0 < R[1] x xStar`, the stricter
`R`-linear conclusion of Theorem 2.2.8 is equivalently the existence of a nonnegative scalar
majorant whose values converge `Q`-linearly to `0`. -/
theorem
    exactLineSearch_exists_nonneg_qLinearMajorant_of_tendsto_isLocalMin_of_angleBound_of_rRate_pos
    (hRpos : 0 < R[1] x xStar) :
    ∃ q : ℕ → ℝ,
        IsNonnegErrorMajorant x xStar q ∧ HasQLinearConvergenceTo q 0 := by
  have _ : 0 < R[1] x xStar := hRpos
  have hAtLeast :
      rAtLeastLinearConvergenceTo x xStar :=
    exactLineSearch_atLeastLinearConvergenceTo_of_tendsto_isLocalMin_of_angleBound
      f x d α xStar ε m M μ h_descent h_exactLineSearch h_update h_hasGradientAt h_tendsto
      h_localMin hμ h_angle hε hC2 hm h_hessianLower h_hessianUpper
  exact (rAtLeastLinearConvergenceTo_iff_exists_nonneg_qLinearMajorant x xStar).1 hAtLeast

end
