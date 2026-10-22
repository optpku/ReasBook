/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_1_1

open Filter InnerProductSpace

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {ε : ℝ} {x₀ : E} {x g d : ℕ → E} {α : ℕ → ℝ}

-- Domain sampling:
-- * source-facing owner: `IsSteepestDescentMethod` in Algorithm 3.1.1;
-- * core/canonical owners inspected: `steepestDescentDirection`, `steepestDescentStep`, and
--   `IsExactLineSearchStepOnNonnegativeRay`;
-- * bridge/view avoided here: a second local run predicate restating the same iterate, gradient,
--   direction, exact-line-search, and update data.
--
-- Triage:
-- * source-facing: the global alternative for a steepest-descent run;
-- * core/canonical: the Chapter 3/Chapter 2 owners above;
-- * bridge/view removed: the concrete `ℝ^n` model, since the theorem only uses the real Hilbert
--   space structure already required by the owner API.
--
-- Primitive data are therefore just the objective `f`, the steepest-descent run data
-- `x, g, d, α`, and the `IsSteepestDescentMethod` witness. The exact line-search and update
-- clauses remain derived through that owner.

/-- Helper for Chapter03 Theorem 3.1.3: if no iterate satisfies `‖gradient f (x k)‖ ≤ ε`, then
every iterate carries the canonical exact-line-search and update data required by
Chapter02 Theorem 2.2.4. -/
lemma steepestDescentStepData_of_forall_notStopped
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α)
    (hNotStopped : ∀ k : ℕ, ε < ‖gradient f (x k)‖) :
    ∀ k : ℕ,
      IsExactLineSearchStepOnNonnegativeRay f (x k) (steepestDescentDirection f (x k)) (α k) ∧
        x (k + 1) = steepestDescentStep f (x k) (α k) := by
  intro k
  -- Translate the nonstopping condition from `gradient f` to the recorded gradient data `g`.
  have hk : ε < ‖g k‖ := by
    simpa [hMethod.gradient_eq k] using hNotStopped k
  exact
    ⟨hMethod.exactLineSearch_steepestDescentDirection hk,
      hMethod.next_eq_steepestDescentStep hk⟩

/-- Helper for Chapter03 Theorem 3.1.3: if the gradient sequence does not converge to `0`, then
some positive lower bound on its norms occurs frequently. -/
lemma frequently_gradientNorm_ge_of_not_tendsto_zero
    (hNot : ¬ Tendsto (gradient f ∘ x) atTop (nhds 0)) :
    ∃ ε > 0, ∃ᶠ k : ℕ in atTop, ε ≤ ‖gradient f (x k)‖ := by
  -- Failure of vector convergence to `0` forces failure of norm convergence to `0`.
  have hNotNorm :
      ¬ Tendsto (fun k : ℕ ↦ ‖gradient f (x k)‖) atTop (nhds (0 : ℝ)) := by
    intro hNorm
    apply hNot
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hNorm
  rw [Metric.tendsto_nhds] at hNotNorm
  push_neg at hNotNorm
  rcases hNotNorm with ⟨ε, hε, hFreq⟩
  refine ⟨ε, hε, ?_⟩
  exact hFreq.mono fun k hk ↦ by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hk

/-- Helper for Chapter03 Theorem 3.1.3: an operator-norm bound on `A` bounds the quadratic form
`⟪v, A v⟫` by `M * ‖v‖²`. -/
lemma quadraticForm_le_mul_normSq_of_bound
    (M : ℝ) (hM_nonneg : 0 ≤ M) (A : E →L[ℝ] E) (v : E)
    (hA : ‖A‖ ≤ M) :
    inner ℝ v (A v) ≤ M * ‖v‖ ^ (2 : ℕ) := by
  -- Combine Cauchy-Schwarz with the operator-norm estimate.
  have hAv : ‖A v‖ ≤ M * ‖v‖ := by
    calc
      ‖A v‖ ≤ ‖A‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
  calc
    inner ℝ v (A v) ≤ ‖v‖ * ‖A v‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * (M * ‖v‖) := mul_le_mul_of_nonneg_left hAv (norm_nonneg _)
    _ = M * ‖v‖ ^ (2 : ℕ) := by
      rw [pow_two]
      ring

/-- Helper for Chapter03 Theorem 3.1.3: the first derivative of the rescaled line-search profile
at `0` is `α * ⟪gradient f x, d⟫`. -/
lemma unitIntervalTraceFirstIteratedDerivZero
    (hC2 : ContDiff ℝ 2 f) (x : E) (d : E) (α : ℝ) :
    iteratedDerivWithin 1 (lineSearchObjective f x (α • d)) (Set.uIcc (0 : ℝ) 1) 0 =
      α * inner ℝ (gradient f x) d := by
  let φ : ℝ → ℝ := lineSearchObjective f x (α • d)
  have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have h0_mem : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    exact Set.mem_uIcc_of_le le_rfl zero_le_one
  have hTraceContDiffAt :
      ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • (α • d)) 0 := by
    -- The affine trace is smooth.
    simpa using (contDiff_const.add (contDiff_id.smul_const (α • d))).contDiffAt
  have hf_contDiffAt :
      ContDiffAt ℝ 2 f (x + (0 : ℝ) • (α • d)) := by
    simpa [zero_smul] using (hC2.contDiffAt (x := x))
  have hφ_contDiffAt : ContDiffAt ℝ 2 φ 0 := by
    -- Compose `f` with the affine trace and specialize at the base point.
    change ContDiffAt ℝ 2 (f ∘ fun t : ℝ ↦ x + t • (α • d)) 0
    exact hf_contDiffAt.comp 0 hTraceContDiffAt
  have hDiff0 : DifferentiableAt ℝ f x :=
    (hC2.contDiffAt (x := x)).differentiableAt (by norm_num)
  calc
    iteratedDerivWithin 1 φ (Set.uIcc (0 : ℝ) 1) 0 = iteratedDeriv 1 φ 0 := by
      exact iteratedDerivWithin_eq_iteratedDeriv hs (hφ_contDiffAt.of_le (by norm_num)) h0_mem
    _ = deriv φ 0 := by simp [iteratedDeriv_one]
    _ = α * inner ℝ (gradient f x) d := by
      -- Evaluate the derivative of the one-dimensional profile at the base point.
      simpa [φ, zero_smul, inner_smul_right, mul_comm, real_inner_comm] using
        deriv_lineSearchObjective_apply f x (α • d) 0 (by simpa [zero_smul] using hDiff0)

/-- Helper for Chapter03 Theorem 3.1.3: the second derivative of the rescaled line-search profile
is the Hessian quadratic form along the traced segment, scaled by `α²`. -/
lemma unitIntervalTraceSecondIteratedDeriv
    (hC2 : ContDiff ℝ 2 f) (x : E) (d : E) (α t : ℝ)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    iteratedDerivWithin 2 (lineSearchObjective f x (α • d)) (Set.uIcc (0 : ℝ) 1) t =
      α ^ (2 : ℕ) * inner ℝ d ((fderiv ℝ (gradient f) (x + t • (α • d))) d) := by
  let φ : ℝ → ℝ := lineSearchObjective f x (α • d)
  let γ : ℝ → E := fun s ↦ x + s • (α • d)
  have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have hTraceContDiffAt : ContDiffAt ℝ 2 γ t := by
    -- The affine trace stays smooth at every point of the unit interval.
    simpa [γ] using (contDiff_const.add (contDiff_id.smul_const (α • d))).contDiffAt
  have hf_contDiffAt : ContDiffAt ℝ 2 f (γ t) := hC2.contDiffAt (x := γ t)
  have hφ_contDiffAt : ContDiffAt ℝ 2 φ t := by
    -- The scalar profile inherits `C²` regularity from `f`.
    change ContDiffAt ℝ 2 (f ∘ γ) t
    exact hf_contDiffAt.comp t hTraceContDiffAt
  have htrace_deriv : HasDerivAt γ (α • d) t := by
    -- Differentiate the affine trace directly.
    simpa [γ, one_smul] using ((hasDerivAt_id' t).smul_const (α • d)).const_add x
  have hdiff : ∀ s : ℝ, DifferentiableAt ℝ f (γ s) := fun s ↦
    (hC2.contDiffAt (x := γ s)).differentiableAt (by norm_num)
  have hderiv_eventually :
      deriv φ =ᶠ[nhds t] fun s ↦ inner ℝ (gradient f (γ s)) (α • d) := by
    -- The derivative bridge holds at every point of the trace.
    filter_upwards with s
    simpa [φ, γ] using deriv_lineSearchObjective_apply f x (α • d) s (hdiff s)
  have hgrad_contDiffAt : ContDiffAt ℝ 1 (gradient f) (γ t) := by
    -- `gradient f` is `C¹` because `f` is `C²`.
    change ContDiffAt ℝ 1 (((toDual ℝ E).symm) ∘ (fderiv ℝ f)) (γ t)
    exact
      (LinearIsometryEquiv.contDiff ((toDual ℝ E).symm)).contDiffAt.comp (γ t)
        hf_contDiffAt.fderiv_right_succ
  have hgrad_trace_deriv :
      HasDerivAt (gradient f ∘ γ)
        ((fderiv ℝ (gradient f) (γ t)) (α • d)) t := by
    -- Chain the derivative of the gradient with the derivative of the trace.
    exact hgrad_contDiffAt.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t htrace_deriv
  have hinner_deriv :
      HasDerivAt (fun s ↦ inner ℝ (gradient f (γ s)) (α • d))
        (inner ℝ ((fderiv ℝ (gradient f) (γ t)) (α • d)) (α • d)) t := by
    -- Differentiate the pairing with the fixed direction.
    simpa [Function.comp, γ] using
      hgrad_trace_deriv.inner ℝ (hasDerivAt_const t (α • d))
  have hderiv_deriv :
      HasDerivAt (deriv φ)
        (inner ℝ ((fderiv ℝ (gradient f) (γ t)) (α • d)) (α • d)) t := by
    exact hinner_deriv.congr_of_eventuallyEq hderiv_eventually
  have hsecond :
      iteratedDeriv 2 φ t =
        inner ℝ ((fderiv ℝ (gradient f) (γ t)) (α • d)) (α • d) := by
    -- Identify the second iterated derivative with the derivative of `deriv φ`.
    calc
      iteratedDeriv 2 φ t = deriv (deriv φ) t := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      _ = inner ℝ ((fderiv ℝ (gradient f) (γ t)) (α • d)) (α • d) := hderiv_deriv.deriv
  calc
    iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) t = iteratedDeriv 2 φ t := by
      exact iteratedDerivWithin_eq_iteratedDeriv hs hφ_contDiffAt ht
    _ = inner ℝ ((fderiv ℝ (gradient f) (γ t)) (α • d)) (α • d) := hsecond
    _ = α ^ (2 : ℕ) * inner ℝ d ((fderiv ℝ (gradient f) (γ t)) d) := by
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, real_inner_comm]

/-- Helper for Chapter03 Theorem 3.1.3: a global Hessian operator-norm bound gives the standard
quadratic upper model along every search ray. -/
lemma lineSearchObjective_le_base_add_linear_add_quadratic_of_globalHessianBound
    (Mbar : ℝ)
    (hMbar_nonneg : 0 ≤ Mbar)
    (hC2 : ContDiff ℝ 2 f)
    (hHessianBound : ∀ y : E, ‖fderiv ℝ (gradient f) y‖ ≤ Mbar)
    (x : E) (d : E) (β : ℝ) :
    lineSearchObjective f x d β ≤
      lineSearchObjective f x d 0 + β * inner ℝ (gradient f x) d +
        (Mbar / 2) * β ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
  -- Rescale the search ray to the unit interval and keep the Taylor remainder explicit.
  let φ : ℝ → ℝ := lineSearchObjective f x (β • d)
  have hTraceContDiff :
      ContDiff ℝ 2 (fun t : ℝ ↦ x + t • (β • d)) := by
    simpa using (contDiff_const.add (contDiff_id.smul_const (β • d)))
  have hφC2 : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) 1) := by
    change ContDiffOn ℝ 2 (f ∘ fun t : ℝ ↦ x + t • (β • d)) (Set.uIcc (0 : ℝ) 1)
    exact (hC2.contDiffOn (s := Set.univ)).comp hTraceContDiff.contDiffOn (by
      intro t ht
      simp)
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := φ) (x := 1) (x₀ := 0) (n := 1) zero_ne_one hφC2
  have hξu : ξ ∈ Set.uIcc (0 : ℝ) 1 := by
    exact ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hsecond_bound :
      iteratedDeriv 2 φ ξ ≤ β ^ (2 : ℕ) * (Mbar * ‖d‖ ^ (2 : ℕ)) := by
    calc
      iteratedDeriv 2 φ ξ =
          iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) ξ := by
            symm
            exact iteratedDerivWithin_eq_iteratedDeriv
              (by
                simpa [Set.uIcc_of_le zero_le_one] using
                  uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
              (by
                change ContDiffAt ℝ 2 (f ∘ fun t : ℝ ↦ x + t • (β • d)) ξ
                exact (hC2.contDiffAt (x := x + ξ • (β • d))).comp ξ
                  hTraceContDiff.contDiffAt)
              hξu
      _ = β ^ (2 : ℕ) * inner ℝ d ((fderiv ℝ (gradient f) (x + ξ • (β • d))) d) := by
            rw [unitIntervalTraceSecondIteratedDeriv hC2 x d β ξ hξu]
      _ ≤ β ^ (2 : ℕ) * (Mbar * ‖d‖ ^ (2 : ℕ)) := by
            gcongr
            exact quadraticForm_le_mul_normSq_of_bound Mbar hMbar_nonneg _ d (hHessianBound _)
  have hfirst :
      iteratedDerivWithin 1 φ (Set.uIcc (0 : ℝ) 1) 0 =
        β * inner ℝ (gradient f x) d :=
    unitIntervalTraceFirstIteratedDerivZero hC2 x d β
  have hTaylor' :
      φ 1 =
        φ 0 + β * inner ℝ (gradient f x) d + iteratedDeriv 2 φ ξ / 2 := by
    -- Expand the first-order Taylor polynomial and isolate the remainder.
    have hbase :
        φ 1 - taylorWithinEval φ 1 (Set.uIcc (0 : ℝ) 1) 0 1 = iteratedDeriv 2 φ ξ / 2 := by
      simpa [pow_two] using hTaylor
    rw [taylorWithinEval_succ, taylor_within_zero_eval] at hbase
    rw [hfirst] at hbase
    norm_num at hbase
    have hbase' :
        φ 1 - (φ 0 + β * inner ℝ (gradient f x) d) = iteratedDeriv 2 φ ξ / 2 := by
      simpa using hbase
    calc
      φ 1 = (φ 1 - (φ 0 + β * inner ℝ (gradient f x) d)) +
          (φ 0 + β * inner ℝ (gradient f x) d) := by ring
      _ = iteratedDeriv 2 φ ξ / 2 + (φ 0 + β * inner ℝ (gradient f x) d) := by
            rw [hbase']
      _ = φ 0 + β * inner ℝ (gradient f x) d + iteratedDeriv 2 φ ξ / 2 := by ring
  calc
    lineSearchObjective f x d β = φ 1 := by
      simp [φ, lineSearchObjective_apply, smul_smul]
    _ = φ 0 + β * inner ℝ (gradient f x) d + iteratedDeriv 2 φ ξ / 2 := hTaylor'
    _ ≤ φ 0 + β * inner ℝ (gradient f x) d +
          (β ^ (2 : ℕ) * (Mbar * ‖d‖ ^ (2 : ℕ))) / 2 := by
            gcongr
    _ = lineSearchObjective f x d 0 + β * inner ℝ (gradient f x) d +
          (Mbar / 2) * β ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
            simp [φ, lineSearchObjective_zero]
            ring

/-- Helper for Chapter03 Theorem 3.1.3: the fixed admissible trial step `1 / max M 1` along the
steepest-descent direction already gives the textbook half-constant decrease. -/
lemma steepestDescentTrialDecrease_ge_half_inv_maxHessianBound_mul_gradientNormSq
    (M : ℝ)
    (hC2 : ContDiff ℝ 2 f)
    (hHessianBound : ∀ y : E, ‖fderiv ℝ (gradient f) y‖ ≤ M) :
    ∀ k : ℕ,
      f (x k) - f (x k + (1 / max M 1) • steepestDescentDirection f (x k)) ≥
        (1 / (2 * max M 1)) * ‖gradient f (x k)‖ ^ (2 : ℕ) := by
  let Mbar : ℝ := max M 1
  have hMbar_pos : 0 < Mbar := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hMbar_nonneg : 0 ≤ Mbar := hMbar_pos.le
  have hHessianBound' : ∀ y : E, ‖fderiv ℝ (gradient f) y‖ ≤ Mbar := fun y ↦
    le_trans (hHessianBound y) (le_max_left M 1)
  intro k
  have hModel :
      lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (1 / Mbar) ≤
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) 0 +
          (1 / Mbar) *
            inner ℝ (gradient f (x k)) (steepestDescentDirection f (x k)) +
          (Mbar / 2) * (1 / Mbar) ^ (2 : ℕ) *
            ‖steepestDescentDirection f (x k)‖ ^ (2 : ℕ) := by
    -- Apply the global quadratic model to the steepest-descent ray.
    simpa [Mbar] using
      lineSearchObjective_le_base_add_linear_add_quadratic_of_globalHessianBound
        Mbar hMbar_nonneg hC2 hHessianBound' (x k) (steepestDescentDirection f (x k)) (1 / Mbar)
  have hModel' :
      f (x k + (1 / Mbar) • steepestDescentDirection f (x k)) ≤
        f (x k) +
          (1 / Mbar) *
            inner ℝ (gradient f (x k)) (steepestDescentDirection f (x k)) +
          (Mbar / 2) * (1 / Mbar) ^ (2 : ℕ) *
            ‖steepestDescentDirection f (x k)‖ ^ (2 : ℕ) := by
    simpa [lineSearchObjective_apply, lineSearchObjective_zero] using hModel
  have hInner :
      inner ℝ (gradient f (x k)) (steepestDescentDirection f (x k)) =
        -(‖gradient f (x k)‖ ^ (2 : ℕ)) := by
    -- The steepest-descent direction is the negative gradient.
    simp [steepestDescentDirection, real_inner_self_eq_norm_sq]
  have hNorm :
      ‖steepestDescentDirection f (x k)‖ ^ (2 : ℕ) =
        ‖gradient f (x k)‖ ^ (2 : ℕ) := by
    -- Negation preserves the norm.
    simp [steepestDescentDirection]
  have hTrialEval :
      f (x k + (1 / Mbar) • steepestDescentDirection f (x k)) ≤
        f (x k) - (1 / (2 * Mbar)) * ‖gradient f (x k)‖ ^ (2 : ℕ) := by
    rw [hInner, hNorm] at hModel'
    have hMbar_ne : Mbar ≠ 0 := ne_of_gt hMbar_pos
    have hRewrite :
        f (x k) + 1 / Mbar * -‖gradient f (x k)‖ ^ (2 : ℕ) +
            Mbar / 2 * (1 / Mbar) ^ (2 : ℕ) * ‖gradient f (x k)‖ ^ (2 : ℕ) =
          f (x k) - (1 / (2 * Mbar)) * ‖gradient f (x k)‖ ^ (2 : ℕ) := by
      field_simp [hMbar_ne]
      ring
    rw [hRewrite] at hModel'
    exact hModel'
  nlinarith [hTrialEval]

/-- Helper for Chapter03 Theorem 3.1.3: in the nonstopping regime, each steepest-descent step
enjoys the Chapter02 exact-line-search decrease bound specialized to angle `0`. -/
lemma steepestDescentStepDecrease_ge_half_inv_hessianBound_mul_gradientNormSq
    (M : ℝ)
    (hC2 : ContDiff ℝ 2 f)
    (hHessianBound : ∀ y : E, ‖fderiv ℝ (gradient f) y‖ ≤ M)
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α)
    (hNotStopped : ∀ k : ℕ, ε < ‖gradient f (x k)‖) :
    ∀ k : ℕ,
      f (x k) - f (x (k + 1)) ≥
        (1 / (2 * max M 1)) * ‖gradient f (x k)‖ ^ (2 : ℕ) := by
  intro k
  let Mbar : ℝ := max M 1
  have hStepData :=
    steepestDescentStepData_of_forall_notStopped hMethod hNotStopped k
  rcases hStepData with ⟨hExact, hNext⟩
  have hTrialStep :
      f (x k) - f (x k + (1 / Mbar) • steepestDescentDirection f (x k)) ≥
        (1 / (2 * Mbar)) * ‖gradient f (x k)‖ ^ (2 : ℕ) := by
    -- First compare with the explicit admissible trial step.
    simpa [Mbar] using
      steepestDescentTrialDecrease_ge_half_inv_maxHessianBound_mul_gradientNormSq
        (x := x) M hC2 hHessianBound k
  have hOpt :
      lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (α k) ≤
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (1 / Mbar) := by
    -- Exact line search does at least as well as the fixed trial step.
    have hMbar_pos : 0 < Mbar := by
      exact lt_of_lt_of_le zero_lt_one (le_max_right M 1)
    exact hExact.optimal (by positivity)
  have hActualLeTrial :
      f (x (k + 1)) ≤
        f (x k + (1 / Mbar) • steepestDescentDirection f (x k)) := by
    -- Rewrite the exact-line-search value back to the next iterate.
    simpa [lineSearchObjective_apply, hNext, steepestDescentStep] using hOpt
  have hCompare :
      f (x k) - f (x (k + 1)) ≥
        f (x k) - f (x k + (1 / Mbar) • steepestDescentDirection f (x k)) := by
    linarith
  have hGoal :
      f (x k) - f (x (k + 1)) ≥
        (1 / (2 * Mbar)) * ‖gradient f (x k)‖ ^ (2 : ℕ) := by
    linarith [hCompare, hTrialStep]
  simpa [Mbar] using hGoal

/-- Chapter03 Theorem 3.1.3 (Global convergence theorem of the steepest descent method): if
`f : E → ℝ` on a real Hilbert space `E` is `C²`, the derivative of `gradient f` is globally
bounded in operator norm by a constant `M`, and `x`, `g`, `d`, `α` are generated by Algorithm
3.1.1 from `x₀` with tolerance `ε`, then the steepest descent method terminates at some finite
iteration, or `f (x k) ⟶ -∞`, or `gradient f (x k) ⟶ 0`. -/
theorem steepestDescent_globalConvergence
    (M : ℝ)
    (hC2 : ContDiff ℝ 2 f)
    (hHessianBound : ∀ y : E, ‖fderiv ℝ (gradient f) y‖ ≤ M)
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α) :
    (∃ k : ℕ, ‖gradient f (x k)‖ ≤ ε) ∨
      Tendsto (f ∘ x) atTop atBot ∨
      Tendsto (gradient f ∘ x) atTop (nhds 0) := by
  by_cases hStop : ∃ k : ℕ, ‖gradient f (x k)‖ ≤ ε
  · -- The theorem's stopping alternative is already available.
    exact Or.inl hStop
  · -- Route correction: after ruling out finite termination, promote the run to the Chapter 2
    -- one-step decrease estimate and then run the source telescoping argument.
    have hNotStopped : ∀ k : ℕ, ε < ‖gradient f (x k)‖ := by
      intro k
      by_contra hk
      exact hStop ⟨k, le_of_not_gt hk⟩
    have hStepDecrease :
        ∀ k : ℕ,
          f (x k) - f (x (k + 1)) ≥
            (1 / (2 * max M 1)) * ‖gradient f (x k)‖ ^ (2 : ℕ) :=
      steepestDescentStepDecrease_ge_half_inv_hessianBound_mul_gradientNormSq
        M hC2 hHessianBound hMethod hNotStopped
    have hObjectiveAntitone : Antitone (fun k : ℕ ↦ f (x k)) := by
      refine antitone_nat_of_succ_le fun k ↦ ?_
      have hNonneg :
          0 ≤ (1 / (2 * max M 1)) * ‖gradient f (x k)‖ ^ (2 : ℕ) := by
        positivity
      have hStep := hStepDecrease k
      linarith
    by_cases hGradTendsto : Tendsto (gradient f ∘ x) atTop (nhds 0)
    · exact Or.inr <| Or.inr hGradTendsto
    · obtain ⟨δ, hδ, hFreq⟩ := frequently_gradientNorm_ge_of_not_tendsto_zero hGradTendsto
      let drop : ℝ := (1 / (2 * max M 1)) * δ ^ (2 : ℕ)
      have hDropPos : 0 < drop := by
        positivity
      obtain ⟨φ, hφmono, hφfreq⟩ := extraction_of_frequently_atTop hFreq
      have hDropAtLargeGradient :
          ∀ n : ℕ, f (x (φ n)) - f (x (φ n + 1)) ≥ drop := by
        intro n
        have hStep := hStepDecrease (φ n)
        have hSq : δ ^ (2 : ℕ) ≤ ‖gradient f (x (φ n))‖ ^ (2 : ℕ) := by
          nlinarith [hδ, hφfreq n, norm_nonneg (gradient f (x (φ n)))]
        have hCoefNonneg : 0 ≤ 1 / (2 * max M 1) := by positivity
        dsimp [drop]
        nlinarith
      have hSubsequenceDrop :
          ∀ n : ℕ, f (x (φ n + 1)) ≤ f (x 0) - (((n + 1 : ℕ) : ℝ) * drop) := by
        intro n
        induction n with
        | zero =>
            have hMono0 : f (x (φ 0)) ≤ f (x 0) := hObjectiveAntitone (Nat.zero_le _)
            have hStep0 := hDropAtLargeGradient 0
            have hStep0' : f (x (φ 0 + 1)) ≤ f (x (φ 0)) - drop := by
              linarith
            have hGoal :
                f (x (φ 0)) - drop ≤ f (x 0) - (((0 + 1 : ℕ) : ℝ) * drop) := by
              norm_num
              linarith
            exact le_trans hStep0' hGoal
        | succ n ih =>
            have hMono :
                f (x (φ (n + 1))) ≤ f (x (φ n + 1)) := by
              exact hObjectiveAntitone (Nat.succ_le_of_lt (hφmono (Nat.lt_succ_self n)))
            have hStep := hDropAtLargeGradient (n + 1)
            have hStep' : f (x (φ (n + 1) + 1)) ≤ f (x (φ (n + 1))) - drop := by
              linarith
            have hMono' : f (x (φ (n + 1))) - drop ≤ f (x (φ n + 1)) - drop := by
              linarith
            have hGoal :
                f (x (φ n + 1)) - drop ≤
                  f (x 0) - (((n + 1 + 1 : ℕ) : ℝ) * drop) := by
              have hGoal' := sub_le_sub_right ih drop
              have hCast :
                  (((n + 1 + 1 : ℕ) : ℝ) * drop) =
                    (((n + 1 : ℕ) : ℝ) * drop) + drop := by
                norm_num [Nat.cast_add, add_mul, mul_add]
              rw [hCast]
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hGoal'
            exact le_trans hStep' (le_trans hMono' hGoal)
      have hAtBot' : Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot := by
        rw [tendsto_atTop_atBot_iff_of_antitone hObjectiveAntitone]
        intro b
        obtain ⟨N, hN⟩ := exists_nat_gt ((f (x 0) - b) / drop)
        refine ⟨φ N + 1, ?_⟩
        have hNReal : ((f (x 0) - b) / drop) < (N : ℝ) := by
          exact_mod_cast hN
        have hBoundN : f (x 0) - b < (N : ℝ) * drop := by
          exact (div_lt_iff₀ hDropPos).mp hNReal
        have hBound : f (x 0) - (((N + 1 : ℕ) : ℝ) * drop) ≤ b := by
          have hTail :
              f (x 0) - (((N + 1 : ℕ) : ℝ) * drop) ≤ f (x 0) - (N : ℝ) * drop := by
            calc
              f (x 0) - (((N + 1 : ℕ) : ℝ) * drop)
                  = f (x 0) - ((N : ℝ) * drop + drop) := by
                      norm_num [Nat.cast_add, add_mul, mul_add]
              _ ≤ f (x 0) - (N : ℝ) * drop := by
                    linarith
          have hHead : f (x 0) - (N : ℝ) * drop < b := by
            nlinarith
          exact le_trans hTail hHead.le
        exact le_trans (hSubsequenceDrop N) hBound
      exact Or.inr <| Or.inl <| by
        change Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot
        exact hAtBot'

/-- Companion form of `steepestDescent_globalConvergence`: the stopping alternative and the
gradient-decay alternative can be read directly on the recorded gradient data `g` carried by
`IsSteepestDescentMethod`. -/
theorem steepestDescent_globalConvergence_recordedGradient
    (M : ℝ)
    (hC2 : ContDiff ℝ 2 f)
    (hHessianBound : ∀ y : E, ‖fderiv ℝ (gradient f) y‖ ≤ M)
    (hMethod : IsSteepestDescentMethod f ε x₀ x g d α) :
    (∃ k : ℕ, ‖g k‖ ≤ ε) ∨
      Tendsto (f ∘ x) atTop atBot ∨
      Tendsto g atTop (nhds 0) := by
  have hg : gradient f ∘ x = g := by
    funext k
    exact hMethod.gradient_eq k
  rcases
      steepestDescent_globalConvergence M hC2 hHessianBound hMethod with
    hStop | hUnbounded | hGradient
  · left
    rcases hStop with ⟨k, hk⟩
    exact ⟨k, by simpa [hMethod.gradient_eq k] using hk⟩
  · right
    exact Or.inl hUnbounded
  · right
    exact Or.inr <| by simpa [hg] using hGradient

end
