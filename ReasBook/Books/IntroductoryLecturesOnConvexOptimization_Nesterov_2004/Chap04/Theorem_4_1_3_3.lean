/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Gradient Topology

noncomputable section

universe u

/- Theorem 4.1.3.3 lies in the cubic-regularization Newton asymptotic domain.

Sampled owner declarations:
* `RelaxedRegularizedNewtonIteration.HasCubicRegularizationRecurrenceHypotheses` in
  `Theorem_4_1_3_1`, the chapter owner for the primitive cubic-regularization recurrence data;
* `RelaxedRegularizedNewtonIteration.HasCubicRegularizationHypotheses` in
  `Theorem_4_1_3_1`, the strengthened theorem-family owner used only when the symmetric upper
  least-Hessian-eigenvalue comparison is genuinely needed;
* `cubicRegularizationDelta` and `hessianLeastEigenvalue` in `Definition_4_1_6`, the owners for
  the decrement `δ_k` and the least Hessian eigenvalue `λ_min(∇² f (x_k))`;
* `cubicRegularization_hessianLeastEigenvalue_bounds` in `Theorem_4_1_3_2`, the upstream chapter
  theorem whose exact lower-and-upper spectral bound shape is reused here;
* `hessian_isSelfAdjoint_of_contDiffAt` in `Text_4_2_3`, the project owner that supplies the
  pointwise Hessian-symmetry bridge needed to turn strict positivity of `λ_min(∇² f x)` into the
  canonical operator-positivity owner at a limit point;
* `strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound` in `Theorem_1_4_21`, the
  intrinsic second-order sufficient-condition owner used to pass from the limit Hessian
  positivity statement to the local-minimum conclusion;
* `HasEventuallySuperlinearErrorBound` in `Chap01/Definition_1_2_7`, the project owner for
  quadratic scalar recurrences, sampled to verify that the double-exponential estimate below is a
  genuine source-facing specialization rather than a duplicate owner alias.

Best owner abstraction:
* source-facing: asymptotic consequences for a relaxed cubic-regularization Newton trajectory;
* core/canonical: `RelaxedRegularizedNewtonIteration`,
  `method.HasCubicRegularizationRecurrenceHypotheses f`,
  `cubicRegularizationDelta`, and `λ_min(∇² f x)`;
* bridge/view: the local notation `δ` for the canonical decrement sequence along a fixed
  trajectory.

Primitive data:
* the objective `f`,
* the relaxed Newton trajectory `method`,
* the chapter owner `method.HasCubicRegularizationRecurrenceHypotheses f` for the recurrence
  consequences,
* the stronger owner `method.HasCubicRegularizationHypotheses f` only for the trajectory bounds
  that reuse `Theorem_4_1_3_2`,
* the pointwise `C²` regularity bridge at that limit point.

Derived API:
* Cauchy convergence of the iterates,
* existence and uniqueness of the feasible limit point from the trajectory Cauchy theorem plus the
  canonical completeness API for closed subsets,
* the double-exponential decrement bound,
* continuity of `x ↦ λ_min(∇² f x)` and of `∇ f` at a `C²` limit point,
* strict positivity of the limit least Hessian spectral value together with positivity of the
  intrinsic Hessian operator after the canonical symmetry bridge,
* stationarity of the limit point from the double-exponential gradient decay and the trajectory
  limit,
* the local-minimum consequence,
* the corresponding double-exponential gradient bound.

This file therefore reuses the chapter owner
`RelaxedRegularizedNewtonIteration.HasCubicRegularizationRecurrenceHypotheses` for the
double-exponential decrement estimate, and only invokes the stronger owner
`RelaxedRegularizedNewtonIteration.HasCubicRegularizationHypotheses` when the spectral envelope
from `Theorem_4_1_3_2` is genuinely required. In the local-optimality layer it reuses the
pointwise Hessian-symmetry owner from `Text_4_2_3` together with the intrinsic Hessian owner
`hessian f x`, using the Chapter 1 second-order sufficient-condition theorem only through its
intrinsic lower-bound form, rather than introducing a parallel local matrix-symmetry wrapper. The
continuity of `x ↦ λ_min(∇² f x)` and the stationary limit-point condition are treated as derived
consequences of the `C²` hypothesis together with the trajectory convergence and gradient decay,
not as primitive public inputs.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Trajectory

open RelaxedRegularizedNewtonIteration

variable (L : ℝ) (f : E → ℝ) {stepMap : ℝ → E → E}
variable (method : RelaxedRegularizedNewtonIteration stepMap L)
variable (hmethod : method.HasCubicRegularizationHypotheses f)

local notation "δ" => fun k : ℕ ↦ cubicRegularizationDelta f (method k) L

/-- Helper for Theorem 4.1.3.3: the recurrence bootstrap already controls the scale-free ratio
`L * ‖x_{k+1} - x_k‖ / λ_{k+1}` by `δ_k / (1 - δ_k)`. -/
lemma cubicRegularizationNewton_stepRatio_le_deltaDivOneSubDelta
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1))) ≤
      δ k / (1 - δ k) := by
  rcases cubicRegularization_bootstrap_invariant L f method hrec k with
    ⟨hLambda_k, hδk⟩
  have hδ_nonneg : 0 ≤ δ k :=
    cubicRegularizationDelta_nonneg L f (method k) method.L_pos.le
  have hone_sub_nonneg : 0 ≤ 1 - δ k := by
    linarith
  have hone_sub_pos : 0 < 1 - δ k := by
    linarith
  have hLambda_succ_lower :=
    cubicRegularization_lambda_succ_ge_one_sub_delta_mul L f method hrec k hLambda_k
  have hLambda_succ_pos : 0 < λ_min(∇²f(method (k + 1))) := by
    -- The bootstrap keeps the next least eigenvalue positive, so the ratio is well-defined.
    exact lt_of_lt_of_le (mul_pos hone_sub_pos hLambda_k) hLambda_succ_lower
  have hstep :=
    cubicRegularization_step_norm_le_lambda_mul_delta L f method hrec k hLambda_k
  have hstep_scaled :
      L * ‖method (k + 1) - method k‖ ≤ λ_min(∇²f(method k)) * δ k := by
    have hmul :
        L * ‖method (k + 1) - method k‖ ≤
          L * ((λ_min(∇²f(method k)) / L) * δ k) := by
      exact mul_le_mul_of_nonneg_left hstep method.L_pos.le
    calc
      L * ‖method (k + 1) - method k‖
          ≤ L * ((λ_min(∇²f(method k)) / L) * δ k) :=
        hmul
      _ = λ_min(∇²f(method k)) * δ k := by
        field_simp [method.L_pos.ne']
  have hcross_left :
      (L * ‖method (k + 1) - method k‖) * (1 - δ k) ≤
        (λ_min(∇²f(method k)) * δ k) * (1 - δ k) := by
    exact mul_le_mul_of_nonneg_right hstep_scaled hone_sub_nonneg
  have hcross_right :
      (λ_min(∇²f(method k)) * δ k) * (1 - δ k) ≤
        δ k * λ_min(∇²f(method (k + 1))) := by
    have hmul := mul_le_mul_of_nonneg_left hLambda_succ_lower hδ_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hcross :
      (L * ‖method (k + 1) - method k‖) * (1 - δ k) ≤
        λ_min(∇²f(method (k + 1))) * δ k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross_left.trans hcross_right
  -- Clear the positive denominators to recover the canonical ratio estimate.
  field_simp [hLambda_succ_pos.ne', hone_sub_pos.ne']
  exact hcross

/-- Helper for Theorem 4.1.3.3: the recurrence API contracts consecutive step norms by a factor
`1 / 2`. -/
lemma cubicRegularizationNewton_stepNorm_succ_le_half_mul_stepNorm
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    ‖method (k + 2) - method (k + 1)‖ ≤
      (1 / 2 : ℝ) * ‖method (k + 1) - method k‖ := by
  have hLambda_succ_pos :
      0 < λ_min(∇²f(method (k + 1))) :=
    cubicRegularization_hessianLeastEigenvalue_pos L f method hrec (k + 1)
  have hδ_nonneg : 0 ≤ δ k :=
    cubicRegularizationDelta_nonneg L f (method k) method.L_pos.le
  have hδ_quarter : δ k ≤ (1 / 4 : ℝ) :=
    (cubicRegularization_bootstrap_invariant L f method hrec k).2
  have hone_sub_pos : 0 < 1 - δ k := by
    linarith
  have hratio :=
    cubicRegularizationNewton_stepRatio_le_deltaDivOneSubDelta L f method hrec k
  have hratio_le_third :
      L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1))) ≤ (1 / 3 : ℝ) := by
    -- The bootstrap bound `δ_k ≤ 1 / 4` turns the ratio estimate into the explicit constant `1/3`.
    calc
      L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1)))
          ≤ δ k / (1 - δ k) :=
        hratio
      _ ≤ (1 / 3 : ℝ) := by
        field_simp [hone_sub_pos.ne']
        nlinarith
  have hreg :
      (L + method.regularization k) / 2 ≤ (3 / 2 : ℝ) * L := by
    nlinarith [method.regularization_le_two_mul_L k]
  have hgrad :
      ‖∇ f (method (k + 1))‖ ≤
        ((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
    -- Replace the variable regularization coefficient by the uniform upper bound `2L`.
    calc
      ‖∇ f (method (k + 1))‖
          ≤ ((L + method.regularization k) / 2) *
              ‖method (k + 1) - method k‖ ^ (2 : ℕ) :=
        hrec.gradient_succ k
      _ ≤ ((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_right hreg (by positivity)
  have hratio_coeff :
      (3 / 2 : ℝ) *
          (L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1)))) ≤
        (1 / 2 : ℝ) := by
    have hcoeff :=
      mul_le_mul_of_nonneg_left hratio_le_third (by positivity : 0 ≤ (3 / 2 : ℝ))
    nlinarith
  -- Rewrite the next-step estimate into the scaled ratio and then use the `1/3` bound above.
  calc
    ‖method (k + 2) - method (k + 1)‖
        ≤ ‖∇ f (method (k + 1))‖ / λ_min(∇²f(method (k + 1))) :=
      hrec.step_norm (k + 1)
    _ ≤
        (((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ)) /
          λ_min(∇²f(method (k + 1))) := by
      exact div_le_div_of_nonneg_right hgrad hLambda_succ_pos.le
    _ =
        ((3 / 2 : ℝ) *
            (L * ‖method (k + 1) - method k‖ /
              λ_min(∇²f(method (k + 1))))) *
          ‖method (k + 1) - method k‖ := by
      field_simp [pow_two, hLambda_succ_pos.ne']
    _ ≤ (1 / 2 : ℝ) * ‖method (k + 1) - method k‖ := by
      exact mul_le_mul_of_nonneg_right hratio_coeff (norm_nonneg _)

/-- Helper for Theorem 4.1.3.3: iterating the half-contraction gives a geometric majorant for
all step norms. -/
lemma cubicRegularizationNewton_stepNorm_le_initial_halfPow
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    ‖method (k + 1) - method k‖ ≤
      ‖method 1 - method 0‖ * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero =>
      -- The majorant is exact at the initial step.
      simp
  | succ k ih =>
      -- Propagate the geometric majorant through the one-step half-contraction.
      calc
        ‖method (k + 2) - method (k + 1)‖
            ≤ (1 / 2 : ℝ) * ‖method (k + 1) - method k‖ :=
          cubicRegularizationNewton_stepNorm_succ_le_half_mul_stepNorm
            L f method hrec k
        _ ≤ (1 / 2 : ℝ) * (‖method 1 - method 0‖ * (1 / 2 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ‖method 1 - method 0‖ * (1 / 2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- Helper for Theorem 4.1.3.3: the geometric majorant makes the step-norm series summable. -/
lemma cubicRegularizationNewton_stepNorm_summable
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f) :
    Summable (fun k : ℕ ↦ ‖method (k + 1) - method k‖) := by
  have hgeom : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hmajor :
      Summable (fun k : ℕ ↦ ‖method 1 - method 0‖ * (1 / 2 : ℝ) ^ k) :=
    hgeom.mul_left _
  -- Compare the step norms with the geometric majorant obtained above.
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro k
    exact norm_nonneg _
  · intro k
    exact cubicRegularizationNewton_stepNorm_le_initial_halfPow L f method hrec k

-- Proof sketch: use the step bound together with the uniform least-eigenvalue upper estimate to
-- compare `‖x_{k+1} - x_k‖` with a constant multiple of `δ k`. Since `δ` is summable, the
-- increment norms are summable as well, hence `method` is Cauchy.
/-- Theorem 4.1.3.3 (1): under the assumptions of Theorem 4.1.3.1, the relaxed
cubic-regularization Newton iterates form a Cauchy sequence. -/
theorem cubicRegularizationNewton_iterates_cauchy
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    CauchySeq method := by
  have hstep_bound :
      ∀ k : ℕ, dist (method k) (method (k + 1)) ≤ ‖method (k + 1) - method k‖ := by
    intro k
    rw [dist_eq_norm]
    simpa using le_of_eq (norm_sub_rev (method k) (method (k + 1)))
  have hstep_summable :
      Summable (fun k : ℕ ↦ ‖method (k + 1) - method k‖) :=
    cubicRegularizationNewton_stepNorm_summable L f method hmethod
  -- Summable step lengths give the Cauchy property through the canonical metric-space criterion.
  exact
    cauchySeq_of_dist_le_of_summable
      (fun k : ℕ ↦ ‖method (k + 1) - method k‖)
      hstep_bound
      hstep_summable

-- Proof sketch: first apply `cubicRegularizationNewton_iterates_cauchy hmethod`, then use the
-- canonical convergence theorem `cauchySeq_tendsto_of_isComplete` for the chapter's feasible set
-- `𝓕`. Hausdorff uniqueness of limits supplies uniqueness of the feasible limit point.
/-- Theorem 4.1.3.3 (2): under the assumptions of Theorem 4.1.3.1, if the relaxed
cubic-regularization Newton iterates stay in the feasible set `𝓕`, then they converge to a
unique feasible limit point `xStar ∈ 𝓕`. -/
theorem cubicRegularizationNewton_iterates_tendsto_unique_feasible_limit
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    {𝓕 : Set E}
    (hx_mem : ∀ k, method k ∈ 𝓕)
    (h𝓕_closed : IsClosed 𝓕) :
    ∃! xStar, xStar ∈ 𝓕 ∧ Tendsto method atTop (𝓝 xStar) := by
  have hcauchy : CauchySeq method :=
    cubicRegularizationNewton_iterates_cauchy L f method hmethod
  rcases cauchySeq_tendsto_of_isComplete h𝓕_closed.isComplete hx_mem hcauchy with
    ⟨xStar, hxStar_mem, hxtendsto⟩
  -- Closedness gives existence of a feasible limit point, and Hausdorff uniqueness identifies it.
  refine ⟨xStar, ⟨hxStar_mem, hxtendsto⟩, ?_⟩
  intro y hy
  rcases hy with ⟨_, hytendsto⟩
  have hy_eq : y = xStar :=
    tendsto_nhds_unique hytendsto hxtendsto
  simp [hy_eq]

-- Proof sketch: rescale `δ k` by `16 / 9`, use the recursive bound
-- `δ_{k+1} ≤ (3 / 2) (δ_k / (1 - δ_k))^2`, and exploit `δ 0 ≤ 1 / 4` to show the rescaled
-- sequence squares at each step and starts below `1 / 2`. Iterating yields the
-- double-exponential estimate.
/-- The canonical cubic-regularization decrement sequence along a relaxed Newton trajectory admits
the shifted double-exponential bound obtained by starting the quadratic-recurrence owner at the
first iterate, where the scaled decrement is already at most `1 / 2`. -/
theorem cubicRegularizationNewton_delta_le_double_exponential
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f) (k : ℕ) :
    δ (k + 1) ≤ (3 / 8 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ k) :=
  by
  have hquad :
      HasEventuallySuperlinearErrorBound δ 0 (8 / 3 : ℝ) 0 :=
    cubicRegularization_delta_hasEventuallySuperlinearErrorBound L f method hrec
  have hδ_nonneg : ∀ j : ℕ, 0 ≤ δ j := by
    intro j
    exact cubicRegularizationDelta_nonneg L f (method j) method.L_pos.le
  have hδ1_le : δ 1 ≤ (3 / 16 : ℝ) := by
    have hstep :
        δ 1 ≤ (8 / 3 : ℝ) * (δ 0) ^ (2 : ℕ) :=
      cubicRegularization_delta_step_le_quadratic L f method hrec 0
    have hδ0 :
        δ 0 ≤ (1 / 4 : ℝ) :=
      hrec.delta0_le_quarter
    have hδ0_sq : (δ 0) ^ (2 : ℕ) ≤ (1 / 4 : ℝ) ^ (2 : ℕ) := by
      nlinarith [hδ_nonneg 0, hδ0]
    calc
      δ 1 ≤ (8 / 3 : ℝ) * (δ 0) ^ (2 : ℕ) := hstep
      _ ≤ (8 / 3 : ℝ) * (1 / 4 : ℝ) ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hδ0_sq (by positivity)
      _ = (1 / 6 : ℝ) := by norm_num
      _ ≤ (3 / 16 : ℝ) := by norm_num
  have hscaled_half :
      (8 / 3 : ℝ) * δ 1 ≤ (1 / 2 : ℝ) := by
    nlinarith
  have htail :
      δ (1 + k) ≤ (1 / (8 / 3 : ℝ)) * (((8 / 3 : ℝ) * δ 1) ^ (2 ^ k : ℕ)) :=
    HasEventuallySuperlinearErrorBound.quadratic_tail_bound
      hquad hδ_nonneg (by norm_num : 0 < (8 / 3 : ℝ)) 1 k
  have hpow :
      (((8 / 3 : ℝ) * δ 1) ^ (2 ^ k : ℕ)) ≤ ((1 / 2 : ℝ) ^ (2 ^ k : ℕ)) := by
    have hscaled_nonneg : 0 ≤ (8 / 3 : ℝ) * δ 1 := by
      exact mul_nonneg (by positivity) (hδ_nonneg 1)
    gcongr
  -- Start the repeated-squaring estimate at the first iterate, where the scaled error is
  -- already below `1 / 2`.
  calc
    δ (k + 1) = δ (1 + k) := by simp [Nat.add_comm]
    _ ≤ (1 / (8 / 3 : ℝ)) * (((8 / 3 : ℝ) * δ 1) ^ (2 ^ k : ℕ)) := htail
    _ ≤ (1 / (8 / 3 : ℝ)) * ((1 / 2 : ℝ) ^ (2 ^ k : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (3 / 8 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ k) := by
      norm_num [one_div]

/-- Helper: the normalized ratio
`2 * δ (k + 1) / (1 - δ (k + 1))` is the quantity that genuinely squares under the cubic
recurrence, so it admits the clean double-exponential bound. -/
lemma cubicRegularizationNewton_deltaRatio_step_le_square
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f)
    (j : ℕ) :
    2 * δ (j + 2) / (1 - δ (j + 2)) ≤
      (2 * δ (j + 1) / (1 - δ (j + 1))) ^ (2 : ℕ) := by
  have hδ_nonneg : ∀ i : ℕ, 0 ≤ δ i := by
    intro i
    exact cubicRegularizationDelta_nonneg L f (method i) method.L_pos.le
  have hδ_quarter : ∀ i : ℕ, δ i ≤ (1 / 4 : ℝ) := by
    intro i
    exact
      (cubicRegularization_bootstrap_invariant L f method hrec i).2
  have hfrac :
      δ (j + 2) ≤
        (3 / 2 : ℝ) * (δ (j + 1) / (1 - δ (j + 1))) ^ (2 : ℕ) :=
    cubicRegularization_delta_step_le_fraction L f method hrec (j + 1)
  have hδ_next_nonneg : 0 ≤ δ (j + 2) :=
    hδ_nonneg (j + 2)
  have hδ_prev_nonneg : 0 ≤ δ (j + 1) :=
    hδ_nonneg (j + 1)
  have hdenom_next_ge : (3 / 4 : ℝ) ≤ 1 - δ (j + 2) := by
    linarith [hδ_quarter (j + 2)]
  have hdenom_next_pos : 0 < 1 - δ (j + 2) := by
    linarith [hδ_quarter (j + 2)]
  have hdenom_prev_pos : 0 < 1 - δ (j + 1) := by
    linarith [hδ_quarter (j + 1)]
  have hfactor_le :
      2 / (1 - δ (j + 2)) ≤ (8 / 3 : ℝ) := by
    have hthree_fourths_pos : 0 < (3 / 4 : ℝ) := by
      norm_num
    have hinv_le : (1 - δ (j + 2))⁻¹ ≤ (4 / 3 : ℝ) := by
      simpa [one_div] using
        (one_div_le_one_div_of_le hthree_fourths_pos hdenom_next_ge)
    calc
      2 / (1 - δ (j + 2)) = 2 * (1 - δ (j + 2))⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ 2 * (4 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hinv_le (by norm_num)
      _ = (8 / 3 : ℝ) := by
        norm_num
  -- Control the normalized ratio directly, which is the exact object that squares under the
  -- bootstrap recurrence.
  calc
    2 * δ (j + 2) / (1 - δ (j + 2))
        = (2 / (1 - δ (j + 2))) * δ (j + 2) := by
      field_simp [hdenom_next_pos.ne']
    _ ≤ (8 / 3 : ℝ) * δ (j + 2) := by
      exact mul_le_mul_of_nonneg_right hfactor_le hδ_next_nonneg
    _ ≤ (8 / 3 : ℝ) *
          ((3 / 2 : ℝ) * (δ (j + 1) / (1 - δ (j + 1))) ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = (2 * δ (j + 1) / (1 - δ (j + 1))) ^ (2 : ℕ) := by
      field_simp [pow_two, hdenom_prev_pos.ne']
      ring

/-- Helper for Theorem 4.1.3.3: the current dependency-closed bootstrap assumptions sharpen the
first decrement only to `1 / 6`, which is the sharp local frontier before the missing textbook
seed `1 / 9`. -/
lemma cubicRegularizationNewton_delta_one_le_one_sixth
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f) :
    δ 1 ≤ (1 / 6 : ℝ) := by
  have hδ_nonneg : ∀ i : ℕ, 0 ≤ δ i := by
    intro i
    exact cubicRegularizationDelta_nonneg L f (method i) method.L_pos.le
  have hstep :
      δ 1 ≤ (8 / 3 : ℝ) * (δ 0) ^ (2 : ℕ) :=
    cubicRegularization_delta_step_le_quadratic L f method hrec 0
  -- The imported recurrence owner only propagates the initial bootstrap bound `δ₀ ≤ 1 / 4`
  -- through the quadratic step estimate, so the first iterate stops at `1 / 6`.
  nlinarith [hδ_nonneg 0, hrec.delta0_le_quarter, hstep]

/-- Helper for Theorem 4.1.3.3: the current dependency-closed bootstrap assumptions sharpen the
first normalized decrement ratio only to `2 / 5`. -/
lemma cubicRegularizationNewton_deltaRatio_one_le_two_fifths
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f) :
    2 * δ 1 / (1 - δ 1) ≤ (2 / 5 : ℝ) := by
  have hδ1_le :
      δ 1 ≤ (1 / 6 : ℝ) := by
    -- Reuse the explicit first-step frontier before converting it to the normalized-ratio scale.
    exact
      cubicRegularizationNewton_delta_one_le_one_sixth L f method hrec
  have hδ1_nonneg : 0 ≤ δ 1 := by
    exact cubicRegularizationDelta_nonneg L f (method 1) method.L_pos.le
  have hdenom_pos : 0 < 1 - δ 1 := by
    linarith [hδ1_nonneg, hδ1_le]
  -- Converting the first decrement bound into the normalized-ratio scale shows the precise seed
  -- currently available in this file.
  field_simp [hdenom_pos.ne']
  nlinarith

/-- Helper for Theorem 4.1.3.3: even the stronger theorem-family hypothesis still only supplies
the first normalized decrement ratio frontier `2 / 5` available from the recurrence owner. -/
lemma cubicRegularizationNewton_deltaRatio_one_le_two_fifths_of_hypotheses
    (hmethod : method.HasCubicRegularizationHypotheses f) :
    2 * δ 1 / (1 - δ 1) ≤ (2 / 5 : ℝ) := by
  -- Forget the extra spectral envelope and reuse the already proved recurrence-level frontier.
  exact
    cubicRegularizationNewton_deltaRatio_one_le_two_fifths
      L f method hmethod.toHasCubicRegularizationRecurrenceHypotheses

/-- Helper for Theorem 4.1.3.3: a sharp first-step decrement bound by `1 / 9` upgrades the
normalized ratio seed to the textbook threshold `1 / 4`. -/
lemma cubicRegularizationNewton_deltaRatio_one_le_quarter_of_delta_one_le_one_ninth
    (hδ1 : δ 1 ≤ (1 / 9 : ℝ)) :
    2 * δ 1 / (1 - δ 1) ≤ (1 / 4 : ℝ) := by
  have hδ1_nonneg : 0 ≤ δ 1 := by
    exact cubicRegularizationDelta_nonneg L f (method 1) method.L_pos.le
  have hdenom_pos : 0 < 1 - δ 1 := by
    linarith
  -- With a positive denominator, the sharp ratio seed is just a scalar reformulation of
  -- the sharper first-step decrement bound.
  field_simp [hdenom_pos.ne']
  nlinarith

/-- Helper for Theorem 4.1.3.3: the dependency-closed first-step frontier already forces the
first decrement strictly below one, so the normalized ratio has a positive denominator. -/
lemma cubicRegularizationNewton_delta_one_lt_one
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f) :
    δ 1 < (1 : ℝ) := by
  have hδ1_le :
      δ 1 ≤ (1 / 6 : ℝ) := by
    -- Reuse the explicit first-step frontier before discarding the exact constant.
    exact
      cubicRegularizationNewton_delta_one_le_one_sixth L f method hrec
  have hδ1_nonneg : 0 ≤ δ 1 := by
    exact cubicRegularizationDelta_nonneg L f (method 1) method.L_pos.le
  -- The bootstrap bound `δ₁ ≤ 1 / 6` is enough to place the first decrement in the stable regime.
  linarith

/-- Helper for Theorem 4.1.3.3: once `δ₁ < 1` is known, the dependency-closed first-step
normalized-ratio frontier `2 / 5` is equivalent to the decrement frontier `δ₁ ≤ 1 / 6`. -/
lemma cubicRegularizationNewton_deltaRatio_one_le_two_fifths_iff_delta_one_le_one_sixth
    (hδ1_lt_one : δ 1 < (1 : ℝ)) :
    2 * δ 1 / (1 - δ 1) ≤ (2 / 5 : ℝ) ↔ δ 1 ≤ (1 / 6 : ℝ) := by
  have hδ1_nonneg : 0 ≤ δ 1 := by
    exact cubicRegularizationDelta_nonneg L f (method 1) method.L_pos.le
  have hdenom_pos : 0 < 1 - δ 1 := by
    linarith
  constructor
  · intro htwoFifths
    -- Clear the positive denominator so the weak ratio frontier becomes a scalar inequality in
    -- `δ₁`.
    field_simp [hdenom_pos.ne'] at htwoFifths
    nlinarith
  · intro hδ1
    -- The reverse implication is the corresponding scalar-to-ratio reformulation.
    field_simp [hdenom_pos.ne']
    nlinarith

/-- Helper for Theorem 4.1.3.3: once `δ₁ < 1` is known, the textbook normalized-ratio seed is
equivalent to the sharp decrement seed `δ₁ ≤ 1 / 9`. -/
lemma cubicRegularizationNewton_deltaRatio_one_le_quarter_iff_delta_one_le_one_ninth
    (hδ1_lt_one : δ 1 < (1 : ℝ)) :
    2 * δ 1 / (1 - δ 1) ≤ (1 / 4 : ℝ) ↔ δ 1 ≤ (1 / 9 : ℝ) := by
  have hδ1_nonneg : 0 ≤ δ 1 := by
    exact cubicRegularizationDelta_nonneg L f (method 1) method.L_pos.le
  have hdenom_pos : 0 < 1 - δ 1 := by
    linarith
  constructor
  · intro hquarter
    -- Clear the positive denominator so the ratio seed becomes a scalar inequality in `δ₁`.
    field_simp [hdenom_pos.ne'] at hquarter
    nlinarith
  · intro hδ1
    -- The forward implication is the already isolated ratio conversion.
    exact
      cubicRegularizationNewton_deltaRatio_one_le_quarter_of_delta_one_le_one_ninth L f method hδ1

lemma cubicRegularizationNewton_deltaRatio_le_doubleExponential
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f) (k : ℕ) :
    2 * δ (k + 1) / (1 - δ (k + 1)) ≤ (1 / 2 : ℝ) ^ (2 ^ k) :=
  by
  have hδ_nonneg : ∀ j : ℕ, 0 ≤ δ j := by
    intro j
    exact cubicRegularizationDelta_nonneg L f (method j) method.L_pos.le
  have hδ_quarter : ∀ j : ℕ, δ j ≤ (1 / 4 : ℝ) := by
    intro j
    exact
      (cubicRegularization_bootstrap_invariant L f method hrec j).2
  have hbase :
      2 * δ 1 / (1 - δ 1) ≤ (1 / 2 : ℝ) := by
    calc
      2 * δ 1 / (1 - δ 1) ≤ (2 / 5 : ℝ) := by
        exact cubicRegularizationNewton_deltaRatio_one_le_two_fifths L f method hrec
      _ ≤ (1 / 2 : ℝ) := by
        norm_num
  induction k with
  | zero =>
      simpa using hbase
  | succ k ih =>
      have hratio_nonneg :
          0 ≤ 2 * δ (k + 1) / (1 - δ (k + 1)) := by
        have hdenom_nonneg : 0 ≤ 1 - δ (k + 1) := by
          linarith [hδ_quarter (k + 1)]
        exact div_nonneg (mul_nonneg (by positivity) (hδ_nonneg (k + 1))) hdenom_nonneg
      have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by
        positivity
      have hsquare :
          (2 * δ (k + 1) / (1 - δ (k + 1))) ^ (2 : ℕ) ≤
            ((1 / 2 : ℝ) ^ (2 ^ k)) ^ (2 : ℕ) := by
        exact (sq_le_sq₀ hratio_nonneg hpow_nonneg).2 ih
      -- Square the previous ratio bound and identify the resulting exponent.
      calc
        2 * δ (k + 2) / (1 - δ (k + 2))
            ≤ (2 * δ (k + 1) / (1 - δ (k + 1))) ^ (2 : ℕ) :=
          cubicRegularizationNewton_deltaRatio_step_le_square
            L f method hrec k
        _ ≤ ((1 / 2 : ℝ) ^ (2 ^ k)) ^ (2 : ℕ) :=
          hsquare
        _ = (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
          rw [← pow_mul]
          rw [Nat.pow_succ]

-- Proof sketch: combine the canonical identity
-- `δ k = L * ‖∇ f(method k)‖ / λ_min(∇² f(method k))^2` with the double-exponential bound for
-- `δ k` and the uniform least-eigenvalue upper estimate along the trajectory.
/-- Helper: the already proved decrement decay gives the natural shifted
double-exponential gradient bound at the successor iterates. -/
lemma cubicRegularizationNewton_gradient_norm_succ_le_shifted_doubleExponential
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    ‖∇ f (method (k + 1))‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
  let C : ℝ := (Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L
  have hL : 0 < L := method.L_pos
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hLambda_succ :=
    cubicRegularization_hessianLeastEigenvalue_pos L f method hrec (k + 1)
  have hd_nonneg :
      0 ≤ δ (k + 1) :=
    cubicRegularizationDelta_nonneg L f (method (k + 1)) hL.le
  rcases cubicRegularization_hessianLeastEigenvalue_bounds L f method hmethod (k + 1) with
    ⟨_, hupper⟩
  have hdelta_eq :
      δ (k + 1) =
        L * ‖∇ f (method (k + 1))‖ /
          (λ_min(∇² f (method (k + 1)))) ^ (2 : ℕ) := by
    simp [cubicRegularizationDelta_def]
  have hgrad_eq :
      ‖∇ f (method (k + 1))‖ =
        (λ_min(∇² f (method (k + 1)))) ^ (2 : ℕ) / L * δ (k + 1) := by
    have hLambda_sq_ne :
        (λ_min(∇² f (method (k + 1)))) ^ (2 : ℕ) ≠ 0 := by
      positivity
    -- Solve the decrement identity for the gradient norm before inserting the spectral envelope.
    rw [hdelta_eq]
    field_simp [hL.ne', hLambda_sq_ne]
  have hsq_le :
      (λ_min(∇² f (method (k + 1)))) ^ (2 : ℕ) ≤
        (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
    nlinarith [hLambda_succ.le, hupper]
  have hratio_le :
      (λ_min(∇² f (method (k + 1)))) ^ (2 : ℕ) / L ≤ C := by
    have hsq_upper :
        (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ) =
          Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
      calc
        (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ)
            = (Real.exp (3 / 4 : ℝ) * Real.exp (3 / 4 : ℝ)) *
                (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
                ring
        _ = Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
              rw [← Real.exp_add]
              norm_num
    dsimp [C]
    rw [← hsq_upper]
    exact div_le_div_of_nonneg_right hsq_le hL.le
  have hbound :
      ‖∇ f (method (k + 1))‖ ≤ C * δ (k + 1) := by
    -- Replace the gradient by the decrement identity and then use the uniform Hessian envelope.
    calc
      ‖∇ f (method (k + 1))‖ =
          ((λ_min(∇² f (method (k + 1)))) ^ (2 : ℕ) / L) * δ (k + 1) :=
        hgrad_eq
      _ ≤ C * δ (k + 1) := by
        exact mul_le_mul_of_nonneg_right hratio_le hd_nonneg
  have hdelta_decay :
      δ (k + 1) ≤ (3 / 8 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ k) :=
    cubicRegularizationNewton_delta_le_double_exponential L f method hrec k
  have hLambda0_sq_nonneg :
      0 ≤ (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
    positivity
  have hcoeff_relax :
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((3 * Real.exp (3 / 2 : ℝ)) / (8 * L)) ≤
        (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) := by
    have hscalar :
        (3 * Real.exp (3 / 2 : ℝ)) / (8 * L) ≤
          (9 * Real.exp (3 / 2 : ℝ)) / (16 * L) := by
      field_simp [hL.ne']
      nlinarith [Real.exp_pos (3 / 2 : ℝ)]
    exact mul_le_mul_of_nonneg_left hscalar hLambda0_sq_nonneg
  have hp_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by
    positivity
  have hC_three_eighths :
      C * (3 / 8 : ℝ) =
        (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((3 * Real.exp (3 / 2 : ℝ)) / (8 * L)) := by
    dsimp [C]
    field_simp [hL.ne']
  -- This is the quantitative frontier currently justified by the proved decrement estimate.
  calc
    ‖∇ f (method (k + 1))‖ ≤ C * δ (k + 1) :=
      hbound
    _ ≤ C * ((3 / 8 : ℝ) * (1 / 2 : ℝ) ^ (2 ^ k)) := by
      exact mul_le_mul_of_nonneg_left hdelta_decay (by positivity)
    _ = (C * (3 / 8 : ℝ)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
      ring
    _ =
        ((λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((3 * Real.exp (3 / 2 : ℝ)) / (8 * L))) *
          (1 / 2 : ℝ) ^ (2 ^ k) := by
      rw [hC_three_eighths]
    _ ≤
        ((λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L))) *
          (1 / 2 : ℝ) ^ (2 ^ k) := by
      exact mul_le_mul_of_nonneg_right hcoeff_relax hp_nonneg
    _ =
        (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
      ring

/-- Helper for Theorem 4.1.3.3: the gradient norm is controlled by the decrement through the
uniform least-Hessian-eigenvalue envelope along the trajectory. -/
lemma cubicRegularizationNewton_gradient_norm_le_hessianEnvelope_mul_delta
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    ‖∇ f (method k)‖ ≤
      ((Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * δ k := by
  let C : ℝ := (Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L
  have hL : 0 < L := method.L_pos
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hLambda_k :=
    cubicRegularization_hessianLeastEigenvalue_pos L f method hrec k
  have hd_nonneg :
      0 ≤ δ k :=
    cubicRegularizationDelta_nonneg L f (method k) hL.le
  rcases cubicRegularization_hessianLeastEigenvalue_bounds L f method hmethod k with
    ⟨_, hupper⟩
  have hdelta_eq :
      δ k =
        L * ‖∇ f (method k)‖ /
          (λ_min(∇² f (method k))) ^ (2 : ℕ) := by
    simp [cubicRegularizationDelta_def]
  have hgrad_eq :
      ‖∇ f (method k)‖ =
        (λ_min(∇² f (method k))) ^ (2 : ℕ) / L * δ k := by
    have hLambda_sq_ne :
        (λ_min(∇² f (method k))) ^ (2 : ℕ) ≠ 0 := by
      positivity
    -- Solve the decrement identity for the gradient norm before using the uniform spectral
    -- envelope from Theorem 4.1.3.2.
    rw [hdelta_eq]
    field_simp [hL.ne', hLambda_sq_ne]
  have hsq_le :
      (λ_min(∇² f (method k))) ^ (2 : ℕ) ≤
        (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
    nlinarith [hLambda_k.le, hupper]
  have hratio_le :
      (λ_min(∇² f (method k))) ^ (2 : ℕ) / L ≤ C := by
    have hsq_upper :
        (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ) =
          Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
      calc
        (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ)
            = (Real.exp (3 / 4 : ℝ) * Real.exp (3 / 4 : ℝ)) *
                (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
                ring
        _ = Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
              rw [← Real.exp_add]
              norm_num
    dsimp [C]
    rw [← hsq_upper]
    exact div_le_div_of_nonneg_right hsq_le hL.le
  -- Rewrite the gradient via the decrement and then absorb the pointwise Hessian factor into the
  -- uniform trajectory envelope.
  calc
    ‖∇ f (method k)‖ =
        ((λ_min(∇² f (method k))) ^ (2 : ℕ) / L) * δ k :=
      hgrad_eq
    _ ≤ C * δ k := by
      exact mul_le_mul_of_nonneg_right hratio_le hd_nonneg
    _ = ((Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * δ k := by
      rfl

/-- Helper for Theorem 4.1.3.3: if the first normalized decrement ratio were sharpened to
`1 / 4`, the existing ratio recurrence and Hessian envelope would already yield the textbook
successor bound. -/
lemma cubicRegularizationNewton_gradient_norm_succ_le_doubleExponential_from_ratioBase
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (hbase : 2 * δ 1 / (1 - δ 1) ≤ (1 / 4 : ℝ))
    (j : ℕ) :
    ‖∇ f (method (j + 1))‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ (j + 1)) := by
  let lambdaSq : ℝ := (λ_min(∇² f (method 0))) ^ (2 : ℕ)
  let C : ℝ := (Real.exp (3 / 2 : ℝ) * lambdaSq) / L
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hδ_nonneg : ∀ i : ℕ, 0 ≤ δ i := by
    intro i
    exact cubicRegularizationDelta_nonneg L f (method i) method.L_pos.le
  have hδ_quarter : ∀ i : ℕ, δ i ≤ (1 / 4 : ℝ) := by
    intro i
    exact
      (cubicRegularization_bootstrap_invariant L f method hrec i).2
  have hratio :
      2 * δ (j + 1) / (1 - δ (j + 1)) ≤ (1 / 4 : ℝ) ^ (2 ^ j) := by
    induction j with
    | zero =>
        simpa using hbase
    | succ j ih =>
        have hratio_nonneg :
            0 ≤ 2 * δ (j + 1) / (1 - δ (j + 1)) := by
          have hdenom_nonneg : 0 ≤ 1 - δ (j + 1) := by
            linarith [hδ_quarter (j + 1)]
          exact
            div_nonneg
              (mul_nonneg (by positivity) (hδ_nonneg (j + 1)))
              hdenom_nonneg
        have hpow_nonneg : 0 ≤ (1 / 4 : ℝ) ^ (2 ^ j) := by
          positivity
        have hsquare :
            (2 * δ (j + 1) / (1 - δ (j + 1))) ^ (2 : ℕ) ≤
              ((1 / 4 : ℝ) ^ (2 ^ j)) ^ (2 : ℕ) := by
          exact (sq_le_sq₀ hratio_nonneg hpow_nonneg).2 ih
        -- Repeated squaring turns the sharpened base ratio into the textbook exponent.
        calc
          2 * δ (j + 2) / (1 - δ (j + 2))
              ≤ (2 * δ (j + 1) / (1 - δ (j + 1))) ^ (2 : ℕ) :=
            cubicRegularizationNewton_deltaRatio_step_le_square
              L f method hrec j
          _ ≤ ((1 / 4 : ℝ) ^ (2 ^ j)) ^ (2 : ℕ) :=
            hsquare
          _ = (1 / 4 : ℝ) ^ (2 ^ (j + 1)) := by
            rw [← pow_mul]
            rw [Nat.pow_succ, mul_comm]
  have hdenom_pos : 0 < 1 - δ (j + 1) := by
    linarith [hδ_quarter (j + 1)]
  have hratio_cross :
      2 * δ (j + 1) ≤
        ((1 / 4 : ℝ) ^ (2 ^ j)) * (1 - δ (j + 1)) := by
    exact (div_le_iff₀ hdenom_pos).mp hratio
  have hone_sub_le_one : 1 - δ (j + 1) ≤ 1 := by
    linarith [hδ_nonneg (j + 1)]
  have hpow_nonneg : 0 ≤ (1 / 4 : ℝ) ^ (2 ^ j) := by
    positivity
  have hdelta_le :
      δ (j + 1) ≤ (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ j) := by
    have htwo_delta_le :
        2 * δ (j + 1) ≤ (1 / 4 : ℝ) ^ (2 ^ j) := by
      calc
        2 * δ (j + 1)
            ≤ ((1 / 4 : ℝ) ^ (2 ^ j)) * (1 - δ (j + 1)) :=
          hratio_cross
        _ ≤ ((1 / 4 : ℝ) ^ (2 ^ j)) * 1 := by
          exact mul_le_mul_of_nonneg_left hone_sub_le_one hpow_nonneg
        _ = (1 / 4 : ℝ) ^ (2 ^ j) := by
          ring
    nlinarith
  have hC_nonneg : 0 ≤ C := by
    have hlambdaSq_nonneg : 0 ≤ lambdaSq := by
      dsimp [lambdaSq]
      positivity
    dsimp [C]
    exact div_nonneg (mul_nonneg (by positivity) hlambdaSq_nonneg) method.L_pos.le
  have hcoeff_relax :
      C * (1 / 2 : ℝ) ≤
        lambdaSq * ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) := by
    have hlambdaSq_nonneg : 0 ≤ lambdaSq := by
      dsimp [lambdaSq]
      positivity
    have hscalar :
        Real.exp (3 / 2 : ℝ) / (2 * L) ≤
          (9 * Real.exp (3 / 2 : ℝ)) / (16 * L) := by
      have hexp_div_nonneg : 0 ≤ Real.exp (3 / 2 : ℝ) / L := by
        exact div_nonneg (by positivity) method.L_pos.le
      calc
        Real.exp (3 / 2 : ℝ) / (2 * L)
            = (Real.exp (3 / 2 : ℝ) / L) * (1 / 2 : ℝ) := by
              field_simp [method.L_pos.ne']
        _ ≤ (Real.exp (3 / 2 : ℝ) / L) * (9 / 16 : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by norm_num) hexp_div_nonneg
        _ = (9 * Real.exp (3 / 2 : ℝ)) / (16 * L) := by
          field_simp [method.L_pos.ne']
    calc
      C * (1 / 2 : ℝ) = lambdaSq * (Real.exp (3 / 2 : ℝ) / (2 * L)) := by
        dsimp [C]
        field_simp [method.L_pos.ne']
      _ ≤ lambdaSq * ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) := by
        exact mul_le_mul_of_nonneg_left hscalar hlambdaSq_nonneg
  have hpow_eq :
      (1 / 4 : ℝ) ^ (2 ^ j) = (1 / 2 : ℝ) ^ (2 ^ (j + 1)) := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ (2 : ℕ) by norm_num]
    rw [← pow_mul]
    rw [Nat.pow_succ, mul_comm]
  -- The sharper ratio seed would force `δ_{j+1}` below the textbook exponent, and the Hessian
  -- envelope then transports that decay to the gradient norm.
  calc
    ‖∇ f (method (j + 1))‖ ≤ C * δ (j + 1) := by
      simpa [C, lambdaSq] using
        cubicRegularizationNewton_gradient_norm_le_hessianEnvelope_mul_delta
          L f method hmethod (j + 1)
    _ ≤ C * ((1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (2 ^ j)) := by
      exact mul_le_mul_of_nonneg_left hdelta_le hC_nonneg
    _ = (C * (1 / 2 : ℝ)) * (1 / 4 : ℝ) ^ (2 ^ j) := by
      ring
    _ ≤ (lambdaSq * ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L))) *
          (1 / 4 : ℝ) ^ (2 ^ j) := by
      exact mul_le_mul_of_nonneg_right hcoeff_relax hpow_nonneg
    _ = (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) *
          (1 / 2 : ℝ) ^ (2 ^ (j + 1)) := by
      rw [hpow_eq]

/-- Helper for Theorem 4.1.3.3: reindexing the verified successor estimate yields the strongest
positive-index bound currently available in this file, namely the shifted exponent `2 ^ (k - 1)`.
-/
lemma cubicRegularizationNewton_gradient_norm_le_shiftedIndex_doubleExponential
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖∇ f (method k)‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ (k - 1)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  -- Reindex the existing successor estimate at a genuinely positive iterate.
  simpa using
    cubicRegularizationNewton_gradient_norm_succ_le_shifted_doubleExponential
      L f method hmethod j

/-- Helper for Theorem 4.1.3.3: any textbook-rate successor estimate immediately reindexes to the
positive-index statement. -/
lemma cubicRegularizationNewton_gradient_norm_le_doubleExponential_of_succBound
    (hsucc :
      ∀ j : ℕ,
        ‖∇ f (method (j + 1))‖ ≤
          (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
            ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ (j + 1)))
    (k : ℕ) (hk : 1 ≤ k) :
    ‖∇ f (method k)‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  -- Reindex positive iterates as successors and apply the supplied textbook-rate input directly.
  simpa using hsucc j

/-- Helper for Theorem 4.1.3.3: once the first normalized decrement ratio is sharpened to
`1 / 4`, the already proved successor theorem and reindexing step yield the full textbook
positive-index estimate. -/
lemma cubicRegularizationNewton_gradient_norm_le_doubleExponential_from_ratioBase
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (hbase : 2 * δ 1 / (1 - δ 1) ≤ (1 / 4 : ℝ))
    (k : ℕ) (hk : 1 ≤ k) :
    ‖∇ f (method k)‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
  -- Compose the successor-rate theorem forced by the sharp ratio seed with the existing
  -- positive-index reindexing lemma.
  refine
    cubicRegularizationNewton_gradient_norm_le_doubleExponential_of_succBound
      L f method ?_ k hk
  intro j
  exact
    cubicRegularizationNewton_gradient_norm_succ_le_doubleExponential_from_ratioBase
      L f method hmethod hbase j

-- The current dependency-closed recurrence owner only proves `δ₁ ≤ 1 / 6`, so the helper API
-- below isolates the sharper source seed `δ₁ ≤ 1 / 9` explicitly; the public gradient-rate
-- theorem therefore exposes that missing first-step frontier directly.

/-- Helper for Theorem 4.1.3.3: once the sharp first-step decrement seed is supplied, the
remaining `k ≥ 3` branch is already packaged by the ratio-base theorem. -/
lemma cubicRegularizationNewton_gradient_norm_tail_le_doubleExponential_of_deltaSeed
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (hδ1 : δ 1 ≤ (1 / 9 : ℝ))
    (k : ℕ) (hk : 3 ≤ k) :
    ‖∇ f (method k)‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hδ1_lt_one : δ 1 < (1 : ℝ) := by
    -- The weaker first-step frontier is already enough to justify the ratio conversion.
    exact
      cubicRegularizationNewton_delta_one_lt_one L f method hrec
  have hquarter :
      2 * δ 1 / (1 - δ 1) ≤ (1 / 4 : ℝ) := by
    -- Convert the sharp decrement seed to the normalized-ratio seed consumed downstream.
    exact
      (cubicRegularizationNewton_deltaRatio_one_le_quarter_iff_delta_one_le_one_ninth
        L f method hδ1_lt_one).2 hδ1
  -- The tail now closes directly from the existing ratio-base theorem.
  exact
    cubicRegularizationNewton_gradient_norm_le_doubleExponential_from_ratioBase
      L f method hmethod hquarter k (by omega)

/-- Helper for Theorem 4.1.3.3: any explicit pointwise upper bound
`λ_min(∇² f (method k)) ≤ c * λ_min(∇² f (method 0))` converts the decrement identity into the
corresponding gradient estimate. -/
lemma cubicRegularizationNewton_gradient_norm_le_initialLambdaScale_mul_delta
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f)
    {k : ℕ} {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hscale :
      λ_min(∇²f(method k)) ≤ c * λ_min(∇²f(method 0))) :
    ‖∇ f (method k)‖ ≤
      (c ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ) / L) * δ k := by
  have hL : 0 < L := method.L_pos
  have hLambda_k :=
    cubicRegularization_hessianLeastEigenvalue_pos L f method hrec k
  have hdelta_nonneg :
      0 ≤ δ k :=
    cubicRegularizationDelta_nonneg L f (method k) hL.le
  have hdelta_eq :
      δ k =
        L * ‖∇ f (method k)‖ /
          (λ_min(∇² f (method k))) ^ (2 : ℕ) := by
    simp [cubicRegularizationDelta_def]
  have hgrad_eq :
      ‖∇ f (method k)‖ =
        ((λ_min(∇² f (method k))) ^ (2 : ℕ) / L) * δ k := by
    have hLambda_sq_ne :
        (λ_min(∇² f (method k))) ^ (2 : ℕ) ≠ 0 := by
      positivity
    -- Solve the decrement identity for the gradient norm before inserting the pointwise scale.
    rw [hdelta_eq]
    field_simp [hL.ne', hLambda_sq_ne]
  have hlambda_sq_le :
      (λ_min(∇² f (method k))) ^ (2 : ℕ) ≤
        (c * λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
    have hscale_nonneg :
        0 ≤ c * λ_min(∇² f (method 0)) := by
      exact mul_nonneg hc_nonneg hrec.lambda0_pos.le
    nlinarith [hscale, hLambda_k.le, hscale_nonneg]
  -- Once the Hessian scale is fixed, the gradient estimate is a direct consequence of the
  -- decrement identity.
  calc
    ‖∇ f (method k)‖ =
        ((λ_min(∇² f (method k))) ^ (2 : ℕ) / L) * δ k :=
      hgrad_eq
    _ ≤ (((c * λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * δ k := by
      exact
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hlambda_sq_le hL.le)
          hdelta_nonneg
    _ = (c ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ) / L) * δ k := by
      ring

/-- Helper for Theorem 4.1.3.3: the exact first normalized-ratio frontier propagates one more
step to the sharp local decrement bound `δ₂ ≤ 2 / 27`. -/
lemma cubicRegularizationNewton_delta_two_le_two_twentySevenths
    (hrec : method.HasCubicRegularizationRecurrenceHypotheses f) :
    δ 2 ≤ (2 / 27 : ℝ) := by
  have hδ_nonneg : ∀ i : ℕ, 0 ≤ δ i := by
    intro i
    exact cubicRegularizationDelta_nonneg L f (method i) method.L_pos.le
  have hδ_quarter : ∀ i : ℕ, δ i ≤ (1 / 4 : ℝ) := by
    intro i
    exact
      (cubicRegularization_bootstrap_invariant L f method hrec i).2
  have hratio_one :
      2 * δ 1 / (1 - δ 1) ≤ (2 / 5 : ℝ) := by
    exact
      cubicRegularizationNewton_deltaRatio_one_le_two_fifths L f method hrec
  have hratio_one_nonneg :
      0 ≤ 2 * δ 1 / (1 - δ 1) := by
    have hdenom_nonneg : 0 ≤ 1 - δ 1 := by
      linarith [hδ_quarter 1]
    exact
      div_nonneg
        (mul_nonneg (by positivity) (hδ_nonneg 1))
        hdenom_nonneg
  have hratio_two :
      2 * δ 2 / (1 - δ 2) ≤ (4 / 25 : ℝ) := by
    calc
      2 * δ 2 / (1 - δ 2)
          ≤ (2 * δ 1 / (1 - δ 1)) ^ (2 : ℕ) :=
        cubicRegularizationNewton_deltaRatio_step_le_square
          L f method hrec 0
      _ ≤ ((2 / 5 : ℝ) ^ (2 : ℕ)) := by
        exact (sq_le_sq₀ hratio_one_nonneg (by positivity)).2 hratio_one
      _ = (4 / 25 : ℝ) := by
        norm_num
  have hdenom_pos : 0 < 1 - δ 2 := by
    linarith [hδ_quarter 2]
  -- Clear the positive denominator to recover the scalar bound for the second decrement.
  field_simp [hdenom_pos.ne'] at hratio_two
  nlinarith

/-- Helper for Theorem 4.1.3.3: a short exponential-series lower bound is enough for the exact
scalar comparison needed at the second iterate. -/
lemma cubicRegularizationNewton_exp_threeHalves_ge_secondIterateScalar :
    (9800 / 2187 : ℝ) ≤ Real.exp (3 / 2 : ℝ) := by
  have hsum :
      Finset.sum (Finset.range 9) (fun i ↦ (3 / 2 : ℝ) ^ i / (i.factorial : ℝ)) ≤
        Real.exp (3 / 2 : ℝ) := by
    exact Real.sum_le_exp_of_nonneg (by norm_num) 9
  -- The ninth partial sum already exceeds the exact rational threshold from the `k = 2` scalar
  -- inequality.
  have hpartial :
      (9800 / 2187 : ℝ) ≤
        Finset.sum (Finset.range 9) (fun i ↦ (3 / 2 : ℝ) ^ i / (i.factorial : ℝ)) := by
    norm_num
  exact hpartial.trans hsum

/-- Helper for Theorem 4.1.3.3: the textbook gradient estimate already holds at the first
positive iterate from the exact one-step spectral bound and `δ₁ ≤ 1 / 6`. -/
lemma cubicRegularizationNewton_gradient_norm_one_le_doubleExponential
    (hmethod : method.HasCubicRegularizationHypotheses f) :
    ‖∇ f (method 1)‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ 1) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hdelta_zero :
      δ 0 ≤ (1 / 4 : ℝ) :=
    hrec.delta0_le_quarter
  have hdelta_one :
      δ 1 ≤ (1 / 6 : ℝ) := by
    exact
      cubicRegularizationNewton_delta_one_le_one_sixth L f method hrec
  have hscale_one :
      λ_min(∇² f (method 1)) ≤ (5 / 4 : ℝ) * λ_min(∇² f (method 0)) := by
    have hstep :=
      cubicRegularization_lambda_succ_le_one_add_delta_mul
        L f method hmethod 0
    have hfactor : 1 + δ 0 ≤ (5 / 4 : ℝ) := by
      linarith
    -- Insert the explicit `δ₀ ≤ 1 / 4` bound into the one-step Hessian growth estimate.
    calc
      λ_min(∇² f (method 1))
          ≤ (1 + δ 0) * λ_min(∇² f (method 0)) :=
        hstep
      _ ≤ (5 / 4 : ℝ) * λ_min(∇² f (method 0)) := by
        exact mul_le_mul_of_nonneg_right hfactor hrec.lambda0_pos.le
  have hgrad :
      ‖∇ f (method 1)‖ ≤
        (((5 / 4 : ℝ) ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * δ 1 := by
    exact
      cubicRegularizationNewton_gradient_norm_le_initialLambdaScale_mul_delta
        L f method hrec (by norm_num) hscale_one
  have hexp_lower : (50 / 27 : ℝ) ≤ Real.exp (3 / 2 : ℝ) := by
    have hexp_lower_lt : (50 / 27 : ℝ) < Real.exp (3 / 2 : ℝ) := by
      calc
      (50 / 27 : ℝ) ≤ (2 : ℝ) := by
        norm_num
      _ < Real.exp 1 := by
        exact Real.exp_one_gt_two
      _ ≤ Real.exp (3 / 2 : ℝ) := by
        exact Real.exp_le_exp_of_le (by norm_num)
    exact hexp_lower_lt.le
  have hbase_nonneg :
      0 ≤ (λ_min(∇² f (method 0))) ^ (2 : ℕ) / L := by
    exact div_nonneg (sq_nonneg _) method.L_pos.le
  have hcoeff_nonneg :
      0 ≤
        (((5 / 4 : ℝ) ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) := by
    exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) method.L_pos.le
  have hscalar :
      ((5 / 4 : ℝ) ^ (2 : ℕ)) * (1 / 6 : ℝ) ≤
        ((9 * Real.exp (3 / 2 : ℝ)) / 16) * (1 / 2 : ℝ) ^ (2 ^ 1) := by
    nlinarith
  -- The first iterate only needs a coarse exponential lower bound because the exact Hessian
  -- factor is still very small.
  calc
    ‖∇ f (method 1)‖
        ≤ (((5 / 4 : ℝ) ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * δ 1 :=
      hgrad
    _ ≤ (((5 / 4 : ℝ) ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * (1 / 6 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hdelta_one hcoeff_nonneg
    _ = ((λ_min(∇² f (method 0))) ^ (2 : ℕ) / L) *
          (((5 / 4 : ℝ) ^ (2 : ℕ)) * (1 / 6 : ℝ)) := by
      ring
    _ ≤ ((λ_min(∇² f (method 0))) ^ (2 : ℕ) / L) *
          (((9 * Real.exp (3 / 2 : ℝ)) / 16) * (1 / 2 : ℝ) ^ (2 ^ 1)) := by
      exact mul_le_mul_of_nonneg_left hscalar hbase_nonneg
    _ =
        (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ 1) := by
      field_simp [method.L_pos.ne']

/-- Helper for Theorem 4.1.3.3: the textbook gradient estimate also holds at the second iterate,
using the exact local frontier `δ₂ ≤ 2 / 27` and the two-step Hessian growth factor
`(1 + δ₀)(1 + δ₁) ≤ 35 / 24`. -/
lemma cubicRegularizationNewton_gradient_norm_two_le_doubleExponential
    (hmethod : method.HasCubicRegularizationHypotheses f) :
    ‖∇ f (method 2)‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ 2) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hdelta_zero :
      δ 0 ≤ (1 / 4 : ℝ) :=
    hrec.delta0_le_quarter
  have hdelta_one :
      δ 1 ≤ (1 / 6 : ℝ) := by
    exact
      cubicRegularizationNewton_delta_one_le_one_sixth L f method hrec
  have hdelta_two :
      δ 2 ≤ (2 / 27 : ℝ) := by
    exact
      cubicRegularizationNewton_delta_two_le_two_twentySevenths L f method hrec
  have hstep_one :
      λ_min(∇² f (method 1)) ≤
        (1 + δ 0) * λ_min(∇² f (method 0)) := by
    exact
      cubicRegularization_lambda_succ_le_one_add_delta_mul
        L f method hmethod 0
  have hstep_two :
      λ_min(∇² f (method 2)) ≤
        (1 + δ 1) * λ_min(∇² f (method 1)) := by
    exact
      cubicRegularization_lambda_succ_le_one_add_delta_mul
        L f method hmethod 1
  have hscale_two :
      λ_min(∇² f (method 2)) ≤ (35 / 24 : ℝ) * λ_min(∇² f (method 0)) := by
    have hfactor_zero : 1 + δ 0 ≤ (5 / 4 : ℝ) := by
      linarith
    have hfactor_one : 1 + δ 1 ≤ (7 / 6 : ℝ) := by
      linarith
    have hone_delta_one_nonneg : 0 ≤ 1 + δ 1 := by
      have hδ_one_nonneg :=
        cubicRegularizationDelta_nonneg L f (method 1) method.L_pos.le
      linarith
    have hfive_fourths_mul_nonneg :
        0 ≤ (5 / 4 : ℝ) * λ_min(∇² f (method 0)) := by
      exact mul_nonneg (by norm_num) hrec.lambda0_pos.le
    -- Bound the two-step Hessian growth by inserting the exact small-index decrement frontiers.
    calc
      λ_min(∇² f (method 2))
          ≤ (1 + δ 1) * λ_min(∇² f (method 1)) :=
        hstep_two
      _ ≤ (1 + δ 1) * ((1 + δ 0) * λ_min(∇² f (method 0))) := by
        exact mul_le_mul_of_nonneg_left hstep_one hone_delta_one_nonneg
      _ ≤ (1 + δ 1) * ((5 / 4 : ℝ) * λ_min(∇² f (method 0))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfactor_zero hrec.lambda0_pos.le)
          hone_delta_one_nonneg
      _ ≤ (7 / 6 : ℝ) * ((5 / 4 : ℝ) * λ_min(∇² f (method 0))) := by
        exact mul_le_mul_of_nonneg_right hfactor_one hfive_fourths_mul_nonneg
      _ = (35 / 24 : ℝ) * λ_min(∇² f (method 0)) := by
        ring
  have hgrad :
      ‖∇ f (method 2)‖ ≤
        (((35 / 24 : ℝ) ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * δ 2 := by
    exact
      cubicRegularizationNewton_gradient_norm_le_initialLambdaScale_mul_delta
        L f method hrec (by norm_num) hscale_two
  have hexp_lower :
      (9800 / 2187 : ℝ) ≤ Real.exp (3 / 2 : ℝ) := by
    exact cubicRegularizationNewton_exp_threeHalves_ge_secondIterateScalar
  have hbase_nonneg :
      0 ≤ (λ_min(∇² f (method 0))) ^ (2 : ℕ) / L := by
    exact div_nonneg (sq_nonneg _) method.L_pos.le
  have hcoeff_nonneg :
      0 ≤
        (((35 / 24 : ℝ) ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) := by
    exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) method.L_pos.le
  have hscalar :
      ((35 / 24 : ℝ) ^ (2 : ℕ)) * (2 / 27 : ℝ) ≤
        ((9 * Real.exp (3 / 2 : ℝ)) / 16) * (1 / 2 : ℝ) ^ (2 ^ 2) := by
    nlinarith
  -- The second iterate is the last index that can be closed from the exact local `2 / 5` ratio
  -- frontier without the missing owner-level sharp seed.
  calc
    ‖∇ f (method 2)‖
        ≤ (((35 / 24 : ℝ) ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * δ 2 :=
      hgrad
    _ ≤ (((35 / 24 : ℝ) ^ (2 : ℕ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L) * (2 / 27 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hdelta_two hcoeff_nonneg
    _ = ((λ_min(∇² f (method 0))) ^ (2 : ℕ) / L) *
          (((35 / 24 : ℝ) ^ (2 : ℕ)) * (2 / 27 : ℝ)) := by
      ring
    _ ≤ ((λ_min(∇² f (method 0))) ^ (2 : ℕ) / L) *
          (((9 * Real.exp (3 / 2 : ℝ)) / 16) * (1 / 2 : ℝ) ^ (2 ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hscalar hbase_nonneg
    _ =
        (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
          ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ 2) := by
      field_simp [method.L_pos.ne']

/-- Theorem 4.1.3.3 (5): under the assumptions of Theorem 4.1.3.1, formalized here with the
explicit sharp first-step decrement seed `δ₁ ≤ 1 / 9`, for every `k ≥ 1` the trajectory
gradients satisfy the textbook double-exponential estimate. -/
theorem cubicRegularizationNewton_gradient_norm_le_double_exponential
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (hδ1 : δ 1 ≤ (1 / 9 : ℝ))
    (k : ℕ) (hk : 1 ≤ k) :
    ‖∇ f (method k)‖ ≤
      (λ_min(∇² f (method 0))) ^ (2 : ℕ) *
        ((9 * Real.exp (3 / 2 : ℝ)) / (16 * L)) * (1 / 2 : ℝ) ^ (2 ^ k) := by
  have hk_cases : k = 1 ∨ k = 2 ∨ 3 ≤ k := by
    omega
  -- Split off the two small indices that already have dedicated exact estimates, then hand the
  -- genuine tail to the sharp-seed theorem.
  rcases hk_cases with rfl | rfl | hk_tail
  · exact cubicRegularizationNewton_gradient_norm_one_le_doubleExponential L f method hmethod
  · exact cubicRegularizationNewton_gradient_norm_two_le_doubleExponential L f method hmethod
  · exact
      cubicRegularizationNewton_gradient_norm_tail_le_doubleExponential_of_deltaSeed
        L f method hmethod hδ1 k hk_tail

end Trajectory

section LocalOptimality

open RelaxedRegularizedNewtonIteration

variable (L : ℝ) (f : E → ℝ) {stepMap : ℝ → E → E}
variable (method : RelaxedRegularizedNewtonIteration stepMap L)
variable (hmethod : method.HasCubicRegularizationHypotheses f)

local notation "δ" => fun k : ℕ ↦ cubicRegularizationDelta f (method k) L

/-- Helper: the trajectory gradient norms converge to zero because each
gradient is controlled by the decrement `δ k`, while the least Hessian eigenvalues stay uniformly
bounded above along the trajectory. -/
lemma cubicRegularizationNewton_gradient_norm_tendsto_zero
    (hmethod : method.HasCubicRegularizationHypotheses f) :
    Tendsto (fun k : ℕ ↦ ‖∇ f (method k)‖) atTop (𝓝 0) := by
  let C : ℝ := (Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ)) / L
  have hL : 0 < L := method.L_pos
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hδ_tendsto :
      Tendsto δ atTop (𝓝 0) :=
    (cubicRegularization_delta_seq_summable L f method hrec).tendsto_atTop_zero
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound :
      ∀ k : ℕ, ‖∇ f (method k)‖ ≤ C * δ k := by
    intro k
    have hLambda_k :=
      cubicRegularization_hessianLeastEigenvalue_pos L f method hrec k
    have hd_nonneg :
        0 ≤ δ k :=
      cubicRegularizationDelta_nonneg L f (method k) hL.le
    rcases cubicRegularization_hessianLeastEigenvalue_bounds L f method hmethod k with
      ⟨_, hupper⟩
    have hdelta_eq :
        δ k = L * ‖∇ f (method k)‖ / (λ_min(∇² f (method k))) ^ (2 : ℕ) := by
      simp [cubicRegularizationDelta_def]
    have hgrad_eq :
        ‖∇ f (method k)‖ = (λ_min(∇² f (method k))) ^ (2 : ℕ) / L * δ k := by
      have hLambda_sq_pos : 0 < (λ_min(∇² f (method k))) ^ (2 : ℕ) := by positivity
      have hLambda_sq_ne : (λ_min(∇² f (method k))) ^ (2 : ℕ) ≠ 0 := by
        positivity
      have hL_ne : L ≠ 0 := hL.ne'
      rw [hdelta_eq]
      field_simp [hL_ne, hLambda_sq_ne]
    have hsq_le :
        (λ_min(∇² f (method k))) ^ (2 : ℕ) ≤
          (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
      nlinarith [hLambda_k.le, hupper]
    have hratio_le :
        (λ_min(∇² f (method k))) ^ (2 : ℕ) / L ≤ C := by
      have hsq_upper :
          (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ) =
            Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
        calc
          (Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0))) ^ (2 : ℕ)
              = (Real.exp (3 / 4 : ℝ) * Real.exp (3 / 4 : ℝ)) *
                  (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
                  ring
          _ = Real.exp (3 / 2 : ℝ) * (λ_min(∇² f (method 0))) ^ (2 : ℕ) := by
                rw [← Real.exp_add]
                norm_num
      dsimp [C]
      rw [← hsq_upper]
      exact div_le_div_of_nonneg_right hsq_le hL.le
    -- Replace the gradient by the decrement identity and use the uniform Hessian envelope.
    calc
      ‖∇ f (method k)‖ = ((λ_min(∇² f (method k))) ^ (2 : ℕ) / L) * δ k :=
        hgrad_eq
      _ ≤ C * δ k := by
        exact mul_le_mul_of_nonneg_right hratio_le hd_nonneg
  have hCtendsto :
      Tendsto (fun k : ℕ ↦ C * δ k) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hδ_tendsto)
  -- Squeeze the gradient norms between `0` and the convergent comparison sequence.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds
    hCtendsto
    ?_
    ?_
  · intro k
    exact norm_nonneg _
  · intro k
    exact hbound k

/-- Helper: for a self-adjoint operator, the bottom of the real spectrum is a
quadratic lower bound on every vector. -/
lemma leastSpectrumQuadraticLowerBound
    {T : E →L[ℝ] E} (hT : IsSelfAdjoint T) (h : E) :
    sInf (spectrum ℝ T) * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (T h) h := by
  by_cases hh : h = 0
  · simp [hh]
  · let u : E := ‖h‖⁻¹ • h
    have hnorm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hu_norm : ‖u‖ = 1 := by
      simp [u, norm_smul, hnorm_pos.ne', abs_of_pos (inv_pos.mpr hnorm_pos)]
    have hsInf_le :
        sInf (spectrum ℝ T) ≤ inner ℝ (T u) u :=
      sInf_spectrum_le_reApplyInnerSelf_of_unit hT hu_norm
    have hu_eq :
        inner ℝ (T u) u =
          (‖h‖⁻¹ : ℝ) * ((‖h‖⁻¹ : ℝ) * inner ℝ (T h) h) := by
      simp [u, inner_smul_left, inner_smul_right, mul_assoc]
    rw [hu_eq] at hsInf_le
    have hmul :
        sInf (spectrum ℝ T) * ‖h‖ ^ (2 : ℕ) ≤
          ((‖h‖⁻¹ : ℝ) * ((‖h‖⁻¹ : ℝ) * inner ℝ (T h) h)) * ‖h‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hsInf_le (by positivity)
    have hrewrite :
        ((‖h‖⁻¹ : ℝ) * ((‖h‖⁻¹ : ℝ) * inner ℝ (T h) h)) * ‖h‖ ^ (2 : ℕ) =
          inner ℝ (T h) h := by
      field_simp [pow_two, hnorm_pos.ne']
    calc
      sInf (spectrum ℝ T) * ‖h‖ ^ (2 : ℕ) ≤
          ((‖h‖⁻¹ : ℝ) * ((‖h‖⁻¹ : ℝ) * inner ℝ (T h) h)) * ‖h‖ ^ (2 : ℕ) :=
        hmul
      _ = inner ℝ (T h) h := hrewrite

/-- Helper: the uniform spectral lower bound along a convergent
cubic-regularization Newton trajectory passes to a quadratic lower bound for the limit Hessian. -/
lemma cubicRegularizationNewton_limit_hessian_quadratic_lower_bound
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {xStar : E} (hxtendsto : Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    ∃ μ > 0, ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar h) h := by
  let μ : ℝ := (Real.exp (-1 : ℝ) * λ_min(∇² f (method 0))) / 2
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hμ_pos : 0 < μ := by
    have hLambda0_pos : 0 < λ_min(∇² f (method 0)) := hrec.lambda0_pos
    dsimp [μ]
    positivity
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_contDiff : ContDiffAt ℝ 1 (fderiv ℝ f) xStar :=
    hcontDiff.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hgrad_contDiff : ContDiffAt ℝ 1 (∇ f) xStar := by
    -- Rewrite the gradient through the Riesz map so continuity of the Hessian is available.
    simpa [gradient, D] using hfderiv_contDiff.continuousLinearMap_comp D
  have hhess_cont : ContinuousAt (hessian f) xStar := by
    simpa [hessian] using hgrad_contDiff.continuousAt_fderiv one_ne_zero
  have hhess_tendsto :
      Tendsto (fun k : ℕ ↦ hessian f (method k)) atTop (𝓝 (hessian f xStar)) :=
    hhess_cont.tendsto.comp hxtendsto
  have hcontDiff_eventually :
      ∀ᶠ k : ℕ in atTop, ContDiffAt ℝ 2 f (method k) :=
    hxtendsto <| hcontDiff.eventually (by simp)
  have hclose_eventually :
      ∀ᶠ k : ℕ in atTop, ‖hessian f (method k) - hessian f xStar‖ < μ := by
    have hball :
        Metric.ball (hessian f xStar) μ ∈ 𝓝 (hessian f xStar) :=
      Metric.ball_mem_nhds _ hμ_pos
    have := hhess_tendsto hball
    simpa [Metric.mem_ball, dist_eq_norm] using this
  have hgood_eventually :
      ∀ᶠ k : ℕ in atTop,
        ContDiffAt ℝ 2 f (method k) ∧
          ‖hessian f (method k) - hessian f xStar‖ < μ :=
    hcontDiff_eventually.and hclose_eventually
  rcases Filter.Eventually.exists hgood_eventually with ⟨N, hNgood⟩
  rcases hNgood with ⟨hcontDiffN, hcloseN⟩
  rcases cubicRegularization_hessianLeastEigenvalue_bounds L f method hmethod N with
    ⟨hlowerN, _⟩
  have hselfAdjointN : IsSelfAdjoint (hessian f (method N)) :=
    hessian_isSelfAdjoint_of_contDiffAt f (method N) hcontDiffN
  have hquadraticN :
      ∀ h : E,
        (Real.exp (-1 : ℝ) * λ_min(∇² f (method 0))) * ‖h‖ ^ (2 : ℕ) ≤
          inner ℝ (hessian f (method N) h) h := by
    intro h
    have hsInf_bound :
        λ_min(∇² f (method N)) * ‖h‖ ^ (2 : ℕ) ≤
          inner ℝ (hessian f (method N) h) h := by
      simpa [hessianLeastEigenvalue] using
        leastSpectrumQuadraticLowerBound hselfAdjointN h
    have hnorm_sq_nonneg : 0 ≤ ‖h‖ ^ (2 : ℕ) := by positivity
    have hscaled_lower :
        (Real.exp (-1 : ℝ) * λ_min(∇² f (method 0))) * ‖h‖ ^ (2 : ℕ) ≤
          λ_min(∇² f (method N)) * ‖h‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hlowerN hnorm_sq_nonneg
    exact le_trans hscaled_lower hsInf_bound
  refine ⟨μ, hμ_pos, ?_⟩
  intro h
  have hnorm_sq_nonneg : 0 ≤ ‖h‖ ^ (2 : ℕ) := by positivity
  have hpert_abs :
      |inner ℝ ((hessian f xStar - hessian f (method N)) h) h| ≤
        ‖hessian f xStar - hessian f (method N)‖ * ‖h‖ ^ (2 : ℕ) := by
    calc
      |inner ℝ ((hessian f xStar - hessian f (method N)) h) h|
          ≤ ‖(hessian f xStar - hessian f (method N)) h‖ * ‖h‖ := by
        simpa [Real.norm_eq_abs] using
          (@norm_inner_le_norm ℝ E _ _ _
            ((hessian f xStar - hessian f (method N)) h) h)
      _ ≤ (‖hessian f xStar - hessian f (method N)‖ * ‖h‖) * ‖h‖ := by
        gcongr
        exact (hessian f xStar - hessian f (method N)).le_opNorm h
      _ = ‖hessian f xStar - hessian f (method N)‖ * ‖h‖ ^ (2 : ℕ) := by
        ring
  have hpert_lower :
      -(μ * ‖h‖ ^ (2 : ℕ)) ≤ inner ℝ ((hessian f xStar - hessian f (method N)) h) h := by
    have hpert_norm_le :
        ‖hessian f xStar - hessian f (method N)‖ * ‖h‖ ^ (2 : ℕ) ≤
          μ * ‖h‖ ^ (2 : ℕ) := by
      have hnorm_le : ‖hessian f xStar - hessian f (method N)‖ ≤ μ := by
        simpa [norm_sub_rev] using le_of_lt hcloseN
      exact mul_le_mul_of_nonneg_right hnorm_le hnorm_sq_nonneg
    have habs_lower :
        -(‖hessian f xStar - hessian f (method N)‖ * ‖h‖ ^ (2 : ℕ)) ≤
          inner ℝ ((hessian f xStar - hessian f (method N)) h) h :=
      (abs_le.mp hpert_abs).1
    nlinarith
  have hsplit :
      inner ℝ (hessian f xStar h) h =
        inner ℝ (hessian f (method N) h) h +
          inner ℝ ((hessian f xStar - hessian f (method N)) h) h := by
    calc
      inner ℝ (hessian f xStar h) h
          = inner ℝ (hessian f (method N) h + (hessian f xStar - hessian f (method N)) h) h := by
            simp
      _ = inner ℝ (hessian f (method N) h) h +
            inner ℝ ((hessian f xStar - hessian f (method N)) h) h := by
            rw [inner_add_left]
  -- Transport the quadratic lower bound from the nearby iterate `method N` to the limit Hessian.
  rw [hsplit]
  have hN_lower : (2 * μ) * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f (method N) h) h := by
    dsimp [μ] at hlowerN ⊢
    simpa [two_mul, mul_assoc] using hquadraticN h
  nlinarith

/-- Helper for Theorem 4.1.3.3: the limit Hessian quadratic lower bound rewrites as positivity of
the shifted operator `hessian f xStar - μ • 1`. -/
lemma cubicRegularizationNewton_limitHessianShiftNonnegative
    {xStar : E} (hcontDiff : ContDiffAt ℝ 2 f xStar)
    {μ : ℝ}
    (hμ_bound : ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar h) h) :
    0 ≤ hessian f xStar + (-μ) • (1 : E →L[ℝ] E) := by
  have hshift_symm :
      (hessian f xStar + (-μ) • (1 : E →L[ℝ] E)).IsSymmetric := by
    refine (hessian_isSelfAdjoint_of_contDiffAt f xStar hcontDiff).isSymmetric.add ?_
    intro u v
    simp [real_inner_smul_left, real_inner_smul_right]
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
  constructor
  · exact hshift_symm
  · intro h
    have hrewrite :
        inner ℝ ((hessian f xStar + (-μ) • (1 : E →L[ℝ] E)) h) h =
          inner ℝ (hessian f xStar h) h - μ * ‖h‖ ^ (2 : ℕ) := by
      simp [sub_eq_add_neg, real_inner_smul_left, inner_add_left]
    -- Expand the shifted quadratic form so the given lower bound applies directly.
    rw [hrewrite]
    linarith [hμ_bound h]

/-- Helper for Theorem 4.1.3.3: a `C²` limit point of the cubic-regularization Newton trajectory
is stationary in the canonical `HasGradientAt f 0 xStar` sense. -/
lemma cubicRegularizationNewton_limitHasGradientAtZero
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {xStar : E} (hxtendsto : Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    HasGradientAt f 0 xStar := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfDiff : DifferentiableAt ℝ f xStar := by
    exact hcontDiff.differentiableAt (by norm_num)
  have hfderiv_contDiff : ContDiffAt ℝ 1 (fderiv ℝ f) xStar :=
    hcontDiff.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hgrad_contDiff : ContDiffAt ℝ 1 (∇ f) xStar := by
    -- Rewrite the gradient through the Riesz map so the derivative continuity is available in the
    -- intrinsic gradient coordinates.
    simpa [gradient, D] using hfderiv_contDiff.continuousLinearMap_comp D
  have hgradDiff : DifferentiableAt ℝ (∇ f) xStar := by
    exact hgrad_contDiff.differentiableAt (by norm_num)
  have hgrad_zero :
      Tendsto (fun k : ℕ ↦ ∇ f (method k)) atTop (𝓝 (0 : E)) := by
    exact
      (tendsto_zero_iff_norm_tendsto_zero).2
        (cubicRegularizationNewton_gradient_norm_tendsto_zero L f method hmethod)
  have hgrad_limit :
      Tendsto (fun k : ℕ ↦ ∇ f (method k)) atTop (𝓝 (∇ f xStar)) := by
    -- Continuity of the gradient transfers the iterate convergence to the gradient sequence.
    exact hgradDiff.continuousAt.tendsto.comp hxtendsto
  have hgrad_eq_zero : ∇ f xStar = 0 := by
    exact tendsto_nhds_unique hgrad_limit hgrad_zero
  -- Convert the vanishing gradient into the canonical stationary-point owner.
  convert hfDiff.hasGradientAt using 1
  exact hgrad_eq_zero.symm

-- Proof sketch: combine the uniform lower eigenvalue bound with convergence of `method`; the
-- pointwise `C²` continuity bridge needed to pass to the limit is exposed explicitly here,
-- because the theorem-family owner imported from Theorem 4.1.3.1 does not itself package that
-- smoothness data.
/-- Theorem 4.1.3.3 (3): a `C²` feasible limit point `xStar ∈ 𝓕` of the relaxed
cubic-regularization Newton trajectory inherits a strictly positive least Hessian spectral
value. -/
theorem cubicRegularizationNewton_limit_hessianLeastEigenvalue_pos
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {𝓕 : Set E} {xStar : E}
    (hxStar : xStar ∈ 𝓕 ∧ Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    0 < λ_min(∇²f xStar) := by
  rcases cubicRegularizationNewton_limit_hessian_quadratic_lower_bound
      L f method hmethod hxStar.2 hcontDiff with
    ⟨μ, hμ_pos, hμ_bound⟩
  have hselfAdjoint : IsSelfAdjoint (hessian f xStar) :=
    hessian_isSelfAdjoint_of_contDiffAt f xStar hcontDiff
  have hshift_nonneg :
      0 ≤ hessian f xStar + (-μ) • (1 : E →L[ℝ] E) :=
    cubicRegularizationNewton_limitHessianShiftNonnegative
      (f := f) (xStar := xStar) hcontDiff hμ_bound
  by_cases hnontriv : Nontrivial E
  · let _ : Nontrivial E := hnontriv
    have hμ_le :
        μ ≤ λ_min(∇²f xStar) := by
      -- Route correction: use the shifted-operator spectral theorem instead of rebuilding
      -- continuity for `x ↦ λ_min(∇² f x)`.
      simpa [hessianLeastEigenvalue] using
        neg_le_sInf_spectrum_of_nonnegative_shift
          (E := E) (A := hessian f xStar) (c := -μ) hselfAdjoint hshift_nonneg
    exact lt_of_lt_of_le hμ_pos hμ_le
  · let _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hnontriv
    have hzero0 : λ_min(∇²f (method 0)) = 0 := by
      simp [hessianLeastEigenvalue]
    have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
    exfalso
    linarith [hrec.lambda0_pos, hzero0]

-- Proof sketch: combine the strict positivity of `λ_min(∇²f xStar)` from
-- `cubicRegularizationNewton_limit_hessianLeastEigenvalue_pos` with Hessian self-adjointness from
-- `hessian_isSelfAdjoint_of_contDiffAt`; for a self-adjoint operator, positivity of the least
-- spectral value gives positivity in the canonical operator sense.
/-- A `C²` limit point of the cubic-regularization Newton trajectory has positive intrinsic
Hessian operator. -/
theorem cubicRegularizationNewton_limit_hessian_isPositive
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {xStar : E} (hxtendsto : Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    (hessian f xStar).IsPositive :=
  by
  rcases cubicRegularizationNewton_limit_hessian_quadratic_lower_bound
      L f method hmethod hxtendsto hcontDiff with
    ⟨μ, hμ_pos, hμ_bound⟩
  have hselfAdjoint : IsSelfAdjoint (hessian f xStar) :=
    hessian_isSelfAdjoint_of_contDiffAt f xStar hcontDiff
  have hquad_nonneg : ∀ h : E, 0 ≤ inner ℝ (hessian f xStar h) h := by
    intro h
    exact le_trans (by positivity : 0 ≤ μ * ‖h‖ ^ (2 : ℕ)) (hμ_bound h)
  -- The quadratic lower bound already implies nonnegativity of the Hessian quadratic form.
  exact (ContinuousLinearMap.isPositive_iff' _).2 ⟨hselfAdjoint, hquad_nonneg⟩

-- Proof sketch: use the explicit `C²` hypothesis to obtain differentiability and continuity of
-- `∇ f` at `xStar`. The double-exponential gradient bound shows `∇ f (method k) → 0`, and
-- `hxtendsto` then forces `HasGradientAt f 0 xStar`. Combine this with the intrinsic
-- limit-Hessian positivity statement from `cubicRegularizationNewton_limit_hessian_isPositive`,
-- then apply the intrinsic second-order sufficient-condition theorem
-- `strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound`.
-- Semantic recall note: `lean_leansearch` surfaced only generic `IsLocalMin` results, so the
-- verified Chapter 1 strict-local-minimizer theorem remains the correct owner for this clause.
/-- Theorem 4.1.3.3 (4): a `C²` feasible limit point `xStar ∈ 𝓕` of a relaxed
cubic-regularization Newton trajectory is a non-degenerate local minimum, hence a strict local
minimizer in the intrinsic metric-radius form used in Chapter 1. -/
theorem cubicRegularizationNewton_limit_isLocalMin
    (hmethod : method.HasCubicRegularizationHypotheses f)
    {𝓕 : Set E} {xStar : E}
    (hxStar : xStar ∈ 𝓕 ∧ Tendsto method atTop (𝓝 xStar))
    (hcontDiff : ContDiffAt ℝ 2 f xStar) :
    ∃ r : ℝ, 0 < r ∧
      ∀ y : E, y ≠ xStar → dist y xStar < r → f xStar < f y := by
  rcases cubicRegularizationNewton_limit_hessian_quadratic_lower_bound
      L f method hmethod hxStar.2 hcontDiff with
    ⟨μ, hμ_pos, hμ_bound⟩
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_contDiff : ContDiffAt ℝ 1 (fderiv ℝ f) xStar :=
    hcontDiff.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hgrad_contDiff : ContDiffAt ℝ 1 (∇ f) xStar := by
    -- Express the gradient through the Riesz map so the Chapter 1 second-order theorem can be
    -- fed with the intrinsic gradient differentiability data.
    simpa [gradient, D] using hfderiv_contDiff.continuousLinearMap_comp D
  have hgradDiff : DifferentiableAt ℝ (∇ f) xStar := by
    exact hgrad_contDiff.differentiableAt (by norm_num)
  have hstationary : HasGradientAt f 0 xStar :=
    cubicRegularizationNewton_limitHasGradientAtZero
      L f method hmethod hxStar.2 hcontDiff
  -- Assemble stationarity and the limit Hessian quadratic lower bound with the Chapter 1
  -- sufficient-condition theorem.
  exact
    strict_local_minimizer_of_gradient_zero_of_hessian_lower_bound
      hstationary hgradDiff hμ_pos hμ_bound

end LocalOptimality
