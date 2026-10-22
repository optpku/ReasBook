/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace RelaxedRegularizedNewtonIteration

variable {stepMap : ℝ → E → E} {L : ℝ}

/-- The primitive cubic-regularization assumptions needed already for Theorem 4.1.3.1 along a
fixed relaxed regularized Newton trajectory. The later recurrence and summability consequences in
this theorem are derived API from this owner. -/
class HasCubicRegularizationRecurrenceHypotheses
    (method : RelaxedRegularizedNewtonIteration stepMap L) (f : E → ℝ) : Prop where
  /-- The initial least Hessian eigenvalue is positive. -/
  lambda0_pos : 0 < λ_min(∇²f(method 0))
  /-- The initial cubic-regularization decrement satisfies the textbook bootstrap bound
  `δ₀ ≤ 1 / 4`. -/
  delta0_le_quarter : cubicRegularizationDelta f (method 0) L ≤ (1 / 4 : ℝ)
  /-- The step length is controlled by the gradient norm and least Hessian eigenvalue. -/
  step_norm (k : ℕ) :
      ‖method (k + 1) - method k‖ ≤
        ‖∇ f (method k)‖ / λ_min(∇²f(method k))
  /-- The least Hessian eigenvalue obeys the one-step lower comparison. -/
  lambda_succ (k : ℕ) :
      λ_min(∇²f(method (k + 1))) ≥
        λ_min(∇²f(method k)) - L * ‖method (k + 1) - method k‖
  /-- The next gradient norm is bounded by the cubic-model error term. -/
  gradient_succ (k : ℕ) :
      ‖∇ f (method (k + 1))‖ ≤
        ((L + method.regularization k) / 2) * ‖method (k + 1) - method k‖ ^ (2 : ℕ)

/-- The full cubic-regularization theorem-family assumptions extend the recurrence owner from
Theorem 4.1.3.1 by the symmetric upper Hessian comparison needed in Theorem 4.1.3.2. -/
class HasCubicRegularizationHypotheses
    (method : RelaxedRegularizedNewtonIteration stepMap L) (f : E → ℝ) : Prop
    extends HasCubicRegularizationRecurrenceHypotheses method f where
  /-- The least Hessian eigenvalue obeys the one-step upper comparison coming from the same
  Hessian-Lipschitz control. -/
  lambda_succ_upper (k : ℕ) :
      λ_min(∇²f(method (k + 1))) ≤
        λ_min(∇²f(method k)) + L * ‖method (k + 1) - method k‖

end RelaxedRegularizedNewtonIteration

/- Theorem 4.1.3.1 lies in the cubic-regularization decrement-recurrence domain.

Sampled owner declarations:
* `RelaxedRegularizedNewtonIteration` in `Definition_4_1_5`, the chapter owner for the iterate
  sequence, regularization schedule, and admissible parameter range;
* `cubicRegularizationDelta` in `Definition_4_1_6`, the chapter owner for the decrement
  `L ‖∇f(x)‖ / λ_min(∇²f(x))^2`;
* `hessianLeastEigenvalue` in `Definition_4_1_6`, the owner for `λ_min(∇² f x)`;
* `HasEventuallySuperlinearErrorBound` in `Chap01/Definition_1_2_7`, the project owner for the
  quadratic scalar recurrence conclusion;
* `method.HasCubicRegularizationRecurrenceHypotheses f`, the source-facing owner for the
  assumptions used already in Theorem 4.1.3.1;
* `method.HasCubicRegularizationHypotheses f`, the extended theorem-family owner used later when
  the upper spectral envelope is needed.

Best owner abstraction:
* source-facing: the recurrence statements for the decrement sequence along a relaxed
  cubic-regularization trajectory;
* core/canonical: `RelaxedRegularizedNewtonIteration`,
  `method.HasCubicRegularizationRecurrenceHypotheses f`,
  `cubicRegularizationDelta`, and `HasEventuallySuperlinearErrorBound`;
* bridge/view: the local notation `δ`, which packages the decrement owner along the trajectory.

Primitive data:
* the objective `f`,
* the relaxed regularized Newton trajectory `method`,
* the recurrence hypothesis owner attached to `(method, f)`.

Derived API:
* positivity of the least Hessian eigenvalue along the trajectory,
* the one-step decrement recurrence,
* the quadratic and linear one-step corollaries,
* the canonical quadratic-rate witness,
* summability and total-sum consequences for the decrement sequence.
-/

section

open RelaxedRegularizedNewtonIteration

variable (L : ℝ) (f : E → ℝ) {stepMap : ℝ → E → E}
variable (method : RelaxedRegularizedNewtonIteration stepMap L)

local notation "δ" => fun k : ℕ ↦ cubicRegularizationDelta f (method k) L

/-- Helper for Theorem 4.1.3.1: every cubic-regularization decrement is nonnegative because it is
`L` times a norm divided by a square. -/
lemma cubicRegularizationDelta_nonneg
    (x : E) (hL : 0 ≤ L) :
    0 ≤ cubicRegularizationDelta f x L := by
  -- Unfold the decrement and use nonnegativity of the norm, the scalar `L`, and the squared
  -- denominator.
  rw [cubicRegularizationDelta_def]
  exact div_nonneg (mul_nonneg hL (norm_nonneg _)) (sq_nonneg _)

/-- Helper for Theorem 4.1.3.1: the raw step bound rewrites into the source estimate
`‖x_{k+1} - x_k‖ ≤ (λ_k / L) δ_k`. -/
lemma cubicRegularization_step_norm_le_lambda_mul_delta
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) (hLambda_k : 0 < λ_min(∇²f(method k))) :
    ‖method (k + 1) - method k‖ ≤
      (λ_min(∇²f(method k)) / L) * δ k := by
  have hL : 0 < L := method.L_pos
  have hdelta_k :
      δ k = L * ‖∇ f (method k)‖ / λ_min(∇²f(method k)) ^ (2 : ℕ) := by
    exact cubicRegularizationDelta_def f (method k) L
  -- Rewrite the raw norm bound exactly into the decrement form used in the source proof.
  calc
    ‖method (k + 1) - method k‖
        ≤ ‖∇ f (method k)‖ / λ_min(∇²f(method k)) :=
      hmethod.step_norm k
    _ = (λ_min(∇²f(method k)) / L) * δ k := by
      rw [hdelta_k]
      field_simp [hL.ne', hLambda_k.ne']

/-- Helper for Theorem 4.1.3.1: the one-step Hessian comparison yields
`(1 - δ_k) λ_k ≤ λ_{k+1}`. -/
lemma cubicRegularization_lambda_succ_ge_one_sub_delta_mul
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) (hLambda_k : 0 < λ_min(∇²f(method k))) :
    (1 - δ k) * λ_min(∇²f(method k)) ≤
      λ_min(∇²f(method (k + 1))) := by
  have hL : 0 < L := method.L_pos
  have hstep :=
    cubicRegularization_step_norm_le_lambda_mul_delta
      (L := L) (f := f) (method := method) hmethod k hLambda_k
  have hmul :
      L * ‖method (k + 1) - method k‖ ≤
        L * ((λ_min(∇²f(method k)) / L) * δ k) := by
    exact mul_le_mul_of_nonneg_left hstep hL.le
  have hsub :
      λ_min(∇²f(method k)) - L * ((λ_min(∇²f(method k)) / L) * δ k) ≤
        λ_min(∇²f(method k)) - L * ‖method (k + 1) - method k‖ := by
    exact sub_le_sub_left hmul _
  -- Substitute the rewritten step estimate into the Hessian lower comparison.
  calc
    (1 - δ k) * λ_min(∇²f(method k))
        = λ_min(∇²f(method k)) - L * ((λ_min(∇²f(method k)) / L) * δ k) := by
      field_simp [hL.ne']
    _ ≤ λ_min(∇²f(method k)) - L * ‖method (k + 1) - method k‖ :=
      hsub
    _ ≤ λ_min(∇²f(method (k + 1))) :=
      hmethod.lambda_succ k

/-- Helper for Theorem 4.1.3.1: under the bootstrap hypotheses
`λ_k > 0` and `δ_k ≤ 1 / 4`, the source fraction recurrence already holds at the next step. -/
lemma cubicRegularization_delta_step_le_fraction_of_quarter_bound
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) (hLambda_k : 0 < λ_min(∇²f(method k))) (hδk : δ k ≤ (1 / 4 : ℝ)) :
    δ (k + 1) ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) := by
  have hL : 0 < L := method.L_pos
  have hd_nonneg : 0 ≤ δ k :=
    cubicRegularizationDelta_nonneg (L := L) (f := f) (x := method k) hL.le
  have hone_sub_nonneg : 0 ≤ 1 - δ k := by
    linarith
  have hone_sub_pos : 0 < 1 - δ k := by
    linarith
  have hLambda_succ_lower :=
    cubicRegularization_lambda_succ_ge_one_sub_delta_mul
      (L := L) (f := f) (method := method) hmethod k hLambda_k
  have hLambda_succ_pos : 0 < λ_min(∇²f(method (k + 1))) := by
    -- The bootstrap inequality keeps the least Hessian eigenvalue strictly positive.
    exact lt_of_lt_of_le (mul_pos hone_sub_pos hLambda_k) hLambda_succ_lower
  have hreg :
      (L + method.regularization k) / 2 ≤ (3 / 2 : ℝ) * L := by
    have hMk := method.regularization_le_two_mul_L k
    linarith
  have hgrad :
      ‖∇ f (method (k + 1))‖ ≤
        ((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
    -- Replace the variable regularization parameter by the uniform bound `2L`.
    calc
      ‖∇ f (method (k + 1))‖
          ≤ ((L + method.regularization k) / 2) *
              ‖method (k + 1) - method k‖ ^ (2 : ℕ) :=
        hmethod.gradient_succ k
      _ ≤ ((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
        have hsq_nonneg : 0 ≤ ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
          positivity
        exact mul_le_mul_of_nonneg_right hreg hsq_nonneg
  have hstep :=
    cubicRegularization_step_norm_le_lambda_mul_delta
      (L := L) (f := f) (method := method) hmethod k hLambda_k
  have hstep_scaled :
      L * ‖method (k + 1) - method k‖ ≤
        λ_min(∇²f(method k)) * δ k := by
    have hmul : L * ‖method (k + 1) - method k‖ ≤
        L * ((λ_min(∇²f(method k)) / L) * δ k) := by
      exact mul_le_mul_of_nonneg_left hstep hL.le
    calc
      L * ‖method (k + 1) - method k‖
          ≤ L * ((λ_min(∇²f(method k)) / L) * δ k) :=
        hmul
      _ = λ_min(∇²f(method k)) * δ k := by
        field_simp [hL.ne']
  have hcross_left :
      (L * ‖method (k + 1) - method k‖) * (1 - δ k) ≤
        (λ_min(∇²f(method k)) * δ k) * (1 - δ k) := by
    exact mul_le_mul_of_nonneg_right hstep_scaled hone_sub_nonneg
  have hcross_right :
      (λ_min(∇²f(method k)) * δ k) * (1 - δ k) ≤
        δ k * λ_min(∇²f(method (k + 1))) := by
    have hmul := mul_le_mul_of_nonneg_left hLambda_succ_lower hd_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hcross :
      (L * ‖method (k + 1) - method k‖) * (1 - δ k) ≤
        λ_min(∇²f(method (k + 1))) * δ k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross_left.trans hcross_right
  have hratio :
      L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1))) ≤
        δ k / (1 - δ k) := by
    -- Cross-multiplication is legitimate because both denominators are strictly positive.
    field_simp [hLambda_succ_pos.ne', hone_sub_pos.ne']
    exact hcross
  have hratio_nonneg :
      0 ≤ L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1))) := by
    exact div_nonneg (mul_nonneg hL.le (norm_nonneg _)) hLambda_succ_pos.le
  have hratio_rhs_nonneg : 0 ≤ δ k / (1 - δ k) := by
    exact div_nonneg hd_nonneg hone_sub_nonneg
  have hratio_sq :
      (L * ‖method (k + 1) - method k‖ / λ_min(∇²f(method (k + 1)))) ^ (2 : ℕ) ≤
        (δ k / (1 - δ k)) ^ (2 : ℕ) := by
    exact (sq_le_sq₀ hratio_nonneg hratio_rhs_nonneg).2 hratio
  have hdelta_scaled :
      δ (k + 1) ≤
        (3 / 2 : ℝ) *
          (L * ‖method (k + 1) - method k‖ /
            λ_min(∇²f(method (k + 1)))) ^ (2 : ℕ) := by
    -- Rewrite the successor decrement so the numerator and denominator can be controlled
    -- separately by the gradient and Hessian estimates.
    have hdelta_succ :
        δ (k + 1) =
          L * ‖∇ f (method (k + 1))‖ /
            λ_min(∇²f(method (k + 1))) ^ (2 : ℕ) := by
      exact cubicRegularizationDelta_def f (method (k + 1)) L
    rw [hdelta_succ]
    calc
      L * ‖∇ f (method (k + 1))‖ / λ_min(∇²f(method (k + 1))) ^ (2 : ℕ)
          ≤
            L *
              (((3 / 2 : ℝ) * L) * ‖method (k + 1) - method k‖ ^ (2 : ℕ)) /
                λ_min(∇²f(method (k + 1))) ^ (2 : ℕ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgrad hL.le) (by positivity)
      _ =
          (3 / 2 : ℝ) *
            (L * ‖method (k + 1) - method k‖ /
              λ_min(∇²f(method (k + 1)))) ^ (2 : ℕ) := by
        field_simp [pow_two, hLambda_succ_pos.ne']
  -- The scaled step ratio is now exactly the source fraction recurrence.
  calc
    δ (k + 1)
        ≤
          (3 / 2 : ℝ) *
            (L * ‖method (k + 1) - method k‖ /
              λ_min(∇²f(method (k + 1)))) ^ (2 : ℕ) :=
      hdelta_scaled
    _ ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hratio_sq (by norm_num)

/-- Helper for Theorem 4.1.3.1: the source bootstrap invariant simultaneously keeps the least
Hessian eigenvalue positive and the decrement bounded by `1 / 4` at every iterate. -/
lemma cubicRegularization_bootstrap_invariant
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    ∀ k : ℕ, 0 < λ_min(∇²f(method k)) ∧ δ k ≤ (1 / 4 : ℝ) := by
  intro k
  induction k with
  | zero =>
      -- The initial iterate satisfies the bootstrap assumptions by hypothesis.
      exact ⟨hmethod.lambda0_pos, hmethod.delta0_le_quarter⟩
  | succ k ih =>
      rcases ih with ⟨hLambda_k, hδk⟩
      have hd_nonneg : 0 ≤ δ k :=
        cubicRegularizationDelta_nonneg (L := L) (f := f) (x := method k) (method.L_pos.le)
      have hone_sub_pos : 0 < 1 - δ k := by
        linarith
      have hLambda_succ_lower :=
        cubicRegularization_lambda_succ_ge_one_sub_delta_mul
          (L := L) (f := f) (method := method) hmethod k hLambda_k
      have hLambda_succ : 0 < λ_min(∇²f(method (k + 1))) := by
        -- Positivity propagates because the comparison factor `1 - δ_k` stays positive.
        exact lt_of_lt_of_le (mul_pos hone_sub_pos hLambda_k) hLambda_succ_lower
      have hfraction :=
        cubicRegularization_delta_step_le_fraction_of_quarter_bound
          (L := L) (f := f) (method := method) hmethod k hLambda_k hδk
      have hcoeff :
          (3 / 2 : ℝ) / (1 - δ k) ^ (2 : ℕ) ≤ (8 / 3 : ℝ) := by
        have hmain :
            (3 / 2 : ℝ) ≤ (8 / 3 : ℝ) * (1 - δ k) ^ (2 : ℕ) := by
          nlinarith
        exact (div_le_iff₀ (sq_pos_of_pos hone_sub_pos)).2 hmain
      have hquadratic : δ (k + 1) ≤ (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) := by
        -- Under `δ_k ≤ 1 / 4`, the source fraction factor is bounded by `16 / 9`.
        calc
          δ (k + 1) ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) :=
            hfraction
          _ = ((3 / 2 : ℝ) / (1 - δ k) ^ (2 : ℕ)) * (δ k) ^ (2 : ℕ) := by
            field_simp [pow_two, hone_sub_pos.ne']
          _ ≤ (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      have hlinear : δ (k + 1) ≤ (2 / 3 : ℝ) * δ k := by
        -- The bootstrap bound turns the quadratic recurrence into the advertised linear one.
        have hbound : (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) ≤ (2 / 3 : ℝ) * δ k := by
          nlinarith
        exact hquadratic.trans hbound
      have hδsucc : δ (k + 1) ≤ (1 / 4 : ℝ) := by
        linarith
      exact ⟨hLambda_succ, hδsucc⟩

/-- Theorem 4.1.3.1 (1): for a relaxed cubic-regularized Newton iteration satisfying the local
step, Hessian, and gradient estimates from the cubic model, the least Hessian eigenvalue stays
positive along the whole iterate sequence. -/
-- Proof sketch: argue by induction on `k`. The step estimate bounds `‖x_{k+1} - x_k‖` by
-- `λ_min(∇² f (x_k)) δ_k / L`; combining this with the Hessian Lipschitz lower bound gives
-- `λ_min(∇² f (x_{k+1})) ≥ (1 - δ_k) λ_min(∇² f (x_k)) > 0`.
theorem cubicRegularization_hessianLeastEigenvalue_pos
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    0 < λ_min(∇²f(method k)) :=
  by
  -- Read off positivity from the first component of the bootstrap invariant.
  exact (cubicRegularization_bootstrap_invariant
    (L := L) (f := f) (method := method) hmethod k).1

/-- Theorem 4.1.3.1 (2): under the cubic-regularization hypotheses, the decrement sequence
satisfies the first displayed one-step bound
`δ_{k+1} ≤ (3 / 2) (δ_k / (1 - δ_k))^2`. -/
-- Proof sketch: use the gradient estimate together with
-- `method.regularization k ≤ 2L`, and rewrite the step-length bound in terms of the decrement
-- `δ_k`.
theorem cubicRegularization_delta_step_le_fraction
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    δ (k + 1) ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) :=
  by
  rcases cubicRegularization_bootstrap_invariant
      (L := L) (f := f) (method := method) hmethod k with
    ⟨hLambda_k, hδk⟩
  -- The source fraction recurrence holds once the bootstrap hypotheses at step `k` are known.
  exact cubicRegularization_delta_step_le_fraction_of_quarter_bound
    (L := L) (f := f) (method := method) hmethod k hLambda_k hδk

/-- Theorem 4.1.3.1 (3): under the cubic-regularization hypotheses, the decrement sequence
satisfies the quadratic one-step estimate `δ_{k+1} ≤ (8 / 3) δ_k^2`. -/
-- Proof sketch: combine the first one-step estimate from
-- `cubicRegularization_delta_step_le_fraction` with the bootstrap bound `δ_k ≤ 1 / 4`.
theorem cubicRegularization_delta_step_le_quadratic
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    δ (k + 1) ≤ (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) :=
  by
  have hδk :=
    (cubicRegularization_bootstrap_invariant
      (L := L) (f := f) (method := method) hmethod k).2
  have hone_sub_pos : 0 < 1 - δ k := by
    linarith
  have hcoeff :
      (3 / 2 : ℝ) / (1 - δ k) ^ (2 : ℕ) ≤ (8 / 3 : ℝ) := by
    have hmain : (3 / 2 : ℝ) ≤ (8 / 3 : ℝ) * (1 - δ k) ^ (2 : ℕ) := by
      nlinarith
    exact (div_le_iff₀ (sq_pos_of_pos hone_sub_pos)).2 hmain
  -- Bound the denominator factor `(1 - δ_k)⁻²` by `16 / 9`.
  calc
    δ (k + 1) ≤ (3 / 2 : ℝ) * (δ k / (1 - δ k)) ^ (2 : ℕ) :=
      cubicRegularization_delta_step_le_fraction
        (L := L) (f := f) (method := method) hmethod k
    _ = ((3 / 2 : ℝ) / (1 - δ k) ^ (2 : ℕ)) * (δ k) ^ (2 : ℕ) := by
      field_simp [pow_two, hone_sub_pos.ne']
    _ ≤ (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

/-- Theorem 4.1.3.1 (4): under the cubic-regularization hypotheses, the decrement sequence
satisfies the linear one-step estimate `δ_{k+1} ≤ (2 / 3) δ_k`. -/
-- Proof sketch: combine the quadratic estimate
-- `cubicRegularization_delta_step_le_quadratic` with the bootstrap bound `δ_k ≤ 1 / 4`.
theorem cubicRegularization_delta_step_le_linear
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f)
    (k : ℕ) :
    δ (k + 1) ≤ (2 / 3 : ℝ) * δ k :=
  by
  have hδk :=
    (cubicRegularization_bootstrap_invariant
      (L := L) (f := f) (method := method) hmethod k).2
  have hd_nonneg : 0 ≤ δ k :=
    cubicRegularizationDelta_nonneg (L := L) (f := f) (x := method k) (method.L_pos.le)
  have hbound : (8 / 3 : ℝ) * (δ k) ^ (2 : ℕ) ≤ (2 / 3 : ℝ) * δ k := by
    nlinarith
  -- The quadratic decay strengthens to linear decay on the bootstrap interval `δ_k ≤ 1 / 4`.
  exact (cubicRegularization_delta_step_le_quadratic
    (L := L) (f := f) (method := method) hmethod k).trans hbound

/-- Helper for Theorem 4.1.3.1: the linear recurrence implies the geometric majorant
`δ_k ≤ δ_0 (2 / 3)^k`. -/
lemma cubicRegularization_delta_le_initial_mul_two_thirds_pow
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    ∀ k : ℕ, δ k ≤ δ 0 * (2 / 3 : ℝ) ^ k := by
  intro k
  induction k with
  | zero =>
      -- At the initial index, the geometric majorant is exact.
      simp
  | succ k ih =>
      -- Propagate the majorant by one application of the linear decay estimate.
      calc
        δ (k + 1) ≤ (2 / 3 : ℝ) * δ k :=
          cubicRegularization_delta_step_le_linear
            (L := L) (f := f) (method := method) hmethod k
        _ ≤ (2 / 3 : ℝ) * (δ 0 * (2 / 3 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = δ 0 * (2 / 3 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- Under the hypotheses of Theorem 4.1.3.1, the decrement sequence satisfies the canonical
quadratic-recurrence owner with the textbook constant `8 / 3`. -/
-- Proof sketch: apply `cubicRegularization_delta_step_le_quadratic` and package the same
-- constant `8 / 3` into `HasEventuallySuperlinearErrorBound δ 0 (8 / 3) 0`.
theorem cubicRegularization_delta_hasEventuallySuperlinearErrorBound
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    HasEventuallySuperlinearErrorBound δ 0 (8 / 3 : ℝ) 0 :=
  by
  -- Package the already proved quadratic recurrence into the canonical owner at lag `0`.
  exact HasEventuallySuperlinearErrorBound.of_quadratic_bound
    (fun k ↦ cubicRegularization_delta_step_le_quadratic
      (L := L) (f := f) (method := method) hmethod k)

/-- Under the hypotheses of Theorem 4.1.3.1, the decrement sequence admits a quadratic recurrence
bound in the source-facing existential form `∃ c > 0, HasEventuallySuperlinearErrorBound δ 0 c 0`.
-/
theorem cubicRegularization_delta_seq_has_quadratic_rate
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    ∃ c > 0, HasEventuallySuperlinearErrorBound δ 0 c 0 :=
  ⟨8 / 3, by norm_num,
    cubicRegularization_delta_hasEventuallySuperlinearErrorBound L f method hmethod⟩

/-- Under the hypotheses of Theorem 4.1.3.1, the decrement sequence is summable. -/
-- Proof sketch: the estimate `δ_{k+1} ≤ (2 / 3) δ_k` from
-- `cubicRegularization_delta_step_le_linear` compares the decrement sequence with the geometric
-- series of ratio `2 / 3`, which is summable.
theorem cubicRegularization_delta_seq_summable
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    Summable δ :=
  by
  have hgeom : Summable (fun k : ℕ ↦ (2 / 3 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hmajor :
      Summable (fun k : ℕ ↦ δ 0 * (2 / 3 : ℝ) ^ k) :=
    hgeom.mul_left _
  -- Compare the decrement sequence with its geometric majorant.
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro k
    exact cubicRegularizationDelta_nonneg
      (L := L) (f := f) (x := method k) (method.L_pos.le)
  · intro k
    exact cubicRegularization_delta_le_initial_mul_two_thirds_pow
      (L := L) (f := f) (method := method) hmethod k

/-- Under the hypotheses of Theorem 4.1.3.1, the total decrement is bounded by `1 - δ₀`;
equivalently, the textbook geometric-series estimate gives
`∑ δ_k ≤ 3 δ₀ ≤ 1 - δ₀`. -/
-- Proof sketch: use the geometric decay `δ_{k+1} ≤ (2 / 3) δ_k` from
-- `cubicRegularization_delta_step_le_linear` to compare the series with
-- `δ₀ * ∑ (2 / 3)^k = 3 δ₀`, and then use `δ₀ ≤ 1 / 4` to conclude `3 δ₀ ≤ 1 - δ₀`.
theorem tsum_cubicRegularization_delta_seq_le_one_sub_initial
    (hmethod : method.HasCubicRegularizationRecurrenceHypotheses f) :
    (∑' k, δ k) ≤ 1 - δ 0 :=
  by
  have hgeom : Summable (fun k : ℕ ↦ (2 / 3 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hmajor :
      Summable (fun k : ℕ ↦ δ 0 * (2 / 3 : ℝ) ^ k) :=
    hgeom.mul_left _
  have hsum_le :
      (∑' k, δ k) ≤ ∑' k, δ 0 * (2 / 3 : ℝ) ^ k := by
    exact (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hmethod).tsum_le_tsum
        (fun k ↦ cubicRegularization_delta_le_initial_mul_two_thirds_pow
          (L := L) (f := f) (method := method) hmethod k)
        hmajor
  have hmajor_tsum :
      (∑' k, δ 0 * (2 / 3 : ℝ) ^ k) = δ 0 * 3 := by
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num)]
    norm_num
  -- Evaluate the geometric series and use `δ₀ ≤ 1 / 4` to conclude `3 δ₀ ≤ 1 - δ₀`.
  calc
    (∑' k, δ k) ≤ ∑' k, δ 0 * (2 / 3 : ℝ) ^ k :=
      hsum_le
    _ = δ 0 * 3 := hmajor_tsum
    _ ≤ 1 - δ 0 := by
      nlinarith [hmethod.delta0_le_quarter]

end
