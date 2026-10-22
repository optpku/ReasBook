/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.1.3.2 lies in the cubic-regularization least-Hessian-eigenvalue domain.

Sampled owner declarations:
* `RelaxedRegularizedNewtonIteration` in `Definition_4_1_5`, the chapter owner for the iterate
  sequence, regularization schedule, and update law;
* `hessianLeastEigenvalue` and `cubicRegularizationDelta` in `Definition_4_1_6`, the owners for
  `λ_min(∇² f x)` and the decrement `δ_k`;
* `RelaxedRegularizedNewtonIteration.HasCubicRegularizationHypotheses` in `Theorem_4_1_3_1`,
  the shared theorem-family owner for the one-step least-eigenvalue comparisons, the decrement
  bootstrap assumptions, and the cubic-model estimates;
* `tsum_cubicRegularization_delta_seq_le_one_sub_initial` in `Theorem_4_1_3_1`, the upstream
  summability consequence reused by the present bound.

Best owner abstraction:
* source-facing: the uniform lower and upper bounds on `λ_min(∇² f (x_k))` along a relaxed
  cubic-regularization trajectory;
* core/canonical: `RelaxedRegularizedNewtonIteration`, `λ_min(∇² f x)`,
  `cubicRegularizationDelta`, and the shared hypothesis owner from `Theorem_4_1_3_1`;
* bridge/view: the local decrement notation `δ` attached to a fixed trajectory.

Primitive data:
* the objective `f`,
* the relaxed regularized Newton trajectory `method`,
* the shared hypothesis owner from Theorem 4.1.3.1.

Derived API:
* the exponential lower and upper bounds for `λ_min(∇² f (method k))`.
-/

section

open RelaxedRegularizedNewtonIteration

variable (L : ℝ) (f : E → ℝ) {stepMap : ℝ → E → E}
variable (method : RelaxedRegularizedNewtonIteration stepMap L)

local notation "δ" => fun k : ℕ ↦ cubicRegularizationDelta f (method k) L

-- Proof sketch: combine `hmethod.lambda_succ` and `hmethod.lambda_succ_upper` with the step
-- estimate to obtain
-- `λ_min(∇² f (x_{i+1})) ∈ [(1 - δ_i) λ_min(∇² f (x_i)), (1 + δ_i) λ_min(∇² f (x_i))]`.
-- The lower bound then comes from summing `log (1 - δ_i)`, while the upper bound comes from
-- summing `log (1 + δ_i)`. In both directions the controlling series estimate is supplied by the
-- theorem-family API from `Theorem_4_1_3_1`.
/-- Helper for Theorem 4.1.3.2: the one-step upper Hessian comparison rewrites into the
multiplicative estimate `λ_{k+1} ≤ (1 + δ_k) λ_k`. -/
lemma cubicRegularization_lambda_succ_le_one_add_delta_mul
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    λ_min(∇²f(method (k + 1))) ≤
      (1 + δ k) * λ_min(∇²f(method k)) := by
  have hL : 0 < L := method.L_pos
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hLambda_k :=
    cubicRegularization_hessianLeastEigenvalue_pos
      (L := L) (f := f) (method := method) hrec k
  have hstep :=
    cubicRegularization_step_norm_le_lambda_mul_delta
      (L := L) (f := f) (method := method) hrec k hLambda_k
  have hmul :
      L * ‖method (k + 1) - method k‖ ≤
        λ_min(∇²f(method k)) * δ k := by
    -- Rewrite the step-length estimate into the decrement form used by the source proof.
    calc
      L * ‖method (k + 1) - method k‖
          ≤ L * ((λ_min(∇²f(method k)) / L) * δ k) := by
        exact mul_le_mul_of_nonneg_left hstep hL.le
      _ = λ_min(∇²f(method k)) * δ k := by
        field_simp [hL.ne']
  -- Substitute the step-length control into the upper Hessian Lipschitz comparison.
  calc
    λ_min(∇²f(method (k + 1)))
        ≤ λ_min(∇²f(method k)) + L * ‖method (k + 1) - method k‖ :=
      hmethod.lambda_succ_upper k
    _ ≤ λ_min(∇²f(method k)) + λ_min(∇²f(method k)) * δ k := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hmul (λ_min(∇²f(method k)))
    _ = (1 + δ k) * λ_min(∇²f(method k)) := by
      ring

/-- Helper for Theorem 4.1.3.2: iterating the one-step multiplicative bounds sandwiches the least
Hessian eigenvalue between the corresponding finite products. -/
lemma cubicRegularization_hessianLeastEigenvalue_between_partial_products
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    (((Finset.prod (Finset.range k) fun i ↦ 1 - δ i) * λ_min(∇²f(method 0))) ≤
        λ_min(∇²f(method k))) ∧
      (λ_min(∇²f(method k)) ≤
        (Finset.prod (Finset.range k) fun i ↦ 1 + δ i) * λ_min(∇²f(method 0))) := by
  induction k with
  | zero =>
      -- At the initial index both finite products are empty, so the bounds are exact.
      simp
  | succ k ih =>
      rcases ih with ⟨hlower, hupper⟩
      have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
      have hLambda_k :=
        cubicRegularization_hessianLeastEigenvalue_pos
          (L := L) (f := f) (method := method) hrec k
      have hd_nonneg :
          0 ≤ δ k :=
        cubicRegularizationDelta_nonneg
          (L := L) (f := f) (x := method k) method.L_pos.le
      have hone_sub_nonneg : 0 ≤ 1 - δ k := by
        have hδk :=
          (cubicRegularization_bootstrap_invariant
            (L := L) (f := f) (method := method) hrec k).2
        linarith
      have hone_add_nonneg : 0 ≤ 1 + δ k := by
        linarith
      have hstep_lower :=
        cubicRegularization_lambda_succ_ge_one_sub_delta_mul
          (L := L) (f := f) (method := method) hrec k hLambda_k
      have hstep_upper :=
        cubicRegularization_lambda_succ_le_one_add_delta_mul
          (L := L) (f := f) (method := method) hmethod k
      constructor
      · -- Multiply the inductive lower bound by `1 - δ_k` and then apply the next-step estimate.
        calc
          (Finset.prod (Finset.range (k + 1)) fun i ↦ 1 - δ i) * λ_min(∇²f(method 0))
              = (1 - δ k) * ((Finset.prod (Finset.range k) fun i ↦ 1 - δ i) *
                  λ_min(∇²f(method 0))) := by
            rw [Finset.prod_range_succ]
            ring
          _ ≤ (1 - δ k) * λ_min(∇²f(method k)) := by
            exact mul_le_mul_of_nonneg_left hlower hone_sub_nonneg
          _ ≤ λ_min(∇²f(method (k + 1))) :=
            hstep_lower
      · -- Multiply the inductive upper bound by `1 + δ_k` and absorb the one-step upper estimate.
        calc
          λ_min(∇²f(method (k + 1)))
              ≤ (1 + δ k) * λ_min(∇²f(method k)) :=
            hstep_upper
          _ ≤ (1 + δ k) * ((Finset.prod (Finset.range k) fun i ↦ 1 + δ i) *
                λ_min(∇²f(method 0))) := by
            exact mul_le_mul_of_nonneg_left hupper hone_add_nonneg
          _ = (Finset.prod (Finset.range (k + 1)) fun i ↦ 1 + δ i) *
                λ_min(∇²f(method 0)) := by
            rw [Finset.prod_range_succ]
            ring

/-- Helper for Theorem 4.1.3.2: the geometric majorant from Theorem 4.1.3.1 gives the sharper
total decrement estimate `∑ δ_k ≤ 3 / 4`. -/
lemma tsum_cubicRegularization_delta_seq_le_three_quarters
    (hmethod : method.HasCubicRegularizationHypotheses f) :
    (∑' k, δ k) ≤ (3 / 4 : ℝ) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hgeom : Summable (fun k : ℕ ↦ (2 / 3 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hmajor :
      Summable (fun k : ℕ ↦ δ 0 * (2 / 3 : ℝ) ^ k) :=
    hgeom.mul_left _
  have hsum_le :
      (∑' k, δ k) ≤ ∑' k, δ 0 * (2 / 3 : ℝ) ^ k := by
    exact (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hrec).tsum_le_tsum
        (fun k ↦ cubicRegularization_delta_le_initial_mul_two_thirds_pow
          (L := L) (f := f) (method := method) hrec k)
        hmajor
  have hmajor_tsum :
      (∑' k, δ 0 * (2 / 3 : ℝ) ^ k) = δ 0 * 3 := by
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num)]
    norm_num
  -- Evaluate the geometric series and use the bootstrap bound on `δ₀`.
  calc
    (∑' k, δ k) ≤ ∑' k, δ 0 * (2 / 3 : ℝ) ^ k :=
      hsum_le
    _ = δ 0 * 3 := hmajor_tsum
    _ ≤ (3 / 4 : ℝ) := by
      nlinarith [hmethod.delta0_le_quarter]

/-- Helper for Theorem 4.1.3.2: every finite upper product is bounded by `exp (3 / 4)` via
`∏ (1 + δ_i) ≤ exp (∑ δ_i)`. -/
lemma cubicRegularization_partialProduct_one_add_le_exp_three_quarters
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    (Finset.prod (Finset.range k) fun i ↦ 1 + δ i) ≤ Real.exp (3 / 4 : ℝ) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hsum_le_tsum :
      Finset.sum (Finset.range k) (fun i ↦ δ i) ≤ ∑' i, δ i := by
    exact (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hrec).sum_le_tsum
        (Finset.range k)
        (fun i _ ↦ cubicRegularizationDelta_nonneg
          (L := L) (f := f) (x := method i) method.L_pos.le)
  -- Compare the finite product with the exponential of the finite sum and then with the total sum.
  calc
    Finset.prod (Finset.range k) (fun i ↦ 1 + δ i)
        ≤ Real.exp (Finset.sum (Finset.range k) fun i ↦ δ i) := by
      exact Real.prod_one_add_le_exp_sum _ (fun i ↦
        cubicRegularizationDelta_nonneg
          (L := L) (f := f) (x := method i) method.L_pos.le)
    _ ≤ Real.exp (∑' i, δ i) := by
      exact Real.exp_le_exp_of_le hsum_le_tsum
    _ ≤ Real.exp (3 / 4 : ℝ) := by
      exact Real.exp_le_exp_of_le <|
        tsum_cubicRegularization_delta_seq_le_three_quarters
          (L := L) (f := f) (method := method) hmethod

/-- Helper for Theorem 4.1.3.2: every finite lower product stays above `exp (-1)` once the
bootstrap bound `δ_i ≤ 1 / 4` is combined with the logarithmic estimate
`1 - (1 - δ_i)⁻¹ ≤ log (1 - δ_i)`. -/
lemma cubicRegularization_exp_neg_one_le_partialProduct_one_sub
    (hmethod : method.HasCubicRegularizationHypotheses f)
    (k : ℕ) :
    Real.exp (-1 : ℝ) ≤ (Finset.prod (Finset.range k) fun i ↦ 1 - δ i) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hsum_le_tsum :
      Finset.sum (Finset.range k) (fun i ↦ δ i) ≤ ∑' i, δ i := by
    exact (cubicRegularization_delta_seq_summable
      (L := L) (f := f) (method := method) hrec).sum_le_tsum
        (Finset.range k)
        (fun i _ ↦ cubicRegularizationDelta_nonneg
          (L := L) (f := f) (x := method i) method.L_pos.le)
  have hone_sub_pos (i : ℕ) : 0 < 1 - δ i := by
    have hδi :=
      (cubicRegularization_bootstrap_invariant
        (L := L) (f := f) (method := method) hrec i).2
    linarith
  have hratio_bound (i : ℕ) :
      δ i / (1 - δ i) ≤ (4 / 3 : ℝ) * δ i := by
    have hd_nonneg :
        0 ≤ δ i :=
      cubicRegularizationDelta_nonneg
        (L := L) (f := f) (x := method i) method.L_pos.le
    have hδi :=
      (cubicRegularization_bootstrap_invariant
        (L := L) (f := f) (method := method) hrec i).2
    have hdenom_ge : (3 / 4 : ℝ) ≤ 1 - δ i := by
      linarith
    have hinv_le : (1 - δ i)⁻¹ ≤ (4 / 3 : ℝ) := by
      have hthree_fourths_pos : 0 < (3 / 4 : ℝ) := by
        norm_num
      simpa [one_div] using
        (one_div_le_one_div_of_le hthree_fourths_pos hdenom_ge)
    -- The bootstrap interval turns the reciprocal factor into the uniform constant `4 / 3`.
    calc
      δ i / (1 - δ i) = δ i * (1 - δ i)⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ δ i * (4 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hinv_le hd_nonneg
      _ = (4 / 3 : ℝ) * δ i := by
        ring
  have hsum_ratio_le_one :
      Finset.sum (Finset.range k) (fun i ↦ δ i / (1 - δ i)) ≤ (1 : ℝ) := by
    calc
      Finset.sum (Finset.range k) (fun i ↦ δ i / (1 - δ i))
          ≤ Finset.sum (Finset.range k) (fun i ↦ (4 / 3 : ℝ) * δ i) := by
        exact Finset.sum_le_sum (fun i _ ↦ hratio_bound i)
      _ = (4 / 3 : ℝ) * Finset.sum (Finset.range k) (fun i ↦ δ i) := by
        rw [Finset.mul_sum]
      _ ≤ (4 / 3 : ℝ) * ∑' i, δ i := by
        exact mul_le_mul_of_nonneg_left hsum_le_tsum (by norm_num)
      _ ≤ (4 / 3 : ℝ) * (3 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (tsum_cubicRegularization_delta_seq_le_three_quarters
            (L := L) (f := f) (method := method) hmethod)
          (by norm_num)
      _ = 1 := by
        norm_num
  have hsum_log_lower :
      -(Finset.sum (Finset.range k) fun i ↦ δ i / (1 - δ i))
        ≤ Finset.sum (Finset.range k) (fun i ↦ Real.log (1 - δ i)) := by
    -- Sum the pointwise logarithmic lower bounds coming from `1 - x⁻¹ ≤ log x`.
    have hsum_neg_le :
        Finset.sum (Finset.range k) (fun i ↦ -(δ i / (1 - δ i)))
          ≤ Finset.sum (Finset.range k) (fun i ↦ Real.log (1 - δ i)) := by
      exact Finset.sum_le_sum (fun i _ ↦ by
        have hterm : -(δ i / (1 - δ i)) ≤ Real.log (1 - δ i) := by
          have hlog :=
            Real.one_sub_inv_le_log_of_pos (hone_sub_pos i)
          have hrewrite :
              1 - (1 - δ i)⁻¹ = -(δ i / (1 - δ i)) := by
            have hne : 1 - δ i ≠ 0 := (hone_sub_pos i).ne'
            field_simp [hne]
            ring
          exact hrewrite ▸ hlog
        exact hterm)
    simpa [Finset.sum_neg_distrib] using hsum_neg_le
  have hprod_pos : 0 < Finset.prod (Finset.range k) (fun i ↦ 1 - δ i) := by
    exact Finset.prod_pos (fun i _ ↦ hone_sub_pos i)
  have hlog_prod_lower :
      -1 ≤ Real.log (Finset.prod (Finset.range k) fun i ↦ 1 - δ i) := by
    calc
      -1 ≤ -(Finset.sum (Finset.range k) fun i ↦ δ i / (1 - δ i)) := by
        nlinarith [hsum_ratio_le_one]
      _ ≤ Finset.sum (Finset.range k) (fun i ↦ Real.log (1 - δ i)) :=
        hsum_log_lower
      _ = Real.log (Finset.prod (Finset.range k) fun i ↦ 1 - δ i) := by
        symm
        exact Real.log_prod (fun i hi ↦ (hone_sub_pos i).ne')
  -- Exponentiate the logarithmic lower bound to recover the scalar product estimate.
  calc
    Real.exp (-1 : ℝ) ≤
        Real.exp (Real.log (Finset.prod (Finset.range k) fun i ↦ 1 - δ i)) := by
      exact Real.exp_le_exp_of_le hlog_prod_lower
    _ = Finset.prod (Finset.range k) (fun i ↦ 1 - δ i) := by
      rw [Real.exp_log hprod_pos]

/-- Theorem 4.1.3.2: under the stronger theorem-family hypotheses
`method.HasCubicRegularizationHypotheses f` extending the recurrence assumptions from
Theorem 4.1.3.1, the least Hessian eigenvalue along the relaxed cubic-regularization iterates
stays between `e⁻¹` and `e^(3/4)` times its initial value. -/
theorem cubicRegularization_hessianLeastEigenvalue_bounds
    (hmethod : method.HasCubicRegularizationHypotheses f) (k : ℕ) :
    Real.exp (-1 : ℝ) * λ_min(∇² f (method 0)) ≤ λ_min(∇² f (method k)) ∧
      λ_min(∇² f (method k)) ≤ Real.exp (3 / 4 : ℝ) * λ_min(∇² f (method 0)) := by
  have hrec := hmethod.toHasCubicRegularizationRecurrenceHypotheses
  have hLambda0 :=
    cubicRegularization_hessianLeastEigenvalue_pos
      (L := L) (f := f) (method := method) hrec 0
  rcases cubicRegularization_hessianLeastEigenvalue_between_partial_products
      (L := L) (f := f) (method := method) hmethod k with
    ⟨hlower, hupper⟩
  constructor
  · -- Control the lower product by `exp (-1)` and then transport it to the least eigenvalue.
    calc
      Real.exp (-1 : ℝ) * λ_min(∇²f(method 0))
          ≤ (Finset.prod (Finset.range k) fun i ↦ 1 - δ i) * λ_min(∇²f(method 0)) := by
        exact mul_le_mul_of_nonneg_right
          (cubicRegularization_exp_neg_one_le_partialProduct_one_sub
            (L := L) (f := f) (method := method) hmethod k)
          hLambda0.le
      _ ≤ λ_min(∇²f(method k)) :=
        hlower
  · -- Control the upper product by `exp (3 / 4)` and then transport it to the least eigenvalue.
    calc
      λ_min(∇²f(method k))
          ≤ (Finset.prod (Finset.range k) fun i ↦ 1 + δ i) * λ_min(∇²f(method 0)) :=
        hupper
      _ ≤ Real.exp (3 / 4 : ℝ) * λ_min(∇²f(method 0)) := by
        exact mul_le_mul_of_nonneg_right
          (cubicRegularization_partialProduct_one_add_le_exp_three_quarters
            (L := L) (f := f) (method := method) hmethod k)
          hLambda0.le

end
