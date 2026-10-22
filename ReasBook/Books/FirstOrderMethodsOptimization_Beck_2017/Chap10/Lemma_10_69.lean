/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_61
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_66
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_67

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open Metric
open scoped DualNorm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} {XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]

section

variable {counterpart : ℕ → E → E} {L : ℕ → PosReal} {x0 : E} {M : ℝ} {Rα : PosReal}
variable {α : ℝ}

local notation "xSeq" => non_euclidean_gradient_method f counterpart L x0
local notation "xDaggerSeq" =>
  non_euclidean_gradient_method_counterpart_sequence f counterpart L x0

/- Lemma 10.69 is a `source-facing` bridge from the chapter owners for the generated
non-Euclidean gradient trajectory and admissible stepsize rules to the textbook quadratic
objective-gap decrease estimate.

Domain sampling in the surrounding Chapter 10 API shows:
- `IsFastProximalGradientProblem` is the canonical owner for the convexity, smoothness, optimizer,
  and optimal-value data of the real-valued objective with zero regularizer;
- `non_euclidean_gradient_method` and
  `non_euclidean_gradient_method_is_admissible` from Algorithm 10.61 are the trajectory owners;
- `uses_non_euclidean_gradient_stepsize_rule` and
  `non_euclidean_gradient_sufficient_decrease_by_stepsize_rule` from Lemma 10.66 are the canonical
  stepsize and sufficient-decrease owners.

The radius bound at the initial level set is supplied explicitly as `hRα`, so the stronger owner
`IsSublevelDistanceBoundedSmoothConvexMinimizationProblem` would be redundant here. -/

-- Proof sketch: apply `non_euclidean_gradient_objective_values_antitone` to obtain
-- `f(x^k) ≤ f(x^0)`, then use `hRα` to bound `infDist (x^k) XStar` by `Rα`. For each optimizer
-- `xStar ∈ XStar`, the convex gradient inequality and Cauchy-Schwarz give
-- `f(x^k) - fOpt ≤ dist (x^k) xStar * ‖f'(x^k)‖_*`; taking the infimum over `xStar ∈ XStar`
-- yields `f(x^k) - fOpt ≤ Rα ‖f'(x^k)‖_*`, while
-- `non_euclidean_gradient_sufficient_decrease_by_stepsize_rule` gives
-- `f(x^k) - f(x^(k+1)) ≥ M ‖f'(x^k)‖_*²`. Combining the two bounds yields the claimed
-- quadratic objective-gap estimate, equivalently the textbook form with `C = R_α^2 / M`.
/-- Helper for Lemma 10.69: every optimizer in `XStar` attains the optimal value `fOpt`. -/
lemma optimal_value_eq_of_mem_optimal_set
    [hfast : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]
    {xStar : E} (hxStar : xStar ∈ XStar) :
    f xStar = fOpt := by
  have hoptset :
      XStar = unconstrained_problem_solutions f :=
    IsFastProximalGradientProblem.optimal_set_eq_unconstrained_problem_solutions hfast
  have hglb :
      IsGLB (Set.range f) fOpt :=
    IsFastProximalGradientProblem.optimal_value_isGLB_range hfast
  -- Rewrite the chapter optimal set as the canonical unconstrained argmin set of `f`.
  have hxStar_opt : xStar ∈ unconstrained_problem_solutions f := by
    simpa [hoptset] using hxStar
  -- The optimizer value lies below every objective value and above the global lower bound `fOpt`.
  apply le_antisymm
  · exact hglb.2 <| by
      rintro _ ⟨y, rfl⟩
      exact (mem_unconstrained_problem_solutions_iff_forall_le.mp hxStar_opt) y
  · exact hglb.1 ⟨xStar, rfl⟩

/-- Helper for Lemma 10.69: a convex differentiable real-valued function on the whole space
satisfies the first-order support inequality in `fderiv` form. -/
lemma convex_support_at_iterate_fderiv
    {xBase yBase : E}
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_diff : DifferentiableAt ℝ f xBase) :
    f yBase ≥ f xBase + fderiv ℝ f xBase (yBase - xBase) := by
  let line : ℝ → E := AffineMap.lineMap xBase yBase
  let ψ : ℝ → ℝ := fun t ↦ f (line t)
  have hψ_convex : ConvexOn ℝ Set.univ ψ := by
    -- Restrict the ambient convex objective to the affine line through `x` and `y`.
    simpa [ψ, line] using
      hf_convex.comp_affineMap (AffineMap.lineMap xBase yBase)
  have hψ_deriv : HasDerivAt ψ (fderiv ℝ f xBase (yBase - xBase)) 0 := by
    -- Differentiate the line restriction at the base point `x`.
    have hbase : HasFDerivAt f (fderiv ℝ f xBase) (line 0) := by
      simpa [line] using hf_diff.hasFDerivAt
    have hline : HasDerivAt line (yBase - xBase) 0 := by
      simpa [line] using
        (show HasDerivAt (AffineMap.lineMap xBase yBase) (yBase - xBase) (0 : ℝ) from
          AffineMap.hasDerivAt_lineMap)
    simpa [ψ, line] using
      HasFDerivAt.comp_hasDerivAt 0 hbase hline
  have hsecant :
      fderiv ℝ f xBase (yBase - xBase) ≤ slope ψ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hψ_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hψ_deriv
  have hsecant' :
      fderiv ℝ f xBase (yBase - xBase) ≤ f yBase - f xBase := by
    simpa [ψ, line, slope] using hsecant
  linarith

/-- Helper for Lemma 10.69: fixing an optimizer `xStar`, the objective gap at iterate `k` is
bounded by the derivative norm times the distance from `x^k` to `xStar`. -/
lemma objective_gap_le_dist_mul_dual_norm_of_mem_optimal_set
    [hfast : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    f (xSeq k) - fOpt ≤ dist (xSeq k) xStar * ‖fderiv ℝ f (xSeq k)‖_* := by
  have hdiff :
      DifferentiableAt ℝ f (xSeq k) :=
    non_euclidean_gradient_method_differentiableAt hadm k
  have hsupport :
      f xStar ≥ f (xSeq k) - fderiv ℝ f (xSeq k) (xSeq k - xStar) := by
    -- Route correction: rewrite the convex support term along `xStar - x^k` into the source
    -- direction `x^k - xStar` before comparing it with the operator norm.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, map_neg] using
      (show
          f xStar ≥ f (xSeq k) + fderiv ℝ f (xSeq k) (xStar - xSeq k) from
        convex_support_at_iterate_fderiv hfast.f_convex hdiff)
  have hgap_le_apply :
      f (xSeq k) - fOpt ≤ fderiv ℝ f (xSeq k) (xSeq k - xStar) := by
    -- Replace the optimizer value by `fOpt` and move the support term to the right-hand side.
    have hxstar_eq : f xStar = fOpt :=
      optimal_value_eq_of_mem_optimal_set hxStar
    rw [← hxstar_eq]
    linarith
  -- Finish with the operator-norm bound and rewrite the ambient norm as a metric distance.
  calc
    f (xSeq k) - fOpt ≤ fderiv ℝ f (xSeq k) (xSeq k - xStar) := hgap_le_apply
    _ ≤ ‖fderiv ℝ f (xSeq k) (xSeq k - xStar)‖ := le_abs_self _
    _ ≤ ‖fderiv ℝ f (xSeq k)‖_* * ‖xSeq k - xStar‖ := by
      simpa [Real.norm_eq_abs] using (fderiv ℝ f (xSeq k)).le_opNorm (xSeq k - xStar)
    _ = dist (xSeq k) xStar * ‖fderiv ℝ f (xSeq k)‖_* := by
      rw [dist_eq_norm]
      ring

/-- Helper for Lemma 10.69: the iterate objective gap is bounded by the distance to the optimal
set times the derivative norm. -/
lemma objective_gap_le_infDist_mul_dual_norm
    [hfast : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (k : ℕ) :
    f (xSeq k) - fOpt ≤ infDist (xSeq k) XStar * ‖fderiv ℝ f (xSeq k)‖_* := by
  by_cases hzero : ‖fderiv ℝ f (xSeq k)‖_* = 0
  · rcases hfast.optimal_set_nonempty with ⟨xStar, hxStar⟩
    -- If the derivative norm is zero, the fixed-optimizer estimate collapses the gap to zero.
    have hgap_le_zero :
        f (xSeq k) - fOpt ≤ 0 := by
      have hgap :=
        objective_gap_le_dist_mul_dual_norm_of_mem_optimal_set
          hadm hxStar k
      simpa [hzero] using hgap
    simpa [hzero] using hgap_le_zero
  · have hnorm_pos : 0 < ‖fderiv ℝ f (xSeq k)‖_* := by
      have hne : 0 ≠ ‖fderiv ℝ f (xSeq k)‖_* := by
        intro h
        exact hzero (by simpa using h.symm)
      exact lt_of_le_of_ne (norm_nonneg _) hne
    have hscaled_le_dist :
        ∀ {xStar : E}, xStar ∈ XStar →
          (f (xSeq k) - fOpt) / ‖fderiv ℝ f (xSeq k)‖_* ≤ dist (xSeq k) xStar := by
      intro xStar hxStar
      -- Divide the pointwise optimizer estimate by the positive derivative norm.
      have hgap :=
        objective_gap_le_dist_mul_dual_norm_of_mem_optimal_set
          hadm hxStar k
      exact (div_le_iff₀ hnorm_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hgap
    have hscaled_le_infDist :
        (f (xSeq k) - fOpt) / ‖fderiv ℝ f (xSeq k)‖_* ≤ infDist (xSeq k) XStar := by
      -- The divided estimate holds against every optimizer, so it holds against the infimum
      -- distance to the optimal set.
      exact (Metric.le_infDist hfast.optimal_set_nonempty).2 <| by
        intro xStar hxStar
        exact hscaled_le_dist hxStar
    have hmul :
        ((f (xSeq k) - fOpt) / ‖fderiv ℝ f (xSeq k)‖_*) * ‖fderiv ℝ f (xSeq k)‖_* ≤
          infDist (xSeq k) XStar * ‖fderiv ℝ f (xSeq k)‖_* := by
      exact mul_le_mul_of_nonneg_right hscaled_le_infDist (norm_nonneg _)
    simpa [div_eq_mul_inv, hzero, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Lemma 10.69: the objective values along the generated non-Euclidean gradient
trajectory are nonincreasing under the admissible stepsize rule. -/
lemma objective_values_antitone_of_admissible_stepsize
    [hfast : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize :
      uses_non_euclidean_gradient_stepsize_rule f Lf xSeq L xDaggerSeq M) :
    Antitone (fun n ↦ f (xSeq n)) := by
  have hM_pos : 0 < M :=
    uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
  refine antitone_nat_of_succ_le ?_
  intro n
  have hdrop :
      f (xSeq n) - f (xSeq (n + 1)) ≥
        M * ‖fderiv ℝ f (xSeq n)‖_* ^ (2 : ℕ) :=
    non_euclidean_gradient_step_decrease_ge_dual_norm_sq hfast.f_smooth hadm hstepsize n
  have hnonneg : 0 ≤ M * ‖fderiv ℝ f (xSeq n)‖_* ^ (2 : ℕ) := by
    exact mul_nonneg (le_of_lt hM_pos) (sq_nonneg ‖fderiv ℝ f (xSeq n)‖_*)
  exact sub_nonneg.mp (le_trans hnonneg hdrop)

/-- Bridge/view layer: any radius bound on a sublevel set `{y | f y ≤ α}` containing the initial
point `x0` yields the same quadratic one-step objective-gap decrease estimate for the generated
non-Euclidean gradient trajectory. The textbook `α = f(x^0)` statement is the specialization
below. -/
theorem non_euclidean_gradient_step_decrease_ge_sq_objective_gap_of_sublevel_distance_bound
    (hx0 : f x0 ≤ α)
    (hRα : ∀ ⦃y : E⦄, f y ≤ α → infDist y XStar ≤ Rα)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize :
      uses_non_euclidean_gradient_stepsize_rule f Lf xSeq L xDaggerSeq M)
    (k : ℕ) :
    f (xSeq k) - f (xSeq (k + 1)) ≥
      (M / ((Rα : ℝ) ^ (2 : ℕ))) * (f (xSeq k) - fOpt) ^ (2 : ℕ) := by
  have hM_pos : 0 < M :=
    uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
  have hantitone :
      Antitone (fun n ↦ f (xSeq n)) :=
    objective_values_antitone_of_admissible_stepsize hadm hstepsize
  have hxk_le_x0 : f (xSeq k) ≤ f x0 := by
    simpa using hantitone (Nat.zero_le k)
  have hxk_le_α : f (xSeq k) ≤ α := by
    exact le_trans hxk_le_x0 hx0
  have hinfDist_le :
      infDist (xSeq k) XStar ≤ Rα :=
    hRα hxk_le_α
  have hgap_inf :
      f (xSeq k) - fOpt ≤ infDist (xSeq k) XStar * ‖fderiv ℝ f (xSeq k)‖_* :=
    objective_gap_le_infDist_mul_dual_norm hadm k
  have hgap_radius :
      f (xSeq k) - fOpt ≤ (Rα : ℝ) * ‖fderiv ℝ f (xSeq k)‖_* := by
    -- Monotonicity keeps `x^k` in the initial sublevel set, so `hRα` upgrades the `infDist`
    -- bound to the source radius `Rα`.
    calc
      f (xSeq k) - fOpt ≤ infDist (xSeq k) XStar * ‖fderiv ℝ f (xSeq k)‖_* := hgap_inf
      _ ≤ (Rα : ℝ) * ‖fderiv ℝ f (xSeq k)‖_* := by
        exact mul_le_mul_of_nonneg_right hinfDist_le (norm_nonneg _)
  have hdrop :
      f (xSeq k) - f (xSeq (k + 1)) ≥
        M * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ) :=
    non_euclidean_gradient_step_decrease_ge_dual_norm_sq
      hproblem.f_smooth hadm hstepsize k
  have hgap_nonneg : 0 ≤ f (xSeq k) - fOpt := by
    have hglb :
        IsGLB (Set.range f) fOpt :=
      IsFastProximalGradientProblem.optimal_value_isGLB_range hproblem
    exact sub_nonneg.mpr (hglb.1 ⟨xSeq k, rfl⟩)
  have hgrad_nonneg : 0 ≤ ‖fderiv ℝ f (xSeq k)‖_* := norm_nonneg _
  have hR_sq_pos : 0 < ((Rα : ℝ) ^ (2 : ℕ)) := by
    simpa [pow_two] using sq_pos_of_pos (PosReal.coe_pos Rα)
  have hgap_sq :
      (f (xSeq k) - fOpt) ^ (2 : ℕ) ≤
        ((Rα : ℝ) ^ (2 : ℕ)) * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ) := by
    -- Squaring the radius estimate is valid because both factors are nonnegative.
    nlinarith [hgap_radius, hgap_nonneg, hgrad_nonneg, PosReal.coe_pos Rα]
  have hM_nonneg : 0 ≤ M := le_of_lt hM_pos
  have hmul :
      M * (f (xSeq k) - fOpt) ^ (2 : ℕ) ≤
        M * (((Rα : ℝ) ^ (2 : ℕ)) * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hgap_sq hM_nonneg
  have hdiv :
      (M * (f (xSeq k) - fOpt) ^ (2 : ℕ)) / ((Rα : ℝ) ^ (2 : ℕ)) ≤
        M * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ) := by
    exact (div_le_iff₀ hR_sq_pos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    f (xSeq k) - f (xSeq (k + 1)) ≥
        M * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ) := hdrop
    _ ≥ (M * (f (xSeq k) - fOpt) ^ (2 : ℕ)) / ((Rα : ℝ) ^ (2 : ℕ)) := hdiv
    _ = (M / ((Rα : ℝ) ^ (2 : ℕ))) * (f (xSeq k) - fOpt) ^ (2 : ℕ) := by
      field_simp [hR_sq_pos.ne']

/-- Lemma 10.69: if the non-Euclidean gradient iterates satisfy the sublevel-distance bound at
level `α = f(x^0)`, then every step obeys the quadratic decrease estimate
`f(x^k) - f(x^(k+1)) ≥ (M / R_α^2) (f(x^k) - f_opt)^2`, where `M` is the sufficient-decrease
constant supplied by the Chapter 10 owner
`uses_non_euclidean_gradient_stepsize_rule`; equivalently, with `C = R_α^2 / M`, one has
`f(x^k) - f(x^(k+1)) ≥ (1 / C) (f(x^k) - f_opt)^2`. -/
theorem non_euclidean_gradient_step_decrease_ge_sq_objective_gap
    (hRα : ∀ ⦃y : E⦄, f y ≤ f x0 → infDist y XStar ≤ Rα)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize :
      uses_non_euclidean_gradient_stepsize_rule f Lf xSeq L xDaggerSeq M)
    (k : ℕ) :
    f (xSeq k) - f (xSeq (k + 1)) ≥
      (M / ((Rα : ℝ) ^ (2 : ℕ))) * (f (xSeq k) - fOpt) ^ (2 : ℕ) := by
  exact
    non_euclidean_gradient_step_decrease_ge_sq_objective_gap_of_sublevel_distance_bound
      (show f x0 ≤ f x0 from le_rfl) hRα hadm hstepsize k

end

end
