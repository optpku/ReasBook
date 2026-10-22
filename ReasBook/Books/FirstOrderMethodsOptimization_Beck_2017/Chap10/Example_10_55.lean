/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Example_10_44
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Example_10_50
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Example_10_53

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

/- Example 10.55 is `source-facing`: it compares the uniform error parameters of three existing
Chapter 10 smoothing owners for `|x|`.

Domain sampling in this file's neighborhood gives:
- `norm_smooth_approximation` from Example 10.44 as the square-root radial smoothing owner;
- `absolute_value_log_sum_exp_smoothing` and
  `absolute_value_log_sum_exp_smoothing_parameter_lower_bounds` from Example 10.50 as the scalar
  shifted log-sum-exp owner and its exact parameter lower-bound theorem, with the `log 2`
  parameter inherited from Example 10.45's canonical `log_cardinality_posreal` at `n = 2`;
- `norm_huber_is_smooth_approximation` from Example 10.53 as the chapter owner theorem for the
  Huber smoothing;
- `IsSmoothApproximationNonneg` from Definition 10.43 as the common comparison predicate.

The primitive data are just these three scalar smoothing families. The public API here should
therefore compare their error parameters at the owner level, reusing the existing Chapter 10
owners directly and adding only the missing nonnegative-parameter companions needed for this
comparison. -/

-- Proof sketch: specialize Example 10.44 to the real inner-product space `ℝ` and then coerce the
-- positive parameters `(1, 1)` to the nonnegative owner via `IsSmoothApproximation.toNonneg`.
/-- The scalar square-root smoothing of `|x|`, namely
`norm_smooth_approximation μ : ℝ → ℝ`, is a nonnegative `1 / μ`-smooth approximation
with error parameter `1`. -/
theorem absolute_value_sqrt_smoothing_is_smooth_approximation_nonneg
    (μ : PosReal) :
    IsSmoothApproximationNonneg
      (abs : ℝ → ℝ)
      (norm_smooth_approximation μ)
      1
      1
      μ := by
  have happrox :
      IsSmoothApproximation
        (norm : ℝ → ℝ)
        (norm_smooth_approximation μ)
        1
        1
        μ :=
    norm_smooth_approximation_is_smooth_approximation μ
  simpa [Real.norm_eq_abs] using happrox.toNonneg

-- Proof sketch: start from the positive-parameter statement in Example 10.50 and coerce the
-- error parameter `log 2` from `PosReal` to `NNReal` via `IsSmoothApproximation.toNonneg`.
/-- The shifted two-term log-sum-exp smoothing of `|x|` is a nonnegative `1 / μ`-smooth
approximation with error parameter `log 2`, encoded by `log_cardinality_nonneg` at `n = 2`. -/
theorem absolute_value_log_sum_exp_smoothing_is_smooth_approximation_nonneg
    (μ : PosReal) :
    IsSmoothApproximationNonneg
      (abs : ℝ → ℝ)
      (absolute_value_log_sum_exp_smoothing μ)
      1
      (log_cardinality_nonneg (show 0 < 2 by decide))
      μ := by
  simpa [log_cardinality_posreal, log_cardinality_nonneg] using
    (absolute_value_log_sum_exp_smoothing_is_smooth_approximation μ).toNonneg

-- Proof sketch: specialize the chapter owner theorem `norm_huber_is_smooth_approximation` from
-- Example 10.53 to the real inner-product space `ℝ`, then coerce the positive parameter `1 / 2`
-- to `NNReal`.
/-- The Huber smoothing of `|x|` is a nonnegative `1 / μ`-smooth approximation with error
parameter `1 / 2`. -/
theorem absolute_value_huber_smoothing_is_smooth_approximation_nonneg
    (μ : PosReal) :
    IsSmoothApproximationNonneg
      (abs : ℝ → ℝ)
      (H[μ] : ℝ → ℝ)
      1
      ((1 : NNReal) / 2)
      μ := by
  have hhalf :
      PosReal.toNNReal ((1 : PosReal) / (1 + 1)) = (1 : NNReal) / 2 := by
    ext
    norm_num [PosReal.coe_one, PosReal.coe_add, PosReal.coe_div]
  have happrox :
      IsSmoothApproximation
        (norm : ℝ → ℝ)
        (H[μ] : ℝ → ℝ)
        1
        ((1 : PosReal) / (1 + 1))
        μ :=
    norm_huber_is_smooth_approximation μ
  simpa [Real.norm_eq_abs, hhalf] using happrox.toNonneg

-- Proof sketch: the square-root gap
-- `|x| - (sqrt (|x|^2 + μ^2) - μ)` tends to `μ` along rays, so any admissible nonnegative error
-- parameter must satisfy `β ≥ 1`.
/-- Any nonnegative smooth-approximation parameter for the square-root smoothing of `|x|` is at
least `1`; the owner theorem from Example 10.44 is therefore sharp in its `β`-coordinate. -/
theorem absolute_value_sqrt_smoothing_parameter_lower_bound
    {μ : PosReal} {β : NNReal}
    (happrox :
      IsSmoothApproximationNonneg
        (abs : ℝ → ℝ)
        (norm_smooth_approximation μ)
        1
        β
        μ) :
    (1 : NNReal) ≤ β := by
  -- Evaluate the square-root gap at the source-faithful witness `x = μ / (1 - β)`.
  by_contra hβ
  have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
  have hβ_nonneg : 0 ≤ (β : ℝ) := β.2
  have hβ_not_real : ¬ (1 : ℝ) ≤ (β : ℝ) := by
    intro hβ_real
    apply hβ
    exact_mod_cast hβ_real
  have hβlt : (β : ℝ) < 1 := by
    linarith
  let x : ℝ := (μ : ℝ) / (1 - (β : ℝ))
  have hden_pos : 0 < 1 - (β : ℝ) := by
    linarith
  have hx_pos : 0 < x := by
    dsimp [x]
    exact div_pos hμ_pos hden_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hupper := happrox.upper_le x
  rw [norm_smooth_approximation_apply, Real.norm_eq_abs, abs_of_pos hx_pos] at hupper
  -- Rearranging `upper_le` makes the contradiction target a lower bound on the square root.
  have hsqrt_ge : x + (μ : ℝ) - (β : ℝ) * (μ : ℝ) ≤ Real.sqrt (x ^ 2 + (μ : ℝ) ^ 2) := by
    linarith
  -- The chosen witness forces the right-hand side to be strictly smaller than that lower bound.
  have hsqrt_arg_nonneg : 0 ≤ x ^ 2 + (μ : ℝ) ^ 2 := by
    positivity
  have hrhs_pos : 0 < x + (μ : ℝ) ^ 2 / x := by
    positivity
  have hsq :
      x ^ 2 + (μ : ℝ) ^ 2 < (x + (μ : ℝ) ^ 2 / x) ^ 2 := by
    field_simp [hx_ne]
    nlinarith [sq_pos_of_pos hμ_pos]
  have hsqrt_lt : Real.sqrt (x ^ 2 + (μ : ℝ) ^ 2) < x + (μ : ℝ) ^ 2 / x := by
    exact (Real.sqrt_lt hsqrt_arg_nonneg hrhs_pos.le).2 hsq
  have hrewrite : x + (μ : ℝ) - (β : ℝ) * (μ : ℝ) = x + (μ : ℝ) ^ 2 / x := by
    dsimp [x]
    field_simp [hden_pos.ne']
    ring
  rw [hrewrite] at hsqrt_ge
  linarith

-- Proof sketch: Example 10.50 already gives the exact owner-level lower bound `β ≥ log 2` for
-- positive parameters. This bridge records the weaker nonnegative consequence `β ≥ 1 / 2` that
-- is sufficient for the least-element comparison in Example 10.55.
/-- Helper for Example 10.55: any admissible nonnegative error parameter for the shifted
log-sum-exp smoothing of `|x|` is strictly positive. -/
lemma absolute_value_log_sum_exp_smoothing_parameter_pos
    {μ : PosReal} {β : NNReal}
    (happrox :
      IsSmoothApproximationNonneg
        (abs : ℝ → ℝ)
        (absolute_value_log_sum_exp_smoothing μ)
        1
        β
        μ) :
    0 < (β : ℝ) := by
  -- Evaluate the approximation inequality at `x = μ`, where the smoothing is strictly below `μ`.
  have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
  have hμ_ne : (μ : ℝ) ≠ 0 := hμ_pos.ne'
  have hβ_nonneg : 0 ≤ (β : ℝ) := β.2
  have hdiv : ((μ : ℝ) / (μ : ℝ)) = 1 := by
    field_simp [hμ_ne]
  have hnegdiv : (-(μ : ℝ) / (μ : ℝ)) = -1 := by
    field_simp [hμ_ne]
  have hupper := happrox.upper_le (μ : ℝ)
  rw [abs_of_pos hμ_pos, absolute_value_log_sum_exp_smoothing_apply, hdiv, hnegdiv] at hupper
  -- Compare the logarithm input with `2 * exp 1`, which gives the strict gap at `x = μ`.
  have hexp_lt : Real.exp (-1 : ℝ) < Real.exp (1 : ℝ) := by
    gcongr
    norm_num
  have hsum_lt :
      Real.exp (1 : ℝ) + Real.exp (-1 : ℝ) < Real.exp (1 : ℝ) + Real.exp (1 : ℝ) := by
    linarith
  have hsum_pos : 0 < Real.exp (1 : ℝ) + Real.exp (-1 : ℝ) := by
    positivity
  have hlog_lt :
      Real.log (Real.exp (1 : ℝ) + Real.exp (-1 : ℝ)) <
        Real.log (Real.exp (1 : ℝ) + Real.exp (1 : ℝ)) := by
    exact Real.log_lt_log hsum_pos hsum_lt
  have htwo_ne : (2 : ℝ) ≠ 0 := by
    norm_num
  have hexp_one_ne : Real.exp (1 : ℝ) ≠ 0 := by
    exact (Real.exp_pos 1).ne'
  have hsum_eq : Real.exp (1 : ℝ) + Real.exp (1 : ℝ) = 2 * Real.exp (1 : ℝ) := by
    ring
  have hlog_two :
      Real.log (Real.exp (1 : ℝ) + Real.exp (1 : ℝ)) = Real.log 2 + 1 := by
    rw [hsum_eq, Real.log_mul htwo_ne hexp_one_ne, Real.log_exp]
  have hvalue_lt :
      (μ : ℝ) * Real.log (Real.exp (1 : ℝ) + Real.exp (-1 : ℝ)) - (μ : ℝ) * Real.log 2 <
        (μ : ℝ) := by
    rw [hlog_two] at hlog_lt
    nlinarith
  have hβμ_pos : 0 < (β : ℝ) * (μ : ℝ) := by
    linarith
  nlinarith

/-- Any nonnegative smooth-approximation parameter for the shifted log-sum-exp smoothing of `|x|`
is at least `1 / 2`. -/
theorem absolute_value_log_sum_exp_smoothing_parameter_lower_bound_half
    {μ : PosReal} {β : NNReal}
    (happrox :
      IsSmoothApproximationNonneg
        (abs : ℝ → ℝ)
        (absolute_value_log_sum_exp_smoothing μ)
        1
        β
        μ) :
    ((1 : NNReal) / 2) ≤ β := by
  -- Repackage the nonnegative parameter as a positive parameter and reuse Example 10.50.
  have hβ_pos : 0 < (β : ℝ) :=
    absolute_value_log_sum_exp_smoothing_parameter_pos happrox
  let βpos : PosReal := ⟨(β : ℝ), hβ_pos⟩
  have happroxPos :
      IsSmoothApproximation
        (abs : ℝ → ℝ)
        (absolute_value_log_sum_exp_smoothing μ)
        1
        βpos
        μ := by
    simpa [βpos] using happrox
  have hlog_le : Real.log 2 ≤ (β : ℝ) := by
    exact (absolute_value_log_sum_exp_smoothing_parameter_lower_bounds μ 1 βpos happroxPos).2
  -- The standard estimate `1 / 2 ≤ log 2` finishes the comparison.
  have htwo_pos : 0 < (2 : ℝ) := by
    norm_num
  have hhalf_le_log : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hlog_aux := Real.one_sub_inv_le_log_of_pos htwo_pos
    norm_num at hlog_aux
    exact hlog_aux
  have hhalf_le_beta : (1 : ℝ) / 2 ≤ (β : ℝ) := le_trans hhalf_le_log hlog_le
  exact_mod_cast hhalf_le_beta

-- Proof sketch: on the affine branch `|x| > μ`, the Huber gap is exactly `μ / 2`, so any
-- admissible nonnegative error parameter must satisfy `β ≥ 1 / 2`.
/-- Any nonnegative smooth-approximation parameter for the Huber smoothing of `|x|` is at least
`1 / 2`; the owner theorem from Example 10.53 is therefore sharp in its `β`-coordinate. -/
theorem absolute_value_huber_smoothing_parameter_lower_bound
    {μ : PosReal} {β : NNReal}
    (happrox :
      IsSmoothApproximationNonneg
        (abs : ℝ → ℝ)
        (H[μ] : ℝ → ℝ)
        1
        β
        μ) :
    ((1 : NNReal) / 2) ≤ β := by
  -- Evaluate the approximation inequality at a point on the affine Huber branch.
  have hx_pos : 0 < ((μ : ℝ) + 1 : ℝ) := by
    exact add_pos (PosReal.coe_pos μ) zero_lt_one
  have hx_abs : |((μ : ℝ) + 1 : ℝ)| = (μ : ℝ) + 1 := abs_of_pos hx_pos
  have hlt : (μ : ℝ) < ((μ : ℝ) + 1 : ℝ) := by
    linarith
  have houter : (μ : ℝ) < ‖((μ : ℝ) + 1 : ℝ)‖ := by
    simpa [Real.norm_eq_abs, hx_abs] using hlt
  have hupper := happrox.upper_le (((μ : ℝ) + 1 : ℝ))
  rw [hx_abs, huber_function_of_mu_lt_norm μ houter, Real.norm_eq_abs, hx_abs] at hupper
  have hβ_real : (1 : ℝ) / 2 ≤ (β : ℝ) := by
    nlinarith [PosReal.coe_pos μ, hupper]
  exact_mod_cast hβ_real

-- Proof sketch: the three candidate approximation theorems give admissible error parameters
-- `1`, `log 2`, and `1 / 2`, and the companion lower-bound arguments for each construction show
-- that no smaller `β` works for the corresponding smoothing. Since `1 / 2 < log 2 < 1`, the
-- Huber parameter is the least element among the three candidate error-parameter sets.
/-- Example 10.55: among the three constructed `1 / μ`-smooth approximations of `|x|`, the Huber
function has the smallest uniform approximation-error parameter. -/
theorem absolute_value_huber_smoothing_has_tightest_uniform_error_bound
    (μ : PosReal) :
    IsLeast
      {β : NNReal |
        IsSmoothApproximationNonneg
            (abs : ℝ → ℝ)
            (norm_smooth_approximation μ)
            1 β μ ∨
          IsSmoothApproximationNonneg
            (abs : ℝ → ℝ)
            (absolute_value_log_sum_exp_smoothing μ)
            1 β μ ∨
          IsSmoothApproximationNonneg
            (abs : ℝ → ℝ)
            (H[μ] : ℝ → ℝ)
            1 β μ}
      ((1 : NNReal) / 2) := by
  refine ⟨?_, ?_⟩
  · exact Or.inr <| Or.inr <| absolute_value_huber_smoothing_is_smooth_approximation_nonneg μ
  · intro β hβ
    rcases hβ with hsqrt | hlog | hhuber
    · exact le_trans (by norm_num : ((1 : NNReal) / 2) ≤ 1)
        (absolute_value_sqrt_smoothing_parameter_lower_bound hsqrt)
    · exact absolute_value_log_sum_exp_smoothing_parameter_lower_bound_half hlog
    · exact absolute_value_huber_smoothing_parameter_lower_bound hhuber

end
