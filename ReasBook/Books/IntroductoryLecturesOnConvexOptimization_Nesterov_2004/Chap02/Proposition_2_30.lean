/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open HasGeometricRateOfConvergence

section

universe u

variable {α : Type u}

/-
Primary domain: scalar convergence rates for fixed-parameter internal suboptimality gaps.

Owner declarations sampled before refining:
* `HasGeometricRateOfConvergence`
* `of_step_bound`
* `exp_bound` in `Chap01/Definition_1_2_6.lean`
* `IsGLB (Set.range (f tk)) optimalValue`, the canonical infimum-value owner interface used
  across the project for exact optimal values

Best owner abstractions:
* `HasGeometricRateOfConvergence` on the scalar gap sequence
  `j ↦ f tk (x j) - optimalValue`
* `IsGLB (Set.range (f tk)) optimalValue` for the fixed-`t_k` optimal value

Source/core/bridge triage:
* source-facing: Proposition 2.30 and its nonnegative-optimal-value corollary
* core/canonical: the exact optimal-value hypothesis above together with
  `HasGeometricRateOfConvergence Δ (√q_f) (2 * Δ 0)`
* bridge/view: the exponential estimate from `exp_bound`

Primitive data:
* the fixed-parameter objective `f tk`
* the exact optimal value `optimalValue`
* the internal trajectory `x`
* the one-step contraction hypothesis
* the exact optimal-value hypothesis

Derived API:
* the scalar gap sequence `Δ`
* the owner geometric-rate statement
* the owner exponential consequence via `exp_bound`
* the specialization using `0 ≤ optimalValue`

No public lower-bound-only surrogate for `optimalValue` is kept: the source-facing gap
`f(t_k; x_j) - f^*(t_k)` is recorded against the actual infimum value.
-/

variable
  (f : ℝ → α → ℝ) (tk optimalValue : ℝ) (x : ℕ → α)
  {qf : ℝ}
  (hqf : qf ∈ Set.Ioc (0 : ℝ) 1)
  (hoptimal : IsGLB (Set.range (f tk)) optimalValue)
  (hstep :
    ∀ j : ℕ,
      f tk (x (j + 1)) - optimalValue ≤
        (1 - Real.sqrt qf) * (f tk (x j) - optimalValue))

local notation "σ" => Real.sqrt qf
local notation "Δ" => fun j : ℕ ↦ f tk (x j) - optimalValue

/-- Helper for Proposition 2.30: exact optimality of `optimalValue` makes every internal gap
`f tk (x j) - optimalValue` nonnegative. -/
lemma sub_nonneg_of_isGLB_range
    {f : ℝ → α → ℝ} {tk optimalValue : ℝ} {x : ℕ → α}
    (hoptimal : IsGLB (Set.range (f tk)) optimalValue) (j : ℕ) :
    0 ≤ f tk (x j) - optimalValue := by
  -- The infimum property gives `optimalValue ≤ f tk (x j)`, which is exactly the desired gap
  -- nonnegativity after rearranging.
  exact sub_nonneg.mpr <| hoptimal.1 ⟨x j, rfl⟩

/-- Helper for Proposition 2.30: when the exact optimal value is nonnegative, the initial
suboptimality gap is bounded by the initial objective value. -/
lemma initial_gap_le_initial_objective
    {f : ℝ → α → ℝ} {tk optimalValue : ℝ} {x : ℕ → α}
    (hoptimal_nonneg : 0 ≤ optimalValue) :
    f tk (x 0) - optimalValue ≤ f tk (x 0) := by
  -- Subtracting a nonnegative number can only decrease the initial objective value.
  nlinarith

include hqf hoptimal hstep

/-- Proposition 2.30: if `optimalValue` is the exact optimal value of the fixed-parameter
objective `f tk`, then the internal suboptimality-gap sequence
`j ↦ f tk (x j) - optimalValue` has geometric rate with contraction factor `1 - √q_f`. -/
-- Proof sketch: apply the one-step contraction inductively to the scalar sequence `Δ`; the
-- pointwise geometric and exponential bounds are then direct owner consequences.
theorem constrainedMinimizationInternalGap_hasGeometricRateOfConvergence :
    HasGeometricRateOfConvergence Δ σ (2 * Δ 0) := by
  have hgap0 : 0 ≤ Δ 0 := sub_nonneg_of_isGLB_range hoptimal 0
  refine of_step_bound (Real.sqrt_le_one.2 hqf.2) ?_ hstep
  nlinarith

/-- If the optimal value at the fixed parameter `t_k` is nonnegative, the owner exponential gap
bound is at most the same exponential factor times the initial objective value `f(t_k; x_0)`. -/
-- Proof sketch: apply `exp_bound` to the owner statement above, then use
-- `0 ≤ optimalValue` to bound `Δ 0 = f tk (x 0) - optimalValue` by `f tk (x 0)`.
theorem constrainedMinimizationInternalGap_le_exponential_rate_of_optimalValue_nonneg
    (hoptimal_nonneg : 0 ≤ optimalValue) :
    ∀ j : ℕ,
      Δ j ≤ (2 * f tk (x 0)) * Real.exp (-(σ * (j : ℝ))) := by
  intro j
  have hgap0 : 0 ≤ Δ 0 := sub_nonneg_of_isGLB_range hoptimal 0
  have hc : 0 ≤ 2 * Δ 0 := by nlinarith
  have hgap :
      Δ j ≤ (2 * Δ 0) * Real.exp (-(σ * (j : ℝ))) := by
    -- The owner exponential estimate is the exact textbook bound for the gap sequence.
    simpa using
      exp_bound
        (constrainedMinimizationInternalGap_hasGeometricRateOfConvergence
          f tk optimalValue x hqf hoptimal hstep)
        hc
        (Real.sqrt_pos.2 hqf.1)
        (Real.sqrt_le_one.2 hqf.2)
        j
  have hgap0_le : Δ 0 ≤ f tk (x 0) := by
    -- Route correction: the last textbook inequality is valid only after explicitly using the
    -- extra hypothesis `0 ≤ optimalValue`.
    simpa using initial_gap_le_initial_objective (f := f) (tk := tk) (optimalValue := optimalValue)
      (x := x) hoptimal_nonneg
  have hcoeff :
      2 * Δ 0 ≤ 2 * f tk (x 0) := by
    nlinarith [hgap0_le]
  have hexp_nonneg : 0 ≤ Real.exp (-(σ * (j : ℝ))) := (Real.exp_pos _).le
  -- Multiply the initial-gap comparison by the nonnegative exponential factor to finish.
  exact hgap.trans <| mul_le_mul_of_nonneg_right hcoeff hexp_nonneg

end
