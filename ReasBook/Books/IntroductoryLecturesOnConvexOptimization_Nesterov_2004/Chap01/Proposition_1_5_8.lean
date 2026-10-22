/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/- Proposition 1.5.8 is `source-facing` in first-order smooth optimization.

Source/core/bridge triage:
* source-facing: the specific scalar function `x ↦ √(1 + x²)` belongs to the textbook class
  `C^{1,1}_1(ℝ)`
* core/canonical: the owner predicates `ContDiff ℝ 1 f` and `LipschitzWith 1 (∇ f)` from
  Definition 1.5.2
* bridge/view: on `ℝ`, mathlib's `gradient_eq_deriv'` identifies the gradient with the usual
  derivative, while `lipschitzWith_of_nnnorm_deriv_le` upgrades a derivative bound to the
  canonical `LipschitzWith` owner

Primary domain:
* first-order smooth optimization on the real line

Sampled owner-style declarations:
* `ContDiff.sqrt`
* `gradient_eq_deriv'`
* `lipschitzWith_of_nnnorm_deriv_le`
* `LipschitzWith.norm_sub_le`

Primitive data:
* the concrete function `fun x : ℝ ↦ √(1 + x ^ 2)`

Derived API:
* its `C¹` regularity
* the global `1`-Lipschitz bound for its gradient

No extra local alias is kept here: the owner abstraction already lives in the canonical pair
`ContDiff ℝ 1 f` and `LipschitzWith 1 (∇ f)`, so the theorem is stated directly on the concrete
function. -/

/-- Proposition 1.5.8: the scalar function `x ↦ √(1 + x^2)` on `ℝ` belongs to the class
`C^{1,1}_1(ℝ)`. -/
-- Proof sketch: the function `x ↦ 1 + x^2` is smooth and never vanishes, so
-- `x ↦ √(1 + x^2)` is `C¹`. On `ℝ`, the gradient agrees with the derivative; the derivative is
-- `x / √(1 + x^2)` and the second derivative is `(1 + x^2)^(-3 / 2)`, which is bounded above by
-- `1` on `ℝ`. Hence the gradient is globally `1`-Lipschitz.
private theorem hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ √(1 + y ^ 2)) (x / √(1 + x ^ 2)) x := by
  have h_inner : HasDerivAt (fun y : ℝ ↦ 1 + y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
      (((hasDerivAt_id x).pow 2).const_add 1)
  have hx : (1 + x ^ 2) ≠ 0 := by
    nlinarith
  convert h_inner.sqrt hx using 1
  field_simp [hx]

private theorem hasDerivAt_div_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y / √(1 + y ^ 2)) ((√(1 + x ^ 2))⁻¹ ^ (3 : ℕ)) x := by
  have hsqrt := hasDerivAt_sqrt_one_add_sq x
  have hx0 : √(1 + x ^ 2) ≠ 0 := by
    exact (Real.sqrt_ne_zero (show 0 ≤ 1 + x ^ 2 by positivity)).2 (by nlinarith)
  have hdiv := (hasDerivAt_id x).div hsqrt hx0
  convert hdiv using 1
  · field_simp [hx0]
    simp only [id_eq]
    rw [Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)]
    ring

theorem sqrt_one_add_sq_mem_contDiffOne_withLipschitzGradient_one :
    ContDiff ℝ 1 (fun x : ℝ ↦ √(1 + x ^ 2)) ∧
      LipschitzWith 1 (∇ (fun x : ℝ ↦ √(1 + x ^ 2))) := by
  have hcontDiff : ContDiff ℝ 1 (fun x : ℝ ↦ √(1 + x ^ 2)) := by
    have hpoly : ContDiff ℝ 1 (fun x : ℝ ↦ 1 + x ^ 2) := by
      fun_prop
    refine hpoly.sqrt ?_
    intro x
    nlinarith
  have hgrad :
      ∇ (fun x : ℝ ↦ √(1 + x ^ 2)) = fun x : ℝ ↦ x / √(1 + x ^ 2) := by
    funext x
    simpa [gradient_eq_deriv'] using (hasDerivAt_sqrt_one_add_sq x).deriv
  refine ⟨hcontDiff, ?_⟩
  rw [hgrad]
  refine lipschitzWith_of_nnnorm_deriv_le ?_ ?_
  · intro x
    exact (hasDerivAt_div_sqrt_one_add_sq x).differentiableAt
  · intro x
    rw [(hasDerivAt_div_sqrt_one_add_sq x).deriv, nnnorm_pow, nnnorm_inv]
    let s : NNReal := ‖√(1 + x ^ 2)‖₊
    have hsqrt_ge_one : 1 ≤ √(1 + x ^ 2) := by
      rw [Real.one_le_sqrt]
      nlinarith [sq_nonneg x]
    have hs_ge_one : (1 : NNReal) ≤ s := by
      change (1 : ℝ) ≤ ‖√(1 + x ^ 2)‖
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt_ge_one
    have hs_inv_le_one : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs_ge_one
    have hs_inv_nonneg : (0 : NNReal) ≤ s⁻¹ := by
      positivity
    have hpow : s⁻¹ ^ (3 : ℕ) ≤ 1 := pow_le_one₀ hs_inv_nonneg hs_inv_le_one
    simpa [s] using hpow

end
