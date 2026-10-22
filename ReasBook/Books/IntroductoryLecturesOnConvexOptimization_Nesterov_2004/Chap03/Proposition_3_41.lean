/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Proposition 3.41 lies in the quantitative strong-convexity / Lipschitz radius-bound domain on
real normed spaces.

Mandatory domain-style sampling before refinement:
* `StrongConvexOn.quadratic_growth_of_isMinOn` in `Chap02/Theorem_2_30`, the owner lower-gap
  theorem at a global minimizer;
* mathlib `LipschitzWith.le_add_mul`, the owner one-sided Lipschitz estimate;
* mathlib `LipschitzWith.norm_sub_le`, the owner distance estimate behind the Lipschitz gap bound;
* `sub_sInf_image_closedBall_le_lipschitz_mul_dist_of_isMinOn` in `Theorem_3_54`, a nearby
  chapter bridge with the same upper-gap pattern stated directly relative to
  `sInf (f '' Metric.closedBall xStar R)`.

Best owner abstraction:
* core/canonical: `StrongConvexOn Q μ f`, `LipschitzOnWith M f Q`, and `IsMinOn f Q xStar`;
* bridge/view: the scalar cancellation lemma below and its constrained-owner derivation.

Primitive data:
* the objective `f`, the points `x₀`, `xStar`, and the scalars `μ`, `M`;
* the coefficient signs `0 < μ` and `0 ≤ M`;
* the lower-gap bound `(μ / 2) * ‖x₀ - xStar‖² ≤ f x₀ - f xStar`;
* the upper-gap bound `f x₀ - f xStar ≤ M * ‖x₀ - xStar‖`.

Derived API:
* the owner lower-gap theorem and owner Lipschitz estimate, used only in the companion theorems.

Source/core/bridge triage:
* source-facing: the displayed scalar implication in Proposition 3.41;
* core/canonical: the strong-convexity, Lipschitz, and minimizer owners above;
* bridge/view: the owner-based derivation theorem below.

The previous refinement promoted the numbered proposition to an owner-level theorem on
`StrongConvexOn`, `LipschitzWith`, and `IsMinOn`. This file restores Proposition 3.41 to its
source-facing bridge role: the main public entry keeps only the two gap inequalities used by the
scalar cancellation argument, while the owner-based derivation is factored through the more
canonical constrained owners and the whole-space theorem is a thin specialization.
-/

variable {E : Type u} [NormedAddCommGroup E]

/-- Proposition 3.41: if `μ > 0`, `M ≥ 0`, the quadratic lower-gap bound at `x₀`, and the linear
upper-gap bound at `x₀` all hold relative to `xStar`, then `‖x₀ - xStar‖ ≤ 2 M / μ`. -/
-- Proof sketch: let `d = ‖x₀ - xStar‖`. The two hypotheses give
-- `(μ / 2) * d² ≤ M * d`. If `d = 0` there is nothing to prove. Otherwise cancel the positive
-- factor `d` and rearrange.
theorem norm_sub_le_two_mul_div_of_quadratic_growth_le_lipschitz
    {f : E → ℝ} {μ M : ℝ} {x₀ xStar : E}
    (hμ : 0 < μ)
    (hM : 0 ≤ M)
    (hquad : (μ / 2) * ‖x₀ - xStar‖ ^ (2 : ℕ) ≤ f x₀ - f xStar)
    (hLip : f x₀ - f xStar ≤ M * ‖x₀ - xStar‖) :
    ‖x₀ - xStar‖ ≤ 2 * M / μ := by
  let d : ℝ := ‖x₀ - xStar‖
  change d ≤ 2 * M / μ
  have hbound : (μ / 2) * d ^ (2 : ℕ) ≤ M * d := by
    simpa [d] using hquad.trans hLip
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    exact norm_nonneg _
  by_cases hd : d = 0
  · rw [hd]
    rw [le_div_iff₀ hμ]
    nlinarith
  · have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (by simpa [eq_comm] using hd)
    have hhalf : (μ / 2) * d ≤ M := by
      have hmul : ((μ / 2) * d) * d ≤ M * d := by
        simpa [pow_two, mul_assoc] using hbound
      exact le_of_mul_le_mul_right hmul hd_pos
    rw [le_div_iff₀ hμ]
    nlinarith

namespace StrongConvexOn

variable [NormedSpace ℝ E]

/-- Constrained-owner derivation of Proposition 3.41 from strong convexity, Lipschitz continuity,
and a minimizer on a common feasible set. -/
-- Proof sketch: obtain the lower-gap bound from
-- `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem`, obtain the upper-gap bound from
-- `LipschitzOnWith.le_add_mul`, and apply
-- `norm_sub_le_two_mul_div_of_quadratic_growth_le_lipschitz`.
theorem norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem
    {Q : Set E} {f : E → ℝ} {μ : ℝ} {M : NNReal} {x₀ xStar : E}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hLip : LipschitzOnWith M f Q)
    (hxStar_mem : xStar ∈ Q) (hxStar : IsMinOn f Q xStar)
    (hx₀ : x₀ ∈ Q) :
    ‖x₀ - xStar‖ ≤ 2 * (M : ℝ) / μ := by
  have hquad : (μ / 2) * ‖x₀ - xStar‖ ^ (2 : ℕ) ≤ f x₀ - f xStar := by
    have hquad0 : f x₀ ≥ f xStar + (μ / 2) * ‖x₀ - xStar‖ ^ (2 : ℕ) := by
      simpa using hf.quadratic_growth_of_isMinOn_of_mem hxStar_mem hxStar x₀ hx₀
    nlinarith
  have hLip' : f x₀ - f xStar ≤ (M : ℝ) * ‖x₀ - xStar‖ := by
    have hLip0 : f x₀ ≤ f xStar + (M : ℝ) * ‖x₀ - xStar‖ := by
      simpa [dist_eq_norm_sub] using hLip.le_add_mul hx₀ hxStar_mem
    nlinarith
  exact norm_sub_le_two_mul_div_of_quadratic_growth_le_lipschitz hμ M.2 hquad hLip'

/-- Whole-space specialization of the constrained-owner derivation of Proposition 3.41. -/
theorem norm_sub_le_two_mul_lipschitz_div_of_isMinOn
    {f : E → ℝ} {μ : ℝ} {M : NNReal} {xStar : E}
    (hf : StrongConvexOn Set.univ μ f) (hμ : 0 < μ)
    (hLip : LipschitzWith M f) (hxStar : IsMinOn f Set.univ xStar)
    (x₀ : E) :
    ‖x₀ - xStar‖ ≤ 2 * (M : ℝ) / μ :=
  hf.norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem
    hμ hLip.lipschitzOnWith (by simp) hxStar (by simp)

end StrongConvexOn
