/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {Index : Type u} {Param : Type v}
variable (estimatedValue : Index → Param → ℝ → ℝ)
variable (k : Index) (X : Param)

local notation "value" => estimatedValue k X

/- Lemma 3.37 is a bridge/view item in the chapter's one-variable convex value-function domain.

Relevant owner declarations sampled before refining:
- `ConvexOn.secant_lower_bound_left_shift` in `Chap02/Proposition_2_26`, the canonical one-variable
  secant owner for convex scalar slices;
- `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right` in `Chap02/Proposition_2_26`, the
  shared owner bridge from convexity plus sign data at a right endpoint to the secant lower bound;
- `secant_lower_bound_left_shift_of_finite_values` in `Chap02/Proposition_2_26`, the chapter's
  finite-value bridge for extended-real convex slices.

Best owner abstraction:
- the fixed scalar slice `estimatedValue k X : ℝ → ℝ` under the shared owner theorem
  `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right`.

Primitive data:
- the scalar function `estimatedValue k X`;
- a real right endpoint `τ`;
- the order comparison `t0 < t1 ≤ τ`;
- the sign data `0 < estimatedValue k X t1` and `estimatedValue k X τ ≤ 0`.

Derived API:
- the strict inequality and displayed secant lower bound from the shared owner theorem.

Source/core/bridge triage:
- source-facing: the chapter statement for the fixed scalar slice `estimatedValue k X` at a chosen
  real right endpoint `τ`;
- core/canonical: `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right`;
- bridge/view: the specialization of that owner theorem to the chapter notation on
  `Set.Iic τ`.
-/

/-- A nonpositive terminal value at the chosen right endpoint still yields the same
strict-right-endpoint conclusion and secant lower bound. -/
-- Proof sketch: apply
-- `ConvexOn.strict_lt_and_secant_lower_bound_of_nonpos_right` directly to the convex slice on
-- `Set.Iic τ`.
theorem estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right
    {t0 t1 τ : ℝ}
    (ht01 : t0 < t1)
    (ht1_le_right : t1 ≤ τ)
    (hpositive : 0 < value t1)
    (hright_nonpos : value τ ≤ 0)
    (hconvex : ConvexOn ℝ (Set.Iic τ) value) :
    t1 < τ ∧
      value t0 ≥
        value t1 +
          ((t1 - t0) / (τ - t1)) * value t1 := by
  have ht0_mem : t0 ∈ Set.Iic τ := ht01.le.trans ht1_le_right
  exact
    hconvex.strict_lt_and_secant_lower_bound_of_nonpos_right
      ht0_mem
      (by simp)
      ht01
      ht1_le_right
      hpositive
      hright_nonpos

/-- Lemma 3.37: if `t₀ < t₁ ≤ τ`, the scalar model value `\hat f_k^*(X; t₁)` is positive,
`\hat f_k^*(X; τ) = 0`, and `t ↦ \hat f_k^*(X; t)` is convex on `(-∞, τ]`, then `τ > t₁` and
the displayed secant lower bound holds. -/
-- Proof sketch: this is the nonpositive-right-endpoint secant estimate above, specialized using
-- the stronger endpoint condition `value τ = 0`.
theorem estimatedValue_strict_lt_right_and_secant_lower_bound_of_eq_zero
    {t0 t1 τ : ℝ}
    (ht01 : t0 < t1)
    (ht1_le_right : t1 ≤ τ)
    (hpositive : 0 < value t1)
    (hright_zero : value τ = 0)
    (hconvex : ConvexOn ℝ (Set.Iic τ) value) :
    τ > t1 ∧
      value t0 ≥
        value t1 +
          ((t1 - t0) / (τ - t1)) * value t1 := by
  simpa [gt_iff_lt] using
    (estimatedValue_strict_lt_right_and_secant_lower_bound_of_nonpos_right
      estimatedValue
      k
      X
      ht01
      ht1_le_right
      hpositive
      (by simp [hright_zero])
      hconvex)

end
