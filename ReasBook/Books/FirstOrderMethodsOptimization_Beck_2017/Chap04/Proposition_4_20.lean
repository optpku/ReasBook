/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_7
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/- Proposition 4.20 is `source-facing`: its new mathematical content is the radius-`α` variant of
the closed-ball square-root barrier from Proposition 4.19. The ambient `core/canonical` owners are
already upstream in the project, namely `conjugate_function` and `dualNorm`, while Proposition
4.19 owns the unit-ball model function. This file therefore keeps the radius-`α` owner together
with a thin scaling bridge to the unit-ball owner, rather than introducing parallel local copies of
the chapter's canonical convex-analysis API. -/

/-- The extended-real-valued function equal to `-√(α² - ‖x‖²)` on the closed ball of radius `α`
and `∞` outside that ball. -/
def negative_sqrt_alpha_sq_sub_norm_sq_extension (α : ℝ) : E → EReal :=
  fun x ↦
    if ‖x‖ ≤ α then ((-Real.sqrt (α ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `negative_sqrt_alpha_sq_sub_norm_sq_extension`; the statement is exactly
-- its defining conditional formula.
/-- Evaluating `negative_sqrt_alpha_sq_sub_norm_sq_extension α` returns `-√(α² - ‖x‖²)` on the
closed ball of radius `α` and `∞` outside. -/
theorem negative_sqrt_alpha_sq_sub_norm_sq_extension_apply (α : ℝ) (x : E) :
    negative_sqrt_alpha_sq_sub_norm_sq_extension α x =
      if ‖x‖ ≤ α then ((-Real.sqrt (α ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) else ⊤ :=
  rfl

/-- On the closed ball of radius `α`, `negative_sqrt_alpha_sq_sub_norm_sq_extension α` takes the
finite value `-√(α² - ‖x‖²)`. -/
@[simp] theorem negative_sqrt_alpha_sq_sub_norm_sq_extension_of_norm_le
    (α : ℝ) {x : E} (hx : ‖x‖ ≤ α) :
    negative_sqrt_alpha_sq_sub_norm_sq_extension α x =
      ((-Real.sqrt (α ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  simp [negative_sqrt_alpha_sq_sub_norm_sq_extension, hx]

/-- Outside the closed ball of radius `α`, `negative_sqrt_alpha_sq_sub_norm_sq_extension α` is
`∞`. -/
@[simp] theorem negative_sqrt_alpha_sq_sub_norm_sq_extension_of_lt_norm
    (α : ℝ) {x : E} (hx : α < ‖x‖) :
    negative_sqrt_alpha_sq_sub_norm_sq_extension α x = ⊤ := by
  simp [negative_sqrt_alpha_sq_sub_norm_sq_extension, not_le.mpr hx]

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall conjugate_function
recall dualNorm

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 4.20: scaling by `1 / α` identifies the closed ball of radius `α`
with the closed unit ball when `α > 0`. -/
lemma norm_inv_smul_le_one_iff (α : ℝ) (hα : 0 < α) (x : E) :
    ‖(1 / α) • x‖ ≤ 1 ↔ ‖x‖ ≤ α := by
  -- Rewrite the scaled norm as `‖x‖ / α` and clear the positive denominator.
  rw [norm_smul, Real.norm_of_nonneg (one_div_nonneg.mpr hα.le)]
  constructor
  · intro hx
    have hx' : ‖x‖ / α ≤ 1 := by
      simpa [div_eq_inv_mul, mul_comm] using hx
    simpa using (div_le_iff₀ hα).mp hx'
  · intro hx
    have hx' : ‖x‖ / α ≤ 1 := by
      exact (div_le_iff₀ hα).2 (by simpa using hx)
    simpa [div_eq_inv_mul, mul_comm] using hx'

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 4.20: on the closed ball of radius `α`, the radical
`√(α² - ‖x‖²)` rescales to the unit-ball radical from Proposition 4.19. -/
lemma sqrt_alpha_sq_sub_norm_sq_rescale
    (α : ℝ) (hα : 0 < α) {x : E} (hx : ‖x‖ ≤ α) :
    Real.sqrt (α ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ)) =
      α * Real.sqrt (1 - ‖(1 / α) • x‖ ^ (2 : ℕ)) := by
  have hscaled : ‖(1 / α) • x‖ ≤ 1 := (norm_inv_smul_le_one_iff α hα x).2 hx
  have hscaled_sq_le : ‖(1 / α) • x‖ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [norm_nonneg ((1 / α) • x), hscaled]
  have hinner_nonneg : 0 ≤ 1 - ‖(1 / α) • x‖ ^ (2 : ℕ) := sub_nonneg.mpr hscaled_sq_le
  have hnorm_smul : ‖(1 / α) • x‖ = ‖x‖ / α := by
    rw [norm_smul, Real.norm_of_nonneg (one_div_nonneg.mpr hα.le)]
    simp [div_eq_inv_mul]
  have hradical :
      α ^ (2 : ℕ) - ‖x‖ ^ (2 : ℕ) =
        α ^ (2 : ℕ) * (1 - ‖(1 / α) • x‖ ^ (2 : ℕ)) := by
    rw [hnorm_smul]
    field_simp [pow_two, hα.ne']
  -- Factor the outer scale out of the radical, then simplify `√(α²)` using `α > 0`.
  rw [hradical, Real.sqrt_mul (by positivity : 0 ≤ α ^ (2 : ℕ))]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hα.le]

omit [FiniteDimensional ℝ E] in
-- Proof sketch: for `α > 0`, the bound `‖x‖ ≤ α` is equivalent to
-- `‖(1 / α) • x‖ ≤ 1`, and the radical rescales as
-- `α * √(1 - ‖(1 / α) • x‖²) = √(α² - ‖x‖²)`. Thus evaluating the radius-`α` barrier at `x`
-- agrees with the positive scalar multiple/precomposition of the unit-ball owner from
-- Proposition 4.19.
/-- For `α > 0`, evaluating the radius-`α` square-root barrier at `x` agrees with the positive
scalar multiple and inverse scaling precomposition of Proposition 4.19's unit-ball barrier. -/
theorem negative_sqrt_alpha_sq_sub_norm_sq_extension_eq_pos_real_mul_unit_ball
    (α : ℝ) (hα : 0 < α) (x : E) :
    negative_sqrt_alpha_sq_sub_norm_sq_extension α x =
      (α : EReal) * negative_sqrt_one_sub_norm_sq_extension ((1 / α) • x) := by
  by_cases hx : ‖x‖ ≤ α
  · have hscaled : ‖(1 / α) • x‖ ≤ 1 := (norm_inv_smul_le_one_iff α hα x).2 hx
    -- On the finite branch, both barriers evaluate to explicit square-root expressions.
    rw [negative_sqrt_alpha_sq_sub_norm_sq_extension_of_norm_le α hx]
    rw [negative_sqrt_one_sub_norm_sq_extension_of_norm_le_one hscaled]
    rw [← EReal.coe_mul]
    congr 1
    -- The helper lemma aligns the two radicals after the inverse scaling.
    rw [sqrt_alpha_sq_sub_norm_sq_rescale α hα hx]
    ring
  · have hscaled : ¬ ‖(1 / α) • x‖ ≤ 1 := by
      intro hx'
      exact hx ((norm_inv_smul_le_one_iff α hα x).1 hx')
    -- Outside the radius-`α` ball, both branches are `∞`,
    -- and positive multiplication preserves `∞`.
    rw [negative_sqrt_alpha_sq_sub_norm_sq_extension_of_lt_norm α (lt_of_not_ge hx)]
    rw [negative_sqrt_one_sub_norm_sq_extension_of_one_lt_norm (lt_of_not_ge hscaled)]
    rw [EReal.coe_mul_top_of_pos hα]

-- Proof sketch: if `0 < α`, rewrite `negative_sqrt_alpha_sq_sub_norm_sq_extension α` as
-- `x ↦ α * negative_sqrt_one_sub_norm_sq_extension ((1 / α) • x)` via
-- `negative_sqrt_alpha_sq_sub_norm_sq_extension_eq_pos_real_mul_unit_ball`, then apply the
-- positive-scaling conjugacy identity from Proposition 4.7 and Proposition 4.19 for the unit-ball
-- case. Simplifying the positive-radius case yields
-- `α * √(1 + ‖y‖_*²)`.
/-- Proposition 4.20: for `α > 0`, if `f_α` is the function equal to `-√(α² - ‖x‖²)` on the
closed ball of radius `α` and `∞` outside, then its Fenchel conjugate at `y ∈ E*` is
`α √(1 + ‖y‖_*²)`. -/
theorem conjugate_negative_sqrt_alpha_sq_sub_norm_sq_extension_eq_alpha_mul_sqrt_one_add_dualNorm_sq
    (α : ℝ) (hα : 0 < α) (y : Module.Dual ℝ E) :
    conjugate_function (negative_sqrt_alpha_sq_sub_norm_sq_extension α) y =
      ((α * Real.sqrt (1 + dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := by
  have hscale :
      negative_sqrt_alpha_sq_sub_norm_sq_extension α =
        fun x : E ↦ (α : EReal) * negative_sqrt_one_sub_norm_sq_extension ((1 / α) • x) := by
    -- Package the pointwise scaling identity as a function equality for the conjugate theorem.
    funext x
    exact negative_sqrt_alpha_sq_sub_norm_sq_extension_eq_pos_real_mul_unit_ball α hα x
  -- Rewrite to the unit-ball owner, then invoke the existing positive-scaling conjugacy formula.
  calc
    conjugate_function (negative_sqrt_alpha_sq_sub_norm_sq_extension α) y
        = conjugate_function
            (fun x ↦ (α : EReal) * negative_sqrt_one_sub_norm_sq_extension ((1 / α) • x)) y := by
              rw [hscale]
    _ = (α : EReal) * conjugate_function negative_sqrt_one_sub_norm_sq_extension y := by
          simpa using
            congrFun
              (conjugate_function_pos_real_precomp_inv_smul
                negative_sqrt_one_sub_norm_sq_extension α hα) y
    _ = (α : EReal) *
          ((Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) : ℝ) : EReal) := by
            rw [conjugate_negative_sqrt_one_sub_norm_sq_extension_eq_sqrt_dualNorm_sq_add_one]
    _ = ((α * Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) : ℝ) : EReal) := by
          rw [← EReal.coe_mul]
    _ = ((α * Real.sqrt (1 + dualNorm y ^ (2 : ℕ)) : ℝ) : EReal) := by
          congr 1
          rw [add_comm]

end
