/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_42
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Proposition 4.19 is `source-facing`: its primitive local data is the concrete extended-valued
unit-ball function `negative_sqrt_one_sub_norm_sq_extension`. The `core/canonical` owner
abstractions already live upstream in the project as Chapter 4's `conjugate_function` and Chapter
1's `dualNorm`, so this file reuses those owners directly instead of restating parallel local
definitions. -/

section

variable {E : Type u} [NormedAddCommGroup E]

/-- The extended-real-valued function equal to `-√(1 - ‖x‖²)` on the closed unit ball and `∞`
outside it. -/
def negative_sqrt_one_sub_norm_sq_extension : E → EReal :=
  fun x ↦
    if ‖x‖ ≤ 1 then ((-Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `negative_sqrt_one_sub_norm_sq_extension`; the statement is exactly its
-- defining conditional formula on the closed unit ball.
/-- Evaluating `negative_sqrt_one_sub_norm_sq_extension` returns `-√(1 - ‖x‖²)` on the closed unit
ball and `∞` outside it. -/
theorem negative_sqrt_one_sub_norm_sq_extension_apply (x : E) :
    negative_sqrt_one_sub_norm_sq_extension x =
      if ‖x‖ ≤ 1 then ((-Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) else ⊤ :=
  rfl

/-- On the closed unit ball, `negative_sqrt_one_sub_norm_sq_extension` evaluates to
`-√(1 - ‖x‖²)`. -/
@[simp] theorem negative_sqrt_one_sub_norm_sq_extension_of_norm_le_one
    {x : E} (hx : ‖x‖ ≤ 1) :
    negative_sqrt_one_sub_norm_sq_extension x =
      ((-Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  simp [negative_sqrt_one_sub_norm_sq_extension, hx]

/-- Outside the closed unit ball, `negative_sqrt_one_sub_norm_sq_extension` is `∞`. -/
@[simp] theorem negative_sqrt_one_sub_norm_sq_extension_of_one_lt_norm
    {x : E} (hx : 1 < ‖x‖) :
    negative_sqrt_one_sub_norm_sq_extension x = ⊤ := by
  simp [negative_sqrt_one_sub_norm_sq_extension, not_le_of_gt hx]

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall conjugate_function
recall conjugate_function_apply
recall dualNorm
recall exists_dualNorm_eq_apply

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 4.19: on the closed unit ball, the Fenchel objective is the coercion of
the corresponding real-valued barrier objective. -/
lemma conjugateObjective_onClosedUnitBall (y : Module.Dual ℝ E) {x : E} (hx : ‖x‖ ≤ 1) :
    ((y x : EReal) - negative_sqrt_one_sub_norm_sq_extension x) =
      (((y x + Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))) : ℝ) : EReal) := by
  -- On the finite branch, subtracting the negative radical is ordinary real subtraction in
  -- `EReal`.
  rw [negative_sqrt_one_sub_norm_sq_extension_of_norm_le_one hx, ← EReal.coe_sub]
  simp [sub_eq_add_neg, add_comm]

/-- Helper for Proposition 4.19: if the dual norm is positive, then some unit vector realizes the
dual pairing value `dualNorm y`. -/
lemma exists_unitDualNormWitnessOfPos (y : Module.Dual ℝ E) (hy : 0 < dualNorm y) :
    ∃ u : E, ‖u‖ = 1 ∧ y u = dualNorm y := by
  obtain ⟨u, hu_ball, hu_dual⟩ := exists_dualNorm_eq_apply y
  have hu_lower : 1 ≤ ‖u‖ := by
    -- The maximizing point cannot have norm strictly smaller than `1`, or the dual norm bound
    -- would force `dualNorm y = 0`.
    have hbound : dualNorm y ≤ dualNorm y * ‖u‖ := by
      calc
        dualNorm y = y u := hu_dual
        _ ≤ |y u| := le_abs_self _
        _ ≤ dualNorm y * ‖u‖ := abs_apply_le_dual_norm_mul_norm y u
    nlinarith
  exact ⟨u, le_antisymm hu_ball hu_lower, hu_dual.symm⟩

/-- Helper for Proposition 4.19: on `[0, 1]`, the scalar objective
`α * d + √(1 - α²)` is bounded above by `√(d² + 1)`. -/
lemma scalarBarrierObjective_le (d α : ℝ) (hd : 0 ≤ d) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α * d + Real.sqrt (1 - α ^ (2 : ℕ)) ≤ Real.sqrt (d ^ (2 : ℕ) + 1) := by
  have hαsq_le : α ^ (2 : ℕ) ≤ 1 := by
    nlinarith [hα0, hα1]
  have hrad_nonneg : 0 ≤ 1 - α ^ (2 : ℕ) := sub_nonneg.mpr hαsq_le
  have hlhs_nonneg : 0 ≤ α * d + Real.sqrt (1 - α ^ (2 : ℕ)) := by
    positivity
  have hsq : (α * d + Real.sqrt (1 - α ^ (2 : ℕ))) ^ (2 : ℕ) ≤ d ^ (2 : ℕ) + 1 := by
    -- Squaring the objective turns the difference from `d² + 1` into a manifest square.
    have haux : 0 ≤ (d * Real.sqrt (1 - α ^ (2 : ℕ)) - α) ^ (2 : ℕ) := by
      positivity
    have hsqrt_sq : Real.sqrt (1 - α ^ (2 : ℕ)) ^ (2 : ℕ) = 1 - α ^ (2 : ℕ) := by
      rw [Real.sq_sqrt hrad_nonneg]
    nlinarith [haux, hsqrt_sq]
  exact (Real.le_sqrt hlhs_nonneg (by positivity)).2 hsq

/-- Helper for Proposition 4.19: the explicit optimizer
`d / √(d² + 1)` attains the scalar upper bound `√(d² + 1)`. -/
lemma scalarBarrierObjective_eq_optimizer (d : ℝ) :
    (d / Real.sqrt (d ^ (2 : ℕ) + 1)) * d +
        Real.sqrt (1 - (d / Real.sqrt (d ^ (2 : ℕ) + 1)) ^ (2 : ℕ)) =
      Real.sqrt (d ^ (2 : ℕ) + 1) := by
  set t : ℝ := Real.sqrt (d ^ (2 : ℕ) + 1)
  have ht_pos : 0 < t := by
    -- The optimizer denominator is the square root of a strictly positive number.
    dsimp [t]
    apply Real.sqrt_pos.2
    positivity
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have ht_sq : t ^ (2 : ℕ) = d ^ (2 : ℕ) + 1 := by
    -- Squaring `t` removes the square root.
    dsimp [t]
    rw [Real.sq_sqrt]
    positivity
  have hrad : 1 - (d / t) ^ (2 : ℕ) = (1 / t) ^ (2 : ℕ) := by
    -- The optimizer leaves exactly the reciprocal denominator inside the radical.
    field_simp [pow_two, ht_ne]
    rw [ht_sq]
    ring
  have hsqrt : Real.sqrt (1 - (d / t) ^ (2 : ℕ)) = 1 / t := by
    -- The reciprocal is nonnegative, so `sqrt` removes the square.
    rw [hrad]
    have hnonneg : 0 ≤ 1 / t := by
      positivity
    rw [Real.sqrt_sq hnonneg]
  change d / t * d + Real.sqrt (1 - (d / t) ^ (2 : ℕ)) = t
  rw [hsqrt]
  field_simp [ht_ne]
  simpa [pow_two, add_comm] using ht_sq.symm

/-- Helper for Proposition 4.19: the unit-ball barrier objective attains the target value
`√(‖y‖_*² + 1)` at some point of the closed unit ball. -/
lemma unitBallBarrierAttainsTargetValue (y : Module.Dual ℝ E) :
    ∃ x : E, ‖x‖ ≤ 1 ∧
      (((y x + Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))) : ℝ) : EReal) =
        ((Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) : ℝ) : EReal) := by
  have hdual_nonneg : 0 ≤ dualNorm y := by
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    exact norm_nonneg _
  by_cases hy0 : dualNorm y = 0
  · -- When `‖y‖_* = 0`, the origin already achieves the target value `1`.
    refine ⟨0, by simp, ?_⟩
    simp [hy0]
  · have hy_zero : 0 ≠ dualNorm y := by
      intro h
      exact hy0 h.symm
    have hypos : 0 < dualNorm y := lt_of_le_of_ne hdual_nonneg hy_zero
    obtain ⟨u, hu_norm, hu_dual⟩ := exists_unitDualNormWitnessOfPos y hypos
    let α : ℝ := dualNorm y / Real.sqrt (dualNorm y ^ (2 : ℕ) + 1)
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      positivity
    have hα_le_one : α ≤ 1 := by
      -- The explicit optimizer radius lies in `[0, 1]`.
      dsimp [α]
      have hsqrt_pos : 0 < Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) := by
        apply Real.sqrt_pos.2
        positivity
      have hbound :
          dualNorm y ≤ Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) := by
        exact (Real.le_sqrt hdual_nonneg (by positivity)).2 (by nlinarith)
      exact (div_le_one hsqrt_pos).2 hbound
    let x : E := α • u
    refine ⟨x, ?_, ?_⟩
    · -- Scaling the unit witness by `α ∈ [0, 1]` keeps it inside the closed unit ball.
      dsimp [x]
      rw [norm_smul, hu_norm, Real.norm_of_nonneg hα_nonneg, mul_one]
      exact hα_le_one
    · -- The scalar optimizer identity finishes the value computation on the chosen witness.
      have hxnorm : ‖x‖ = α := by
        dsimp [x]
        rw [norm_smul, hu_norm, Real.norm_of_nonneg hα_nonneg, mul_one]
      have hyx : y x = α * dualNorm y := by
        dsimp [x, α]
        rw [map_smul, hu_dual, smul_eq_mul]
      have hscalar :
          α * dualNorm y + Real.sqrt (1 - α ^ (2 : ℕ)) =
            Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) := by
        dsimp [α]
        exact scalarBarrierObjective_eq_optimizer (dualNorm y)
      rw [hyx, hxnorm, hscalar]

-- Proof sketch: unfold `conjugate_function` and restrict the supremum to the closed unit ball,
-- since the function is `⊤` outside it. Write `x = α u` with `α ∈ [0, 1]` and `‖u‖ = 1`; then
-- the inner supremum over `u` is `α * dualNorm y` by the chapter dual-norm formula. The remaining
-- one-variable maximization of `α * dualNorm y + √(1 - α²)` over `α ∈ [0, 1]` is attained at
-- `α = dualNorm y / √(dualNorm y ^ 2 + 1)`, giving the value `√(dualNorm y ^ 2 + 1)`.
/-- Proposition 4.19: for the function equal to `-√(1 - ‖x‖²)` on the closed unit ball and `∞`
outside it, the Fenchel conjugate at a dual vector `y ∈ E*` is `√(‖y‖_*² + 1)`. -/
theorem conjugate_negative_sqrt_one_sub_norm_sq_extension_eq_sqrt_dualNorm_sq_add_one
    (y : Module.Dual ℝ E) :
    conjugate_function negative_sqrt_one_sub_norm_sq_extension y =
      ((Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) : ℝ) : EReal) := by
  have hdual_nonneg : 0 ≤ dualNorm y := by
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    exact norm_nonneg _
  rw [conjugate_function_apply]
  apply le_antisymm
  · -- Every point outside the unit ball contributes `⊥`, and every point inside is bounded by the
    -- scalar barrier inequality.
    refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : ‖x‖ ≤ 1
    · change
        ((y x : EReal) - negative_sqrt_one_sub_norm_sq_extension x) ≤
          ((Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) : ℝ) : EReal)
      rw [conjugateObjective_onClosedUnitBall y hx]
      have hreal :
          y x + Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) ≤
            Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) := by
        calc
          y x + Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))
              ≤ dualNorm y * ‖x‖ + Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) := by
                gcongr
                exact le_trans (le_abs_self _) (abs_apply_le_dual_norm_mul_norm y x)
          _ ≤ Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) := by
            simpa [mul_comm] using
              scalarBarrierObjective_le (dualNorm y) ‖x‖ hdual_nonneg (norm_nonneg x) hx
      simpa [← EReal.coe_add] using hreal
    · -- Outside the closed unit ball, the objective is `⊥`, so the upper bound is immediate.
      change
        ((y x : EReal) - negative_sqrt_one_sub_norm_sq_extension x) ≤
          ((Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) : ℝ) : EReal)
      rw [negative_sqrt_one_sub_norm_sq_extension_of_one_lt_norm (lt_of_not_ge hx)]
      simp
  · -- The explicit witness from the closed unit ball realizes the target value, so the supremum
    -- is at least that large.
    obtain ⟨x, hx, hvalue⟩ := unitBallBarrierAttainsTargetValue y
    refine le_sSup ?_
    refine ⟨x, ?_⟩
    change
      ((y x : EReal) - negative_sqrt_one_sub_norm_sq_extension x) =
        ((Real.sqrt (dualNorm y ^ (2 : ℕ) + 1) : ℝ) : EReal)
    rw [conjugateObjective_onClosedUnitBall y hx]
    exact hvalue

end
