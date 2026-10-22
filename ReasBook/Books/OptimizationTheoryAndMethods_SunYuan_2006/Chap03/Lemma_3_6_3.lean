/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Operations
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_2

open scoped Topology
open Filter

section RegularZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Source/core/bridge triage:
-- * source-facing: the Chapter 3.6 owner `IsRegularZero`
-- * core/canonical: `ContinuousLinearMap.IsInvertible` and local inverse-function APIs
-- * bridge/view: this explicit two-sided norm comparison near a regular zero

/-- Helper for Chapter03 Lemma 3.6.3: a regular zero provides a `C¹` germ at the root. -/
lemma regularZero_contDiffAt
    (F : E → E) (xStar : E)
    (h_regular : IsRegularZero F xStar) :
    ContDiffAt ℝ 1 F xStar := by
  -- The neighborhood `C¹` witness stored in `IsRegularZero` gives the pointwise `C¹` fact.
  rcases h_regular with ⟨_, ⟨s, hs_nhds, hs_contDiff⟩, _⟩
  exact hs_contDiff.contDiffAt hs_nhds

/-- Helper for Chapter03 Lemma 3.6.3: near a regular zero, the first-order remainder is
bounded by any prescribed positive multiple of `‖y - xStar‖`. -/
lemma regularZero_remainderBound
    (F : E → E) (xStar : E) (γ : ℝ)
    (h_regular : IsRegularZero F xStar)
    (hγ : 0 < γ) :
    ∃ δ > 0, ∀ {y : E}, ‖y - xStar‖ < δ →
      ‖F y - F xStar - fderiv ℝ F xStar (y - xStar)‖ ≤ γ * ‖y - xStar‖ := by
  have hcontDiffAt : ContDiffAt ℝ 1 F xStar := regularZero_contDiffAt F xStar h_regular
  -- The `C¹` germ yields the textbook first-order remainder estimate `(3.6.20)`.
  have hremainderEvent :
      ∀ᶠ y in nhds xStar,
        ‖F y - F xStar - fderiv ℝ F xStar (y - xStar)‖ ≤ γ * ‖y - xStar‖ := by
    simpa using hcontDiffAt.differentiableAt_one.hasFDerivAt.isLittleO.bound hγ
  rcases Metric.eventually_nhds_iff_ball.mp hremainderEvent with ⟨δ, hδ, hbound⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  -- Convert the norm-ball hypothesis back to the neighborhood event obtained above.
  have hyBall : y ∈ Metric.ball xStar δ := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, norm_sub_rev] using hy
  exact hbound y hyBall

/-- Helper for Chapter03 Lemma 3.6.3: the inverse of an invertible derivative controls the
ambient norm by the derivative image norm. -/
lemma norm_le_inverseNorm_mul_image
    (A : E →L[ℝ] E) (hAinv : A.IsInvertible) (z : E) :
    ‖z‖ ≤ ‖A.inverse‖ * ‖A z‖ := by
  -- Rewrite through the exact inverse identity and then apply the operator norm bound.
  calc
    ‖z‖ = ‖A.inverse (A z)‖ := by rw [hAinv.inverse_apply_self]
    _ ≤ ‖A.inverse‖ * ‖A z‖ := A.inverse.le_opNorm (A z)

/-- Helper for Chapter03 Lemma 3.6.3: the remainder estimate gives the upper residual bound
`‖F y‖ ≤ ‖A (y - xStar)‖ + γ * ‖y - xStar‖`. -/
lemma sourceResidualBound_generic
    (F : E → E) (A : E →L[ℝ] E) (xStar y : E) (γ : ℝ)
    (h_root : F xStar = 0)
    (h_remainder :
      ‖F y - F xStar - A (y - xStar)‖ ≤ γ * ‖y - xStar‖) :
    ‖F y‖ ≤ ‖A (y - xStar)‖ + γ * ‖y - xStar‖ := by
  -- Split `F y` into its linear part and the first-order remainder, then use the triangle
  -- inequality.
  calc
    ‖F y‖ =
        ‖(F y - F xStar - A (y - xStar)) + A (y - xStar)‖ := by
          simp [h_root, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤ ‖F y - F xStar - A (y - xStar)‖ + ‖A (y - xStar)‖ := norm_add_le _ _
    _ ≤ γ * ‖y - xStar‖ + ‖A (y - xStar)‖ := by
      gcongr
    _ = ‖A (y - xStar)‖ + γ * ‖y - xStar‖ := by ring

/-- Helper for Chapter03 Lemma 3.6.3: the same remainder estimate also bounds the linearized
image by the source norm plus the remainder term. -/
lemma linearizationBoundOfResidual
    (F : E → E) (A : E →L[ℝ] E) (xStar y : E) (γ : ℝ)
    (h_root : F xStar = 0)
    (h_remainder :
      ‖F y - F xStar - A (y - xStar)‖ ≤ γ * ‖y - xStar‖) :
    ‖A (y - xStar)‖ ≤ ‖F y‖ + γ * ‖y - xStar‖ := by
  -- Rewrite the linearized term as `F y` minus the remainder and apply the triangle inequality.
  calc
    ‖A (y - xStar)‖ =
        ‖F y - (F y - F xStar - A (y - xStar))‖ := by
          simp [h_root, sub_eq_add_neg, add_comm]
    _ ≤ ‖F y‖ + ‖F y - F xStar - A (y - xStar)‖ := norm_sub_le _ _
    _ ≤ ‖F y‖ + γ * ‖y - xStar‖ := by
      gcongr

/-- Chapter03 Lemma 3.6.3: if `xStar` is a regular zero of `F`, so in particular
`fderiv ℝ F xStar` is invertible, and `β = ‖(fderiv ℝ F xStar).inverse‖`,
`α = max (‖fderiv ℝ F xStar‖ + 1 / (2 * β)) (2 * β)`, then `‖F y‖` is bounded above and
below by constant multiples of `‖y - xStar‖` for `y` sufficiently close to `xStar`.
This is the generic real-normed-space bridge theorem; the source `ℝⁿ` statement is obtained by
specialization. -/
theorem norm_image_bounds_near_root_of_invertible_fderiv
    (F : E → E) (xStar : E)
    (h_regular : IsRegularZero F xStar) :
    let β : ℝ := ‖(fderiv ℝ F xStar).inverse‖
    let α : ℝ := max (‖fderiv ℝ F xStar‖ + 1 / (2 * β)) (2 * β)
    ∃ δ > 0, ∀ ⦃y : E⦄, ‖y - xStar‖ < δ →
      (1 / α) * ‖y - xStar‖ ≤ ‖F y‖ ∧ ‖F y‖ ≤ α * ‖y - xStar‖ := by
  let A : E →L[ℝ] E := fderiv ℝ F xStar
  let β : ℝ := ‖A.inverse‖
  let α : ℝ := max (‖A‖ + 1 / (2 * β)) (2 * β)
  have h_root : F xStar = 0 := h_regular.1
  have hAinv : A.IsInvertible := by
    simpa [A] using h_regular.2.2
  have hmain :
      ∃ δ > 0, ∀ ⦃y : E⦄, ‖y - xStar‖ < δ →
        (1 / α) * ‖y - xStar‖ ≤ ‖F y‖ ∧ ‖F y‖ ≤ α * ‖y - xStar‖ := by
    by_cases hβ : β = 0
    · refine ⟨1, zero_lt_one, ?_⟩
      intro y hy
      -- If `β = 0`, the inverse-transport estimate forces `y = xStar`, so both bounds are
      -- immediate.
      have he_bound : ‖y - xStar‖ ≤ β * ‖A (y - xStar)‖ := by
        simpa [β] using norm_le_inverseNorm_mul_image A hAinv (y - xStar)
      have he_bound_zero : ‖y - xStar‖ ≤ 0 := by
        simpa [hβ] using he_bound
      have he_norm_zero : ‖y - xStar‖ = 0 := by
        exact le_antisymm he_bound_zero (by simp)
      have hy_eq : y = xStar := by
        exact sub_eq_zero.mp (norm_eq_zero.mp he_norm_zero)
      constructor <;> simp [hy_eq, h_root]
    · have hβ_nonneg : 0 ≤ β := by
        dsimp [β]
        exact norm_nonneg _
      have hβ_pos : 0 < β := lt_of_le_of_ne hβ_nonneg (Ne.symm hβ)
      let γ : ℝ := 1 / (2 * β)
      have hγ_pos : 0 < γ := by
        have h2β_pos : 0 < 2 * β := by
          nlinarith
        dsimp [γ]
        exact one_div_pos.mpr h2β_pos
      rcases regularZero_remainderBound F xStar γ h_regular hγ_pos with
        ⟨δ, hδ, hremainder⟩
      refine ⟨δ, hδ, ?_⟩
      intro y hy
      let e : E := y - xStar
      have hremainder_y :
          ‖F y - F xStar - A e‖ ≤ γ * ‖e‖ := by
        simpa [A, e] using hremainder (y := y) hy
      have hupper_core : ‖F y‖ ≤ ‖A e‖ + γ * ‖e‖ := by
        simpa [e] using sourceResidualBound_generic F A xStar y γ h_root hremainder_y
      have himage_core : ‖A e‖ ≤ ‖F y‖ + γ * ‖e‖ := by
        simpa [e] using linearizationBoundOfResidual F A xStar y γ h_root hremainder_y
      have hupper : ‖F y‖ ≤ α * ‖e‖ := by
        -- Combine the residual estimate with the operator norm bound for `A`.
        calc
          ‖F y‖ ≤ ‖A e‖ + γ * ‖e‖ := hupper_core
          _ ≤ ‖A‖ * ‖e‖ + γ * ‖e‖ := by
            gcongr
            exact A.le_opNorm e
          _ = (‖A‖ + γ) * ‖e‖ := by ring
          _ ≤ α * ‖e‖ := by
            gcongr
            exact le_max_left (‖A‖ + γ) (2 * β)
      have he_image : ‖e‖ ≤ β * ‖A e‖ := by
        simpa [β] using norm_le_inverseNorm_mul_image A hAinv e
      have hscaled_image :
          β * ‖A e‖ ≤ β * (‖F y‖ + γ * ‖e‖) := by
        exact mul_le_mul_of_nonneg_left himage_core hβ_nonneg
      have hβγ : β * γ = (1 : ℝ) / 2 := by
        dsimp [γ]
        field_simp [hβ]
      have htwoβ : ‖e‖ ≤ (2 * β) * ‖F y‖ := by
        -- Move the remainder contribution to the left, using the special choice
        -- `γ = 1 / (2 * β)`.
        have hstep : ‖e‖ ≤ β * ‖F y‖ + ((1 : ℝ) / 2) * ‖e‖ := by
          calc
            ‖e‖ ≤ β * ‖A e‖ := he_image
            _ ≤ β * (‖F y‖ + γ * ‖e‖) := hscaled_image
            _ = β * ‖F y‖ + (β * γ) * ‖e‖ := by ring
            _ = β * ‖F y‖ + ((1 : ℝ) / 2) * ‖e‖ := by rw [hβγ]
        nlinarith [norm_nonneg (F y), norm_nonneg e]
      have hα_ge_twoβ : 2 * β ≤ α := le_max_right (‖A‖ + γ) (2 * β)
      have hα_pos : 0 < α := by
        have htwoβ_pos : 0 < 2 * β := by
          nlinarith
        exact lt_of_lt_of_le htwoβ_pos hα_ge_twoβ
      have hα_mul : ‖e‖ ≤ α * ‖F y‖ := by
        calc
          ‖e‖ ≤ (2 * β) * ‖F y‖ := htwoβ
          _ ≤ α * ‖F y‖ := by
            exact mul_le_mul_of_nonneg_right hα_ge_twoβ (norm_nonneg (F y))
      have hlower_div : ‖e‖ / α ≤ ‖F y‖ := by
        exact (div_le_iff₀ hα_pos).2 (by simpa [mul_comm] using hα_mul)
      have hlower : (1 / α) * ‖e‖ ≤ ‖F y‖ := by
        simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlower_div
      exact ⟨by simpa [e] using hlower, by simpa [e] using hupper⟩
  simpa [A, β, α] using hmain

end RegularZero
