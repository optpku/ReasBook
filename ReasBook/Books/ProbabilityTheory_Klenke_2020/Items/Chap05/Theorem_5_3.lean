/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable section

/- Theorem 5.3 (1): Item (i). If two real random variables have the same distribution, equivalently
are identically distributed under `P`, then they have the same expectation. -/
recall ProbabilityTheory.IdentDistrib.integral_eq

/- Theorem 5.3 (2): Item (ii). For an integrable real random variable `X` and `c ∈ ℝ`, the scalar
multiple `cX` is again integrable. -/
recall MeasureTheory.Integrable.const_mul

/- Theorem 5.3 (3): Item (ii). If `X` and `Y` are integrable real random variables, then `X + Y`
is integrable as well. -/
recall MeasureTheory.Integrable.add

/- Theorem 5.3 (4): Item (ii). Expectation is homogeneous: `𝔼[cX] = c 𝔼[X]`. -/
recall MeasureTheory.integral_const_mul

/- Theorem 5.3 (5): Item (ii). Expectation is additive on integrable real random variables:
`𝔼[X + Y] = 𝔼[X] + 𝔼[Y]`. -/
recall MeasureTheory.integral_add

/- Theorem 5.3 (6): Item (iii). For a nonnegative integrable real random variable, expectation
vanishes exactly when the random variable is zero almost surely. -/
recall MeasureTheory.integral_eq_zero_iff_of_nonneg_ae

/- Theorem 5.3 (7): Item (iv). Expectation is monotone with respect to almost-sure order. -/
recall MeasureTheory.integral_mono_ae

/- Theorem 5.3 (8): Item (iv). Under an almost-sure inequality `X ≤ Y`, equality of expectations
is equivalent to almost-sure equality `X = Y`. -/
recall MeasureTheory.integral_eq_iff_of_ae_le

/- Theorem 5.3 (9): Item (v). The expectation satisfies the triangle inequality
`|𝔼[X]| ≤ 𝔼[|X|]`. -/
recall MeasureTheory.abs_integral_le_integral_abs

-- Proof sketch: apply `lintegral_tsum` to the nonnegative maps
-- `ω ↦ ENNReal.ofReal (X n ω)`, then identify each summand lower integral with the textbook
-- extended expectation `ENNReal.ofReal (∫ ω, X n ω ∂μ)` via
-- `ofReal_integral_eq_lintegral_ofReal`.
/-- Theorem 5.3 (1): Item (vi), written in the canonical lower-integral form. For a sequence of
nonnegative integrable real random variables, the lower-integral expectation of the pointwise
series is the series of the extended expectations of the summands. -/
theorem lintegral_tsum_of_nonnegative_integrable_sequence {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX_int : ∀ n, Integrable (X n) μ) (hX_nonneg : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∫⁻ ω, ∑' n, ENNReal.ofReal (X n ω) ∂μ = ∑' n, ENNReal.ofReal (∫ ω, X n ω ∂μ) := by
  rw [lintegral_tsum fun n ↦ (hX_int n).1.aemeasurable.ennreal_ofReal]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hX_int _) (hX_nonneg _)]

section MonotoneLimit

variable {μ : Measure Ω}
variable {ZSeq : ℕ → Ω → ℝ} {Z : Ω → ℝ}

/-- In the monotone-limit setting, the negative part of the limit is controlled by the negative
part of the first integrable term. -/
private theorem lintegral_neg_limit_lt_top_of_monotone_limit
    (hZSeq_int : ∀ n, Integrable (ZSeq n) μ)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ ZSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ZSeq n ω) atTop (𝓝 (Z ω))) :
    ∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ < ⊤ := by
  have h_le_limit : ZSeq 0 ≤ᵐ[μ] Z := by
    filter_upwards [h_mono, h_tendsto] with ω hω_mono hω_tendsto
    exact Monotone.ge_of_tendsto hω_mono hω_tendsto 0
  have hneg_bound :
      (fun ω ↦ ENNReal.ofReal (-Z ω)) ≤ᵐ[μ] fun ω ↦ ENNReal.ofReal (-ZSeq 0 ω) := by
    filter_upwards [h_le_limit] with ω hω
    exact ENNReal.ofReal_le_ofReal (neg_le_neg hω)
  exact lt_of_le_of_lt (lintegral_mono_ae hneg_bound) (hZSeq_int 0).neg.lintegral_lt_top

-- Proof sketch: shift the increasing sequence by the integrable lower bound `ZSeq 0` to obtain a
-- nonnegative monotone sequence, apply Beppo Levi to the shifted sequence, and then rewrite the
-- result in the textbook extended-expectation form as a difference of lower integrals.
/-- Theorem 5.3 (2): Item (vii). If an increasing sequence of integrable real random variables
converges almost surely to `Z`, then the expectations converge to the extended expectation of `Z`,
written canonically as the difference of the lower integrals of the positive and negative parts. -/
theorem expectation_tendsto_ereal_of_monotone_limit
    (hZSeq_int : ∀ n, Integrable (ZSeq n) μ)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ ZSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ZSeq n ω) atTop (𝓝 (Z ω))) :
    Tendsto
      (fun n ↦ ((∫ ω, ZSeq n ω ∂μ : ℝ) : EReal))
      atTop
      (𝓝
        (((∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : EReal))) := by
  have hpos :
      Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (ZSeq n ω) ∂μ) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro n
      exact (hZSeq_int n).1.aemeasurable.ennreal_ofReal
    · exact h_mono.mono fun ω hω ↦
        fun i j hij ↦ ENNReal.ofReal_le_ofReal (hω hij)
    · exact h_tendsto.mono fun ω hω ↦
        (ENNReal.continuous_ofReal.tendsto _).comp hω
  have hneg :
      Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_antitone ?_ ?_ ?_ ?_
    · intro n
      exact (hZSeq_int n).neg.1.aemeasurable.ennreal_ofReal
    · exact h_mono.mono fun ω hω ↦
        fun i j hij ↦ ENNReal.ofReal_le_ofReal (neg_le_neg (hω hij))
    · exact (hZSeq_int 0).neg.lintegral_lt_top.ne
    · exact h_tendsto.mono fun ω hω ↦
        (ENNReal.continuous_ofReal.tendsto _).comp (Filter.Tendsto.neg hω)
  have hneg_limit_ne_top : ∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ ≠ ⊤ :=
    (lintegral_neg_limit_lt_top_of_monotone_limit hZSeq_int h_mono h_tendsto).ne
  have hpos_ereal :
      Tendsto (fun n ↦ ((∫⁻ ω, ENNReal.ofReal (ZSeq n ω) ∂μ) : EReal)) atTop
        (𝓝 (((∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) : EReal))) := by
    simpa using EReal.tendsto_coe_ennreal.2 hpos
  have hneg_ereal :
      Tendsto (fun n ↦ ((∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ) : EReal)) atTop
        (𝓝 (((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : EReal))) := by
    simpa using EReal.tendsto_coe_ennreal.2 hneg
  have hneg_ereal_neg :
      Tendsto
        (fun n ↦ -(((∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ) : EReal))) atTop
        (𝓝 (-(((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : EReal)))) := by
    exact Filter.Tendsto.neg hneg_ereal
  have hterm :
      (fun n ↦ ((∫ ω, ZSeq n ω ∂μ : ℝ) : EReal)) =
        fun n ↦
          (((∫⁻ ω, ENNReal.ofReal (ZSeq n ω) ∂μ) : EReal) -
            ((∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ) : EReal)) := by
    funext n
    have hpos_ne_top : ∫⁻ ω, ENNReal.ofReal (ZSeq n ω) ∂μ ≠ ⊤ :=
      (hZSeq_int n).lintegral_lt_top.ne
    have hneg_ne_top : ∫⁻ ω, ENNReal.ofReal (-ZSeq n ω) ∂μ ≠ ⊤ :=
      (hZSeq_int n).neg.lintegral_lt_top.ne
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hZSeq_int n)]
    rw [← EReal.coe_ennreal_toReal hpos_ne_top, ← EReal.coe_ennreal_toReal hneg_ne_top]
    norm_num
  rw [hterm]
  simpa [sub_eq_add_neg] using
    (EReal.continuousAt_add
      (Or.inr <| by simpa [EReal.neg_eq_bot_iff] using hneg_limit_ne_top)
      (Or.inl <| EReal.coe_ennreal_ne_bot (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ))).tendsto.comp
      (hpos_ereal.prodMk_nhds hneg_ereal_neg)

-- Proof sketch: the monotone limit dominates the first integrable term `ZSeq 0`, so its negative
-- part is controlled by the integrable function `-ZSeq 0`. This rules out the value `-∞` for the
-- extended expectation computed in the previous clause.
/-- Theorem 5.3 (3): Item (vii). In the monotone convergence situation, the extended expectation
of the limit belongs to `(-∞, ∞]`, equivalently it is not equal to `-∞`. -/
theorem extended_expectation_ne_bot_of_monotone_limit
    (hZSeq_int : ∀ n, Integrable (ZSeq n) μ)
    (h_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ ZSeq n ω)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ZSeq n ω) atTop (𝓝 (Z ω))) :
    (((∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : EReal)) ≠ ⊥ := by
  have hneg_lt_top : ∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ < ⊤ :=
    lintegral_neg_limit_lt_top_of_monotone_limit hZSeq_int h_mono h_tendsto
  have hpos_ne_bot : (((∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) : ENNReal) : EReal) ≠ ⊥ :=
    EReal.coe_ennreal_ne_bot _
  have hneg_ne_top : (((∫⁻ ω, ENNReal.ofReal (-Z ω) ∂μ) : ENNReal) : EReal) ≠ ⊤ := by
    intro h_top
    exact hneg_lt_top.ne (EReal.coe_ennreal_eq_top_iff.1 h_top)
  intro h_bot
  rw [sub_eq_add_neg, EReal.add_eq_bot_iff] at h_bot
  rcases h_bot with h_bot | h_bot
  · exact hpos_ne_bot h_bot
  · exact hneg_ne_top ((EReal.neg_eq_bot_iff.1 h_bot))

end MonotoneLimit
