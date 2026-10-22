/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ContinuousLinearMap ENNReal

universe u

noncomputable section

section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

local instance instFactOneLeConjExponent (p : ENNReal) [Fact (1 ≤ p)] :
    Fact (1 ≤ conjExponent p) :=
  ⟨HolderConjugate.one_le (conjExponent p) p⟩

/-- Helper for Lemma 7.49: the real sign map is measurable. -/
private theorem measurable_real_sign_map : Measurable (Real.sign : ℝ → ℝ) := by
  classical
  change Measurable
      ((({r : ℝ | r < 0}).piecewise (fun _ ↦ (-1 : ℝ))
          ((({r : ℝ | 0 < r}).piecewise (fun _ ↦ (1 : ℝ)) fun _ ↦ (0 : ℝ)))))
  refine Measurable.piecewise ?_ measurable_const ?_
  · exact measurableSet_lt measurable_id measurable_const
  · refine Measurable.piecewise ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const measurable_id

/- The real-valued sign used in the chapter agrees with the canonical ordered-ring sign. -/
private theorem real_sign_eq_sign (r : ℝ) : Real.sign r = (SignType.sign r : ℝ) := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · have hs : SignType.sign r = -1 := sign_neg hr
    simp [Real.sign_of_neg hr, hs]
  · simp
  · have hs : SignType.sign r = 1 := sign_pos hr
    simp [Real.sign_of_pos hr, hs]

/- Helper for Lemma 7.49: the sign of an `Lp` function defines an `L∞` test function of norm at
most `1`. -/
lemma sign_test_function {q : ENNReal} (f : Lp ℝ q μ) :
    ∃ g : Lp ℝ ∞ μ, ‖g‖ ≤ 1 ∧ g =ᵐ[μ] fun x ↦ Real.sign (f x) := by
  let hsign_mem : MemLp (fun x ↦ Real.sign (f x)) ∞ μ :=
    MeasureTheory.memLp_top_of_bound
      ((measurable_real_sign_map.comp_aemeasurable
          (Lp.aestronglyMeasurable f).aemeasurable).aestronglyMeasurable)
      1 <| by
        -- The pointwise sign only takes the values `-1`, `0`, and `1`.
        filter_upwards with x
        obtain hx | hx | hx := Real.sign_apply_eq (f x)
        · simp [hx]
        · simp [hx]
        · simp [hx]
  refine ⟨hsign_mem.toLp (fun x ↦ Real.sign (f x)), ?_, MemLp.coeFn_toLp hsign_mem⟩
  -- Rewrite the `L∞` norm as an essential supremum and use the pointwise bound `|sign| ≤ 1`.
  rw [Lp.norm_toLp, eLpNorm_exponent_top, MeasureTheory.eLpNormEssSup_eq_essSup_enorm]
  calc
    (essSup (fun x ↦ ‖Real.sign (f x)‖ₑ) μ).toReal ≤ (1 : ENNReal).toReal := by
      exact ENNReal.toReal_mono one_ne_top <| essSup_le_of_ae_le (1 : ℝ≥0∞) <| by
        filter_upwards with x
        obtain hx | hx | hx := Real.sign_apply_eq (f x)
        · simp [hx]
        · simp [hx]
        · simp [hx]
    _ = 1 := by simp

/- Helper for Lemma 7.49: Hölder's inequality gives the generic upper bound on the pairing norm. -/
lemma lp_pairing_norm_le_norm (p : ENNReal) [Fact (1 ≤ p)] [SFinite μ]
    (f : Lp ℝ (conjExponent p) μ) :
    ‖(mul ℝ ℝ).lpPairing μ (conjExponent p) p f‖ ≤ ‖f‖ := by
  -- Bound the operator norm of the partially applied pairing by testing against an arbitrary `g`.
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro g
  have hholder : (mul ℝ ℝ).holder 1 f g =ᵐ[μ] fun x ↦ f x * g x := by
    simpa using (mul ℝ ℝ).coeFn_holder f g
  calc
    ‖((mul ℝ ℝ).lpPairing μ (conjExponent p) p f) g‖ = ‖∫ x, f x * g x ∂μ‖ := by
      simpa using congrArg norm ((mul ℝ ℝ).lpPairing_eq_integral f g)
    _ = ‖L1.integral ((mul ℝ ℝ).holder 1 f g)‖ := by
      rw [L1.integral_eq_integral]
      congr 1
      exact integral_congr_ae <| by simpa using hholder.symm
    _ ≤ ‖(mul ℝ ℝ).holder 1 f g‖ := L1.norm_integral_le _
    _ ≤ ‖mul ℝ ℝ‖ * ‖f‖ * ‖g‖ := by
      simpa using
        (show ‖(mul ℝ ℝ).holder 1 f g‖ ≤ ‖mul ℝ ℝ‖ * ‖f‖ * ‖g‖ from
          (mul ℝ ℝ).norm_holder_apply_apply_le f g)
    _ = ‖f‖ * ‖g‖ := by simp [ContinuousLinearMap.opNorm_mul]

/- Helper for Lemma 7.49: in the `q = 1` endpoint, the sign test function gives the reverse
inequality. -/
lemma lp_pairing_norm_ge_of_L1 [SFinite μ] (f : Lp ℝ 1 μ) :
    ‖f‖ ≤ ‖(mul ℝ ℝ).lpPairing μ 1 ∞ f‖ := by
  rcases sign_test_function f with ⟨g, hg_norm, hg_eq⟩
  have hpair : ((mul ℝ ℝ).lpPairing μ 1 ∞ f) g = ∫ x, |f x| ∂μ := by
    -- The sign choice turns the pairing integral into the `L¹` norm integral.
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hg_eq] with x hx
    rw [hx, real_sign_eq_sign]
    exact self_mul_sign (f x)
  calc
    ‖f‖ = ∫ x, |f x| ∂μ := by
      -- Rewrite the `L¹` norm by the standard integral formula.
      rw [Lp.norm_def, MeasureTheory.toReal_eLpNorm (Lp.aestronglyMeasurable f)]
      simpa using MeasureTheory.lpNorm_one_eq_integral_norm (Lp.aestronglyMeasurable f)
    _ = |((mul ℝ ℝ).lpPairing μ 1 ∞ f) g| := by
      rw [hpair, abs_of_nonneg]
      positivity
    _ ≤ ‖(mul ℝ ℝ).lpPairing μ 1 ∞ f‖ * ‖g‖ := by
      simpa [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm
        ((mul ℝ ℝ).lpPairing μ 1 ∞ f) g
    _ ≤ ‖(mul ℝ ℝ).lpPairing μ 1 ∞ f‖ := by
      nlinarith [hg_norm, norm_nonneg ((mul ℝ ℝ).lpPairing μ 1 ∞ f)]

/- Internal helper for Lemma 7.49: a strict lower bound below the `L∞` norm forces the
corresponding superlevel set to have positive measure. -/
private lemma superlevel_pos_of_lt_lpNorm_top [SFinite μ] (f : Lp ℝ ∞ μ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc : c < ‖f‖) :
    0 < μ {x | c < |f x|} := by
  by_contra hzero
  have hS0 : μ {x | c < |f x|} = 0 := le_antisymm (le_of_not_gt hzero) bot_le
  have h_ae_le : ∀ᵐ x ∂μ, |f x| ≤ c := by
    -- If the superlevel set has zero measure, then `|f| ≤ c` almost everywhere.
    have h_not_mem : ∀ᵐ x ∂μ, x ∉ {x | c < |f x|} := by
      rw [ae_iff]
      simp [hS0]
    simpa using h_not_mem
  have hnorm_le : ‖f‖ ≤ c := by
    -- Rewrite the `L∞` norm as an essential supremum and use the almost-everywhere bound.
    rw [Lp.norm_def, eLpNorm_exponent_top, MeasureTheory.eLpNormEssSup_eq_essSup_enorm]
    simpa [ENNReal.toReal_ofReal hc_nonneg] using
      (ENNReal.toReal_mono (by simp)
        (essSup_le_of_ae_le (ENNReal.ofReal c) <| by
          filter_upwards [h_ae_le] with x hx
          simpa [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff hc_nonneg] using hx))
  exact (not_le_of_gt hc) hnorm_le

/- Internal helper for Lemma 7.49: a nonzero restricted measure has a nonzero finite `sfiniteSeq`
summand. -/
private lemma existsNonzeroFiniteRestrictPiece [SFinite μ] {S : Set Ω}
    (hS_nonzero : μ.restrict S ≠ 0) :
    ∃ n, MeasureTheory.sfiniteSeq (μ.restrict S) n ≠ 0 := by
  by_contra hno
  have hzero : ∀ n, MeasureTheory.sfiniteSeq (μ.restrict S) n = 0 := by
    intro n
    by_cases hn : MeasureTheory.sfiniteSeq (μ.restrict S) n = 0
    · exact hn
    · exact False.elim <| hno ⟨n, hn⟩
  have hsum_zero : Measure.sum (MeasureTheory.sfiniteSeq (μ.restrict S)) = 0 := by
    ext t ht
    simp [hzero]
  exact hS_nonzero <| by
    simpa [MeasureTheory.sum_sfiniteSeq] using hsum_zero

/- Internal helper for Lemma 7.49: a nonzero finite restriction supported on a superlevel set
produces an `L¹` test function whose norm is at most `1` and whose pairing is bounded below by the
superlevel threshold. -/
/- Helper for Lemma 7.49: the normalized indicator of a finite positive measurable set has
`L¹` norm `1`. -/
private lemma normalizedIndicatorLpNorm_one {T : Set Ω} (hT_meas : MeasurableSet T)
    (hT_nonzero : μ T ≠ 0) (hT_finite : μ T < ∞) :
    ‖(indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ)‖ = 1 := by
  have hTreal_pos : 0 < μ.real T := ENNReal.toReal_pos hT_nonzero hT_finite.ne
  have hindicator_norm :
      ‖(indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ)‖
        = ‖((μ.real T)⁻¹ : ℝ)‖ * μ.real T ^ (1 / (1 : ENNReal).toReal) :=
    norm_indicatorConstLp' one_ne_zero hT_nonzero
  -- Specialize the standard indicator norm formula to exponent `1`.
  calc
    ‖(indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ)‖
      = ‖((μ.real T)⁻¹ : ℝ)‖ * μ.real T ^ (1 / (1 : ENNReal).toReal) := by
          exact hindicator_norm
    _ = |(μ.real T)⁻¹| * μ.real T := by simp
    _ = 1 := by
          rw [abs_of_nonneg (inv_nonneg.2 hTreal_pos.le), inv_mul_cancel₀ hTreal_pos.ne']

/- Helper for Lemma 7.49: pairing against the signed normalized indicator of `T` produces the
normalized set integral of `|f|`. -/
private lemma signIndicatorPairing_eq_setIntegral [SigmaFinite μ] (f : Lp ℝ ∞ μ)
    {s : Lp ℝ ∞ μ} (hs_eq : s =ᵐ[μ] fun x ↦ Real.sign (f x)) {T : Set Ω}
    (hT_meas : MeasurableSet T) (hT_finite : μ T < ∞) :
    ((mul ℝ ℝ).lpPairing μ ∞ 1 f)
        (s • indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹))
      = ∫ x in T, |f x| * (μ.real T)⁻¹ ∂μ := by
  have hsg :
      ((s • indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ) : Lp ℝ 1 μ)
        =ᵐ[μ] fun x ↦ s x * indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) x := by
    change ((s • indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ) =ᵐ[μ]
      fun x ↦ s x * indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) x)
    simpa using
      (Lp.coeFn_lpSMul s (indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ))
  have hindicator :
      ((indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ) : Ω → ℝ)
        =ᵐ[μ] T.indicator (fun _ ↦ (μ.real T)⁻¹) := by
    simpa using
      (indicatorConstLp_coeFn :
        ((indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ) : Ω → ℝ)
          =ᵐ[μ] T.indicator (fun _ ↦ (μ.real T)⁻¹))
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  calc
    ∫ x, f x * (s • indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹) : Lp ℝ 1 μ) x ∂μ
      = ∫ x, T.indicator (fun x ↦ |f x| * (μ.real T)⁻¹) x ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hsg, hs_eq, hindicator] with x hxg hxs hu
          rw [hxg, hxs, hu]
          by_cases hxT : x ∈ T
          · rw [Set.indicator_of_mem hxT, Set.indicator_of_mem hxT, real_sign_eq_sign]
            calc
              f x * ((SignType.sign (f x) : ℝ) * (μ.real T)⁻¹)
                  = (f x * (SignType.sign (f x) : ℝ)) * (μ.real T)⁻¹ := by
                      rw [mul_assoc]
              _ = |f x| * (μ.real T)⁻¹ := by rw [self_mul_sign]
          · simp [hxT]
    _ = ∫ x in T, |f x| * (μ.real T)⁻¹ ∂μ := by
        rw [MeasureTheory.integral_indicator hT_meas]

/- Helper for Lemma 7.49: the normalized set integral of `|f|` dominates any almost-everywhere
lower threshold on `T`. -/
private lemma threshold_le_normalizedSetIntegral [SigmaFinite μ] (f : Lp ℝ ∞ μ) {T : Set Ω}
    {c : ℝ} (_hT_meas : MeasurableSet T) (hT_nonzero : μ T ≠ 0) (hT_finite : μ T < ∞)
    (hc_on_T : ∀ᵐ x ∂μ.restrict T, c ≤ |f x|) :
    c ≤ ∫ x in T, |f x| * (μ.real T)⁻¹ ∂μ := by
  have hTreal_pos : 0 < μ.real T := ENNReal.toReal_pos hT_nonzero hT_finite.ne
  have h_const_integrable : IntegrableOn (fun _ : Ω ↦ c * (μ.real T)⁻¹) T μ := by
    exact integrableOn_const hT_finite.ne
  have hLp_integrable : Integrable (fun x ↦ f x) (μ.restrict T) := by
    -- Restrict the `L∞` function to the finite set `T` to gain `L¹` integrability.
    simpa [IntegrableOn] using
      (integrableOn_Lp_of_measure_ne_top f (by simp) hT_finite.ne)
  have h_abs_integrable : IntegrableOn (fun x ↦ |f x| * (μ.real T)⁻¹) T μ := by
    -- The restricted absolute value remains integrable after scaling by the normalization factor.
    simpa [IntegrableOn, Real.norm_eq_abs, mul_comm] using
      hLp_integrable.norm.mul_const ((μ.real T)⁻¹)
  have hscaled :
      (fun _ : Ω ↦ c * (μ.real T)⁻¹) ≤ᵐ[μ.restrict T] fun x ↦ |f x| * (μ.real T)⁻¹ := by
    -- Multiply the threshold inequality by the nonnegative scalar `(μ.real T)⁻¹`.
    filter_upwards [hc_on_T] with x hx
    exact mul_le_mul_of_nonneg_right hx (inv_nonneg.2 hTreal_pos.le)
  have hmono :
      ∫ x in T, c * (μ.real T)⁻¹ ∂μ ≤ ∫ x in T, |f x| * (μ.real T)⁻¹ ∂μ := by
    exact setIntegral_mono_ae_restrict h_const_integrable h_abs_integrable hscaled
  have hconst :
      ∫ x in T, c * (μ.real T)⁻¹ ∂μ = c := by
    -- The normalization is chosen so that the constant function integrates to `c`.
    rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
    field_simp [hTreal_pos.ne']
  calc
    c = ∫ x in T, c * (μ.real T)⁻¹ ∂μ := hconst.symm
    _ ≤ ∫ x in T, |f x| * (μ.real T)⁻¹ ∂μ := hmono

/- Helper for Lemma 7.49: a finite positive superlevel set yields a normalized signed-indicator
test function with pairing at least the threshold. -/
private lemma lpPairing_ge_threshold_of_signIndicator [SigmaFinite μ] (f : Lp ℝ ∞ μ) {T : Set Ω}
    {c : ℝ} (hT_meas : MeasurableSet T) (hT_nonzero : μ T ≠ 0) (hT_finite : μ T < ∞)
    (hc_on_T : ∀ᵐ x ∂μ.restrict T, c ≤ |f x|) :
    ∃ g : Lp ℝ 1 μ, ‖g‖ ≤ 1 ∧ c ≤ |((mul ℝ ℝ).lpPairing μ ∞ 1 f) g| := by
  rcases sign_test_function f with ⟨s, hs_norm, hs_eq⟩
  let g0 : Lp ℝ 1 μ := indicatorConstLp 1 hT_meas hT_finite.ne ((μ.real T)⁻¹)
  let g : Lp ℝ 1 μ := s • g0
  refine ⟨g, ?_, ?_⟩
  · have hg0_norm : ‖g0‖ = 1 := by
      -- Normalize the indicator so the witness lies in the unit ball of `L¹`.
      simpa [g0] using normalizedIndicatorLpNorm_one hT_meas hT_nonzero hT_finite
    calc
      ‖g‖ ≤ ‖s‖ * ‖g0‖ := by
            simpa [g] using (Lp.norm_smul_le s g0)
      _ ≤ ‖g0‖ := by
            nlinarith [hs_norm, norm_nonneg g0]
      _ = 1 := hg0_norm
  · have hpair_eq :
        ((mul ℝ ℝ).lpPairing μ ∞ 1 f) g
          = ∫ x in T, |f x| * (μ.real T)⁻¹ ∂μ := by
            -- The signed indicator turns the pairing into the normalized absolute-value integral.
            simpa [g, g0] using
              signIndicatorPairing_eq_setIntegral f hs_eq hT_meas hT_finite
    calc
      c ≤ ∫ x in T, |f x| * (μ.real T)⁻¹ ∂μ := by
            exact threshold_le_normalizedSetIntegral f hT_meas hT_nonzero hT_finite hc_on_T
      _ = |((mul ℝ ℝ).lpPairing μ ∞ 1 f) g| := by
            rw [hpair_eq, abs_of_nonneg]
            positivity

/- Internal helper for Lemma 7.49: a nonzero finite restriction supported on a superlevel set
produces an `L¹` test function whose norm is at most `1` and whose pairing is bounded below by the
superlevel threshold. -/
private lemma superlevel_restrict_test_function [SigmaFinite μ] (f : Lp ℝ ∞ μ) {S : Set Ω}
    {c : ℝ}
    (hS_nonzero : μ.restrict S ≠ 0) (hS_null : NullMeasurableSet S μ)
    (hc : ∀ᵐ x ∂μ.restrict S, c ≤ |f x|) :
    ∃ g : Lp ℝ 1 μ, ‖g‖ ≤ 1 ∧ c ≤ |((mul ℝ ℝ).lpPairing μ ∞ 1 f) g| := by
  -- Route correction: replace the unfinished RN-derivative witness with a normalized signed
  -- indicator supported on a finite measurable subset of the superlevel set.
  obtain ⟨U, hUS, hU_meas, hU_ae_eq⟩ := hS_null.exists_measurable_subset_ae_eq
  have hrestrict_eq : μ.restrict U = μ.restrict S := Measure.restrict_congr_set hU_ae_eq
  have hU_restrict_nonzero : μ.restrict U ≠ 0 := by
    rw [hrestrict_eq]
    exact hS_nonzero
  have hU_nonzero : μ U ≠ 0 := by
    intro hU_zero
    exact hU_restrict_nonzero ((Measure.restrict_eq_zero).2 hU_zero)
  have hU_pos : 0 < μ U := bot_lt_iff_ne_bot.mpr hU_nonzero
  obtain ⟨T, hT_meas, hTU, hT_pos, hT_finite⟩ := Measure.exists_subset_measure_lt_top hU_meas hU_pos
  have hT_nonzero : μ T ≠ 0 := ne_of_gt hT_pos
  have hc_on_S : ∀ᵐ x ∂μ, x ∈ S → c ≤ |f x| := (MeasureTheory.ae_restrict_iff'₀ hS_null).1 hc
  have hc_on_T : ∀ᵐ x ∂μ.restrict T, c ≤ |f x| := by
    -- Transport the superlevel bound from `S` down to the chosen measurable subset `T`.
    rw [MeasureTheory.ae_restrict_iff' hT_meas]
    exact hc_on_S.mono fun x hx hxT ↦ hx (hUS (hTU hxT))
  exact lpPairing_ge_threshold_of_signIndicator f hT_meas hT_nonzero hT_finite hc_on_T

/- Helper for Lemma 7.49: the `L∞` endpoint should use an almost norm-attaining superlevel-set
test built from a normalized finite restriction of the superlevel measure. -/
lemma lp_pairing_norm_ge_of_top [SigmaFinite μ] (f : Lp ℝ ∞ μ) :
    ‖f‖ ≤ ‖(mul ℝ ℝ).lpPairing μ ∞ 1 f‖ := by
  by_contra hlt
  let c : ℝ := (‖(mul ℝ ℝ).lpPairing μ ∞ 1 f‖ + ‖f‖) / 2
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc_lt_norm : c < ‖f‖ := by
    dsimp [c]
    linarith
  have hnorm_lt_c : ‖(mul ℝ ℝ).lpPairing μ ∞ 1 f‖ < c := by
    dsimp [c]
    linarith
  let S : Set Ω := {x | c < |f x|}
  have hS_pos : 0 < μ S := superlevel_pos_of_lt_lpNorm_top f hc_nonneg hc_lt_norm
  have hS_nonzero : μ.restrict S ≠ 0 := by
    intro hzero
    exact ne_of_gt hS_pos ((Measure.restrict_eq_zero).1 hzero)
  have hS_nullMeasurable : MeasureTheory.NullMeasurableSet S μ := by
    simpa [S] using nullMeasurableSet_lt
      aemeasurable_const ((Lp.aestronglyMeasurable f).norm.aemeasurable)
  have hc_restrict : ∀ᵐ x ∂μ.restrict S, c ≤ |f x| := by
    rw [MeasureTheory.ae_restrict_iff'₀ hS_nullMeasurable]
    exact Filter.Eventually.of_forall fun x hx ↦ le_of_lt hx
  rcases superlevel_restrict_test_function f hS_nonzero hS_nullMeasurable hc_restrict with
    ⟨g, hg_norm, hpair_ge⟩
  have hopNorm :
      |((mul ℝ ℝ).lpPairing μ ∞ 1 f) g|
        ≤ ‖(mul ℝ ℝ).lpPairing μ ∞ 1 f‖ * ‖g‖ := by
    simpa [Real.norm_eq_abs] using
      ContinuousLinearMap.le_opNorm ((mul ℝ ℝ).lpPairing μ ∞ 1 f) g
  have hpair_lt_c : |((mul ℝ ℝ).lpPairing μ ∞ 1 f) g| < c := by
    have hpair_le_norm : |((mul ℝ ℝ).lpPairing μ ∞ 1 f) g| ≤ ‖(mul ℝ ℝ).lpPairing μ ∞ 1 f‖ := by
      have hnorm_nonneg : 0 ≤ ‖(mul ℝ ℝ).lpPairing μ ∞ 1 f‖ := norm_nonneg _
      have hg_nonneg : 0 ≤ ‖g‖ := norm_nonneg g
      nlinarith
    exact lt_of_le_of_lt hpair_le_norm hnorm_lt_c
  exact not_lt_of_ge hpair_ge hpair_lt_c

/-- Helper for Lemma 7.49: in the finite-conjugate case, the standard extremizer identity holds
pointwise. -/
lemma finite_conj_pointwise (p : ENNReal) [Fact (1 ≤ p)] [Fact (1 < p)] [Fact (p < ∞)] (r : ℝ) :
    r * (Real.sign r * (|r| ^ (conjExponent p - 1).toReal)) = |r| ^ (conjExponent p).toReal := by
  have hq_ne_top : conjExponent p ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one (conjExponent p) p).2 <| by
      simpa using (Fact.out : 1 < p).ne'
  have hq_ne_zero : conjExponent p ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (ENNReal.HolderConjugate.one_le (conjExponent p) p)).ne'
  by_cases hr : r = 0
  · -- The zero case is immediate because the conjugate exponent is positive.
    simp [hr, Real.zero_rpow (ENNReal.toReal_pos hq_ne_zero hq_ne_top).ne']
  have hq_sub_ne_top : conjExponent p - 1 ≠ ∞ := sub_ne_top hq_ne_top
  have hq_toReal : (conjExponent p - 1).toReal + 1 = (conjExponent p).toReal := by
    -- Convert `q = (q - 1) + 1` to real exponents.
    symm
    simpa [tsub_add_cancel_of_le (ENNReal.HolderConjugate.one_le (conjExponent p) p),
      ENNReal.toReal_one] using ENNReal.toReal_add hq_sub_ne_top one_ne_top
  rw [← mul_assoc, real_sign_eq_sign, self_mul_sign]
  conv_lhs => enter [1]; rw [show |r| = |r| ^ (1 : ℝ) by simp]
  rw [← Real.rpow_add (abs_pos.2 hr)]
  congr 1
  linarith

/-- Helper for Lemma 7.49: for `1 < p < ∞`, the power `|f|^(q-1)` lies in `L^p`, where
`q = conjExponent p`. -/
lemma abs_power_memLp (p : ENNReal) [Fact (1 ≤ p)] [Fact (1 < p)] [Fact (p < ∞)]
    [SFinite μ] (f : Lp ℝ (conjExponent p) μ) :
    MemLp (fun x ↦ ‖f x‖ ^ (conjExponent p - 1).toReal) p μ := by
  have hp_ne_zero : p ≠ 0 :=
    (show (0 : ENNReal) < p from lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hp_ne_top : p ≠ ∞ := (Fact.out : p < ∞).ne
  have hq_ne_top : conjExponent p ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one (conjExponent p) p).2 <| by
      simpa using (Fact.out : 1 < p).ne'
  have hq_gt_one : 1 < conjExponent p := by
    simpa [lt_top_iff_ne_top] using
      (ENNReal.HolderConjugate.lt_top_iff_one_lt p (conjExponent p)).1
        (Fact.out : p < ∞)
  have hq_sub_ne_zero : conjExponent p - 1 ≠ 0 := (tsub_pos_of_lt hq_gt_one).ne'
  have hq_sub_ne_top : conjExponent p - 1 ≠ ∞ := sub_ne_top hq_ne_top
  have hp_eq : p = conjExponent p / (conjExponent p - 1) := by
    have hq_div : conjExponent p / p = conjExponent p - 1 := by
      simpa using
        (ENNReal.HolderConjugate.div_conj_eq_sub_one : conjExponent p / p = conjExponent p - 1)
    -- Re-express the conjugacy relation as `p = q / (q - 1)`.
    apply (ENNReal.eq_div_iff hq_sub_ne_zero hq_sub_ne_top).2
    have hmul : p * (conjExponent p - 1) = conjExponent p := by
      exact (ENNReal.eq_div_iff hp_ne_zero hp_ne_top).1 hq_div.symm
    simpa [mul_comm] using hmul
  let P : ENNReal → Prop :=
    fun r ↦ MemLp (fun x ↦ ‖f x‖ ^ (conjExponent p - 1).toReal) r μ
  have hmem : P (conjExponent p / (conjExponent p - 1)) :=
    (Lp.memLp f).norm_rpow_div (conjExponent p - 1)
  exact Eq.mp (congrArg P hp_eq).symm hmem

/-- Helper for Lemma 7.49: for `1 < p < ∞`, the `L^p` norm of `|f|^(q-1)` is the expected power
of the `L^q` norm of `f`. -/
lemma abs_power_norm (p : ENNReal) [Fact (1 ≤ p)] [Fact (1 < p)] [Fact (p < ∞)] [SFinite μ]
    (f : Lp ℝ (conjExponent p) μ) :
    ‖(abs_power_memLp p f).toLp
        (fun x ↦ ‖f x‖ ^ (conjExponent p - 1).toReal)‖ =
      ‖f‖ ^ (conjExponent p - 1).toReal := by
  have hp_ne_zero : p ≠ 0 :=
    (show (0 : ENNReal) < p from lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hp_ne_top : p ≠ ∞ := (Fact.out : p < ∞).ne
  have hq_ne_top : conjExponent p ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one (conjExponent p) p).2 <| by
      simpa using (Fact.out : 1 < p).ne'
  have hq_sub_ne_top : conjExponent p - 1 ≠ ∞ := sub_ne_top hq_ne_top
  have hmul : p * ENNReal.ofReal (conjExponent p - 1).toReal = conjExponent p := by
    have hq_div : conjExponent p / p = conjExponent p - 1 := by
      simpa using
        (ENNReal.HolderConjugate.div_conj_eq_sub_one : conjExponent p / p = conjExponent p - 1)
    have hmul' : p * (conjExponent p - 1) = conjExponent p := by
      exact (ENNReal.eq_div_iff hp_ne_zero hp_ne_top).1 hq_div.symm
    simpa [ENNReal.ofReal_toReal hq_sub_ne_top] using hmul'
  calc
    ‖(abs_power_memLp p f).toLp
        (fun x ↦ ‖f x‖ ^ (conjExponent p - 1).toReal)‖
      = (eLpNorm (fun x ↦ ‖f x‖ ^ (conjExponent p - 1).toReal) p μ).toReal := by
          rw [Lp.norm_toLp]
    _ = (eLpNorm (fun x ↦ f x) (p * ENNReal.ofReal (conjExponent p - 1).toReal) μ ^
          (conjExponent p - 1).toReal).toReal := by
          rw [MeasureTheory.eLpNorm_norm_rpow]
          have hq_gt_one : 1 < conjExponent p := by
            simpa [lt_top_iff_ne_top] using
              (ENNReal.HolderConjugate.lt_top_iff_one_lt p (conjExponent p)).1
                (Fact.out : p < ∞)
          exact ENNReal.toReal_pos (tsub_pos_of_lt hq_gt_one).ne' hq_sub_ne_top
    _ = (eLpNorm (fun x ↦ f x) (conjExponent p) μ ^ (conjExponent p - 1).toReal).toReal := by
          simp [hmul]
    _ = ‖f‖ ^ (conjExponent p - 1).toReal := by
          symm
          simpa [Lp.norm_def] using ENNReal.toReal_rpow
            (eLpNorm (fun x ↦ f x) (conjExponent p) μ) ((conjExponent p - 1).toReal)

/-- Helper for Lemma 7.49: the integral of `|f|^q` is the `q`th power of the `L^q` norm. -/
lemma conj_integral_eq_norm_rpow (p : ENNReal) [Fact (1 ≤ p)] [Fact (1 < p)] [Fact (p < ∞)]
    [SFinite μ] (f : Lp ℝ (conjExponent p) μ) :
    ∫ x, |f x| ^ (conjExponent p).toReal ∂μ = ‖f‖ ^ (conjExponent p).toReal := by
  have hq_ne_zero : conjExponent p ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (ENNReal.HolderConjugate.one_le (conjExponent p) p)).ne'
  have hq_ne_top : conjExponent p ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one (conjExponent p) p).2 <| by
      simpa using (Fact.out : 1 < p).ne'
  have hq_pos : 0 < (conjExponent p).toReal := ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hnorm :
      ‖f‖ = (∫ x, |f x| ^ (conjExponent p).toReal ∂μ) ^ ((conjExponent p).toReal)⁻¹ := by
    rw [Lp.norm_def, MeasureTheory.toReal_eLpNorm (Lp.aestronglyMeasurable f)]
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        hq_ne_zero hq_ne_top (Lp.aestronglyMeasurable f))
  have hint_nonneg : 0 ≤ ∫ x, |f x| ^ (conjExponent p).toReal ∂μ := by
    refine integral_nonneg ?_
    intro x
    exact Real.rpow_nonneg (abs_nonneg (f x)) _
  symm
  calc
    ‖f‖ ^ (conjExponent p).toReal
      = ((∫ x, |f x| ^ (conjExponent p).toReal ∂μ) ^ ((conjExponent p).toReal)⁻¹) ^
          (conjExponent p).toReal := by rw [hnorm]
    _ = (∫ x, |f x| ^ (conjExponent p).toReal ∂μ) ^
          (((conjExponent p).toReal)⁻¹ * (conjExponent p).toReal) := by
            rw [Real.rpow_mul hint_nonneg]
    _ = ∫ x, |f x| ^ (conjExponent p).toReal ∂μ := by
            rw [inv_mul_cancel₀ hq_pos.ne', Real.rpow_one]

/-- Helper for Lemma 7.49: for `1 < p < ∞`, the power `‖f‖^q` splits as
`‖f‖ * ‖f‖^(q-1)`. -/
lemma split_power (p : ENNReal) [Fact (1 ≤ p)] [Fact (1 < p)] [Fact (p < ∞)] {r : ℝ}
    (hr : 0 < r) :
    r ^ (conjExponent p).toReal = r * r ^ (conjExponent p - 1).toReal := by
  have hq_ne_top : conjExponent p ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one (conjExponent p) p).2 <| by
      simpa using (Fact.out : 1 < p).ne'
  have hq_sub_ne_top : conjExponent p - 1 ≠ ∞ := sub_ne_top hq_ne_top
  have hq_toReal : (conjExponent p - 1).toReal + 1 = (conjExponent p).toReal := by
    symm
    simpa [tsub_add_cancel_of_le (ENNReal.HolderConjugate.one_le (conjExponent p) p),
      ENNReal.toReal_one] using ENNReal.toReal_add hq_sub_ne_top one_ne_top
  calc
    r ^ (conjExponent p).toReal = r ^ ((conjExponent p - 1).toReal + 1) := by rw [hq_toReal]
    _ = r ^ (conjExponent p - 1).toReal * r ^ (1 : ℝ) := by rw [Real.rpow_add hr]
    _ = r * r ^ (conjExponent p - 1).toReal := by simp [mul_comm]

/- Helper for Lemma 7.49: for `1 < p < ∞`, the extremizer
`sign(f) * |f| ^ ((conjExponent p - 1).toReal)` should attain the operator norm. -/
lemma lp_pairing_norm_ge_of_finite_conj (p : ENNReal) [Fact (1 ≤ p)] [Fact (1 < p)]
    [Fact (p < ∞)] [SFinite μ]
    (f : Lp ℝ (conjExponent p) μ) :
    ‖f‖ ≤ ‖(mul ℝ ℝ).lpPairing μ (conjExponent p) p f‖ := by
  by_cases hf_zero : ‖f‖ = 0
  · -- The zero-norm case is immediate.
    simp [hf_zero]
  rcases sign_test_function f with ⟨s, hs_norm, hs_eq⟩
  let hpow_mem := abs_power_memLp p f
  let hpow : Lp ℝ p μ := hpow_mem.toLp
    (fun x ↦ ‖f x‖ ^ (conjExponent p - 1).toReal)
  let g : Lp ℝ p μ := s • hpow
  have hf_pos : 0 < ‖f‖ := by
    exact lt_of_le_of_ne (norm_nonneg _) (by simpa [eq_comm] using hf_zero)
  have hg_norm : ‖g‖ ≤ ‖f‖ ^ (conjExponent p - 1).toReal := by
    -- The sign factor has norm at most `1`, so the extremizer norm is controlled by the power term.
    calc
      ‖g‖ ≤ ‖s‖ * ‖hpow‖ := Lp.norm_smul_le s hpow
      _ ≤ ‖hpow‖ := by nlinarith [hs_norm, norm_nonneg hpow]
      _ = ‖f‖ ^ (conjExponent p - 1).toReal := abs_power_norm p f
  have hpair :
      ((mul ℝ ℝ).lpPairing μ (conjExponent p) p f) g
        = ‖f‖ ^ (conjExponent p).toReal := by
    -- The textbook extremizer collapses the pairing to the common `|f|^q` integral.
    have hsmul :
        (s • hpow : Lp ℝ p μ) =ᵐ[μ] ⇑s • ⇑hpow := by
      simpa using (Lp.coeFn_lpSMul s hpow)
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    calc
      ∫ x, f x * g x ∂μ
        = ∫ x, |f x| ^ (conjExponent p).toReal ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hsmul, hs_eq, MemLp.coeFn_toLp hpow_mem] with x hx hxsign hxpow
            rw [hx]
            have hxg :
                (⇑s • ⇑hpow) x = Real.sign (f x) * (|f x| ^ (conjExponent p - 1).toReal) := by
              change s x * hpow x = Real.sign (f x) * (|f x| ^ (conjExponent p - 1).toReal)
              rw [hxsign, show hpow x = ‖f x‖ ^ (conjExponent p - 1).toReal by
                exact hxpow]
              simp [Real.norm_eq_abs]
            rw [hxg]
            simpa [mul_assoc, mul_left_comm, mul_comm] using finite_conj_pointwise p (f x)
      _ = ‖f‖ ^ (conjExponent p).toReal := conj_integral_eq_norm_rpow p f
  have hpow_pos : 0 < ‖f‖ ^ (conjExponent p - 1).toReal := by
    exact Real.rpow_pos_of_pos hf_pos _
  have hineq :
      ‖f‖ * ‖f‖ ^ (conjExponent p - 1).toReal
        ≤ ‖(mul ℝ ℝ).lpPairing μ (conjExponent p) p f‖ * ‖f‖ ^ (conjExponent p - 1).toReal := by
    calc
      ‖f‖ * ‖f‖ ^ (conjExponent p - 1).toReal = ‖f‖ ^ (conjExponent p).toReal := by
            symm
            exact split_power p hf_pos
      _ = |((mul ℝ ℝ).lpPairing μ (conjExponent p) p f) g| := by
            rw [hpair, abs_of_nonneg]
            positivity
      _ ≤ ‖(mul ℝ ℝ).lpPairing μ (conjExponent p) p f‖ * ‖g‖ := by
            simpa [Real.norm_eq_abs] using
              ContinuousLinearMap.le_opNorm ((mul ℝ ℝ).lpPairing μ (conjExponent p) p f) g
      _ ≤ ‖(mul ℝ ℝ).lpPairing μ (conjExponent p) p f‖ * ‖f‖ ^ (conjExponent p - 1).toReal := by
            gcongr
  exact le_of_mul_le_mul_right hineq hpow_pos

/- Helper for Lemma 7.49: transporting an `Lp` vector along an equality of exponents preserves
its norm. -/
private lemma lpNorm_cast_eq {p q : ENNReal} (h : p = q) (f : Lp ℝ p μ) :
    ‖f‖ = ‖cast (by rw [h]) f‖ := by
  subst h
  rfl

/-- Helper for Lemma 7.49: transporting an `Lp` vector along an equality of source exponents
preserves the partially applied pairing functional. -/
private lemma lpPairing_cast_eq {p q r : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [HolderConjugate p r] [HolderConjugate q r] (h : p = q) (f : Lp ℝ p μ) :
    (mul ℝ ℝ).lpPairing μ q r (cast (by rw [h]) f) = (mul ℝ ℝ).lpPairing μ p r f := by
  -- Once the source exponent is rewritten abstractly, the casted pairing is definitionally equal.
  subst h
  rfl

/- Helper for Lemma 7.49: transport the `p = 1` endpoint inequality from the casted `L∞`
witness back to the original `conjExponent 1` source exponent. -/
private lemma lpPairing_endpoint_transport_pOne (h : conjExponent (1 : ENNReal) = ∞)
    (f : Lp ℝ (conjExponent 1) μ) :
    (‖cast (by rw [h]) f‖ ≤ ‖(mul ℝ ℝ).lpPairing μ ∞ 1 (cast (by rw [h]) f)‖) →
      ‖f‖ ≤ ‖(mul ℝ ℝ).lpPairing μ (conjExponent (1 : ENNReal)) 1 f‖ := by
  intro hineq
  have hpair :
      ‖(mul ℝ ℝ).lpPairing μ ∞ 1 (cast (by rw [h]) f)‖
        = ‖(mul ℝ ℝ).lpPairing μ (conjExponent (1 : ENNReal)) 1 f‖ := by
    -- Rewrite the pairing after transporting the source `Lp` vector across the endpoint equality.
    simpa using congrArg norm (lpPairing_cast_eq h f)
  -- The endpoint inequality now matches the branch goal after the two transport rewrites.
  simpa [lpNorm_cast_eq h f, hpair] using hineq

/- Helper for Lemma 7.49: transport the `p = ∞` endpoint inequality from the casted `L¹`
witness back to the original `conjExponent ∞` source exponent. -/
private lemma lpPairing_endpoint_transport_pTop (h : conjExponent (∞ : ENNReal) = 1)
    (f : Lp ℝ (conjExponent ∞) μ) :
    (‖cast (by rw [h]) f‖ ≤ ‖(mul ℝ ℝ).lpPairing μ 1 ∞ (cast (by rw [h]) f)‖) →
      ‖f‖ ≤ ‖(mul ℝ ℝ).lpPairing μ (conjExponent (∞ : ENNReal)) ∞ f‖ := by
  intro hineq
  have hpair :
      ‖(mul ℝ ℝ).lpPairing μ 1 ∞ (cast (by rw [h]) f)‖
        = ‖(mul ℝ ℝ).lpPairing μ (conjExponent (∞ : ENNReal)) ∞ f‖ := by
    -- Rewrite the pairing after transporting the source `Lp` vector across the endpoint equality.
    simpa using congrArg norm (lpPairing_cast_eq h f)
  -- The endpoint inequality now matches the branch goal after the two transport rewrites.
  simpa [lpNorm_cast_eq h f, hpair] using hineq

-- Proof sketch: the upper bound is Hölder's inequality. For the reverse inequality, use the
-- standard extremizing choices: `g = 1` when `q = 1`, `g = |f|^(q - 1) sign(f)` when
-- `1 < q < ∞`, and normalized indicators of finite-measure superlevel sets when `q = ∞`.
/-- Companion norm formula for `lpDualityMap_isometry`. -/
theorem norm_lpDualityMap_eq (p : ENNReal) [Fact (1 ≤ p)] [SigmaFinite μ]
    (f : Lp ℝ (conjExponent p) μ) :
    ‖(mul ℝ ℝ).lpPairing μ (conjExponent p) p f‖ = ‖f‖ := by
  refine le_antisymm (lp_pairing_norm_le_norm p f) ?_
  by_cases hp_one : p = 1
  · -- When `p = 1`, the conjugate exponent is `∞`, so the `L∞` endpoint applies.
    subst p
    letI : Fact (1 ≤ (∞ : ENNReal)) := ⟨le_top⟩
    have hq : conjExponent (1 : ENNReal) = ∞ := by simp [ENNReal.conjExponent]
    let hf : Lp ℝ ∞ μ := cast (by rw [hq]) f
    have h_endpoint : ‖hf‖ ≤ ‖(mul ℝ ℝ).lpPairing μ ∞ 1 hf‖ :=
      lp_pairing_norm_ge_of_top hf
    -- Transport the endpoint inequality back to the original source exponent in one step.
    exact lpPairing_endpoint_transport_pOne hq f <| by simpa [hf] using h_endpoint
  · by_cases hp_top : p = ∞
    · -- When `p = ∞`, the conjugate exponent is `1`, so we reduce to the `L¹` endpoint.
      subst p
      letI : Fact (1 ≤ (1 : ENNReal)) := ⟨le_rfl⟩
      have hq : conjExponent (∞ : ENNReal) = 1 := by simp [ENNReal.conjExponent]
      let hf : Lp ℝ 1 μ := cast (by rw [hq]) f
      have h_endpoint : ‖hf‖ ≤ ‖(mul ℝ ℝ).lpPairing μ 1 ∞ hf‖ :=
        lp_pairing_norm_ge_of_L1 hf
      -- Transport the endpoint inequality back to the original source exponent in one step.
      exact lpPairing_endpoint_transport_pTop hq f <| by simpa [hf] using h_endpoint
    · -- The remaining case is the standard finite conjugate-extremizer argument.
      have hp_gt_one : 1 < p := lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp_one)
      have hp_lt_top : p < ∞ := lt_of_le_of_ne le_top hp_top
      letI : Fact (1 < p) := ⟨hp_gt_one⟩
      letI : Fact (p < ∞) := ⟨hp_lt_top⟩
      exact lp_pairing_norm_ge_of_finite_conj p f

/-- Lemma 7.49: let `p, q ∈ [1, ∞]` with `1 / p + 1 / q = 1`. The canonical map
`κ : L^q(μ) → (L^p(μ))'` given by `κ(f)(g) = ∫ x, f x * g x ∂μ` is an isometry; that is, the
associated functional on `L^p(μ)` has operator norm `‖f‖`. In the source proof, the `q = ∞`
endpoint chooses a measurable subset `A_ε` of a positive superlevel set with
`0 < μ A_ε < ∞`; in this Lean formalization, that ambient measure-side context is supplied by
`[SigmaFinite μ]` via `Measure.exists_subset_measure_lt_top`. Here `q` is represented by
`ENNReal.conjExponent p`. -/
theorem lpDualityMap_isometry {p : ENNReal} [Fact (1 ≤ p)] [SigmaFinite μ] :
    Isometry
      ((mul ℝ ℝ).lpPairing μ (conjExponent p) p :
        Lp ℝ (conjExponent p) μ → StrongDual ℝ (Lp ℝ p μ)) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  intro f
  exact norm_lpDualityMap_eq p f

end
