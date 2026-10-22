/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Helper for Exercise 7.1.2: if `c < eLpNorm f ∞ μ`, then the superlevel set
`{x | ENNReal.ofReal c < ‖f x‖ₑ}` has positive measure. -/
lemma measure_ne_zero_of_lt_eLpNormEssSup {f : Ω → ℝ} {c : ℝ}
    (hc : ENNReal.ofReal c < eLpNorm f ∞ μ) :
    μ {x | ENNReal.ofReal c < ‖f x‖ₑ} ≠ 0 := by
  -- If the superlevel set were null, then `‖f x‖ₑ ≤ ENNReal.ofReal c` almost everywhere.
  intro hzero
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ENNReal.ofReal c := by
    have hnull : ∀ᵐ x ∂μ, x ∉ {x | ENNReal.ofReal c < ‖f x‖ₑ} := by
      rw [ae_iff]
      simpa [hzero]
    exact hnull.mono fun x hx => by
      simpa [Set.mem_setOf, not_lt] using hx
  have hle : eLpNorm f ∞ μ ≤ ENNReal.ofReal c := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_enorm_bound hbound
  exact hc.not_ge hle

/-- Helper for Exercise 7.1.2: for a finite positive constant `a`, the factors `a ^ (1 / q)`
approach `1` as `q → ∞`. -/
lemma tendsto_rpow_div_atTop_one {a : ℝ≥0∞} {k : ℝ} (hk : 0 ≤ k) (ha0 : 0 < a)
    (ha_top : a < ∞) :
    Tendsto (fun q : NNReal ↦ a ^ (k / q)) atTop (𝓝 1) := by
  -- Rewrite the base through `a.toReal` and use continuity of the real map `x ↦ a^x` at `0`.
  have hInv : Tendsto (fun q : NNReal ↦ (q : ℝ)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp <| (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hDiv : Tendsto (fun q : NNReal ↦ k / q) atTop (𝓝 0) := by
    have hMul : Tendsto (fun q : NNReal ↦ k * (q : ℝ)⁻¹) atTop (𝓝 ((k : ℝ) * 0)) :=
      tendsto_const_nhds.mul hInv
    simpa [div_eq_mul_inv] using hMul
  have haReal0 : (0 : ℝ) < a.toReal := ENNReal.toReal_pos ha0.ne' ha_top.ne
  have hReal :
      Tendsto (fun q : NNReal ↦ (a.toReal : ℝ) ^ (k / q)) atTop
        (𝓝 ((a.toReal : ℝ) ^ (0 : ℝ))) := by
    exact (Real.continuousAt_const_rpow haReal0.ne').tendsto.comp hDiv
  have hOfReal :
      Tendsto (fun q : NNReal ↦ ENNReal.ofReal ((a.toReal : ℝ) ^ (k / q))) atTop
        (𝓝 (ENNReal.ofReal ((a.toReal : ℝ) ^ (0 : ℝ)))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hReal
  have hEq :
      (fun q : NNReal ↦ a ^ (k / q)) =
        fun q : NNReal ↦ ENNReal.ofReal ((a.toReal : ℝ) ^ (k / q)) := by
    funext q
    have hpow :=
      ENNReal.ofReal_rpow_of_nonneg (x := a.toReal) ENNReal.toReal_nonneg
        (div_nonneg hk (show 0 ≤ (q : ℝ) by exact NNReal.coe_nonneg q))
    simpa [ha_top.ne] using hpow
  simpa [hEq, ha_top.ne, Real.rpow_zero] using hOfReal

/-- Helper for Exercise 7.1.2: the special case `a ^ (1 / q) → 1` of the previous asymptotic
lemma. -/
lemma tendsto_rpow_inv_atTop_one {a : ℝ≥0∞} (ha0 : 0 < a) (ha_top : a < ∞) :
    Tendsto (fun q : NNReal ↦ a ^ ((q : ℝ)⁻¹)) atTop (𝓝 1) := by
  simpa [one_div] using
    (tendsto_rpow_div_atTop_one (a := a) (k := 1) (by positivity) ha0 ha_top)

/-- Helper for Exercise 7.1.2: an a.e. `L^∞` bound together with `MemLp f r μ` controls all larger
finite exponents. -/
lemma eLpNorm_le_of_ae_bound_of_memLp {f : Ω → ℝ} {r q : NNReal} (hr : 0 < r) (hrq : r ≤ q)
    {C : NNReal} (hC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNorm f (q : ℝ≥0∞) μ ≤
      (C : ℝ≥0∞) ^ (1 - (r : ℝ) / q) * eLpNorm f (r : ℝ≥0∞) μ ^ ((r : ℝ) / q) := by
  -- Raise the pointwise bound to compare the `L¹` norms of `|f|^q` and `|f|^r`.
  have hq : 0 < q := lt_of_lt_of_le hr hrq
  have hq_real : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpow :
      ∀ᵐ x ∂μ, ‖f x‖ ^ (q : ℝ) ≤ (C : ℝ) ^ ((q : ℝ) - r) * ‖f x‖ ^ (r : ℝ) := by
    filter_upwards [hC] with x hx
    have hqr : 0 ≤ (q : ℝ) - r := sub_nonneg.mpr (by exact_mod_cast hrq)
    calc
      ‖f x‖ ^ (q : ℝ) = ‖f x‖ ^ (((q : ℝ) - r) + r) := by
        congr 2
        ring
      _ = ‖f x‖ ^ ((q : ℝ) - r) * ‖f x‖ ^ (r : ℝ) := by
        simpa using (Real.rpow_add_of_nonneg (norm_nonneg _) hqr hr.le :
          ‖f x‖ ^ (((q : ℝ) - r) + r) = ‖f x‖ ^ ((q : ℝ) - r) * ‖f x‖ ^ (r : ℝ))
      _ ≤ (C : ℝ) ^ ((q : ℝ) - r) * ‖f x‖ ^ (r : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
        exact Real.rpow_le_rpow (norm_nonneg _) (by exact_mod_cast hx) hqr
  have hpow' :
      ∀ᵐ x ∂μ,
        ‖‖f x‖ ^ (q : ℝ)‖ ≤ (C : ℝ) ^ ((q : ℝ) - r) * ‖‖f x‖ ^ (r : ℝ)‖ := by
    filter_upwards [hpow] with x hx
    have hq_nonneg : 0 ≤ ‖f x‖ ^ (q : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have hr_nonneg : 0 ≤ ‖f x‖ ^ (r : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have hr_eq : ‖‖f x‖ ^ (r : ℝ)‖ = ‖f x‖ ^ (r : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg, hr_eq]
    exact hx
  have hL1 :
      eLpNorm (fun x ↦ ‖f x‖ ^ (q : ℝ)) 1 μ ≤
        ENNReal.ofReal ((C : ℝ) ^ ((q : ℝ) - r)) *
          eLpNorm (fun x ↦ ‖f x‖ ^ (r : ℝ)) 1 μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpow' 1
  have hqpow :
      eLpNorm (fun x ↦ ‖f x‖ ^ (q : ℝ)) 1 μ = eLpNorm f q μ ^ (q : ℝ) := by
    simpa using (eLpNorm_norm_rpow (p := (1 : ℝ≥0∞)) (μ := μ) f hq_real)
  have hrpow :
      eLpNorm (fun x ↦ ‖f x‖ ^ (r : ℝ)) 1 μ = eLpNorm f r μ ^ (r : ℝ) := by
    have hr_real : 0 < (r : ℝ) := by exact_mod_cast hr
    simpa using (eLpNorm_norm_rpow (p := (1 : ℝ≥0∞)) (μ := μ) f hr_real)
  rw [hqpow, hrpow] at hL1
  have hroot := ENNReal.rpow_le_rpow hL1 (inv_nonneg.2 hq_real.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq_real.le)] at hroot
  have hqmul : (q : ℝ) * (q : ℝ)⁻¹ = 1 := by field_simp [hq_real.ne]
  rw [← ENNReal.rpow_mul, hqmul, ENNReal.rpow_one] at hroot
  have hq_nonneg : 0 ≤ 1 - (r : ℝ) / q := by
    have hqr : 0 ≤ (q : ℝ) - r := sub_nonneg.mpr (by exact_mod_cast hrq)
    have hexp : ((q : ℝ) - r) * (q : ℝ)⁻¹ = 1 - (r : ℝ) / q := by
      field_simp [hq_real.ne]
    rw [← hexp]
    exact mul_nonneg hqr (inv_nonneg.2 hq_real.le)
  have hCsplit :
      ENNReal.ofReal ((C : ℝ) ^ ((q : ℝ) - r)) ^ ((q : ℝ)⁻¹) =
        (C : ℝ≥0∞) ^ (1 - (r : ℝ) / q) := by
    have hexp : ((q : ℝ) - r) * (q : ℝ)⁻¹ = 1 - (r : ℝ) / q := by
      field_simp [hq_real.ne]
    calc
      ENNReal.ofReal ((C : ℝ) ^ ((q : ℝ) - r)) ^ ((q : ℝ)⁻¹)
          = ENNReal.ofReal (((C : ℝ) ^ ((q : ℝ) - r)) ^ ((q : ℝ)⁻¹)) := by
              exact
                (ENNReal.ofReal_rpow_of_nonneg
                  (x := (C : ℝ) ^ ((q : ℝ) - r))
                  (Real.rpow_nonneg C.2 _)
                  (inv_nonneg.2 hq_real.le))
      _ = ENNReal.ofReal ((C : ℝ) ^ (((q : ℝ) - r) * (q : ℝ)⁻¹)) := by
        congr 1
        exact (Real.rpow_mul C.2 _ _).symm
      _ = (C : ℝ≥0∞) ^ (1 - (r : ℝ) / q) := by
        rw [hexp]
        simpa using
          (ENNReal.ofReal_rpow_of_nonneg (show 0 ≤ (C : ℝ) by exact C.2) hq_nonneg).symm
  have hrsplit :
      (eLpNorm f r μ ^ (r : ℝ)) ^ ((q : ℝ)⁻¹) = eLpNorm f r μ ^ ((r : ℝ) / q) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (ENNReal.rpow_mul (eLpNorm f r μ) (r : ℝ) ((q : ℝ)⁻¹)).symm
  rw [hCsplit, hrsplit] at hroot
  exact hroot

/-- Exercise 7.1.2 (1): canonical `MemLp` form of clause (i). If `f` belongs to `L^p(μ)` for some
positive finite exponent, then its finite-exponent seminorms converge to the `L^∞` seminorm as
`p → ∞`. -/
-- Proof sketch: compare the seminorms for different exponents using the standard `eLpNorm`
-- comparison inequalities, use the finite-exponent hypothesis to control all large exponents, and
-- identify the limiting upper and lower bounds with `eLpNorm f ∞ μ`.
theorem tendsto_eLpNorm_atTop_of_exists_memLp {f : Ω → ℝ}
    (hfin : ∃ p : NNReal, 0 < p ∧ MemLp f p μ) :
    Tendsto (fun p : NNReal ↦ eLpNorm f p μ) atTop (𝓝 (eLpNorm f ∞ μ)) := by
  -- Route correction: the proof is organized through order convergence, with lower bounds coming
  -- from positive-measure superlevel sets and upper bounds coming from an a.e. `L^∞` bound.
  rcases hfin with ⟨r, hr, hf⟩
  by_cases hL0 : eLpNorm f ∞ μ = 0
  · -- If the `L^∞` seminorm is zero, then `f = 0` almost everywhere and every `eLpNorm` vanishes.
    have hzero : f =ᵐ[μ] 0 := by
      rwa [eLpNorm_exponent_top, eLpNormEssSup_eq_zero_iff] at hL0
    have hfun :
        (fun p : NNReal ↦ eLpNorm f p μ) =ᶠ[atTop] fun _ ↦ (0 : ℝ≥0∞) := by
      refine Eventually.of_forall ?_
      intro p
      exact eLpNorm_eq_zero_of_ae_zero hzero
    simpa [hL0] using (tendsto_congr' hfun).2 (tendsto_const_nhds : Tendsto (fun _ : NNReal ↦ (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hLower :
      ∀ ⦃a : ℝ≥0∞⦄, a < eLpNorm f ∞ μ → ∀ᶠ q : NNReal in atTop, a < eLpNorm f q μ := by
    intro a ha
    obtain ⟨c, hac, hcL⟩ := exists_between ha
    have hc_top : c < ∞ := lt_of_lt_of_le hcL le_top
    have hc_pos : 0 < c := lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ a from zero_le _) hac
    let g : Ω → ℝ := hf.aestronglyMeasurable.mk f
    let s : Set Ω := {x | c < ‖g x‖ₑ}
    have hg_eq : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
    have hg_mem : MemLp g r μ := hf.ae_eq hg_eq
    have hs : MeasurableSet s := by
      simpa [s, g] using measurableSet_lt measurable_const hf.aestronglyMeasurable.measurable_mk.enorm
    have hμs_ne_zero : μ s ≠ 0 := by
      have hcL' : ENNReal.ofReal c.toReal < eLpNorm g ∞ μ := by
        simpa [g, ENNReal.ofReal_toReal hc_top.ne, eLpNorm_congr_ae hg_eq] using hcL
      simpa [s, g, ENNReal.ofReal_toReal hc_top.ne] using
        measure_ne_zero_of_lt_eLpNormEssSup (f := g) (c := c.toReal) hcL'
    let t : Set Ω := {x | c.toNNReal ≤ ‖g x‖₊}
    have hcNN0 : c.toNNReal ≠ 0 := by
      intro hc0
      have : c = 0 := by simpa [hc0] using (ENNReal.coe_toNNReal hc_top.ne).symm
      exact hc_pos.ne' this
    have hμt_top : μ t < ∞ := by
      simpa [t, g] using
        hg_mem.meas_ge_lt_top (μ := μ) (by exact_mod_cast hr.ne') (by simp) hcNN0
    have hst : s ⊆ t := by
      intro x hx
      simp only [s, t, Set.mem_setOf] at hx ⊢
      exact ENNReal.coe_le_coe.mp (by simpa [ENNReal.coe_toNNReal hc_top.ne] using hx.le)
    have hμs_top : μ s < ∞ := lt_of_le_of_lt (measure_mono hst) hμt_top
    have hsBound : ∀ᵐ x ∂μ, x ∈ s → c.toNNReal ≤ ‖g x‖₊ := by
      refine Eventually.of_forall ?_
      intro x hx
      simp only [s, Set.mem_setOf] at hx
      exact ENNReal.coe_le_coe.mp (by simpa [ENNReal.coe_toNNReal hc_top.ne] using hx.le)
    have hPow : Tendsto (fun q : NNReal ↦ μ s ^ ((q : ℝ)⁻¹)) atTop (𝓝 1) :=
      tendsto_rpow_inv_atTop_one
        (lt_of_le_of_ne (show (0 : ℝ≥0∞) ≤ μ s from zero_le _) hμs_ne_zero.symm)
        hμs_top
    have hProd : Tendsto (fun q : NNReal ↦ c * μ s ^ ((q : ℝ)⁻¹)) atTop (𝓝 c) := by
      simpa using ENNReal.Tendsto.const_mul hPow (Or.inr hc_top.ne)
    have hGt : ∀ᶠ q : NNReal in atTop, a < c * μ s ^ ((q : ℝ)⁻¹) :=
      hProd.eventually (Ioi_mem_nhds hac)
    have hLe : ∀ᶠ q : NNReal in atTop, c * μ s ^ ((q : ℝ)⁻¹) ≤ eLpNorm f q μ := by
      filter_upwards [eventually_gt_atTop (0 : NNReal)] with q hq
      have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
      have hqLe : c.toNNReal • μ s ^ (1 / (q : ℝ)) ≤ eLpNorm g q μ :=
        le_eLpNorm_of_bddBelow (μ := μ) (p := (q : ℝ≥0∞)) hq0 (by simp)
          (C := c.toNNReal) (s := s) hs hsBound
      have hEq : eLpNorm g q μ = eLpNorm f q μ := by
        simpa using (eLpNorm_congr_ae hg_eq.symm : eLpNorm g q μ = eLpNorm f q μ)
      have hRewrite :
          c * μ s ^ ((q : ℝ)⁻¹) ≤ eLpNorm f q μ := by
        simpa [one_div, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal hc_top.ne] using
          hqLe.trans_eq hEq
      exact hRewrite
    exact (hGt.and hLe).mono fun q hq ↦ lt_of_lt_of_le hq.1 hq.2
  by_cases hLtop : eLpNorm f ∞ μ = ∞
  · refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact hLower ha
    · intro b hb
      have : False := by simpa [hLtop] using hb
      exact this.elim
  · have hUpper :
        ∀ ⦃b : ℝ≥0∞⦄, eLpNorm f ∞ μ < b → ∀ᶠ q : NNReal in atTop, eLpNorm f q μ < b := by
      intro b hb
      obtain ⟨B, hLB, hBb⟩ := exists_between hb
      have hB_top : B < ∞ := lt_of_lt_of_le hBb le_top
      have hB_pos : 0 < B := lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ eLpNorm f ∞ μ from zero_le _) hLB
      have hBound : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ B.toNNReal := by
        filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with x hx
        have hx' : ‖f x‖ₑ ≤ B := by
          simpa [eLpNorm_exponent_top] using hx.trans hLB.le
        exact ENNReal.coe_le_coe.mp <| by
          simpa [ENNReal.coe_toNNReal hB_top.ne] using hx'
      have hA_pos : 0 < eLpNorm f r μ := by
        by_contra hA
        have hA0 : eLpNorm f r μ = 0 := by
          exact le_antisymm (le_of_not_gt hA) (show (0 : ℝ≥0∞) ≤ eLpNorm f r μ from zero_le _)
        have hzero : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hf.aestronglyMeasurable (by exact_mod_cast hr.ne')).mp hA0
        have : eLpNorm f ∞ μ = 0 := by
          rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
        exact hL0 this
      have hA_top : eLpNorm f r μ < ∞ := hf.eLpNorm_lt_top
      have hExp :
          Tendsto (fun q : NNReal ↦ (eLpNorm f r μ) ^ ((r : ℝ) / q)) atTop (𝓝 1) :=
        tendsto_rpow_div_atTop_one (by positivity) hA_pos hA_top
      have hUpperControl :
          Tendsto
            (fun q : NNReal ↦
              ENNReal.ofReal
                ((B.toReal : ℝ) ^ (1 - (r : ℝ) / q) *
                  (eLpNorm f r μ).toReal ^ ((r : ℝ) / q)))
            atTop (𝓝 B) := by
        have hDiv :
            Tendsto (fun q : NNReal ↦ (r : ℝ) / q) atTop (𝓝 0) := by
          have hInv : Tendsto (fun q : NNReal ↦ (q : ℝ)⁻¹) atTop (𝓝 0) := by
            exact tendsto_inv_atTop_zero.comp <| (NNReal.tendsto_coe_atTop.2 tendsto_id)
          have hMul :
              Tendsto (fun q : NNReal ↦ (r : ℝ) * (q : ℝ)⁻¹) atTop
                (𝓝 (((r : ℝ)) * 0)) := tendsto_const_nhds.mul hInv
          simpa [div_eq_mul_inv] using hMul
        have hOneSub :
            Tendsto (fun q : NNReal ↦ (1 : ℝ) - (r : ℝ) / q) atTop (𝓝 1) := by
          simpa using (tendsto_const_nhds.sub hDiv)
        have hBreal0 : (B.toReal : ℝ) ≠ 0 :=
          (ENNReal.toReal_pos hB_pos.ne' hB_top.ne).ne'
        have hAreal0 : ((eLpNorm f r μ).toReal : ℝ) ≠ 0 :=
          (ENNReal.toReal_pos hA_pos.ne' hA_top.ne).ne'
        have hBpow :
            Tendsto (fun q : NNReal ↦ (B.toReal : ℝ) ^ (1 - (r : ℝ) / q)) atTop
              (𝓝 ((B.toReal : ℝ) ^ (1 : ℝ))) := by
          exact (Real.continuousAt_const_rpow hBreal0).tendsto.comp hOneSub
        have hApow :
            Tendsto (fun q : NNReal ↦ (eLpNorm f r μ).toReal ^ ((r : ℝ) / q)) atTop
              (𝓝 ((eLpNorm f r μ).toReal ^ (0 : ℝ))) := by
          exact (Real.continuousAt_const_rpow hAreal0).tendsto.comp hDiv
        have hMul := hBpow.mul hApow
        have hOfReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hMul
        simpa [ENNReal.ofReal_toReal hB_top.ne, Real.rpow_one, Real.rpow_zero] using hOfReal
      have hEventuallyControl :
          ∀ᶠ q : NNReal in atTop,
            ENNReal.ofReal
                ((B.toReal : ℝ) ^ (1 - (r : ℝ) / q) *
                  (eLpNorm f r μ).toReal ^ ((r : ℝ) / q)) < b :=
        hUpperControl.eventually (Iio_mem_nhds hBb)
      have hEventuallyBound :
          ∀ᶠ q : NNReal in atTop, eLpNorm f q μ ≤
            ENNReal.ofReal
                ((B.toReal : ℝ) ^ (1 - (r : ℝ) / q) *
                  (eLpNorm f r μ).toReal ^ ((r : ℝ) / q)) := by
        filter_upwards [eventually_ge_atTop r] with q hq
        have hInterp := eLpNorm_le_of_ae_bound_of_memLp hr hq hBound
        have hq_nonneg : 0 ≤ 1 - (r : ℝ) / q := by
          have hq_pos : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le hr hq
          have hqr' : (r : ℝ) ≤ q := by exact_mod_cast hq
          have hqr : (r : ℝ) / q ≤ 1 := by
            calc
              (r : ℝ) / q ≤ q / q := div_le_div_of_nonneg_right hqr' hq_pos.le
              _ = 1 := by field_simp [hq_pos.ne]
          linarith
        have hr_nonneg : 0 ≤ (r : ℝ) / q := by
          exact div_nonneg hr.le (show 0 ≤ (q : ℝ) by exact NNReal.coe_nonneg q)
        have hInterp' :
            eLpNorm f q μ ≤ B ^ (1 - (r : ℝ) / q) * eLpNorm f r μ ^ ((r : ℝ) / q) := by
          simpa [ENNReal.coe_toNNReal hB_top.ne] using hInterp
        have hEq :
            (B : ℝ≥0∞) ^ (1 - (r : ℝ) / q) * eLpNorm f r μ ^ ((r : ℝ) / q) =
              ENNReal.ofReal
                ((B.toReal : ℝ) ^ (1 - (r : ℝ) / q) *
                  (eLpNorm f r μ).toReal ^ ((r : ℝ) / q)) := by
          rw [← ENNReal.ofReal_toReal hB_top.ne, ← ENNReal.ofReal_toReal hA_top.ne]
          rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq_nonneg]
          rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hr_nonneg]
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
          simpa [ENNReal.ofReal_toReal hB_top.ne, ENNReal.ofReal_toReal hA_top.ne]
        exact hInterp'.trans_eq hEq
      exact (hEventuallyBound.and hEventuallyControl).mono fun q hq ↦ lt_of_le_of_lt hq.1 hq.2
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact hLower ha
    · intro b hb
      exact hUpper hb

/-- Exercise 7.1.2 (1): source-facing bridge from measurable finite-exponent data to the
canonical `MemLp` statement. -/
theorem tendsto_eLpNorm_atTop_of_finite_exponent {f : Ω → ℝ} (hf_meas : Measurable f)
    (hfin : ∃ p : NNReal, 0 < p ∧ eLpNorm f p μ < ∞) :
    Tendsto (fun p : NNReal ↦ eLpNorm f p μ) atTop (𝓝 (eLpNorm f ∞ μ)) :=
  tendsto_eLpNorm_atTop_of_exists_memLp <| by
    rcases hfin with ⟨p, hp, hpfin⟩
    exact ⟨p, hp, ⟨hf_meas.aestronglyMeasurable, hpfin⟩⟩

/-- Exercise 7.1.2 (2): Clause (ii). On `ℝ` with Lebesgue measure, the measurable constant
function `1` shows that the finite-exponent integrability assumption in clause (i) is necessary. -/
-- Proof sketch: for the constant function `1` on `ℝ`, every finite `L^p` seminorm is infinite
-- because `volume univ = ∞`, while the `L^∞` seminorm is `1`; hence the finite-exponent seminorms
-- cannot converge to the `L^∞` seminorm as `p → ∞`.
theorem not_tendsto_eLpNorm_const_one_atTop :
    ¬ Tendsto (fun p : NNReal ↦ eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) p volume) atTop
      (𝓝 (eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume)) := by
  intro h
  have hconst :
      (fun p : NNReal ↦ eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) p volume) =ᶠ[atTop]
        fun _ ↦ (∞ : ℝ≥0∞) := by
    filter_upwards [eventually_gt_atTop (0 : NNReal)] with p hp
    rw [eLpNorm_const' (1 : ℝ) (by exact_mod_cast hp.ne') (by simp)]
    simp [hp, one_div]
  have h' : Tendsto (fun _ : NNReal ↦ (∞ : ℝ≥0∞)) atTop
      (𝓝 (eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume)) :=
    (tendsto_congr' hconst).mp h
  have hEq : (∞ : ℝ≥0∞) = eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume :=
    tendsto_const_nhds_iff.mp h'
  rw [eLpNorm_exponent_top, eLpNormEssSup_const _] at hEq
  · norm_num at hEq
  · intro hvolume
    simpa [hvolume] using (Real.volume_univ : volume (Set.univ : Set ℝ) = ∞)

end MeasureTheory
