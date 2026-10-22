/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Exercise_23_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Exercise_23_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

local instance integrableExpSetMemDecidableCauchy
    (X : ℝ → ℝ) (P : Measure ℝ) (t : ℝ) :
    Decidable (t ∈ integrableExpSet X P) :=
  Classical.decPred _ t

/-- Helper for Exercise 23.2.5: reflecting both the center and the evaluation point leaves the
real Cauchy density unchanged. -/
lemma cauchyPDFReal_neg_center_neg (x₀ : ℝ) (γ : NNReal) (x : ℝ) :
    cauchyPDFReal (-x₀) γ (-x) = cauchyPDFReal x₀ γ x := by
  -- Proof comment: the Cauchy density depends on `x` only through the squared distance
  -- `(x - x₀)^2`.
  rw [cauchyPDFReal_def, cauchyPDFReal_def]
  congr 2
  ring

/-- Helper for Exercise 23.2.5: on a far right tail, a nondegenerate Cauchy density dominates a
fixed multiple of `x⁻²`. -/
lemma cauchyPDFReal_lower_right_tail
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧
      ∀ x ≥ R, ((γ : ℝ) / (5 * Real.pi)) / x ^ 2 ≤ cauchyPDFReal x₀ γ x := by
  let R : ℝ := max 1 (max |x₀| γ)
  refine ⟨R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  have hx_one : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx_one
  have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos hx_pos
  have habs_le : |x₀| ≤ x := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hgamma_le : (γ : ℝ) ≤ x := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have habs_sub : |x - x₀| ≤ (2 : ℝ) * x := by
    have htriangle : |x - x₀| ≤ x + |x₀| := by
      calc
        |x - x₀| ≤ |x| + |-x₀| := by
          simpa [sub_eq_add_neg] using abs_add_le x (-x₀)
        _ = x + |x₀| := by simp [abs_of_nonneg hx_pos.le]
    nlinarith
  have hsq_sub : (x - x₀) ^ 2 ≤ (4 : ℝ) * x ^ 2 := by
    have hsq :
        (x - x₀) ^ 2 ≤ (((2 : ℝ) * x) ^ 2) := by
      have hright_nonneg : 0 ≤ (2 : ℝ) * x := by positivity
      have habs_sub' : |x - x₀| ≤ |(2 : ℝ) * x| := by
        simpa [abs_of_nonneg hright_nonneg] using habs_sub
      exact sq_le_sq.mpr habs_sub'
    nlinarith [hsq]
  have hsq_gamma : (γ : ℝ) ^ 2 ≤ x ^ 2 := by
    nlinarith
  have hdenom_le : (x - x₀) ^ 2 + (γ : ℝ) ^ 2 ≤ 5 * x ^ 2 := by
    nlinarith [hsq_sub, hsq_gamma]
  have hdenom_mul :
      Real.pi * ((x - x₀) ^ 2 + (γ : ℝ) ^ 2) ≤ (5 * Real.pi) * x ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hdenom_le Real.pi_pos.le
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hgamma_ne : (γ : ℝ) ≠ 0 := by
    exact_mod_cast hγ
  have hpi_denom_pos : 0 < Real.pi * ((x - x₀) ^ 2 + (γ : ℝ) ^ 2) := by
    have hgamma_sq_pos : 0 < (γ : ℝ) ^ 2 := sq_pos_of_ne_zero hgamma_ne
    exact mul_pos Real.pi_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) hgamma_sq_pos)
  have hinv :
      1 / ((5 * Real.pi) * x ^ 2) ≤
        1 / (Real.pi * ((x - x₀) ^ 2 + (γ : ℝ) ^ 2)) := by
    refine one_div_le_one_div_of_le hpi_denom_pos hdenom_mul
  have hmul :
      (γ : ℝ) * (1 / ((5 * Real.pi) * x ^ 2)) ≤
        (γ : ℝ) * (1 / (Real.pi * ((x - x₀) ^ 2 + (γ : ℝ) ^ 2))) := by
    have hgamma_nonneg : 0 ≤ (γ : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hinv hgamma_nonneg
  have hx_sq_ne : x ^ 2 ≠ 0 := by positivity
  have hleft :
      ((γ : ℝ) / (5 * Real.pi)) / x ^ 2 = (γ : ℝ) * (1 / ((5 * Real.pi) * x ^ 2)) := by
    field_simp [hx_sq_ne, Real.pi_ne_zero]
  have hright :
      (γ : ℝ) * (1 / (Real.pi * ((x - x₀) ^ 2 + (γ : ℝ) ^ 2))) =
        cauchyPDFReal x₀ γ x := by
    rw [cauchyPDFReal_def]
    field_simp [Real.pi_ne_zero, hpi_denom_pos.ne']
  have hresult : ((γ : ℝ) / (5 * Real.pi)) / x ^ 2 ≤ cauchyPDFReal x₀ γ x := by
    rw [hleft, ← hright]
    exact hmul
  simpa using hresult

/-- Helper for Exercise 23.2.5: the same `x⁻²` lower bound holds on a far left tail. -/
lemma cauchyPDFReal_lower_left_tail
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧
      ∀ x ≤ -R, ((γ : ℝ) / (5 * Real.pi)) / x ^ 2 ≤ cauchyPDFReal x₀ γ x := by
  rcases cauchyPDFReal_lower_right_tail (-x₀) hγ with ⟨R, hR_pos, hR⟩
  refine ⟨R, hR_pos, ?_⟩
  intro x hx
  -- Proof comment: reflect the right-tail estimate for center `-x₀` through `x ↦ -x`.
  have hnegx_ge : R ≤ -x := by linarith
  simpa [cauchyPDFReal_neg_center_neg] using hR (-x) hnegx_ge

/-- Helper for Exercise 23.2.5: on a sufficiently far right tail, a positive exponential divided
by `x²` dominates `x⁻¹`. -/
lemma eventually_inv_le_const_mul_exp_div_sq {a C : ℝ} (ha : 0 < a) (hC : 0 < C) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x ≥ R, x⁻¹ ≤ C * Real.exp (a * x) / x ^ (2 : ℕ) := by
  rcases
      eventually_atTop.1
        ((tendsto_exp_mul_div_rpow_atTop 1 a ha).eventually_ge_atTop (1 / C)) with
    ⟨R, hR⟩
  refine ⟨max R 1, le_max_right _ _, ?_⟩
  intro x hx
  have hxR : R ≤ x := le_trans (le_max_left _ _) hx
  have hx_one : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx_one
  have htail : 1 / C ≤ Real.exp (a * x) / x := by
    simpa [Real.rpow_natCast] using hR x hxR
  have hmul_div : (1 / C) * x ≤ Real.exp (a * x) := by
    exact (le_div_iff₀ hx_pos).1 htail
  have hx_le : x ≤ C * Real.exp (a * x) := by
    have hmul := mul_le_mul_of_nonneg_left hmul_div hC.le
    calc
      x = C * ((1 / C) * x) := by field_simp [hC.ne']
      _ ≤ C * Real.exp (a * x) := hmul
  have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos hx_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  refine (le_div_iff₀ hx_sq_pos).2 ?_
  calc
    x⁻¹ * x ^ 2 = x := by field_simp [hx_ne]
    _ ≤ C * Real.exp (a * x) := hx_le

/-- Helper for Exercise 23.2.5: membership in `integrableExpSet` for a nondegenerate Cauchy law
rewrites to Lebesgue integrability against the explicit real Cauchy density. -/
lemma integrable_mul_cauchyPDFReal_of_mem_integrableExpSet
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) {t : ℝ}
    (ht_mem : t ∈ integrableExpSet id (cauchyMeasure x₀ γ)) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x) * cauchyPDFReal x₀ γ x) volume := by
  change Integrable (fun x : ℝ ↦ Real.exp (t * x)) (cauchyMeasure x₀ γ) at ht_mem
  rw [cauchyMeasure_of_scale_ne_zero x₀ hγ] at ht_mem
  have hfinite : ∀ᵐ x ∂volume, cauchyPDF x₀ γ x < ⊤ := by
    exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hraw :
      Integrable
        (fun x : ℝ ↦ Real.exp (t * x) * (cauchyPDF x₀ γ x).toReal) volume :=
    (MeasureTheory.integrable_withDensity_iff
      (μ := volume) (f := cauchyPDF x₀ γ) (hf := measurable_cauchyPDF x₀ γ)
      (hflt := hfinite)).1 ht_mem
  have hpdf_toReal :
      (fun x : ℝ ↦ Real.exp (t * x) * (cauchyPDF x₀ γ x).toReal) =
        fun x : ℝ ↦ Real.exp (t * x) * cauchyPDFReal x₀ γ x := by
    funext x
    rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos x₀ hγ x).le]
  exact hpdf_toReal ▸ hraw

/-- Helper for Exercise 23.2.5: Lebesgue integrability against the explicit real Cauchy density
puts the corresponding tilt back into `integrableExpSet`. -/
lemma mem_integrableExpSet_of_integrable_mul_cauchyPDFReal
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) {t : ℝ}
    (hInt : Integrable (fun x : ℝ ↦ Real.exp (t * x) * cauchyPDFReal x₀ γ x) volume) :
    t ∈ integrableExpSet id (cauchyMeasure x₀ γ) := by
  change Integrable (fun x : ℝ ↦ Real.exp (t * x)) (cauchyMeasure x₀ γ)
  rw [cauchyMeasure_of_scale_ne_zero x₀ hγ]
  have hfinite : ∀ᵐ x ∂volume, cauchyPDF x₀ γ x < ⊤ := by
    exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hpdf_toReal :
      (fun x : ℝ ↦ Real.exp (t * x) * (cauchyPDF x₀ γ x).toReal) =
        fun x : ℝ ↦ Real.exp (t * x) * cauchyPDFReal x₀ γ x := by
    funext x
    rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos x₀ hγ x).le]
  have hraw :
      Integrable
        (fun x : ℝ ↦ Real.exp (t * x) * (cauchyPDF x₀ γ x).toReal) volume := by
    exact hpdf_toReal.symm ▸ hInt
  exact
    (MeasureTheory.integrable_withDensity_iff
      (μ := volume) (f := cauchyPDF x₀ γ) (hf := measurable_cauchyPDF x₀ γ)
      (hflt := hfinite)).2 hraw

/-- Helper for Exercise 23.2.5: on a sufficiently far right tail, the positive tilted Cauchy
density dominates `|x⁻¹|`. -/
lemma eventually_norm_inv_le_norm_exp_mul_cauchyPDFReal_right_tail
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∃ R : ℝ, ∀ x ≥ R, ‖x⁻¹‖ ≤ ‖Real.exp (t * x) * cauchyPDFReal x₀ γ x‖ := by
  have hgamma_pos : 0 < (γ : ℝ) := by
    exact_mod_cast (show 0 < γ from pos_iff_ne_zero.mpr hγ)
  have hconst_pos : 0 < (γ : ℝ) / (5 * Real.pi) := by
    have hpi_pos : 0 < 5 * Real.pi := by positivity
    exact div_pos hgamma_pos hpi_pos
  rcases cauchyPDFReal_lower_right_tail x₀ hγ with ⟨R₁, _, hR₁⟩
  rcases eventually_inv_le_const_mul_exp_div_sq ht hconst_pos with ⟨R₂, hR₂_one, hR₂⟩
  refine ⟨max R₁ R₂, ?_⟩
  intro x hx
  have hxR₁ : R₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxR₂ : R₂ ≤ x := le_trans (le_max_right _ _) hx
  have hx_one : 1 ≤ x := le_trans hR₂_one hxR₂
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx_one
  have hinv_lower : x⁻¹ ≤ ((γ : ℝ) / (5 * Real.pi)) * Real.exp (t * x) / x ^ (2 : ℕ) :=
    hR₂ x hxR₂
  have hpdf_lower :
      ((γ : ℝ) / (5 * Real.pi)) / x ^ 2 ≤ cauchyPDFReal x₀ γ x := hR₁ x hxR₁
  have hexp_nonneg : 0 ≤ Real.exp (t * x) := by positivity
  have hscaled :
      ((γ : ℝ) / (5 * Real.pi)) * Real.exp (t * x) / x ^ 2 ≤
        Real.exp (t * x) * cauchyPDFReal x₀ γ x := by
    have hmul_pdf := mul_le_mul_of_nonneg_left hpdf_lower hexp_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul_pdf
  have hpoint : x⁻¹ ≤ Real.exp (t * x) * cauchyPDFReal x₀ γ x :=
    le_trans hinv_lower hscaled
  have hpdf_nonneg : 0 ≤ cauchyPDFReal x₀ γ x := (cauchyPDF_pos x₀ hγ x).le
  have hright_nonneg : 0 ≤ Real.exp (t * x) * cauchyPDFReal x₀ γ x := by
    exact mul_nonneg hexp_nonneg hpdf_nonneg
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx_pos.le, abs_of_nonneg hexp_nonneg,
    abs_of_nonneg hpdf_nonneg, abs_of_nonneg hright_nonneg] using hpoint

/-- Helper for Exercise 23.2.5: a positive tilt of a nondegenerate Cauchy law is not
exponentially integrable. -/
lemma cauchyMeasure_not_mem_integrableExpSet_of_pos
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) {t : ℝ} (ht : 0 < t) :
    t ∉ integrableExpSet id (cauchyMeasure x₀ γ) := by
  intro ht_mem
  have hInt :
      Integrable (fun x : ℝ ↦ Real.exp (t * x) * cauchyPDFReal x₀ γ x) volume := by
    exact integrable_mul_cauchyPDFReal_of_mem_integrableExpSet x₀ hγ ht_mem
  rcases eventually_norm_inv_le_norm_exp_mul_cauchyPDFReal_right_tail x₀ hγ ht with ⟨R, hR⟩
  have hTail : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Set.Ioi R) volume := by
    -- Proof comment: on the right tail, the tilted Cauchy density dominates `x ↦ x⁻¹`.
    change Integrable (fun x : ℝ ↦ x⁻¹) (volume.restrict (Set.Ioi R))
    refine Integrable.mono' (hInt.restrict) ?_ ?_
    · exact measurable_inv.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hexp_nonneg : 0 ≤ Real.exp (t * x) := by positivity
      have hpdf_nonneg : 0 ≤ cauchyPDFReal x₀ γ x := (cauchyPDF_pos x₀ hγ x).le
      have hright_nonneg : 0 ≤ Real.exp (t * x) * cauchyPDFReal x₀ γ x := by
        exact mul_nonneg hexp_nonneg hpdf_nonneg
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hexp_nonneg, abs_of_nonneg hpdf_nonneg,
        abs_of_nonneg hright_nonneg] using hR x hx.le
  exact not_integrableOn_Ioi_inv (a := R) hTail

/-- Helper for Exercise 23.2.5: a negative tilt of a nondegenerate Cauchy law is not
exponentially integrable. -/
lemma cauchyMeasure_not_mem_integrableExpSet_of_neg
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) {t : ℝ} (ht : t < 0) :
    t ∉ integrableExpSet id (cauchyMeasure x₀ γ) := by
  intro ht_mem
  have hInt :
      Integrable (fun x : ℝ ↦ Real.exp (t * x) * cauchyPDFReal x₀ γ x) volume := by
    exact integrable_mul_cauchyPDFReal_of_mem_integrableExpSet x₀ hγ ht_mem
  have hReflected :
      Integrable (fun x : ℝ ↦ Real.exp ((-t) * x) * cauchyPDFReal (-x₀) γ x) volume := by
    -- Proof comment: compose the weighted density with `x ↦ -x` and simplify the Cauchy center.
    have hComp :
        Integrable (fun x : ℝ ↦ cauchyPDFReal x₀ γ (-x) * Real.exp (-(t * x))) volume := by
      simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using hInt.comp_neg
    have hComp' :
        Integrable (fun x : ℝ ↦ cauchyPDFReal (-x₀) γ x * Real.exp (-(t * x))) volume := by
      refine hComp.congr ?_
      filter_upwards with x
      simpa using (cauchyPDFReal_neg_center_neg (-x₀) γ x)
    simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using hComp'
  have hmem_neg : -t ∈ integrableExpSet id (cauchyMeasure (-x₀) γ) := by
    exact mem_integrableExpSet_of_integrable_mul_cauchyPDFReal (-x₀) hγ hReflected
  have hneg_pos : 0 < -t := by
    linarith
  exact cauchyMeasure_not_mem_integrableExpSet_of_pos (-x₀) hγ hneg_pos hmem_neg

/-- Helper for Exercise 23.2.5: the exponential-integrability domain of a nondegenerate Cauchy law
is exactly `{0}`. -/
lemma cauchyMeasure_integrableExpSet_eq_singleton_zero
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) :
    integrableExpSet id (cauchyMeasure x₀ γ) = ({0} : Set ℝ) := by
  ext t
  constructor
  · intro ht
    -- Proof comment: every nonzero tilt is excluded by one of the two sign-specific obstructions.
    by_cases hzero : t = 0
    · simp [hzero]
    · rcases lt_or_gt_of_ne hzero with ht_neg | ht_pos
      · exact False.elim (cauchyMeasure_not_mem_integrableExpSet_of_neg x₀ hγ ht_neg ht)
      · exact False.elim (cauchyMeasure_not_mem_integrableExpSet_of_pos x₀ hγ ht_pos ht)
  · intro ht
    -- Proof comment: at `t = 0`, the exponential weight is the constant function `1`.
    rcases Set.mem_singleton_iff.mp ht with rfl
    simp [integrableExpSet]

/-- Helper for Exercise 23.2.5: once the exponential-integrability domain is `{0}`, the same
singleton-domain Legendre-Fenchel argument from Chapter 23 shows that the rate function is
identically zero. -/
lemma legendreFenchelRateFunction_eq_zero_of_integrableExpSet_eq_singleton_zero
    (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℝ → ℝ)
    (hSet : integrableExpSet X P = ({0} : Set ℝ)) :
    ∀ x : ℝ, legendreFenchelRateFunction (Λ(X; P)) x = 0 := by
  intro x
  refine le_antisymm ?_ ?_
  · rw [legendreFenchelRateFunction]
    refine sSup_le ?_
    rintro _ ⟨t, rfl⟩
    change (((t * x : ℝ) : EReal) - Λ(X; P) t) ≤ 0
    by_cases ht : t = 0
    · -- Proof comment: the distinguished `t = 0` summand is exactly `0`.
      rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet (X := X) (P := P)]
      · simp [ht]
      · simp [hSet, ht]
    · -- Proof comment: every nonzero tilt leaves the effective domain, so the summand is `⊥`.
      rw [extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet (X := X) (P := P)]
      · simp
      · simp [hSet, ht]
  · rw [legendreFenchelRateFunction]
    -- Proof comment: the `t = 0` summand belongs to the defining range and equals `0`.
    let f : ℝ → EReal := fun t ↦ ((t * x : ℝ) : EReal) - Λ(X; P) t
    have hmem : f 0 ∈ Set.range f := ⟨0, rfl⟩
    have hzero : f 0 = 0 := by
      change (((0 * x : ℝ) : EReal) - Λ(X; P) 0) = 0
      rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet (X := X) (P := P)]
      · simp
      · simp [hSet]
    have hle : f 0 ≤ sSup (Set.range f) := le_sSup hmem
    rw [hzero] at hle
    simpa using hle

/-- At the origin, the chapter's extended logarithmic moment-generating function of a Cauchy law
equals `0`. -/
theorem cauchyMeasure_extendedLogMomentGeneratingFunction_zero
    (x₀ : ℝ) (γ : NNReal) :
    Λ(id; cauchyMeasure x₀ γ) 0 = 0 := by
  -- Proof comment: at `t = 0`, the exponential tilt is the constant function `1`, so `Λ`
  -- agrees with the normalized cumulant-generating function.
  rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
    (X := id) (P := cauchyMeasure x₀ γ)]
  · simp
  · simp [integrableExpSet]

-- Proof sketch: for every nonzero `t`, one of the tails of `exp (t x)` against a nondegenerate
-- Cauchy density is nonintegrable, so the chapter's extended logarithmic moment-generating
-- function takes the value `⊤`.
/-- Away from the origin, the chapter's extended logarithmic moment-generating function of a
nondegenerate Cauchy law equals `⊤`. -/
theorem cauchyMeasure_extendedLogMomentGeneratingFunction_eq_top
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    Λ(id; cauchyMeasure x₀ γ) t = ⊤ := by
  -- Proof comment: a nonzero tilt is either positive or negative, and each branch is ruled out
  -- by the corresponding Cauchy-tail nonintegrability lemma.
  rw [extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
    (X := id) (P := cauchyMeasure x₀ γ)]
  rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
  · exact cauchyMeasure_not_mem_integrableExpSet_of_neg x₀ hγ ht_neg
  · exact cauchyMeasure_not_mem_integrableExpSet_of_pos x₀ hγ ht_pos

-- Proof sketch: after substituting the explicit Cauchy formula for `Λ`, every term with `t ≠ 0`
-- becomes `-∞`, while the term `t = 0` contributes `0`; hence the supremum defining the
-- Legendre-Fenchel transform is `0` for every `x`.
/-- Exercise 23.2.5: for a nondegenerate Cauchy law, the chapter's extended logarithmic
moment-generating function is `Λ(0) = 0` and `Λ(t) = ⊤` for `t ≠ 0`, so its Legendre-Fenchel
transform is the trivial rate function `Λ*(x) = 0` for every `x`. This means that Theorem 23.11
yields only the degenerate large-deviation picture with zero exponential rate in the Cauchy
case. -/
theorem cauchyMeasure_legendreFenchelRateFunction_eq_zero
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) (x : ℝ) :
    legendreFenchelRateFunction (Λ(id; cauchyMeasure x₀ γ)) x = 0 := by
  -- Proof comment: once the effective domain is known to be `{0}`, the general singleton-domain
  -- Legendre-Fenchel argument applies verbatim.
  exact
    legendreFenchelRateFunction_eq_zero_of_integrableExpSet_eq_singleton_zero
      (P := cauchyMeasure x₀ γ) (X := id)
      (cauchyMeasure_integrableExpSet_eq_singleton_zero x₀ hγ) x

end ProbabilityTheory
