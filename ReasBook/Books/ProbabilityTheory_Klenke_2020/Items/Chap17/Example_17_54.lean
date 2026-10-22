/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- Helper for Example 17.54: monotonicity forces
`(f x - f y) * (g x - g y)` to be nonnegative. -/
lemma sub_mul_sub_nonneg_of_monotone {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g)
    (x y : ℝ) : 0 ≤ (f x - f y) * (g x - g y) := by
  -- Compare `x` and `y`; monotonicity gives the same sign for both differences.
  rcases le_total x y with hxy | hyx
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hxy)) (sub_nonpos.mpr (hg hxy))
  · exact mul_nonneg (sub_nonneg.mpr (hf hyx)) (sub_nonneg.mpr (hg hyx))

/-- Helper for Example 17.54: the covariance of the difference functions on `μ.prod μ`
collapses to twice the original covariance. -/
lemma covariance_prod_difference_eq_two_mul_covariance {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f g : ℝ → ℝ} (hf_sq : MemLp f 2 μ) (hg_sq : MemLp g 2 μ) :
    cov[fun p : ℝ × ℝ ↦ f p.1 - f p.2, fun p : ℝ × ℝ ↦ g p.1 - g p.2; μ.prod μ] =
      2 * cov[f, g; μ] := by
  have hsub_f : (fun p : ℝ × ℝ ↦ f p.1 - f p.2) = (fun p ↦ f p.1) - fun p ↦ f p.2 := by
    funext p
    rfl
  have hsub_g : (fun p : ℝ × ℝ ↦ g p.1 - g p.2) = (fun p ↦ g p.1) - fun p ↦ g p.2 := by
    funext p
    rfl
  have hf_fst : MemLp (fun p : ℝ × ℝ ↦ f p.1) 2 (μ.prod μ) := hf_sq.comp_fst μ
  have hf_snd : MemLp (fun p : ℝ × ℝ ↦ f p.2) 2 (μ.prod μ) := hf_sq.comp_snd μ
  have hg_fst : MemLp (fun p : ℝ × ℝ ↦ g p.1) 2 (μ.prod μ) := hg_sq.comp_fst μ
  have hg_snd : MemLp (fun p : ℝ × ℝ ↦ g p.2) 2 (μ.prod μ) := hg_sq.comp_snd μ
  have hfst : HasLaw (fun p : ℝ × ℝ ↦ p.1) μ (μ.prod μ) :=
    ⟨measurable_fst.aemeasurable, by
      simpa using (measurePreserving_fst (μ := μ) (ν := μ)).map_eq⟩
  have hsnd : HasLaw (fun p : ℝ × ℝ ↦ p.2) μ (μ.prod μ) :=
    ⟨measurable_snd.aemeasurable, by
      simpa using (measurePreserving_snd (μ := μ) (ν := μ)).map_eq⟩
  have hdiag_fst :
      cov[fun p : ℝ × ℝ ↦ f p.1, fun p : ℝ × ℝ ↦ g p.1; μ.prod μ] = cov[f, g; μ] := by
    -- The first projection has law `μ`, so covariance transports directly.
    simpa [Function.comp_apply] using
      hfst.covariance_fun_comp hf_sq.aemeasurable hg_sq.aemeasurable
  have hdiag_snd :
      cov[fun p : ℝ × ℝ ↦ f p.2, fun p : ℝ × ℝ ↦ g p.2; μ.prod μ] = cov[f, g; μ] := by
    -- The second projection has the same law `μ`.
    simpa [Function.comp_apply] using
      hsnd.covariance_fun_comp hf_sq.aemeasurable hg_sq.aemeasurable
  have hmixed_fst_snd :
      cov[fun p : ℝ × ℝ ↦ f p.1, fun p : ℝ × ℝ ↦ g p.2; μ.prod μ] = 0 :=
    covariance_fst_snd_prod hf_sq hg_sq
  have hmixed_snd_fst :
      cov[fun p : ℝ × ℝ ↦ f p.2, fun p : ℝ × ℝ ↦ g p.1; μ.prod μ] = 0 := by
    -- Commute the covariance and reuse the standard product-independence lemma.
    rw [covariance_comm]
    simpa using (covariance_fst_snd_prod hg_sq hf_sq : _)
  -- Expand the covariance bilinearly and rewrite the four pieces.
  rw [hsub_f, hsub_g]
  rw [covariance_sub_left hf_fst hf_snd (hg_fst.sub hg_snd)]
  rw [covariance_sub_right hf_fst hg_fst hg_snd]
  rw [covariance_sub_right hf_snd hg_fst hg_snd]
  rw [hdiag_fst, hmixed_fst_snd, hmixed_snd_fst, hdiag_snd]
  ring

/-- The covariance of two monotone increasing real functions under a probability law on `ℝ`
is nonnegative when both functions have finite second moment. -/
-- Proof sketch: take two independent random variables with law `μ`, observe that
-- `(f x - f y) * (g x - g y) ≥ 0` by monotonicity, integrate this nonnegative quantity over the
-- product law, and rewrite the result as `2 * cov[f, g; μ]`.
theorem covariance_nonneg_of_monotone {μ : Measure ℝ} [IsProbabilityMeasure μ] {f g : ℝ → ℝ}
    (hf : Monotone f) (hg : Monotone g) (hf_sq : MemLp f 2 μ) (hg_sq : MemLp g 2 μ) :
    0 ≤ cov[f, g; μ] := by
  have hsub_f : (fun p : ℝ × ℝ ↦ f p.1 - f p.2) = (fun p ↦ f p.1) - fun p ↦ f p.2 := by
    funext p
    rfl
  have hsub_g : (fun p : ℝ × ℝ ↦ g p.1 - g p.2) = (fun p ↦ g p.1) - fun p ↦ g p.2 := by
    funext p
    rfl
  have hfst : HasLaw (fun p : ℝ × ℝ ↦ p.1) μ (μ.prod μ) :=
    ⟨measurable_fst.aemeasurable, by
      simpa using (measurePreserving_fst (μ := μ) (ν := μ)).map_eq⟩
  have hsnd : HasLaw (fun p : ℝ × ℝ ↦ p.2) μ (μ.prod μ) :=
    ⟨measurable_snd.aemeasurable, by
      simpa using (measurePreserving_snd (μ := μ) (ν := μ)).map_eq⟩
  have hF_mem : MemLp (fun p : ℝ × ℝ ↦ f p.1 - f p.2) 2 (μ.prod μ) :=
    hf_sq.comp_fst μ |>.sub (hf_sq.comp_snd μ)
  have hG_mem : MemLp (fun p : ℝ × ℝ ↦ g p.1 - g p.2) 2 (μ.prod μ) :=
    hg_sq.comp_fst μ |>.sub (hg_sq.comp_snd μ)
  have hfst_integral_f : ∫ p, f p.1 ∂μ.prod μ = ∫ x, f x ∂μ := by
    simpa [Function.comp_apply] using hfst.integral_comp hf_sq.aestronglyMeasurable
  have hsnd_integral_f : ∫ p, f p.2 ∂μ.prod μ = ∫ x, f x ∂μ := by
    simpa [Function.comp_apply] using hsnd.integral_comp hf_sq.aestronglyMeasurable
  have hfst_integral_g : ∫ p, g p.1 ∂μ.prod μ = ∫ x, g x ∂μ := by
    simpa [Function.comp_apply] using hfst.integral_comp hg_sq.aestronglyMeasurable
  have hsnd_integral_g : ∫ p, g p.2 ∂μ.prod μ = ∫ x, g x ∂μ := by
    simpa [Function.comp_apply] using hsnd.integral_comp hg_sq.aestronglyMeasurable
  have hF_mean_zero : (μ.prod μ)[fun p : ℝ × ℝ ↦ f p.1 - f p.2] = 0 := by
    have h_integral_sub :
        ∫ p, ((fun p : ℝ × ℝ ↦ f p.1) - fun p : ℝ × ℝ ↦ f p.2) p ∂μ.prod μ =
          ∫ p, f p.1 ∂μ.prod μ - ∫ p, f p.2 ∂μ.prod μ := by
      simpa using
        (integral_sub (f := fun p : ℝ × ℝ ↦ f p.1) (g := fun p : ℝ × ℝ ↦ f p.2)
          ((hf_sq.comp_fst μ).integrable (by norm_num))
          ((hf_sq.comp_snd μ).integrable (by norm_num)))
    -- Both coordinates have law `μ`, so the two expectations cancel.
    rw [hsub_f, h_integral_sub]
    rw [hfst_integral_f, hsnd_integral_f]
    simp
  have hG_mean_zero : (μ.prod μ)[fun p : ℝ × ℝ ↦ g p.1 - g p.2] = 0 := by
    have h_integral_sub :
        ∫ p, ((fun p : ℝ × ℝ ↦ g p.1) - fun p : ℝ × ℝ ↦ g p.2) p ∂μ.prod μ =
          ∫ p, g p.1 ∂μ.prod μ - ∫ p, g p.2 ∂μ.prod μ := by
      simpa using
        (integral_sub (f := fun p : ℝ × ℝ ↦ g p.1) (g := fun p : ℝ × ℝ ↦ g p.2)
          ((hg_sq.comp_fst μ).integrable (by norm_num))
          ((hg_sq.comp_snd μ).integrable (by norm_num)))
    -- The same cancellation argument works for `g`.
    rw [hsub_g, h_integral_sub]
    rw [hfst_integral_g, hsnd_integral_g]
    simp
  have hcov_nonneg :
      0 ≤ cov[fun p : ℝ × ℝ ↦ f p.1 - f p.2, fun p : ℝ × ℝ ↦ g p.1 - g p.2; μ.prod μ] := by
    -- Once the means vanish, covariance is just the integral of the pointwise nonnegative product.
    rw [covariance_eq_sub hF_mem hG_mem, hF_mean_zero, hG_mean_zero, zero_mul, sub_zero]
    refine integral_nonneg_of_ae ?_
    filter_upwards with p
    simpa using sub_mul_sub_nonneg_of_monotone hf hg p.1 p.2
  -- Rewrite the product-law covariance as `2 * cov[f, g; μ]` and divide by the positive scalar `2`.
  rw [covariance_prod_difference_eq_two_mul_covariance hf_sq hg_sq] at hcov_nonneg
  linarith

namespace HasLaw

/-- Transport `covariance_nonneg_of_monotone` along the law of a real random variable. -/
-- Proof sketch: use `ProbabilityTheory.covariance_nonneg_of_monotone` on the law `ν` of `X`,
-- then rewrite the covariance on `Ω` by `HasLaw.covariance_fun_comp`.
theorem covariance_nonneg_of_monotone_comp {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ν : Measure ℝ} {X : Ω → ℝ} (hX : HasLaw X ν μ)
    {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) (hf_sq : MemLp f 2 ν)
    (hg_sq : MemLp g 2 ν) :
    0 ≤ cov[fun ω ↦ f (X ω), fun ω ↦ g (X ω); μ] := by
  letI : IsProbabilityMeasure ν := hX.isProbabilityMeasure_iff.mp inferInstance
  have hcov : 0 ≤ cov[f, g; ν] := ProbabilityTheory.covariance_nonneg_of_monotone hf hg hf_sq hg_sq
  -- Transport the covariance statement from the law `ν` back to the ambient space `Ω`.
  simpa [hX.covariance_fun_comp hf.measurable.aemeasurable hg.measurable.aemeasurable,
    Function.comp_apply] using hcov

end HasLaw

/-- Example 17.54: if `X` is a real random variable and `f`, `g : ℝ → ℝ` are monotone increasing
with finite second moments, then `f(X)` and `g(X)` are nonnegatively correlated. -/
-- Proof sketch: package `X` as the canonical law statement `HasLaw X (Measure.map X μ) μ`, turn
-- the `MemLp` hypotheses on `f ∘ X` and `g ∘ X` into `MemLp` hypotheses on the pushforward law,
-- and apply `HasLaw.covariance_nonneg_of_monotone_comp`.
theorem monotone_comp_covariance_nonneg {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {f g : ℝ → ℝ} (hX : AEMeasurable X μ)
    (hf : Monotone f) (hg : Monotone g) (hf_sq : MemLp (fun ω ↦ f (X ω)) 2 μ)
    (hg_sq : MemLp (fun ω ↦ g (X ω)) 2 μ) :
    0 ≤ cov[fun ω ↦ f (X ω), fun ω ↦ g (X ω); μ] := by
  have hLaw : HasLaw X (Measure.map X μ) μ := ⟨hX, rfl⟩
  letI : IsProbabilityMeasure (Measure.map X μ) := hLaw.isProbabilityMeasure_iff.mp inferInstance
  have hf_map : MemLp f 2 (Measure.map X μ) := by
    -- Turn the second-moment hypothesis on `f ∘ X` into a law-level `MemLp` statement.
    rw [memLp_map_measure_iff hf.measurable.aestronglyMeasurable hX]
    simpa [Function.comp_apply] using hf_sq
  have hg_map : MemLp g 2 (Measure.map X μ) := by
    -- The same transport applies to `g`.
    rw [memLp_map_measure_iff hg.measurable.aestronglyMeasurable hX]
    simpa [Function.comp_apply] using hg_sq
  -- Apply the law-transport theorem to the canonical pushforward law of `X`.
  exact hLaw.covariance_nonneg_of_monotone_comp hf hg hf_map hg_map

end ProbabilityTheory
