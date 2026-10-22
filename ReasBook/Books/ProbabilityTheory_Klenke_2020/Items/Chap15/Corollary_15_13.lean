/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Example_3_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_12

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped NNReal

/- Corollary 15.13 (1): Item (i). The Gaussian convolution identity is the mathlib owner theorem
`gaussianReal_conv_gaussianReal`; the source's positivity assumptions on the variances are
redundant for the statement. -/
recall gaussianReal_conv_gaussianReal

/-- Corollary 15.13 (2): Item (ii). For common rate `θ > 0` and shapes `r`, `s > 0`, the
convolution of the Gamma laws `Γ_{θ,r}` and `Γ_{θ,s}` is `Γ_{θ,r+s}`. -/
-- Proof sketch: multiply the characteristic functions from the Gamma formula in Theorem 15.12 and
-- identify the resulting transform with that of `gammaMeasure (r + s) θ`.
theorem gammaMeasure_conv_same_rate
    (θ r s : ℝ) (hθ : 0 < θ) (hr : 0 < r) (hs : 0 < s) :
    gammaMeasure r θ ∗ gammaMeasure s θ = gammaMeasure (r + s) θ := by
  letI : IsProbabilityMeasure (gammaMeasure r θ) := isProbabilityMeasure_gammaMeasure hr hθ
  letI : IsProbabilityMeasure (gammaMeasure s θ) := isProbabilityMeasure_gammaMeasure hs hθ
  letI : IsProbabilityMeasure (gammaMeasure (r + s) θ) :=
    isProbabilityMeasure_gammaMeasure (add_pos hr hs) hθ
  letI : IsFiniteMeasure (gammaMeasure r θ ∗ gammaMeasure s θ) := by infer_instance
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_conv, charFun_gammaMeasure r θ hr hθ, charFun_gammaMeasure s θ hs hθ,
    charFun_gammaMeasure (r + s) θ (add_pos hr hs) hθ]
  have hz : (1 - (t / θ) * Complex.I : ℂ) ≠ 0 := by
    intro h
    have : ((1 - (t / θ) * Complex.I : ℂ)).re = 0 := by simp [h]
    norm_num at this
  rw [← Complex.cpow_add _ _ hz]
  simp [add_comm]

/-- Corollary 15.13 (3): Item (iii). The centered Cauchy laws are stable under convolution, with
scale parameter adding under convolution. -/
-- Proof sketch: use the explicit characteristic function of the centered Cauchy law for positive
-- scales, derive the zero-scale case from the canonical owner lemma
-- `ProbabilityTheory.cauchyMeasure_zero_scale`, and recognize the resulting transform as that of
-- `cauchyMeasure 0 (a + b)`.
theorem cauchyMeasure_conv_centered (a b : ℝ≥0) :
    cauchyMeasure 0 a ∗ cauchyMeasure 0 b = cauchyMeasure 0 (a + b) := by
  letI : IsFiniteMeasure (cauchyMeasure 0 a ∗ cauchyMeasure 0 b) := by infer_instance
  refine Measure.ext_of_charFun ?_
  ext t
  have hchar (γ : ℝ≥0) :
      charFun (cauchyMeasure 0 γ) t = Complex.exp (-((γ : ℝ)) * |t|) := by
    by_cases hγ : γ = 0
    · subst hγ
      simp [cauchyMeasure_zero_scale]
    · have hγ' : 0 < (γ : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hγ)
      simpa [Real.toNNReal_of_nonneg γ.2] using
        charFun_centeredCauchyMeasure (γ : ℝ) hγ' t
  rw [charFun_conv, hchar a, hchar b, hchar (a + b), ← Complex.exp_add]
  congr 1
  simp [NNReal.coe_add, add_comm, add_mul]

/- Corollary 15.13 (4): Item (iv). The common-success-parameter binomial convolution identity is
already formalized upstream as `example_3_4_binomial_conv`. -/
recall example_3_4_binomial_conv

/- Corollary 15.13 (5): Item (v). The common-success-parameter negative-binomial convolution
identity is already formalized upstream as `negativeBinomialMeasure_conv`. -/
recall negativeBinomialMeasure_conv

/- Corollary 15.13 (6): Item (vi). The Poisson convolution identity is already formalized
upstream as `poissonMeasure_conv_poissonMeasure`. -/
recall poissonMeasure_conv_poissonMeasure
