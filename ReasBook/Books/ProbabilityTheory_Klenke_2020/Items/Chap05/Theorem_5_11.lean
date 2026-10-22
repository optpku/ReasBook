/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: apply Markov's inequality to the nonnegative random variable
-- `ω ↦ (f ‖X ω‖₊ : ℝ≥0∞)`, use monotonicity of `f` to bound it below by `f ε` on the event
-- `{ω | ε ≤ ‖X ω‖₊}`, and divide by the positive constant `f ε`.
/-- Theorem 5.11 (1): Markov's inequality for a monotone nonnegative transform of `|X|`, written
with the nonnegative Lebesgue integral of `f ∘ |X|`. -/
theorem markov_inequality_of_monotone
    (μ : Measure Ω) (X : Ω → ℝ) (f : ℝ≥0 → ℝ≥0) (ε : ℝ≥0)
    (hX : Measurable X) (hf : Monotone f) (hfε : 0 < f ε) :
    μ {ω | ε ≤ ‖X ω‖₊} ≤ (∫⁻ ω, (f ‖X ω‖₊ : ℝ≥0∞) ∂μ) / f ε := by
  refine (measure_mono fun ω hω ↦ hf hω).trans ?_
  have h_markov :
      μ {ω | (f ε : ℝ≥0∞) ≤ ((f ‖X ω‖₊ : ℝ≥0) : ℝ≥0∞)} ≤
        (∫⁻ ω, ((f ‖X ω‖₊ : ℝ≥0) : ℝ≥0∞) ∂μ) / (f ε : ℝ≥0∞) :=
    meas_ge_le_lintegral_div
      (((hf.measurable.comp hX.nnnorm).coe_nnreal_ennreal).aemeasurable)
      (by exact_mod_cast hfε.ne')
      (by simp)
  simpa using h_markov

-- Proof sketch: specialize the previous Markov inequality to `f x = x ^ 2`; then rewrite
-- `(‖X ω‖₊ : ℝ≥0∞) ^ 2` as `ENNReal.ofReal (X ω ^ 2)`.
/-- Theorem 5.11 (2): For `f(x) = x^2`, the Markov inequality becomes the standard second-moment
bound, written with the nonnegative Lebesgue integral of `X^2`. -/
theorem markov_inequality_sq
    (μ : Measure Ω) (X : Ω → ℝ) (ε : ℝ) (hX : Measurable X) (hε : 0 < ε) :
    μ {ω | ε ≤ |X ω|} ≤
      (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ) / ENNReal.ofReal (ε ^ 2) := by
  have hεNN : 0 < (Real.toNNReal ε : ℝ≥0) := Real.toNNReal_pos.mpr hε
  have hmain :=
    markov_inequality_of_monotone μ X (fun x ↦ x ^ 2) (Real.toNNReal ε) hX
      (fun ⦃a b⦄ hab ↦ pow_le_pow_left₀ a.2 hab 2) (sq_pos_of_pos hεNN)
  calc
    μ {ω | ε ≤ |X ω|} = μ {ω | (Real.toNNReal ε : ℝ≥0) ≤ ‖X ω‖₊} := by
      congr with ω
      rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm, Real.norm_eq_abs]
    _ ≤ (∫⁻ ω, (((‖X ω‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) ∂μ) / (((Real.toNNReal ε : ℝ≥0) ^ 2 : ℝ≥0)) :=
      hmain
    _ = (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ) / ENNReal.ofReal (ε ^ 2) := by
      congr 1
      · congr with ω
        rw [ENNReal.ofReal_eq_coe_nnreal (sq_nonneg (X ω))]
        exact congrArg (fun t : ℝ≥0 ↦ (t : ℝ≥0∞)) <| by
          apply NNReal.coe_inj.mp
          simp [NNReal.coe_pow, sq_abs]
      · rw [ENNReal.ofReal_eq_coe_nnreal (sq_nonneg ε)]
        exact congrArg (fun t : ℝ≥0 ↦ (t : ℝ≥0∞)) <| by
          apply NNReal.coe_inj.mp
          simp [NNReal.coe_pow, Real.toNNReal_of_nonneg hε.le]

/- Theorem 5.11 (3): For a finite measure, Chebyshev's inequality is the canonical theorem
`meas_ge_le_variance_div_sq`, bounding the deviation probability from the mean by
`Var[X; μ] / ε^2`. -/
recall meas_ge_le_variance_div_sq
