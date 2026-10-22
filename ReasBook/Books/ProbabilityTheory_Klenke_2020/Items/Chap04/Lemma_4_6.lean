/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- Canonical monotonicity of the nonnegative integral. -/
recall MeasureTheory.lintegral_mono

-- Proof sketch: this is the textbook measurable version of the canonical theorem
-- `MeasureTheory.lintegral_mono`.
/-- Lemma 4.6 (1): (i) Monotonicity of the nonnegative integral for measurable maps. -/
theorem lintegral_mono_of_measurable
    (μ : Measure Ω) {f g : Ω → ENNReal} (hf : Measurable f) (hg : Measurable g) (hfg : f ≤ g) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, g ω ∂μ := by
  have _ := hf
  have _ := hg
  simpa using lintegral_mono hfg

/- Canonical monotone convergence for nonnegative measurable functions. -/
recall MeasureTheory.lintegral_iSup

-- Proof sketch: rewrite `f` pointwise as the supremum of the increasing sequence `fSeq`, then use
-- the canonical measurable monotone convergence theorem `MeasureTheory.lintegral_iSup`.
/-- Lemma 4.6 (2): (ii) If `f_n` increases pointwise to `f`, then the nonnegative integrals have
supremum `∫ f dμ`. -/
theorem lintegral_monotone_convergence
    (μ : Measure Ω) {f : Ω → ENNReal} {fSeq : ℕ → Ω → ENNReal} (hf : Measurable f)
    (hfSeq : ∀ n, Measurable (fSeq n)) (h_mono : Monotone fSeq)
    (h_sup : ∀ ω, (⨆ n, fSeq n ω) = f ω) :
    (⨆ n, ∫⁻ ω, fSeq n ω ∂μ) = ∫⁻ ω, f ω ∂μ := by
  have _ := hf
  calc
    (⨆ n, ∫⁻ ω, fSeq n ω ∂μ) = ∫⁻ ω, ⨆ n, fSeq n ω ∂μ := by
      simpa using (lintegral_iSup hfSeq h_mono).symm
    _ = ∫⁻ ω, f ω ∂μ := by
      simp [h_sup]

-- Proof sketch: first pull the coefficients `α` and `β` out of the integral using
-- `MeasureTheory.lintegral_const_mul`, then apply additivity with
-- `MeasureTheory.lintegral_add_left` to the measurable functions `ω ↦ α * f ω` and
-- `ω ↦ β * g ω`.
/-- Lemma 4.6 (3): (iii) The nonnegative integral is linear over coefficients `α, β ∈ [0, ∞]`,
with the usual convention `∞ * 0 = 0` built into `ENNReal`. -/
theorem lintegral_add_const_mul
    (μ : Measure Ω) (α β : ENNReal) {f g : Ω → ENNReal} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ ω, α * f ω + β * g ω ∂μ = α * ∫⁻ ω, f ω ∂μ + β * ∫⁻ ω, g ω ∂μ := by
  have hαf : Measurable (fun ω ↦ α * f ω) := measurable_const.mul hf
  calc
    ∫⁻ ω, α * f ω + β * g ω ∂μ = ∫⁻ ω, α * f ω ∂μ + ∫⁻ ω, β * g ω ∂μ := by
      simpa using lintegral_add_left hαf (fun ω ↦ β * g ω)
    _ = α * ∫⁻ ω, f ω ∂μ + β * ∫⁻ ω, g ω ∂μ := by
      rw [lintegral_const_mul α hf, lintegral_const_mul β hg]
