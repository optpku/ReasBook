/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/-
Theorem 4.9 (1): (i) If `f, g : α → ℝ` are integrable and `f ≤ g` almost everywhere, then
`∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`.
-/
recall integral_mono_ae

/-
Theorem 4.9 (2): (i) If `f, g : α → ℝ` agree almost everywhere, then they have the same integral.
-/
recall integral_congr_ae

/-
Theorem 4.9 (3): (ii) For an integrable real-valued function, the absolute value of the integral is
bounded by the integral of the absolute value.
-/
recall abs_integral_le_integral_abs

/-- Theorem 4.9 (1): (iii) If `f` and `g` are integrable, then every real linear combination
`a • f + b • g` is integrable. -/
theorem integrable_linear_combination {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (a b : ℝ) : Integrable (a • f + b • g) μ := by
  simpa using (hf.smul a).add (hg.smul b)

/-- Theorem 4.9 (2): (iii) The integral is linear on real-valued integrable functions. -/
theorem integral_linear_combination {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (a b : ℝ) :
    ∫ x, (a • f + b • g) x ∂μ = a • (∫ x, f x ∂μ) + b • (∫ x, g x ∂μ) := by
  change ∫ x, (a • f) x + (b • g) x ∂μ = _
  rw [integral_add (hf.smul a) (hg.smul b)]
  exact congrArg₂ (· + ·) (hf.integral_smul a) (hg.integral_smul b)
