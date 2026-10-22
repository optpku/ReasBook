/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_32

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

open scoped BigOperators MeasureTheory

/- Definition 2.29: On `ℤ`, the convolution of two probability measures is the specialization of
the canonical probability-measure convolution `ProbabilityMeasure.conv`. -/
recall MeasureTheory.ProbabilityMeasure.conv

-- Proof sketch: unfold probability-measure convolution to the underlying measure convolution on
-- `ℤ`, rewrite that convolution as the pushforward of the product measure along addition, apply
-- the singleton-fiber summation formula, and simplify the singleton masses of the product measure.
/-- The convolution law on `ℤ` has the usual singleton-mass formula. -/
theorem intProbabilityMeasureConvolution_apply_singleton
    (μ ν : ProbabilityMeasure ℤ) (n : ℤ) :
    μ.conv ν ({n} : Set ℤ) =
      ∑' m : ℤ, μ ({m} : Set ℤ) * ν ({n - m} : Set ℤ) := sorry

/-- The positive convolution powers of a probability measure on `ℤ`, indexed so that `1`
corresponds to the first convolution power. -/
noncomputable abbrev intProbabilityMeasureConvolutionPower
    (μ : ProbabilityMeasure ℤ) (n : ℕ+) : ProbabilityMeasure ℤ :=
  μ ^ (n : ℕ)

/-- The first convolution power is the original probability measure. -/
theorem intProbabilityMeasureConvolutionPower_one
    (μ : ProbabilityMeasure ℤ) :
    intProbabilityMeasureConvolutionPower μ 1 = μ := by
  simp [intProbabilityMeasureConvolutionPower]

/-- Successive positive convolution powers are obtained by convolving once more with `μ`. -/
theorem intProbabilityMeasureConvolutionPower_succ
    (μ : ProbabilityMeasure ℤ) (n : ℕ+) :
    intProbabilityMeasureConvolutionPower μ (n + 1) =
      (intProbabilityMeasureConvolutionPower μ n).conv μ := by
  simpa [intProbabilityMeasureConvolutionPower] using pow_succ μ (n : ℕ)
