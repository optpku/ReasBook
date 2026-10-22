/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 4.13: For a measure `μ` on `(Ω, 𝓐)` and a measurable nonnegative density `f`,
the textbook measure `f μ` is the canonical measure-with-density construction
`MeasureTheory.Measure.withDensity`; when `f : Ω → ℝ≥0`, this is written in Lean as
`μ.withDensity fun ω ↦ (f ω : ℝ≥0∞)`. -/
recall MeasureTheory.Measure.withDensity

/- On measurable sets, `μ.withDensity f` evaluates as the lower integral `∫⁻ ω in A, f ω ∂μ`,
which is Lean's form of the textbook formula `ν(A) = ∫ (1_A f) dμ`. -/
recall MeasureTheory.withDensity_apply
