/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_20

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped InnerProductSpace

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/- Theorem 7.21: the canonical bracket on the real space `ℒ²(μ)` of square-integrable
representatives, modeled by `mem_lp_submodule 2 μ`, is the semi-inner product space structure
`memLpTwoPreInnerProductSpaceCore`. -/
recall memLpTwoPreInnerProductSpaceCore

/- Theorem 7.21: the canonical bracket on the real quotient space `L²(μ) = MeasureTheory.Lp ℝ 2 μ`
is the mathlib inner product space structure `MeasureTheory.L2.innerProductSpace`. -/
recall L2.innerProductSpace

/-- The textbook identity `‖f‖₂ = √⟪f, f⟫` for a square-integrable real representative, expressed
on its canonical class in `L²(μ)`. -/
theorem lpNorm_two_eq_sqrt_inner_toLp {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ = Real.sqrt ⟪hf.toLp f, hf.toLp f⟫_ℝ := by
  rw [← toReal_eLpNorm hf.aestronglyMeasurable, ← Lp.norm_toLp f hf, norm_eq_sqrt_real_inner]

/-- For a square-integrable real representative, the `L²` seminorm is the square root of the
integral of its pointwise square. -/
theorem lpNorm_two_eq_sqrt_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [lpNorm_two_eq_sqrt_inner_toLp hf, inner_toLp_eq_integral_mul hf hf]
  simp [sq]

/-- For a square-integrable real representative in `ℒ²(μ)`, the `L²` seminorm is the square root
of its canonical semi-inner product with itself. -/
theorem lpNorm_two_eq_sqrt_inner_memLpSubmodule (f : mem_lp_submodule 2 μ) :
    lpNorm (f : Ω → ℝ) 2 μ = Real.sqrt ⟪f, f⟫_ℝ := by
  rw [lpNorm_two_eq_sqrt_integral_sq f.2, inner_memLp_two_eq_integral_mul]
  simp [sq]
