/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Remark_15_35Support

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

/-- Remark 15.35: for a real probability law `μ`, the characteristic function is differentiable at
`0` with derivative `(m : ℂ) * Complex.I` if and only if the tail term
`x * μ.real {y | x < |y|}` tends to `0` and the truncated first moments on `[-x, x]` converge
to `m`. -/
theorem hasDerivAt_charFun_zero_iff_tendsto_tail_and_truncated_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) :
    HasDerivAt (charFun μ) ((m : ℂ) * Complex.I) 0 ↔
      Tendsto (fun x ↦ x * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) ∧
        Tendsto (fun x ↦ ∫ y in Set.Icc (-x) x, y ∂μ) atTop (𝓝 m) := by
  simpa using
    Remark1535Support.hasDerivAtCharFunZeroIffTendstoTailAndTruncatedMean μ m
