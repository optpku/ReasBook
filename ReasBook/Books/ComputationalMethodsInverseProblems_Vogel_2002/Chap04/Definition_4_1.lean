/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.CDF

public section

/- Definition 4.1 (1). A probability space on `Ω` is formalized by an ambient
measurable space `[MeasurableSpace Ω]` together with a measure `μ` carrying the
instance `[MeasureTheory.IsProbabilityMeasure μ]`. -/
#check MeasureTheory.IsProbabilityMeasure

/- Definition 4.1 (2). A random variable `X : Ω → ℝ` is formalized as a
measurable function. -/
#check Measurable

namespace ProbabilityTheory

universe u

/-- Definition 4.1 (3). For a measurable real-valued random variable `X`, the
associated cumulative distribution function is the source-facing pushforward
specialization of `cdf_eq_real`:
`F_X x = μ.real {ω | X ω ≤ x}`. -/
theorem cdf_map_eq_prob_le
    {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (x : ℝ) :
    cdf (μ.map X) x = μ.real {ω | X ω ≤ x} := by
  have hmap : MeasureTheory.IsProbabilityMeasure (μ.map X) :=
    μ.isProbabilityMeasure_map hX.aemeasurable
  calc
    cdf (μ.map X) x = (μ.map X).real (Set.Iic x) := by
      simpa using (@cdf_eq_real (μ.map X) hmap x)
    _ = μ.real {ω | X ω ≤ x} := by
      rw [MeasureTheory.map_measureReal_apply hX measurableSet_Iic]
      simp only [Set.preimage, Set.mem_Iic]

end ProbabilityTheory

/- Definition 4.1 (4). Monotonicity of the cumulative distribution function is
the canonical theorem `ProbabilityTheory.monotone_cdf`. -/
#check ProbabilityTheory.monotone_cdf

/- Definition 4.1 (5). Right continuity of the cumulative distribution function
is inherited from the `StieltjesFunction` API. -/
#check StieltjesFunction.right_continuous

/- Definition 4.1 (6). The cumulative distribution function tends to `0` at
`-∞` and to `1` at `+∞`. -/
#check ProbabilityTheory.tendsto_cdf_atBot
#check ProbabilityTheory.tendsto_cdf_atTop
