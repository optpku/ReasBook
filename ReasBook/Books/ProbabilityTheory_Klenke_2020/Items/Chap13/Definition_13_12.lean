/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported Topology

section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/- Definition 13.12 (1): weak convergence of finite measures is the canonical convergence notion
`Tendsto μs atTop (𝓝 μ)` on `FiniteMeasure E`; its textbook test-function characterization is the
owner theorem `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`. -/
recall MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto

/-- Definition 13.12 (2): a sequence of Radon measures on the metric space `E` converges vaguely
to `μ` when the integrals of all compactly supported continuous real-valued test functions
converge to the corresponding integral against `μ`. -/
def radonMeasureVaguelyConvergesTo (μs : ℕ → Measure E) (μ : Measure E) : Prop :=
  IsRadonMeasure μ ∧
    (∀ n, IsRadonMeasure (μs n)) ∧
    ∀ f : C_c(E, ℝ),
      Tendsto (fun n ↦ ∫ x, f x ∂μs n) atTop (𝓝 (∫ x, f x ∂μ))

omit [BorelSpace E] in
-- Proof sketch: this is just the defining conjunction for vague convergence, recording both the
-- Radon-measure domain conditions and the convergence of compactly supported continuous test
-- function integrals.
/-- Vague convergence of Radon measures means exactly convergence of integrals against all
compactly supported continuous real-valued test functions, together with the ambient Radon-measure
assumptions on the sequence and its limit. -/
theorem radonMeasureVaguelyConvergesTo_iff
    (μs : ℕ → Measure E) (μ : Measure E) :
    radonMeasureVaguelyConvergesTo μs μ ↔
      IsRadonMeasure μ ∧
        (∀ n, IsRadonMeasure (μs n)) ∧
        ∀ f : C_c(E, ℝ),
          Tendsto (fun n ↦ ∫ x, f x ∂μs n) atTop (𝓝 (∫ x, f x ∂μ)) :=
  Iff.rfl

end
