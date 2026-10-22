/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/-- Theorem 13.6: every finite Borel measure on a Polish space is a regular measure. -/
-- Proof sketch: mathlib gives the stronger owner fact `Measure.Regular μ` for finite Borel
-- measures on Polish spaces. The chapter predicate `IsRegularMeasure μ` is then obtained by
-- combining `σ`-finiteness from `IsFiniteMeasure μ` with the induced inner and outer regularity.
theorem finite_measure_regular_of_polish (μ : Measure E) [IsFiniteMeasure μ] :
    IsRegularMeasure μ :=
  IsRegularMeasure.of_owner μ

/-- Every finite Borel measure on a Polish space is a Radon measure. -/
-- Proof sketch: the same stronger owner fact `Measure.Regular μ` provides compact-set finiteness,
-- hence local finiteness on a Polish space, together with the induced inner regularity.
theorem finite_measure_radon_of_polish (μ : Measure E) [IsFiniteMeasure μ] :
    IsRadonMeasure μ :=
  IsRadonMeasure.of_owner μ

namespace MeasureTheory
namespace FiniteMeasure

/-- The textbook inclusion `𝓜_f(E) ⊆ 𝓜(E)` is the owner-level fact that every finite Borel
measure on a Polish space is Radon. -/
theorem isRadonMeasure_of_polish (μ : FiniteMeasure E) :
    IsRadonMeasure (μ : Measure E) :=
  finite_measure_radon_of_polish (μ : Measure E)

end FiniteMeasure
end MeasureTheory
