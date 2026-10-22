/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Corollary 7.34 (1): for `σ`-finite measures, absolute continuity is equivalent to equality with
the canonical Radon--Nikodym density; this is exactly the canonical theorem
`Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`. -/
recall MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq

/- Corollary 7.34 (2): the canonical Radon--Nikodym density `ν.rnDeriv μ` is measurable. -/
recall MeasureTheory.Measure.measurable_rnDeriv

/- Corollary 7.34 (3): if `ν` is `σ`-finite, then `ν.rnDeriv μ` is finite `μ`-almost
everywhere. -/
recall MeasureTheory.Measure.rnDeriv_lt_top

namespace MeasureTheory
namespace Measure

/-- A `σ`-finite measure `ν` has a measurable density with respect to `μ` exactly when `ν` is
absolutely continuous with respect to `μ`. -/
theorem exists_density_iff_absolutelyContinuous {μ ν : Measure Ω} [SigmaFinite μ] [SigmaFinite ν] :
    (∃ f : Ω → ℝ≥0∞, Measurable f ∧ μ.withDensity f = ν) ↔ ν ≪ μ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, -, rfl⟩
    exact withDensity_absolutelyContinuous μ f
  · intro hνμ
    exact ⟨ν.rnDeriv μ, measurable_rnDeriv ν μ, withDensity_rnDeriv_eq ν μ hνμ⟩

end Measure
end MeasureTheory
