/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ProbabilityTheory

universe u v w

namespace ProbabilityTheory

variable {ι : Type u} [Preorder ι]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [mE : MeasurableSpace E]

/-- Definition 17.1: a process has the Markov property with respect to a filtration `ℱ` if, for
it is adapted to `ℱ`, and for every measurable set `A` and all times `s ≤ t`, the conditional
probability of the future event `{X_t ∈ A}` given `ℱ s` agrees almost surely with the conditional
probability given the present state `X s`. -/
def HasMarkovProperty (ℱ : Filtration ι mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → E) : Prop :=
  Adapted ℱ X ∧
    ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ ⦃s t : ι⦄, s ≤ t →
      μ⟦X t ⁻¹' A | ℱ s⟧ =ᵐ[μ]
        μ⟦X t ⁻¹' A | MeasurableSpace.comap (X s) mE⟧

theorem HasMarkovProperty.adapted {ℱ : Filtration ι mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → E} (h : HasMarkovProperty ℱ μ X) :
    Adapted ℱ X :=
  h.1

theorem HasMarkovProperty.measurable {ℱ : Filtration ι mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → E} (h : HasMarkovProperty ℱ μ X) (t : ι) :
    Measurable (X t) :=
  h.adapted.measurable

-- Proof sketch: unfold `HasMarkovProperty`; this is the defining adaptedness plus conditional-
-- probability identity written as an explicit `↔`, which is the useful elimination form for later
-- rewriting.
/-- Having the Markov property is equivalent to adaptedness together with the conditional-
probability identity for all measurable state events and all times `s ≤ t`. -/
theorem hasMarkovProperty_iff (ℱ : Filtration ι mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → E) :
    HasMarkovProperty ℱ μ X ↔
      Adapted ℱ X ∧
        ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ ⦃s t : ι⦄, s ≤ t →
          μ⟦X t ⁻¹' A | ℱ s⟧ =ᵐ[μ]
            μ⟦X t ⁻¹' A | MeasurableSpace.comap (X s) mE⟧ :=
  Iff.rfl

end ProbabilityTheory
