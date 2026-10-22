/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped NNReal

universe u v

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

variable (X : ℝ≥0 → Ω → E)

/- Definition 25.5 (1): a continuous-time process is product measurable when the time-first
uncurried map is measurable. In mathlib's process convention, this is exactly
`Measurable (Function.uncurry X)`. -/
#check (Measurable (Function.uncurry X))

/- The textbook `Ω × ℝ≥0` formulation of product measurability is equivalent to the canonical
time-first statement `Measurable (Function.uncurry X)`. -/
theorem measurable_uncurry_swap_iff :
    Measurable (Function.uncurry fun ω t ↦ X t ω) ↔ Measurable (Function.uncurry X) := by
  simpa [Function.uncurry, Function.comp] using
    (measurable_swap_iff : Measurable ((Function.uncurry X) ∘ Prod.swap) ↔
      Measurable (Function.uncurry X))

end MeasureTheory

/- Definition 25.5 (2): the canonical mathlib notion of a progressively measurable
continuous-time process is `MeasureTheory.ProgMeasurable`; it encodes measurability of the
restriction to each strip `[0, t] × Ω` using `Set.Iic t × Ω`. -/
recall ProgMeasurable

/- Definition 25.5 (3): the canonical mathlib notion of a predictable continuous-time process is
`MeasureTheory.IsPredictable`. -/
recall IsPredictable

/- The predictable `σ`-algebra appearing in Definition 25.5 (3) is the canonical measurable space
`MeasureTheory.Filtration.predictable` on time-space. -/
recall Filtration.predictable
