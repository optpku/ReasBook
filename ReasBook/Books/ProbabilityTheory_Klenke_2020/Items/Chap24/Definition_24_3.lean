/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E]

/-
Definition 24.3 is source-facing: it keeps the textbook random measure as a measure-valued random
variable, while the measurable owner abstraction for that ambient data is the canonical kernel
object `Kernel Ω E`.
-/
/-- Definition 24.3: a random measure on `E` under the probability law `P` is a measurable
`Measure E`-valued random variable whose values are locally finite almost surely. Mathlib's
canonical measurable-space structure on `Measure E` and the owner abstraction `Kernel Ω E`
model the measurable part of the textbook ambient space `\widetilde{\mathcal M}(E)`, while the
almost-sure local-finiteness clause formalizes `\mathbf{P}[X \in \mathcal{M}(E)] = 1`. -/
def IsRandomMeasure (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  Measurable X ∧ ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω)

namespace IsRandomMeasure

/-- A random measure is measurable as a `Measure E`-valued map. -/
theorem measurable {P : ProbabilityMeasure Ω} {X : Ω → Measure E} (hX : IsRandomMeasure P X) :
    Measurable X :=
  hX.1

/-- A random measure is almost everywhere measurable under the ambient probability law. -/
theorem aemeasurable {P : ProbabilityMeasure Ω} {X : Ω → Measure E} (hX : IsRandomMeasure P X) :
    AEMeasurable X (P : Measure Ω) :=
  hX.measurable.aemeasurable

/-- A random measure is locally finite almost surely. -/
theorem ae_isLocallyFiniteMeasure
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E} (hX : IsRandomMeasure P X) :
    ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω) :=
  hX.2

end IsRandomMeasure

end ProbabilityTheory
