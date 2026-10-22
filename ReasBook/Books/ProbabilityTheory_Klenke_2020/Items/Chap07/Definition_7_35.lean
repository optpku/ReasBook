/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

namespace MeasureTheory
namespace Measure

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Definition 7.35: A measure `ν` is totally continuous with respect to `μ` if every
`ε > 0` admits a `δ > 0` such that every measurable set of `μ`-measure less than `δ` has
`ν`-measure less than `ε`. -/
def TotallyContinuous (ν μ : Measure Ω) : Prop :=
  ∀ ⦃ε : ℝ≥0∞⦄, 0 < ε →
    ∃ δ > 0, ∀ ⦃s : Set Ω⦄, MeasurableSet s → μ s < δ → ν s < ε

end Measure
end MeasureTheory
