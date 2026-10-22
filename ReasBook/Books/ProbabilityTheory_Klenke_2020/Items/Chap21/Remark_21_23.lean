/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u

namespace MeasureTheory

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

namespace Filtration

local notation:arg ℱ "^+*[" μ "]" => completed_right_continuous_filtration μ ℱ

/- Remark 21.23 is a `bridge/view`: the source says the completed right-continuous filtration
satisfies the usual conditions, and the chapter owner abstraction for that property is
`Filtration.UsualConditions`. Package the existing theorem
`completed_right_continuous_filtration_usual_conditions` for `ℱ^+*[μ]` into the owner instance
instead of
restating its fields locally. -/
instance completed_right_continuous_filtration_usualConditions
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    UsualConditions (ℱ^+*[μ]) μ.completion := by
  exact completed_right_continuous_filtration_usual_conditions μ ℱ

end Filtration

end MeasureTheory
