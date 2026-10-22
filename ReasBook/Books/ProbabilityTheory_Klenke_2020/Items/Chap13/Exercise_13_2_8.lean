/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
variable [TopologicalSpace.SeparableSpace E]

/- The first part of Exercise 13.2.8 is that the textbook distance `(13.3)` on `𝓜_1(E)`, which
Exercise 13.2.1 identifies with the Lévy-Prokhorov distance, is a genuine metric on
`ProbabilityMeasure E`. This is the canonical metric-space instance on the type synonym
`LevyProkhorov (ProbabilityMeasure E)`. -/
#check (inferInstance : MetricSpace (LevyProkhorov (ProbabilityMeasure E)))

/- Exercise 13.2.8: after identifying `(13.3)` with the Lévy-Prokhorov distance from Exercise
13.2.1, the induced metric topology on `𝓜_1(E)` is exactly the topology of weak convergence.
This is the canonical theorem `LevyProkhorov.eq_convergenceInDistribution`. -/
recall LevyProkhorov.eq_convergenceInDistribution

end
