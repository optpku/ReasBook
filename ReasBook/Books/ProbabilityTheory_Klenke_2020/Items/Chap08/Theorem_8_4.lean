/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Theorem 8.4: the canonical mathlib theorem `ProbabilityTheory.cond_isProbabilityMeasure`
states that conditioning a probability measure on an event of nonzero probability again yields a
probability measure; the textbook positive-probability hypothesis implies this by `ne_of_gt`. -/
recall ProbabilityTheory.cond_isProbabilityMeasure
