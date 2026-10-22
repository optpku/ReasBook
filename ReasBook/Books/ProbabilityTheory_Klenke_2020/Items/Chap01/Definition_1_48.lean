/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 1.48: For an outer measure `μ*`, the family `𝓜(μ*)` of `μ*`-measurable sets is
the measurable space `MeasureTheory.OuterMeasure.caratheodory μ*`; equivalently, a set `A` is
measurable exactly when `∀ E, μ* E = μ* (A ∩ E) + μ* (E \ A)`, i.e. `μ* (A ∩ E) + μ* (Aᶜ ∩ E) =
μ* E` for every `E`. -/
recall MeasureTheory.OuterMeasure.caratheodory
