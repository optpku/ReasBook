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

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/- Definition 6.20: A family in `ℒ^p(μ)` is formalized as a subset of the normed space
`MeasureTheory.Lp ℝ p μ`; boundedness of such a family is the canonical bornological notion
`Bornology.IsBounded`, equivalently uniform boundedness of the `Lp` norms. -/
recall Bornology.IsBounded
