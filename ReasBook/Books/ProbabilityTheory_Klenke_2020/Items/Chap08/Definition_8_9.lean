/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-
Definition 8.9 is a `bridge/view` item. The owner abstraction for conditioning on an event is the
conditioned measure `P[|A] = (P A)⁻¹ • P.restrict A`; the source-facing conditional expectation
given `A` is then the canonical set average, and mathlib's general bridge
`MeasureTheory.setAverage_eq'` identifies it with integration against that conditioned measure.

Mathlib states this bridge for arbitrary functions, so the textbook `L¹(P)` case is a special
case rather than a separate owner definition.
-/
recall ProbabilityTheory.cond

/- The source-facing set average is the canonical bridge to integration against the normalized
restriction. Combined with `ProbabilityTheory.cond`, this is exactly the event-conditioned
expectation from the textbook. -/
recall MeasureTheory.setAverage_eq'
