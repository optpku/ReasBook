/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 8.34: an isomorphism of measurable spaces is the canonical owner notion
`MeasurableEquiv`, i.e. a bijection whose forward and inverse maps are both measurable. -/
recall MeasurableEquiv

/- A measure-space isomorphism is not a separate owner structure: it is a measurable equivalence
`e : α ≃ᵐ β` together with the canonical measure-preservation predicate
`MeasureTheory.MeasurePreserving e μ ν`. -/
recall MeasureTheory.MeasurePreserving
