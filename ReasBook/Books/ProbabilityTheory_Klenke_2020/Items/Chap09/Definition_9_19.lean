/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Definition 9.19: For a stopping time `τ` with respect to a filtration `ℱ`, the σ-algebra of
the `τ`-past is the canonical mathlib measurable space `IsStoppingTime.measurableSpace`
attached to a proof `hτ : IsStoppingTime ℱ τ`. -/
recall IsStoppingTime.measurableSpace

/- Membership in the stopping-time past σ-algebra is characterized by the textbook condition
`A ∩ {τ ≤ t} ∈ ℱ_t` for every time `t`. -/
recall IsStoppingTime.measurableSet
