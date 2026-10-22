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

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}

/- Definition 7.1: The textbook space `L^p(Ω, 𝒜, μ)` of almost-everywhere equivalence classes of
real-valued `ℒ^p` functions modulo null functions is formalized by the canonical type
`Lp ℝ p μ`. -/
recall Lp

/- The quotient-class representative map `f ↦ \bar f` is the canonical construction
`MemLp.toLp`, sending a real-valued `ℒ^p` function to its class in `Lp ℝ p μ`. -/
recall MemLp.toLp

/- The norm of an `L^p` class is the `ℒ^p` seminorm of any representative, formalized by
`Lp.norm_toLp`. -/
recall Lp.norm_toLp

/- The integral descends to almost-everywhere equivalence classes whenever a representative is
integrable, because almost-everywhere equal representatives have the same integral by
`integral_congr_ae`. -/
recall integral_congr_ae
