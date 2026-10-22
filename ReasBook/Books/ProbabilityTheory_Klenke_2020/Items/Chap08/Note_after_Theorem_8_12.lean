/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} {ℱ : MeasurableSpace Ω}
variable {X Y : Ω → ℝ}

/- Note after Theorem 8.12: equalities involving conditional expectations are interpreted as
almost-sure equalities with respect to the underlying measure. The owner abstraction is
`Filter.EventuallyEq` on the `ae P` filter, written in measure-theoretic notation as
`P[X | ℱ] =ᵐ[P] P[Y | ℱ]`. -/
recall Filter.EventuallyEq

/- The textbook equality of conditional expectations is therefore read in Lean using the canonical
`=ᵐ[P]` notation. -/
#check (P[X | ℱ] =ᵐ[P] P[Y | ℱ])
