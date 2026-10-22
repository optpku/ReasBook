/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω}

/- Lemma 8.10 (1): For an integrable real random variable `X`, the conditional expectation
`P[X | ℱ]` is `ℱ`-strongly measurable. This is the canonical mathlib form of the textbook
measurability statement. -/
recall MeasureTheory.stronglyMeasurable_condExp

variable {ℱ : MeasurableSpace Ω} {X : Ω → ℝ}

/- The textbook `ℱ`-measurability statement is the direct corollary
`MeasureTheory.stronglyMeasurable_condExp.measurable`. -/
#check (stronglyMeasurable_condExp.measurable : Measurable[ℱ] (P[X | ℱ]))

/- Lemma 8.10 (2): For an integrable real random variable `X`, the conditional expectation
`P[X | ℱ]` lies in `ℒ¹(P)`. Mathlib states the stronger fact without any extra integrability
assumption on `X`, since `P[X | ℱ]` is defined to be `0` outside the usual domain. -/
recall MeasureTheory.integrable_condExp

/- Lemma 8.10 (3): If `A ∈ ℱ`, then the conditional expectation has the same integral as `X`
over `A`. -/
recall MeasureTheory.setIntegral_condExp
