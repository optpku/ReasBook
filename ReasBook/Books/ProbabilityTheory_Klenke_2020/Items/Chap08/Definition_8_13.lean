/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {S : Type v} [mS : MeasurableSpace S]

/- Definition 8.13 is a `bridge/view` item. The owner abstraction remains
`MeasureTheory.condExp`; for an integrable real random variable `X` and a measurable random
variable `Y`, conditioning on `Y` means conditioning on the pullback σ-algebra `σ(Y) = mS.comap Y`.
-/
recall MeasureTheory.condExp

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : Ω → ℝ} {Y : Ω → S}

/-- Under the textbook hypotheses, the conditional expectation of `X` given `Y` is the canonical
conditional expectation on `σ(Y)`, characterized by equality of integrals on `σ(Y)`-measurable
sets. -/
theorem setIntegral_condExp_comap
    (hX : Integrable X P) (hY : Measurable Y) {s : Set Ω}
    (hs : MeasurableSet[mS.comap Y] s) :
    ∫ ω in s, P[X | mS.comap Y] ω ∂P = ∫ ω in s, X ω ∂P :=
  setIntegral_condExp hY.comap_le hX hs
