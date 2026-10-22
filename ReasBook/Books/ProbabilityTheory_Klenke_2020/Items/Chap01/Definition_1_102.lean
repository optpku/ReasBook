/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

/- Definition 1.102: A random variable with values in a measurable space `(Ω', 𝓐')` is exactly a
measurable map `X : Ω → Ω'` in the canonical mathlib sense, and in particular a real random
variable is a measurable map into `ℝ` with its Borel `σ`-algebra. -/
recall Measurable

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Definition 1.102: a real random variable is exactly a measurable map into `ℝ` equipped with
its canonical Borel `σ`-algebra. -/
theorem measurable_real_iff_borel {X : Ω → ℝ} :
    Measurable X ↔ @Measurable Ω ℝ ‹MeasurableSpace Ω› (borel ℝ) X :=
  Iff.rfl
