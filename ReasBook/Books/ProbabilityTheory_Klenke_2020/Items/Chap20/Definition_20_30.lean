/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_34
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Definition 20.30 is a `bridge/view`: the source notation `h(P, τ)` for a
probability-preserving dynamical system is represented in this chapter by the canonical owner
`kolmogorov_sinai_entropy P τ hτ`, specialized from a measure-preserving hypothesis via
`MeasurePreserving.measurable` when needed. -/
recall kolmogorov_sinai_entropy (P : Measure Ω) [IsProbabilityMeasure P]
  (τ : Ω → Ω) (hτ : Measurable τ) : EReal
