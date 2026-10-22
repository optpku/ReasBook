/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

/- Example 7.42: If `μ⁺` and `μ⁻` are finite measures, then their difference defines a signed
measure. In Lean this is the canonical term
`μpos.toSignedMeasure - μneg.toSignedMeasure : SignedMeasure Ω`; the later statement that every signed
measure admits such a representation is deferred to subsequent results. -/
#check
  fun {Ω : Type u} [MeasurableSpace Ω] (μpos μneg : Measure Ω)
    [IsFiniteMeasure μpos] [IsFiniteMeasure μneg] ↦
      μpos.toSignedMeasure - μneg.toSignedMeasure
