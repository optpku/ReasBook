/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 1.98: For a measurable map `X : Ω → Ω'` and a measure `μ` on `Ω`, the image
measure of `μ` under `X` is the canonical mathlib pushforward measure `μ.map X` on `Ω'`. -/
recall MeasureTheory.Measure.map

/-- On measurable sets `A'`, the image measure `μ.map X` is given by the textbook formula
`μ.map X A' = μ (X ⁻¹' A')`. -/
recall MeasureTheory.Measure.map_apply
