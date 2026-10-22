/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 1.46: An outer measure on `Ω` is the canonical mathlib object
`MeasureTheory.OuterMeasure Ω`, namely a set function `2^Ω → [0, ∞]` that satisfies
(i) `μ* ∅ = 0`, (ii) monotonicity, and (iii) `σ`-subadditivity. -/
recall MeasureTheory.OuterMeasure
