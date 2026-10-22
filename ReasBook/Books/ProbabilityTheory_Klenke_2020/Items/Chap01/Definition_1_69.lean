/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 1.69: A measure space `(Ω, 𝓐, μ)` is complete exactly when the measure `μ` is
complete in the canonical mathlib sense, recorded by `MeasureTheory.Measure.IsComplete μ`; this
means every `μ`-null set belongs to the ambient `σ`-algebra. -/
recall MeasureTheory.Measure.IsComplete
