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

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ≥0∞)

/- Remark 4.14: the set function `ν(A) = ∫⁻ ω in A, f ω ∂μ` from Definition 4.13 is already the
canonical measure `μ.withDensity f` in mathlib. Thus the textbook verification via Theorem 1.36,
finite additivity, and monotone convergence is absorbed by the existing construction. -/
#check (μ.withDensity f : Measure Ω)
