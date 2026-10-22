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

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}

section

variable [Fact (1 ≤ p)]

-- `MeasureTheory.Lp.instCompleteSpace` is the canonical completeness result for `L^p` spaces over
-- any complete codomain; Theorem 7.18 is its specialization to real-valued `L^p(μ)`.
/- Theorem 7.18: for every exponent `p ∈ [1, ∞]`, the real `L^p(μ)` space equipped with its
canonical norm is complete, hence a Banach space. -/
recall MeasureTheory.Lp.instCompleteSpace

end
