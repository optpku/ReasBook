/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 7.17: Minkowski's inequality for real-valued `ℒ^p(μ)` functions is the canonical
seminorm estimate `MeasureTheory.lpNorm_add_le`. Mathlib states it in the more general form for
functions into any normed additive commutative group, and only the first `MemLp` hypothesis is
needed because the right-hand side is allowed to take the value `∞`. -/
recall MeasureTheory.lpNorm_add_le
