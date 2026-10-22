/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 7.16: if `f ∈ ℒ^p(μ)` and `g ∈ ℒ^q(μ)` with Hölder-conjugate exponents, then
`f * g ∈ ℒ¹(μ)`. This is the canonical theorem `MeasureTheory.MemLp.mul`, specialized to the
instance `ENNReal.HolderTriple p q 1` induced by `p.HolderConjugate q`. -/
recall MeasureTheory.MemLp.mul

/- Theorem 7.16: Hölder's inequality for real-valued `ℒ^p(μ)` and `ℒ^q(μ)` functions is the
canonical seminorm estimate `MeasureTheory.eLpNorm_smul_le_mul_eLpNorm`. For `ℝ`-valued
functions, the pointwise scalar product `φ • f` is exactly the pointwise product `φ * f`, and the
same `ENNReal.HolderTriple p q 1` instance coming from `p.HolderConjugate q` yields the textbook
product estimate. -/
recall MeasureTheory.eLpNorm_smul_le_mul_eLpNorm
