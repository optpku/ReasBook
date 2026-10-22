/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 6.9: If `f_n → f` in `L¹(μ)`, then in particular the integrals converge,
`∫ x, f_n x ∂μ → ∫ x, f x ∂μ`. This is the canonical continuity of the Bochner integral with
respect to `L¹` convergence. -/
recall MeasureTheory.tendsto_integral_of_L1'
