/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {𝕜 E : Type u} [RCLike 𝕜] [TopologicalSpace E] [CompactSpace E]

/- Theorem 15.2: the Stone--Weierstrass theorem for compact Hausdorff spaces over `ℝ` or `ℂ` is
the canonical mathlib theorem
`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`, formulated for star
subalgebras of `C(E, 𝕜)`; in the real case the star condition is automatic, and in the complex case
it is exactly closure under complex conjugation. -/
recall ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
