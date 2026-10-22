/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.4: A convex subset of a vector space is the canonical mathlib predicate
`Convex 𝕜 G` on a set `G`, expressing closure under convex combinations of two points of `G`.
This is the owner abstraction used throughout mathlib for convexity. -/
recall Convex

/- The textbook coefficient formulation of convexity is the standard characterization
`convex_iff_add_mem`: if `x, y ∈ G` and `a, b ≥ 0` with `a + b = 1`, then
`a • x + b • y ∈ G`. Specializing to `a = λ` and `b = 1 - λ` recovers the
usual `λ x + (1 - λ) y` condition for `λ ∈ [0,1]`. -/
recall convex_iff_add_mem
