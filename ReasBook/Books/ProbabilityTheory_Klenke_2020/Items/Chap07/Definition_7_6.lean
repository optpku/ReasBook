/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.6: For a function `φ : E → ℝ` on a convex set `G`, the textbook notion of
convexity is the canonical mathlib predicate `ConvexOn ℝ G φ`, expressing
`φ (λ • x + (1 - λ) • y) ≤ λ • φ x + (1 - λ) • φ y` for points `x, y ∈ G` and
coefficients `λ ∈ [0,1]`. -/
recall ConvexOn

/- The corresponding notion of a concave function on a convex set is the canonical predicate
`ConcaveOn ℝ G φ`. -/
recall ConcaveOn

/- The textbook formulation that `φ` is concave exactly when `-φ` is convex is the standard
mathlib equivalence `neg_convexOn_iff`. -/
recall neg_convexOn_iff
