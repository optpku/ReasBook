/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use the primitive convexity hypothesis on `effectiveDomain f`, unfold
-- `IsProxPoint` through the canonical owner `Argmin` of `proximalObjective f x`, rewrite the
-- resulting minimizer condition as the corresponding pointwise inequality, and expand the
-- quadratic term on both sides.
/-- Proposition 12.26: if `f` is convex on its effective domain (in particular if `f ∈ Γ₀(H)`),
then a point `p` is a proximal point of `f` at `x` exactly when it satisfies the textbook
variational inequality `(12.25)`,
`⟪y - p, x - p⟫ + f(p) ≤ f(y)` for every `y ∈ H`. -/
theorem isProxPoint_iff_forall_inner_add_le
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (x p : H) :
    IsProxPoint f x p ↔
      ∀ y, (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal) := sorry

end ERealFunction
