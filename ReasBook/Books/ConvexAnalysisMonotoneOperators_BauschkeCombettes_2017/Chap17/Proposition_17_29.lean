/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
  [Module ℝ H] [ContinuousSMul ℝ H]

-- Proof sketch: argue by contradiction. If `f` fails to be convex on its effective domain, choose
-- a segment with a strict Jensen violation and restrict `f` to that line. Corollary 17.28 then
-- yields two points on the segment with strictly positive opposite directional derivatives, which
-- contradicts the assumed inequality `f'(x; y - x) ≤ -f'(y; x - y)`. Since the codomain already
-- excludes `-∞`, the only primitive data needed from source-level properness is that the effective
-- domain is nonempty.
/-- Proposition 17.29: an `]-∞,+∞]`-valued function is convex on its effective domain if that
domain is nonempty and convex, if the finite-valued restriction is lower semicontinuous on the
effective domain, and if every pair of effective-domain points admits directional derivatives along
the connecting segment that satisfy `f'(x; y - x) ≤ -f'(y; x - y)`. -/
theorem convexOn_effectiveDomain_of_directionalDerivative_antisymmetry
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)
    (hdom_convex : Convex ℝ (effectiveDomain f))
    (hlsc : LowerSemicontinuousOn f.asEReal (effectiveDomain f))
    (hderiv :
      ∀ ⦃x y : H⦄, x ∈ effectiveDomain f → y ∈ effectiveDomain f →
        ∃ ξ η : EReal,
          HasDirectionalDerivativeAt f x (y - x) ξ ∧
            HasDirectionalDerivativeAt f y (x - y) η ∧
            ξ ≤ -η) :
    ConvexOn f (effectiveDomain f) := sorry

end ERealFunction
