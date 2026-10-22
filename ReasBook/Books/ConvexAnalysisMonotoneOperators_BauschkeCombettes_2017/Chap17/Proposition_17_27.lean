/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
  [Module ℝ H] [ContinuousSMul ℝ H]

-- Proof sketch: parametrize the segment by `g(t) = f (AffineMap.lineMap x0 x1 t)`. Lower
-- semicontinuity on the closed segment gives the corresponding endpoint control for `g` on
-- `[0,1]`, while the directional-derivative assumption on `[x0,x1[` yields right derivatives of
-- `g` on `[0,1[` with value at most `0`. The latter already forces every point of `[x0,x1[` to lie
-- in `effectiveDomain f`, so no separate domain hypothesis is needed there. The one-dimensional
-- interval argument then gives `g 1 ≤ g 0`, i.e. `f x1 ≤ f x0`.
/-- Proposition 17.27: if the restriction of `f` to `[x0,x1]` is lower semicontinuous, and if
every directional derivative along `x1 - x0` on `[x0,x1[` exists with value at most `0`, then
`f x1 ≤ f x0`. -/
theorem apply_right_le_left_of_nonpos_directionalDerivativeOn_segment
    (f : H → Set.Ioi (⊥ : EReal)) {x0 x1 : H}
    (hlsc : LowerSemicontinuousOn f.asEReal (segment ℝ x0 x1))
    (hderiv : ∀ x ∈ closedOpenSegment x0 x1,
      ∃ ξ, HasDirectionalDerivativeAt f x (x1 - x0) ξ ∧ ξ ≤ 0) :
    f.asEReal x1 ≤ f.asEReal x0 := sorry

end ERealFunction
