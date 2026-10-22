/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: if either effective domain is empty, then the corresponding function is
-- identically `+∞`, so the inequality is immediate. Otherwise apply the Fenchel--Young inequality
-- to `f` at `(x, -u)` and to `g` at `(x, u)`, then add the resulting inequalities and simplify the
-- pairing terms, which cancel.
/-- Proposition 15.9 (1): every primal value dominates the negative dual value, i.e.
`-fenchelDualObjective f g u ≤ primalObjective f g x`. -/
theorem primalObjective_ge_neg_dualObjective
    (f g : H → Set.Ioi (⊥ : EReal))
    (x u : H) :
    -fenchelDualObjective f g u ≤ primalObjective f g x := sorry

-- Proof sketch: combine the improper-case triviality with the pointwise estimate from part (1),
-- then pass to the infimum over `x` on the left and over `u` on the right.
/-- Proposition 15.9 (2): the infimum of the primal objective is bounded below by the negative of
the infimum of the dual objective. -/
theorem iInf_primalObjective_ge_neg_iInf_dualObjective
    (f g : H → Set.Ioi (⊥ : EReal)) :
    -(⨅ u : H, fenchelDualObjective f g u) ≤ ⨅ x : H, primalObjective f g x := sorry

end FenchelDuality

end ERealFunction
