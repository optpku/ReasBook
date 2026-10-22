/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: apply the Fenchel--Young inequality to `f` at `(x, -L.adjoint v)` and to `g` at
-- `(L x, v)`, then rewrite the first pairing with `ContinuousLinearMap.adjoint_inner_right` so the
-- two pairings cancel. This is the composite-objective analogue of Proposition 15.9 in the
-- source-facing adjoint form from Definition 15.19.
/-- Proposition 15.18 (1): every primal value `f(x) + g(Lx)` dominates the negative of the
corresponding adjoint-based composite dual objective. -/
theorem compositePrimalObjective_ge_neg_compositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (x : H) (v : K) :
    compositePrimalObjective f g L x ≥ -(compositeDualObjective f g L v) := sorry

-- Proof sketch: apply the pointwise inequality from clause (1) for each `x` and fixed `v`, take
-- the infimum over `x`, and then take the infimum over `v` on the dual side.
/-- Proposition 15.18 (2): the primal optimal value of `x ↦ f(x) + g(Lx)` is bounded below by the
negative of the corresponding adjoint-based composite dual optimal value. -/
theorem compositePrimalOptimalValue_ge_neg_compositeDualOptimalValue
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    compositePrimalOptimalValue f g L ≥ -(compositeDualOptimalValue f g L) := sorry

end FenchelRockafellarDuality

end ERealFunction
