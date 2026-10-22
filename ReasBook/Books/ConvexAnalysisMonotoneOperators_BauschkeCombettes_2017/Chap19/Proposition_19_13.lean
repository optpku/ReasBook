/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: Proposition 13.44 identifies the value at `0` of the canonical value function
-- `Prod.snd ▷ F` with its biconjugate there from the convexity, lower semicontinuity, and
-- effective-domain hypotheses. Finally,
-- Proposition 19.12 rewrites that biconjugate value as the negative infimum of the dual slice
-- `v ↦ F^*(0, v)`.
/-- Proposition 19.13: if the canonical value function `Prod.snd ▷ F` is convex, lower
semicontinuous at the origin, and finite there in the canonical sense
`0 ∈ effectiveDom (Prod.snd ▷ F)`, then the primal infimum `inf_x F(x, 0)` equals the negative
dual infimum `- inf_v F^*(0, v)`.
-/
theorem valueFunction_zero_eq_neg_sInf_perturbationDualObjective_of_lscAt_and_finite
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : IsConvex (Prod.snd ▷ F))
    (hlsc : LowerSemicontinuousAt (Prod.snd ▷ F) (0 : K))
    (hzero : (0 : K) ∈ effectiveDom (Prod.snd ▷ F)) :
    (Prod.snd ▷ F) 0 = -sInf (Set.range (perturbationDualObjective F)) := sorry

end ParametricDuality

end ERealFunction
