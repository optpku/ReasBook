/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: expand the conjugate of the value function `Prod.snd ▷ F` directly on `K`, use
-- `infimalPostcomposition_snd_apply` to rewrite the value function as the fiberwise infimum of the
-- slices `x ↦ F (x, y)`, and then commute the outer supremum in `y` with the inner infimum in `x`
-- to obtain the explicit dual-objective formula `v ↦ F^*(0, v)`.
/-- Proposition 19.12 (1): if `ϑ = Prod.snd ▷ F`, then `ϑ*` is the dual objective
`v ↦ F^*(0, v)` of `F`. -/
theorem conjugate_valueFunction_eq_dualObjective
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    (Prod.snd ▷ F)∗ = perturbationDualObjective F := sorry

-- Proof sketch: specialize `conjugate_zero_eq_neg_iInf` to `ϑ* = (Prod.snd ▷ F)∗`, then rewrite
-- the resulting infimum with clause (1).
/-- Proposition 19.12 (2): the negative infimum of the slice `v ↦ F^*(0, v)` equals the value of
`ϑ**` at the origin. -/
theorem neg_sInf_perturbationDualObjective_eq_biconjugate_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    -sInf (Set.range (perturbationDualObjective F)) =
      (Prod.snd ▷ F)∗∗ 0 := by
  rw [← conjugate_valueFunction_eq_dualObjective]
  simpa [sInf_range] using
    (conjugate_zero_eq_neg_iInf ((Prod.snd ▷ F)∗)).symm

-- Proof sketch: this is `biconjugate_le` for the canonical owner `Prod.snd ▷ F`, evaluated at
-- `0`.
/-- Proposition 19.12 (3): the biconjugate of the value function at the origin is bounded above by
its value at the origin. -/
theorem biconjugate_valueFunction_zero_le_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    (Prod.snd ▷ F)∗∗ 0 ≤ (Prod.snd ▷ F) 0 := by
  simpa using (biconjugate_le (Prod.snd ▷ F)) 0

/- Proposition 19.12 (4) is the specialization at `0` of the defining evaluation formula for the
canonical owner `Prod.snd ▷ F`. -/
recall infimalPostcomposition_snd_apply

end ParametricDuality

end

end ERealFunction
