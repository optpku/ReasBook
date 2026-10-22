/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: Proposition 15.9 (2) is already the indexed-infimum inequality for the canonical
-- primal and dual objectives. Rewrite those indexed infima as `primalOptimalValue f g` and
-- `dualOptimalValue f g` using the owner API from Definition 15.10.
/-- Proposition 15.12 (1): the primal optimal value `μ` is at least the negative of the dual
optimal value `μ*`. -/
theorem primalOptimalValue_ge_neg_dualOptimalValue
    (f g : H → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue f g ≥ -dualOptimalValue f g := by
  simpa [primalOptimalValue_eq_iInf_primalObjective,
    dualOptimalValue_eq_iInf_fenchelDualObjective] using
    iInf_primalObjective_ge_neg_iInf_dualObjective f g

-- Proof sketch: unfold `dualityGap`; in the exceptional branch the gap is `0`, and otherwise it is
-- `primalOptimalValue f g + dualOptimalValue f g`, which is nonnegative by clause (1).
/-- Proposition 15.12 (2): the duality gap `Δ(f, g)` lies in `[0, +∞]`, equivalently it is
nonnegative. -/
theorem dualityGap_nonnegative
    (f g : H → Set.Ioi (⊥ : EReal)) :
    0 ≤ dualityGap f g := sorry

-- Proof sketch: unfold `dualityGap` and split on the exceptional case from Definition 15.10; in
-- the non-exceptional branch, clause (1) shows that `primalOptimalValue f g + dualOptimalValue f g`
-- vanishes exactly when `primalOptimalValue f g = -dualOptimalValue f g`.
/-- Proposition 15.12 (3): the primal-dual equality `μ = -μ*` holds exactly when the duality gap
vanishes. -/
theorem primalOptimalValue_eq_neg_dualOptimalValue_iff_dualityGap_eq_zero
    (f g : H → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue f g = -dualOptimalValue f g ↔ dualityGap f g = 0 := sorry

end FenchelDuality

end ERealFunction
