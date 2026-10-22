/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_10

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 15.13 is the chapter's Fenchel-duality attainment statement under
  the textbook regularity hypothesis `0 ∈ sri (effectiveDomain f - effectiveDomain g)`.
- `core/canonical`: the owner declarations are `fenchelDualObjective`, `primalOptimalValue`, and
  `Argmin`.
- `bridge/view`: Corollary 15.14 specializes the same owner theorem to an indicator-function
  constraint model.
-/

-- Proof sketch: Theorem 15.3 upgrades the strong-relative-interior hypothesis to strong Fenchel
-- duality, giving `primalOptimalValue f g = -dualOptimalValue f g`. The source proof then rewrites
-- `dualOptimalValue f g` as the minimum of the canonical dual objective
-- `fenchelDualObjective f g`, so some `u ∈ Argmin (fenchelDualObjective f g)` realizes the common
-- value.
/-- Proposition 15.13: if `f, g ∈ Γ₀(H)` and `0 ∈ sri (dom f - dom g)`, then the primal optimal
value is the negative of the minimum of the Fenchel dual objective
`u ↦ f^*(-u) + g^*(u)`. -/
theorem
    exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    ∃ u ∈ Argmin (fenchelDualObjective f g),
      primalOptimalValue f g = -(fenchelDualObjective f g u) := sorry

end FenchelDuality

end ERealFunction
