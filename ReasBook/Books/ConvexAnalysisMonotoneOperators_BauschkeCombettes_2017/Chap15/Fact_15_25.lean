/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Fact 15.25 is the attainment statement under the textbook polyhedral
  regularity alternatives:
  `K` finite-dimensional, `g` polyhedral, and either
  `effectiveDomain g ∩ ri (L '' effectiveDomain f) ≠ ∅` or
  `H` finite-dimensional, `f` polyhedral, and
  `effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅`.
- `core/canonical`: the owner objects are the Chapter 15 declarations
  `compositePrimalOptimalValue`, `compositeDualObjective`, and `compositeDualOptimalValue` from
  Definition 15.19.
- `bridge/view`: Proposition 15.24 and Theorem 15.23 provide one proof route to this fact, but
  Fact 15.25 itself remains the source-facing polyhedral alternative rather than an `sri` bridge.
-/

-- Proof sketch: keep the source-facing polyhedral alternatives explicit, derive the Chapter 15
-- owner regularity `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)` via Proposition 15.24,
-- and then apply Theorem 15.23.
set_option linter.style.longLine false in
/-- Fact 15.25: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, `K` is finite-dimensional, `g` is polyhedral, and
either (i) `effectiveDomain g` meets `ri (L '' effectiveDomain f)` or (ii) `H` is
finite-dimensional, `f` is polyhedral, and `effectiveDomain g` meets `L '' effectiveDomain f`,
then the composite primal optimal value is the negative of the minimum of the dual objective
`v ↦ f^*(-L^* v) + g^*(v)`. -/
theorem exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) [FiniteDimensional ℝ K] (hg_polyhedral : Polyhedral g.asEReal)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := sorry

-- Proof sketch: apply the source-facing attainment theorem above and rewrite the attained minimum
-- as `compositeDualOptimalValue f g L`.
/-- Companion reformulation of Fact 15.25: the attained dual minimum rewrites to the canonical
dual optimal value `compositeDualOptimalValue f g L`. -/
theorem compositePrimalOptimalValue_eq_neg_compositeDualOptimalValue_of_polyhedral_regularity
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) [FiniteDimensional ℝ K] (hg_polyhedral : Polyhedral g.asEReal)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := sorry

end FenchelRockafellarDuality

end ERealFunction
