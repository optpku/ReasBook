/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace ERealFunction

section FitzpatrickFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))

local notation "f⋆" => f∗[hf]

-- Proof sketch: fix `(x, u)` and expand `F_{∂ f}(x, u)`, written in Lean as
-- `F[(∂ f)] (x, u)`, as
-- the supremum over graph points `(y, v)` of `∂ f`. Proposition 16.10 rewrites
-- `v ∈ (∂ f) y` as Fenchel--Young equality `f y + f^*(v) = ⟪y, v⟫`, and Proposition 13.15 gives
-- `⟪y, u⟫ - f y ≤ f^*(u)` together with `⟪x, v⟫ - f^*(v) ≤ f^{**}(x) = f x` by
-- Corollary 13.38. Taking the supremum yields the pointwise bound by `f ⊕ f^*`.
/-- The Fitzpatrick function of the subdifferential of a `Γ₀(H)` function is bounded above by the
separable sum `f ⊕ f*`, represented in the project by the canonical packaged conjugate `f∗[hf]`.
-/
theorem fitzpatrickFunction_subdifferential_le_separableSum_gammaZeroConjugate
    :
    F[(∂ f)] ≤
      (f ⊕ f⋆).asEReal := sorry

-- Proof sketch: if `(x, u)` lies in `dom f × dom f*`, then the separable sum
-- `(f ⊕ f⋆) (x, u)` is finite. The preceding Fitzpatrick bound implies
-- `F[(∂ f)] (x, u) < ⊤`, so `(x, u)` lies in the domain of the
-- Fitzpatrick function.
/-- Any pair of finite points for `f` and its Fenchel conjugate `f*`, represented by
the canonical packaged conjugate `f∗[hf]`, lies in the domain of the Fitzpatrick function of
`∂ f`. -/
theorem dom_prod_gammaZeroConjugate_subset_dom_fitzpatrickFunction_subdifferential
    :
    effectiveDomain f ×ˢ effectiveDomain f⋆ ⊆
      dom (F[(∂ f)]) := sorry

-- Proof sketch: the first clause is exactly the Fitzpatrick upper bound proved above. For the
-- second clause, use that any point of `dom f × dom f*` makes `(f ⊕ f*) (x, u)` finite, then
-- apply the upper bound to conclude that `F_{∂ f} (x, u)` is finite as well.
/-- Example 20.55: if `f ∈ Γ₀(H)`, then `F_{∂ f} ≤ f ⊕ f*` and
`dom f × dom f* ⊆ dom F_{∂ f}`, where `f*` is represented by the canonical packaged conjugate
`f∗[hf]`. -/
theorem fitzpatrickFunction_subdifferential_le_separableSum_gammaZeroConjugate_and_dom_prod_subset
    :
    F[(∂ f)] ≤
        (f ⊕ f⋆).asEReal ∧
      effectiveDomain f ×ˢ effectiveDomain f⋆ ⊆
        dom (F[(∂ f)]) := by
  exact
    ⟨fitzpatrickFunction_subdifferential_le_separableSum_gammaZeroConjugate f hf,
      dom_prod_gammaZeroConjugate_subset_dom_fitzpatrickFunction_subdifferential f hf⟩

end FitzpatrickFunction

end ERealFunction
