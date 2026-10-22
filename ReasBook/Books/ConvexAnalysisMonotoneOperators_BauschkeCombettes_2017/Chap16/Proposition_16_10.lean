/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)

-- Proof sketch: rewrite `u ∈ ∂ f x` using Definition 16.1, then use Proposition 13.15 on the
-- canonical `EReal` coercion of `f`, whose properness is equivalent here to the nonempty
-- effective domain hypothesis. Unfold `conjugate f u` as the supremum of the affine defects and
-- observe that equality is equivalent to the defining subgradient inequality being tight at `x`.
/-- Proposition 16.10: for an `]-∞,+∞]`-valued function with nonempty effective domain, `u` is a
subgradient of `f` at `x` exactly when equality holds in the Fenchel--Young inequality
`f(x) + f^*(u) = ⟪x, u⟫`. -/
theorem mem_subdifferential_iff_fenchel_young_eq
    (x u : H) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := sorry

-- Proof sketch: extensionality reduces the operator equality to pointwise membership. Rewrite
-- the left side with `SetValuedOperator.mem_inverse_iff`, then apply
-- `mem_subdifferential_iff_fenchel_young_eq` in both directions.
/-- The inverse of the subdifferential of `f` is the subdifferential of its packaged Fenchel
conjugate `properConjugateIoi f hdom`. -/
theorem inverse_subdifferential_eq_subdifferential_properConjugateIoi :
    ((∂ f).inverse : SetValuedOperator H H) = ∂ (properConjugateIoi f hdom) := sorry

-- Proof sketch: rewrite membership in `∂ (properConjugateIoi f hdom)` using the inverse-operator
-- identity above and `SetValuedOperator.mem_inverse_iff`, then apply
-- `mem_subdifferential_iff_fenchel_young_eq`.
/-- The Fenchel--Young equality criterion can be read equally as membership of `x` in the
subdifferential of the packaged Fenchel conjugate at `u`. -/
theorem mem_subdifferential_properConjugateIoi_iff_fenchel_young_eq
    (x u : H) :
    x ∈ ((∂ (properConjugateIoi f hdom) : H → Set H) u) ↔
      (f x : EReal) + f.asEReal∗ u =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := sorry

end SubdifferentialConjugation

end

end ERealFunction
