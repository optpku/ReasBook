/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

-- Proof sketch: Proposition 14.16 identifies coercivity of an element of `Γ₀(H)` with
-- membership of `0` in the interior of the domain of its Fenchel conjugate. Apply this to the
-- linear perturbation `x ↦ f x - ⟪x, u⟫`, then use Proposition 13.23 (iii) with zero translation
-- and constant term to rewrite its conjugate as the translate
-- `v ↦ f^*(v + u)`, which moves the interior-domain condition from `0` to `u`.
/-- Theorem 14.17: the Moreau--Rockafellar coercivity criterion says that for `f ∈ Γ₀(H)` and
`u ∈ H`, the linear perturbation `x ↦ f x - ⟪x, u⟫` is coercive exactly when `u` lies in the
interior of the domain of the Fenchel conjugate `f*`. -/
theorem coercive_sub_inner_iff_mem_interior_dom_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    Coercive (f.asEReal - fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) ↔
      u ∈ interior (dom f.asEReal∗) := sorry

end Conjugation

end ERealFunction
