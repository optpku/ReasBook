/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u v

namespace ERealFunction

open ContinuousLinearMap

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

variable [CompleteSpace H] [CompleteSpace K]

-- Proof sketch: Proposition 16.6 already gives the inclusion
-- `∂ f + L.adjoint '' (∂ g) (L x) ⊆ ∂ (f + g ∘ L)`. For the reverse inclusion, take
-- `u ∈ ∂ (f + g ∘ L) x`, rewrite this by Fenchel--Young equality using Proposition 16.10, and
-- use the assumed conjugate formula for the canonical owner `compositePrimalObjective f g L` to
-- choose `v` on the adjoint fiber of `u`. Applying the Fenchel--Young characterization again to
-- `f` and `g` yields
-- `u - L.adjoint v ∈ ∂ f x` and `v ∈ ∂ g (L x)`.
/-- Proposition 16.42: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, `L (effectiveDomain f)` meets
`effectiveDomain g`, and the conjugate formula
`conjugate (compositePrimalObjective f g L) = f^* □ (L^* ▷ g^*)` holds, then the subdifferential
of `f + g ∘ L` is `∂ f + L^* ∂ g L`, realized by the canonical owner
`(∂ f) + adjointImageSubdifferential L g`. -/
theorem subdifferential_add_comp_eq_add_adjoint_image_of_conjugate_formula
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hdom : (L '' effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hconj :
      conjugate (compositePrimalObjective f g L) =
        f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)) :
    ∂ (f + g ∘ L) = (∂ f) + adjointImageSubdifferential L g :=
      sorry

end SubdifferentialCalculus

end ERealFunction
