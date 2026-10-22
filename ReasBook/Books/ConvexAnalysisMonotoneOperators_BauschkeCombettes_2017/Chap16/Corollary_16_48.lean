/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Theorem_16_47

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Corollary 16.48 regularity reduction: clauses `(ii)` through `(iv)` of the textbook
assumptions imply the canonical regularity hypothesis
`0 ∈ sri (effectiveDomain f - effectiveDomain g)`. -/
theorem zero_mem_strongRelativeInterior_sub_effectiveDomain_of_inter_dom_or_dom_univ_or_ri
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hregular :
      (effectiveDomain f ∩ interior (effectiveDomain g)).Nonempty ∨
        effectiveDomain g = univ ∨
        (FiniteDimensional ℝ H ∧ (ri (effectiveDomain f) ∩ ri (effectiveDomain g)).Nonempty)) :
    (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) := by
  have howner :
      strongRelativeInteriorSubImageRegularity (effectiveDomain g) (effectiveDomain f)
        (ContinuousLinearMap.id ℝ H) := by
    rcases hregular with hinter | hdom_univ | hri
    · dsimp [strongRelativeInteriorSubImageRegularity]
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
          simpa using
            (Or.inl hinter :
              (effectiveDomain f ∩ interior (effectiveDomain g)).Nonempty ∨
                (effectiveDomain g ∩ interior (effectiveDomain f)).Nonempty)
    · have hinter : (effectiveDomain f ∩ interior (effectiveDomain g)).Nonempty := by
        simpa [hdom_univ] using hf.2.nonempty
      dsimp [strongRelativeInteriorSubImageRegularity]
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
          simpa using
            (Or.inl hinter :
              (effectiveDomain f ∩ interior (effectiveDomain g)).Nonempty ∨
                (effectiveDomain g ∩ interior (effectiveDomain f)).Nonempty)
    · dsimp [strongRelativeInteriorSubImageRegularity]
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
        simpa using hri
  simpa using
    (zero_mem_strongRelativeInterior_sub_image_effectiveDomain_of_owner_regularity
      hg.2.nonempty
      hf.2.nonempty
      hg.2.convex_effectiveDomain
      hf.2.convex_effectiveDomain
      (ContinuousLinearMap.id ℝ H)
      howner)

-- Proof sketch: apply Theorem 16.47 to `g + f ∘ id` with `L = ContinuousLinearMap.id ℝ H`, then
-- rewrite both sides using commutativity of pointwise addition and the identity-map adjoint-image
-- subdifferential.
/-- Companion theorem: under the canonical regularity hypothesis
`0 ∈ sri (effectiveDomain f - effectiveDomain g)`, the subdifferential of `f + g` splits as the
sum of the subdifferentials. -/
theorem subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (∂ (f + g) : SetValuedOperator H H) = (∂ f) + (∂ g) := by
  have hid :
      ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) f = ∂ f := by
    ext x u
    simp [ContinuousLinearMap.adjointImageSubdifferential]
  have hsum : (∂ (g + f) : SetValuedOperator H H) = (∂ f) + (∂ g) := by
    simpa [hid, add_comm] using
      (subdifferential_add_comp_eq_add_adjoint_image_of_regular
        hg
        hf
        (ContinuousLinearMap.id ℝ H)
        (by simpa using hsri))
  have hadd : f + g = g + f := by
    ext x
    simp [add_comm]
  calc
    (∂ (f + g) : SetValuedOperator H H) = ∂ (g + f) := by simp [hadd]
    _ = (∂ f) + (∂ g) := hsum

-- Proof sketch: first derive the canonical Chapter 15 regularity hypothesis
-- `0 ∈ sri (effectiveDomain f - effectiveDomain g)` from the textbook clauses `(ii)` through
-- `(iv)`, then apply the companion `sri` sum rule above.
/-- Corollary 16.48: if `f, g ∈ Γ₀(H)` and one of the textbook regularity clauses `(ii)` through
`(iv)` holds, namely
`effectiveDomain f ∩ interior (effectiveDomain g) ≠ ∅`, or `effectiveDomain g = univ`, or `H` is
finite-dimensional and `ri (effectiveDomain f) ∩ ri (effectiveDomain g) ≠ ∅`, then
`∂ (f + g) = ∂ f + ∂ g`. -/
theorem subdifferential_add_eq_add_of_inter_dom_or_dom_univ_or_ri
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hregular :
      (effectiveDomain f ∩ interior (effectiveDomain g)).Nonempty ∨
        effectiveDomain g = univ ∨
        (FiniteDimensional ℝ H ∧ (ri (effectiveDomain f) ∩ ri (effectiveDomain g)).Nonempty)) :
    (∂ (f + g) : SetValuedOperator H H) = (∂ f) + (∂ g) := by
  refine subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain hf hg ?_
  exact
    zero_mem_strongRelativeInterior_sub_effectiveDomain_of_inter_dom_or_dom_univ_or_ri
      hf hg hregular

end SubdifferentialCalculus

end ERealFunction
