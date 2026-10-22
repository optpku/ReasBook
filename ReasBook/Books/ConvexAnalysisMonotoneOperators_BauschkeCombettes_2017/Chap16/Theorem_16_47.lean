/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Theorem_15_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_42

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u v

namespace ERealFunction

open ContinuousLinearMap

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: apply Theorem 15.27 under the chapter owner regularity
-- `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`, then feed the resulting composite
-- conjugate formula into Proposition 16.42.
/-- Theorem 16.47: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, and
`0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`, then
`∂ (x ↦ f x + g (L x)) = ∂ f + L^* ∂ g L`, realized as
`(∂ f) + ERealFunction.ContinuousLinearMap.adjointImageSubdifferential L g`. -/
theorem subdifferential_add_comp_eq_add_adjoint_image_of_regular
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    ∂ (f + g ∘ L) = (∂ f) + adjointImageSubdifferential L g := by
  have hdom : (L '' effectiveDomain f ∩ effectiveDomain g).Nonempty := by
    rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
    rcases Set.mem_sub.mp hzero with ⟨y, hy, z, hz, hyz⟩
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨L x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simpa [sub_eq_zero.mp hyz] using hy
  exact subdifferential_add_comp_eq_add_adjoint_image_of_conjugate_formula hf hg L hdom
    (conjugate_addComp_eq_dualInfimalConvolution_of_regular f g L)

end SubdifferentialCalculus

end ERealFunction
