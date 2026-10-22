/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section PointwiseAddRegularity

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] [SequentialSpace H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

omit [SequentialSpace H] in
-- Proof sketch: membership in `sri (effectiveDomain f - effectiveDomain g)` implies membership in
-- `effectiveDomain f - effectiveDomain g`, so `0 = x - y` for some `x ∈ effectiveDomain f` and
-- `y ∈ effectiveDomain g`; hence `x = y`, and the effective domains intersect.
private theorem effectiveDomain_inter_nonempty_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (effectiveDomain f ∩ effectiveDomain g).Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, hx, ?_⟩
  simpa [sub_eq_zero.mp hxy] using hy

-- Proof sketch: use the previous domain-intersection lemma and the canonical Chapter 9 owner
-- `pointwiseAdd_mem_gammaZero`.
/-- Theorem 15.3: (Attouch--Brézis) if `f, g ∈ Γ₀(H)` and
`0 ∈ sri (effectiveDomain f - effectiveDomain g)`, then `f + g ∈ Γ₀(H)`. -/
theorem pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    f + g ∈ Γ₀(H) :=
  pointwiseAdd_mem_gammaZero f g hf hg
    (effectiveDomain_inter_nonempty_of_zero_mem_sri_sub_effectiveDomain f g hsri)

end PointwiseAddRegularity

section AttouchBrezisTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: follow the Attouch--Brézis reduction to the closed linear span of
-- `effectiveDomain f - effectiveDomain g`, where the translated restrictions satisfy the
-- Chapter 15 core regularity hypothesis; then apply Proposition 15.2 on that Hilbert subspace
-- and transport the resulting conjugacy identity back to `H`.
/-- Theorem 15.3: (Attouch--Brézis) if `f, g ∈ Γ₀(H)` and
`0 ∈ sri (effectiveDomain f - effectiveDomain g)`, then the Fenchel conjugate of `f + g` is
`f^* □ g^*`. -/
theorem conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ := sorry

-- Proof sketch: the same reduction as above yields exactness of the infimal convolution of the
-- packaged Fenchel conjugates.
/-- Theorem 15.3: (Attouch--Brézis) under the same hypothesis, the infimal convolution of the
canonical `Γ₀(H)`-valued Fenchel conjugates is exact. -/
theorem infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    infimalConvolution.Exact (gammaZeroConjugate f hf) (gammaZeroConjugate g hg) := sorry

end AttouchBrezisTheorem

end ERealFunction
