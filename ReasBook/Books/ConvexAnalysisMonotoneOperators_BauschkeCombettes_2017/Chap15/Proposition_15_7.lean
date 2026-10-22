/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Theorem_15_3

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section AttouchBrezisTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: `InfimalConvolutionRegularity` is the proposition-specific five-branch
  regularity predicate from Proposition 15.7.
- `core/canonical`: the derived conclusions should land in the existing owners
  `infimalConvolution.Exact` and `IsProper (f □ g) ∧ (f □ g) ∈ gamma H`, using the Chapter 12,
  14, and 15 regularity criteria rather than introducing a second exactness/properness wrapper.
- `bridge/view`: the five source clauses are kept literally here, and the derived API below routes
  them to the chapter owners.
-/
/-- The five source regularity alternatives from Proposition 15.7 that force exactness and
proper convexity of the infimal convolution `f □ g`. Clause (ii) uses the reflected owner
`g.asERealᵛ`. -/
def InfimalConvolutionRegularity
    (f g : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ((0 : H) ∈
      sri (dom f.asEReal∗ - dom g.asEReal∗)) ∨
    (Coercive (f.asEReal + g.asERealᵛ) ∧
      (0 : H) ∈ sri (dom f.asEReal - dom g.asERealᵛ)) ∨
    (Coercive f.asEReal ∧ BddBelow (range g)) ∨
    dom f.asEReal∗ = univ ∨
    Supercoercive f.asEReal

namespace InfimalConvolutionRegularity

-- Proof sketch: use the fifth disjunct in the definition of
-- `InfimalConvolutionRegularity`.
/-- Supercoercivity of the left summand is one of the regularity alternatives in
`InfimalConvolutionRegularity`. -/
theorem of_supercoercive
    (f g : H → Set.Ioi (⊥ : EReal))
    (hsuper : Supercoercive f.asEReal) :
    InfimalConvolutionRegularity f g := sorry

-- Proof sketch: apply the Attouch--Brezis exactness statement on the dual side under clause (i).
-- Clause (ii) reduces to clause (i) by Proposition 14.16 after identifying the reflected domain
-- difference, while clauses (iii)--(v) imply the needed dual regularity through Propositions 14.15
-- and 14.16.
/-- Proposition 15.7 (1): under any of the five source regularity alternatives, the infimal
convolution `f □ g` is exact. -/
theorem exact
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hreg : InfimalConvolutionRegularity f g) :
    infimalConvolution.Exact f g := sorry

-- Proof sketch: combine exactness from Proposition 15.7 (1) with the Attouch--Brezis
-- identification of `f □ g` as a conjugate of a pointwise sum on the dual side. Theorem 15.3 and
-- Fenchel--Moreau then give lower semicontinuity and convexity, and properness is recovered from
-- the same dual representation.
/-- Proposition 15.7 (2): under the same regularity alternatives, the infimal convolution `f □ g`
is proper, convex, and lower semicontinuous. In the project's unbundled API, this is expressed as
`IsProper (f □ g)` together with membership of `f □ g` in `γ(H)`, which is the canonical form of
`f □ g ∈ Γ₀(H)` before repackaging into `]-∞,+∞]`-valued form. -/
theorem isProper_and_mem_gamma
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hreg : InfimalConvolutionRegularity f g) :
    IsProper (f □ g) ∧ (f □ g) ∈ gamma H := sorry

end InfimalConvolutionRegularity

end AttouchBrezisTheorem

end ERealFunction
