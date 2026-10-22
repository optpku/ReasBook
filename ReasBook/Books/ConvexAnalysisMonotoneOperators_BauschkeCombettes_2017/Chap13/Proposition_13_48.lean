/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_45

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

universe u v

namespace ERealFunction

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
variable (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)

-- Proof sketch: Proposition 13.24(5) gives the universal inequality
-- `(g.asEReal ∘ L)∗ ≤ L.adjoint ▷ g.asEReal∗`, and the range-domain hypothesis is the textbook
-- regularity condition under which that infimal postcomposition has no duality gap.
/-- Proposition 13.48: if `range L` meets `effectiveDomain g`, then the Fenchel conjugate of
`g ∘ L` is the infimal postcomposition of the Fenchel conjugate of `g` along `L.adjoint`. -/
theorem conjugate_comp_eq_adjointInfimalPostcomposition
    (hdom : (range L ∩ effectiveDomain g).Nonempty) :
    (g.asEReal ∘ L)∗ = L.adjoint ▷ g.asEReal∗ := sorry

-- Proof sketch: combine Proposition 13.48 with Proposition 13.45. The range-domain hypothesis
-- gives nonemptiness of the domain of the conjugate of `L.adjoint ▷ g.asEReal∗`, so its Fenchel
-- biconjugate is its lower semicontinuous convex envelope.
/-- Proposition 13.48, range-intersection consequence: if `range L` meets `effectiveDomain g`,
then the Fenchel conjugate of `g ∘ L` is the lower semicontinuous convex envelope of the infimal
postcomposition of the Fenchel conjugate of `g` along `L.adjoint`. -/
theorem conjugate_comp_eq_lowerSemicontinuousConvexEnvelope_adjointInfimalPostcomposition
    (hdom : (range L ∩ effectiveDomain g).Nonempty) :
    (g.asEReal ∘ L)∗ =
      lowerSemicontinuousConvexEnvelope (L.adjoint ▷ g.asEReal∗) := sorry

end FenchelMoreau

end ERealFunction
