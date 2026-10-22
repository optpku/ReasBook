/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

noncomputable section

namespace ERealFunction

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_innerProductSpace_l2

section SubdifferentialAndEpigraphNormalCone

-- Proof sketch: the epigraph normal-cone computation gives `(i) ↔ (ii)`, and convexity of `f`
-- identifies that criterion with equality in the Fenchel--Young identity `(iii)`. The
-- proper-conjugate clause `(iv)` is the downstream bridge owned by Proposition 16.10, so it is
-- recorded separately below only in the source direction `(iii) → (iv)`.
/-- Proposition 16.16, clauses (i)-(iii): for a convex `]-∞,+∞]`-valued function, the following
are equivalent: `u ∈ ∂ f x`, `(u, -1)` lies in the normal cone to the real-height epigraph of `f`
at `(x, f x)`, and equality holds in the Fenchel--Young identity
`f(x) + f^*(u) = ⟪x, u⟫`. -/
theorem subdifferential_normalCone_fenchelYoung_tfae
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (x u : H) :
    List.TFAE
      [u ∈ (∂ f) x,
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal),
        (f x : EReal) + f.asEReal∗ u =
          ((⟪x, u⟫_ℝ : ℝ) : EReal)] := sorry

/-- Proposition 16.16, clause (iv): under the properness hypothesis encoded by `hdom`,
Fenchel--Young equality implies that `x` lies in the subdifferential of the packaged Fenchel
conjugate `properConjugateIoi f hdom` at `u`. -/
theorem mem_subdifferential_properConjugateIoi_of_fenchel_young_eq
    (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) (x u : H)
    (hfy : (f x : EReal) + f.asEReal∗ u =
      ((⟪x, u⟫_ℝ : ℝ) : EReal)) :
    x ∈ (∂ (properConjugateIoi f hdom).asEReal) u :=
  (mem_subdifferential_properConjugateIoi_iff_fenchel_young_eq f hdom x u).2 hfy

/-- Companion to Proposition 16.16: the subdifferential criterion is equivalent to the epigraph
normal-cone criterion. -/
theorem mem_subdifferential_iff_mem_normalCone_epigraph
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (x u : H) :
    u ∈ (∂ f) x ↔
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) :=
  (subdifferential_normalCone_fenchelYoung_tfae f hconv x u).out 0 1

end SubdifferentialAndEpigraphNormalCone

end ERealFunction
