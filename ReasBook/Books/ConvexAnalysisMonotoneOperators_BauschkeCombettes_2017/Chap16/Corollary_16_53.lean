/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Corollary_15_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Theorem_16_47

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

/- Source/core/bridge triage:
- `source-facing`: Corollary 16.53 is the zero-function specialization of the composite
  subdifferential chain rule under the textbook regularity alternatives.
- `core/canonical`: the owner statements are
  `subdifferential_add_comp_eq_add_adjoint_image_of_regular` from Theorem 16.47 and the operator
  `adjointImageSubdifferential`.
- `bridge/view`: Corollary 15.28 supplies the source-facing regularity package for the pure
  composition case `g ∘ L`, while this corollary keeps only the specialized statement surface.
-/

-- Proof sketch: specialize Theorem 16.47 to the zero function on `H`. Its effective domain is
-- all of `H`, so the regularity hypothesis becomes the stated condition with `Set.range L`, and
-- `L '' Set.univ = Set.range L`. The subdifferential of the zero function is `{0}`, so the
-- polyhedral branch from Corollary 15.28 matches the textbook alternative, and the
-- Minkowski-sum bridge from Theorem 16.47 reduces to `adjointImageSubdifferential L g`.
/-- Corollary 16.53: if `g ∈ Γ₀(K)` and either (i)
`0 ∈ sri (effectiveDomain g - Set.range L)` or (ii) `K` is finite-dimensional, `g` has
polyhedral epigraph, and `effectiveDomain g` meets `Set.range L`, then
`∂ (g ∘ L) = L^* ∘ (∂ g) ∘ L`, realized as `adjointImageSubdifferential L g`. -/
theorem subdifferential_comp_eq_adjoint_image_of_regular
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - Set.range L) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ Set.range L).Nonempty)) :
    ∂ (g ∘ L) = adjointImageSubdifferential L g := sorry

end SubdifferentialCalculus

end ERealFunction
