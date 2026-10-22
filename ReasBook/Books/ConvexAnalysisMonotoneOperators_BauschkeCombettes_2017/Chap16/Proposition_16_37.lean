/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

open Set
open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))

local notation "f⋆" => gammaZeroConjugate f hf

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.37 is the segment-affineness statement for the Fenchel conjugate.
- `core/canonical`: the owner objects are `gammaZeroConjugate f hf`, `effectiveDomain`, and the
  subdifferential `∂ f`.
- `bridge/view`: the real-valued trace `u ↦ (f⋆ u : EReal).toReal` is used only after explicit
  finiteness on the whole segment, so the public statement does not silently collapse `⊤` via
  `EReal.toReal`.
-/

-- Proof sketch: if every point of the closed segment lies in `(∂ f) x`, then Theorem 16.29 gives
-- Fenchel--Young equality at each point of that segment. Evaluating this equality along the
-- parameterization `AffineMap.lineMap u0 u1` shows that the conjugate values coincide with the
-- affine interpolation of their endpoint values on `Set.Icc (0 : ℝ) 1`.
/-- Proposition 16.37 (1): if the whole segment `[u₀,u₁]` lies in the subdifferential `∂ f(x)`,
then the Fenchel conjugate `f*`, represented by `gammaZeroConjugate f hf`, is finite on that
segment, and its finite-valued trace is affine there. In Lean, the affineness clause is expressed
by equality with the affine interpolation of the endpoint values along the line-map
parameterization of `[u₀,u₁]`, after recording the needed effective-domain control explicitly. -/
theorem gammaZeroConjugate_eq_lineMap_on_segment_of_segment_subset_subdifferential
    (x u0 u1 : H) (hseg : segment ℝ u0 u1 ⊆ (∂ f) x) :
    segment ℝ u0 u1 ⊆ effectiveDomain f⋆ ∧
      EqOn
        (fun α : ℝ ↦ (f⋆ (AffineMap.lineMap u0 u1 α) : EReal).toReal)
        (AffineMap.lineMap
          ((f⋆ u0 : EReal).toReal)
          ((f⋆ u1 : EReal).toReal))
        (Icc (0 : ℝ) 1) := sorry

-- Proof sketch: choose an interior point `u` on `]u₀,u₁[` with `x ∈ ∂ f*(u)` from the image
-- hypothesis. Theorem 16.29 rewrites this as Fenchel--Young equality at `u`. Affineness of `f*`
-- on the closed segment then forces the same equality at the endpoints `u₀` and `u₁`, so
-- Theorem 16.29 yields `u₀, u₁ ∈ (∂ f) x`. Finally, Proposition 16.4 gives convexity of
-- `(∂ f) x`, hence the whole closed segment lies in `(∂ f) x`.
/-- Proposition 16.37 (2): if the Fenchel conjugate `f*`, represented by `gammaZeroConjugate f hf`,
is finite on `[u₀,u₁]`, its finite-valued trace is affine there, and `x` belongs to the image of
the open segment `]u₀,u₁[` under `∂ f*`, then the entire segment `[u₀,u₁]` is contained in
`∂ f(x)`. -/
theorem segment_subset_subdifferential_of_eq_lineMap_on_segment_of_mem_image_openSegment
    (x u0 u1 : H)
    (hfin : segment ℝ u0 u1 ⊆ effectiveDomain f⋆)
    (haff :
      EqOn
        (fun α : ℝ ↦ (f⋆ (AffineMap.lineMap u0 u1 α) : EReal).toReal)
        (AffineMap.lineMap
          ((f⋆ u0 : EReal).toReal)
          ((f⋆ u1 : EReal).toReal))
        (Icc (0 : ℝ) 1))
    (hint : x ∈ SetValuedOperator.image (∂ f⋆) (openSegment ℝ u0 u1)) :
    segment ℝ u0 u1 ⊆ (∂ f) x := sorry

end SubdifferentialConjugation

end ERealFunction
