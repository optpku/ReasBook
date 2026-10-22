/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 16.56 is the textbook segment mean-value statement for subgradients.
- `core/canonical`: the owner objects are `∂ f`, `effectiveDomain f`, `openSegment ℝ x0 x1`,
  and the affine line through the endpoints, represented canonically by `line[ℝ, x0, x1]`.
- `bridge/view`: the regularity hypothesis is stated directly on that canonical line owner rather
  than through a repeated raw `affineSpan ℝ ({x0, x1} : Set H)` expression.
-/
-- Proof sketch: restrict `f` to the affine line through `x0` and `x1` via
-- `t ↦ f (AffineMap.lineMap x0 x1 t)`. The three regularity branches ensure that this one-variable
-- restriction belongs to `Γ₀(ℝ)` and has the required continuity on `[0,1]`. Apply the
-- one-dimensional minimizer argument to the auxiliary function used in the textbook proof, obtain
-- `t ∈ (0,1)` with `0 ∈ ∂h(t)`, and then rewrite `∂h(t)` through the subdifferential chain rule
-- to produce a point `x ∈ ]x0,x1[` and a subgradient `u ∈ (∂ f) x` realizing the endpoint value
-- difference.
/-- Theorem 16.56: if `f ∈ Γ₀(H)`, if `x₀` and `x₁` belong to `effectiveDomain f`, and if one of
the following holds, with the affine line `aff{x₀,x₁}` represented by the canonical owner
`line[ℝ, x₀, x₁]`: (i) `0 ∈ sri (effectiveDomain f - aff{x₀,x₁})`; (ii) `aff{x₀,x₁}` meets
`interior (effectiveDomain f)`; or (iii) `H` is finite-dimensional and `aff{x₀,x₁}` meets
`ri (effectiveDomain f)`, then the endpoint value difference `f x₁ - f x₀` is the inner product
of `x₁ - x₀` with some subgradient of `f` at a point of `]x₀,x₁[`. -/
theorem exists_subgradient_on_openSegment_eq_endpoint_value_difference_of_segment_regularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x0 x1 : H}
    (hx0 : x0 ∈ effectiveDomain f) (hx1 : x1 ∈ effectiveDomain f)
    (hregular :
      (0 : H) ∈ sri (effectiveDomain f - (line[ℝ, x0, x1] : Set H)) ∨
        ((line[ℝ, x0, x1] : Set H) ∩ interior (effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧
          ((line[ℝ, x0, x1] : Set H) ∩ ri (effectiveDomain f)).Nonempty)) :
    ∃ x ∈ openSegment ℝ x0 x1, ∃ u ∈ (∂ f) x,
      (f x1 : EReal) - (f x0 : EReal) = (⟪x1 - x0, u⟫_ℝ : EReal) := sorry

end SubdifferentialCalculus

end ERealFunction
