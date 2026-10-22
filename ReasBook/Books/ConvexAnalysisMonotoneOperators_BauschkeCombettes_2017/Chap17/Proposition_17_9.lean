/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_33
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_56
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_7

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace Set
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section ConvexityCriterion

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Proposition 17.7 supplies the first-order route on `effectiveDomain h`.
-- For clause (ii), the source-facing second-order hypothesis is expressed pointwise through
-- Definition 2.56: at each point of `effectiveDomain h`, the finite representative of `h` is
-- twice Fréchet differentiable and every second Fréchet derivative there has nonnegative
-- quadratic form. This pointwise source clause is then bridged to the canonical second-order
-- criterion used in Proposition 17.7.
/-- Under the hypotheses of Proposition 17.9, the proper function `h` is convex on its effective
domain. The second-order clause is stated directly in the language of Definition 2.56 on
`effectiveDomain h`, rather than through a separately chosen global Hessian field. -/
theorem convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
    (h : H → Set.Ioi (⊥ : EReal)) (hdom_nonempty : (effectiveDomain h).Nonempty)
    (hopen : IsOpen (effectiveDomain h)) (hconv : Convex ℝ (effectiveDomain h))
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
    (hcriterion :
      GateauxDerivativeMonotoneOn
          (fun x ↦
            toDual ℝ H
              (gradientWithin (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x))
          (effectiveDomain h) ∨
        ∀ x ∈ effectiveDomain h,
          TwiceFrechetDifferentiableWithinAt ℝ
              (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x ∧
            ∀ A₂ : H →L[ℝ] H →L[ℝ] ℝ,
              HasSecondFrechetDerivWithinAt ℝ
                  (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x A₂ →
                ∀ z : H, 0 ≤ A₂ z z) :
    ConvexOn h (effectiveDomain h) := sorry

end ConvexityCriterion

section Proposition_17_9

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] Classical.propDecidable

variable (h : H → Set.Ioi (⊥ : EReal))
variable (hopen : IsOpen (effectiveDomain h)) (hconv : Convex ℝ (effectiveDomain h))
variable (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
variable (hcriterion :
  GateauxDerivativeMonotoneOn
      (fun x ↦
        toDual ℝ H
          (gradientWithin (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x))
      (effectiveDomain h) ∨
    ∀ x ∈ effectiveDomain h,
      TwiceFrechetDifferentiableWithinAt ℝ
          (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x ∧
        ∀ A₂ : H →L[ℝ] H →L[ℝ] ℝ,
          HasSecondFrechetDerivWithinAt ℝ
              (fun z ↦ (h z : EReal).toReal) (effectiveDomain h) x A₂ →
            ∀ z : H, 0 ≤ A₂ z z)

-- Proof sketch: apply the Chapter 9 segment-limit theorem to the canonical boundary-liminf
-- extension, use that this extension lies in `Γ₀(H)`, and compare its segment trace with the
-- original function `h` on `effectiveDomain h`.
/-- Under the hypotheses of Proposition 17.9, the canonical boundary-liminf extension recovers
the textbook boundary-segment limit formula along every segment from
`x ∈ closure (effectiveDomain h)` to a chosen point `y : effectiveDomain h`. -/
theorem tendsto_lineMap_to_boundaryLiminfExtension
    {x : H} (y : effectiveDomain h) (hx : x ∈ closure (effectiveDomain h)) :
    Filter.Tendsto
      (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
      (𝓝[>] (0 : ℝ))
      (𝓝 (boundaryLiminfExtensionEReal h x)) := sorry

-- Proof sketch: on `effectiveDomain h`, the canonical owner uses its interior branch and agrees
-- with `h`; on `closure (effectiveDomain h) \ effectiveDomain h`, the preceding segment-limit
-- theorem identifies the value with the segment liminf; and outside
-- `closure (effectiveDomain h)` the canonical extension is `+∞`.
/-- Under the hypotheses of Proposition 17.9, the canonical boundary-liminf extension is given by
the textbook segment formula determined by a chosen point `y : effectiveDomain h`. -/
theorem boundaryLiminfExtensionEReal_eq_segmentFormula
    (y : effectiveDomain h) :
    boundaryLiminfExtensionEReal h =
      fun x ↦
        if x ∈ effectiveDomain h then
          (h x : EReal)
        else if x ∈ closure (effectiveDomain h) then
          Filter.liminf
            (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        else
          ⊤ := sorry

-- Proof sketch: the convexity criterion above and differentiability-implies-continuity reduce the
-- statement to Proposition 9.33 for the boundary-liminf extension.
/-- Under the hypotheses of Proposition 17.9, the canonical boundary-liminf extension belongs to
`Γ₀(H)`. -/
theorem boundaryLiminfExtension_mem_gammaZero_of_criterion
    (hdom_nonempty : (effectiveDomain h).Nonempty) :
    boundaryLiminfExtension h
        (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
          h hdom_nonempty hopen hconv hdiff hcriterion)
        hopen
        hdiff.continuousOn ∈
      Γ₀(H) := sorry

-- Proof sketch: on `effectiveDomain h`, the boundary-liminf extension uses its interior branch,
-- so it agrees with `h` and is therefore finite.
/-- Every point of `effectiveDomain h` lies in the effective domain of the canonical
boundary-liminf extension from Proposition 17.9. -/
theorem domain_subset_effectiveDomain_boundaryLiminfExtension
    (hdom_nonempty : (effectiveDomain h).Nonempty) :
    effectiveDomain h ⊆
      effectiveDomain
        (boundaryLiminfExtension h
          (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
            h hdom_nonempty hopen hconv hdiff hcriterion)
          hopen
          hdiff.continuousOn) := sorry

-- Proof sketch: outside `closure (effectiveDomain h)`, the boundary-liminf extension is on its
-- `+∞` branch, so no such point lies in its effective domain.
/-- The effective domain of the canonical boundary-liminf extension from Proposition 17.9 is
contained in `closure (effectiveDomain h)`. -/
theorem effectiveDomain_boundaryLiminfExtension_subset_closure
    (hdom_nonempty : (effectiveDomain h).Nonempty) :
    effectiveDomain
        (boundaryLiminfExtension h
          (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
            h hdom_nonempty hopen hconv hdiff hcriterion)
          hopen
          hdiff.continuousOn) ⊆
      closure (effectiveDomain h) := sorry

-- Proof sketch: on `effectiveDomain h`, the extension is given by the interior branch of the
-- boundary-liminf construction, which is exactly `h`.
/-- On `effectiveDomain h`, the canonical boundary-liminf extension from Proposition 17.9 agrees
with the original function `h`. -/
theorem boundaryLiminfExtension_eqOn_domain
    (hdom_nonempty : (effectiveDomain h).Nonempty) :
    EqOn
      (boundaryLiminfExtension h
        (convexOn_effectiveDomain_of_gradientMonotone_or_pointwise_secondFrechet_nonnegative
          h hdom_nonempty hopen hconv hdiff hcriterion)
        hopen
        hdiff.continuousOn)
      h
      (effectiveDomain h) := sorry

end Proposition_17_9

end ERealFunction
