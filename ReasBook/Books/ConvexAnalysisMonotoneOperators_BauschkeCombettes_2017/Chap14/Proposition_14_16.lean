/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use Proposition 11.12 for `(i) ↔ (ii)`. For `(ii) → (iii)`, argue by contradiction:
-- if the asymptotic quotient has nonpositive liminf, convexity lets one interpolate a bounded
-- lower-level sequence with norms tending to `+∞`. The implication `(iii) → (i)` is immediate.
-- Proposition 14.14 gives `(iii) ↔ (iv)` and the canonical equivalence between affine lower bounds
-- and boundedness of the Fenchel conjugate `f*` on closed balls around `0`, while the standard
-- local boundedness criterion for convex functions identifies boundedness of `f*` on a
-- neighborhood of `0` with `0 ∈ interior (dom f*)`.
/-- Proposition 14.16: for `f ∈ Γ₀(H)`, the following are equivalent: `f` is coercive; every real
lower level set of `f` is bounded; the asymptotic quotient `f(x) / ‖x‖` has strictly positive
liminf at infinity; `f` admits a global affine lower bound of the form `α ‖x‖ + β` with `α > 0`;
the Fenchel conjugate `f*` is bounded above on some closed ball around `0` (equivalently, on some
neighborhood of `0`); and `0` belongs to the interior of its domain. -/
theorem coercive_tfae_lowerLevelSet_asymptoticSlope_affineLowerBound_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    List.TFAE
      [Coercive f.asEReal,
        ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet f.asEReal ξ),
        ((0 : ℝ) : EReal) <
          Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
            (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop),
        ∃ α : Set.Ioi (0 : ℝ), ∃ β : ℝ,
          (scaledNormKernelOfPos α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal,
        ∃ ε : Set.Ioi (0 : ℝ), ∃ γ : ℝ,
          ∀ u : H, u ∈ Metric.closedBall (0 : H) (ε : ℝ) →
            f.asEReal∗ u ≤ (γ : EReal),
        (0 : H) ∈ interior (dom f.asEReal∗)] := sorry

end Conjugation

end ERealFunction
