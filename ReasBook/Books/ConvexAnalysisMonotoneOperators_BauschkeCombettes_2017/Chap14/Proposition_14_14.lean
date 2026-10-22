/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Metric

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section

variable [CompleteSpace H]

-- Proof sketch: the strict liminf inequality at infinity yields a radius beyond which
-- `f x / ‖x‖` stays above `α`, hence `f x ≥ α ‖x‖` outside a large ball. On the complementary
-- closed ball, properness of a `Γ₀(H)` function gives a finite real lower bound, which can be
-- absorbed into a global affine-norm minorant.
/-- Proposition 14.14 (1): if `f ∈ Γ₀(H)` and the liminf of `f(x) / ‖x‖` at infinity is strictly
larger than `α`, then `f` admits a global affine lower bound of slope `α`. -/
theorem exists_affine_norm_lowerBound_of_liminf_div_norm_gt
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (α : ℝ)
    (hliminf :
      (α : EReal) <
        Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop)) :
    ∃ β : ℝ,
      (fun x : H ↦ ((α * ‖x‖ + β : ℝ) : EReal)) ≤ f.asEReal := sorry

end

-- Proof sketch: Corollary 13.39 turns the global lower bound
-- `α ‖·‖ + β ≤ f` into the upper bound
-- `f∗ ≤ (fun x : H ↦ ((α * ‖x‖ + β : ℝ) : EReal))∗` by the order-reversing property of
-- Fenchel conjugation. Proposition 13.23 computes the conjugate effect of the additive constant,
-- and Example 13.3(v) identifies the conjugate of `x ↦ α ‖x‖` with the indicator of the closed
-- ball of radius `α`. This is exactly boundedness of `f*` on that ball.
/-- Proposition 14.14 (2): for `0 ≤ α`, a global affine lower bound of slope `α` is equivalent to
the Fenchel conjugate `f*` being bounded above on the closed ball `B(0; α)`. -/
theorem exists_affine_norm_lowerBound_iff_conjugate_boundedAbove_on_closedBall
    (f : H → Set.Ioi (⊥ : EReal)) (α : NNReal) :
    (∃ β : ℝ,
      (scaledNormKernel α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal) ↔
      ∃ γ : ℝ,
        ∀ u ∈ closedBall (0 : H) (α : ℝ), f.asEReal∗ u ≤ (γ : EReal) := sorry

-- Proof sketch: first convert the closed-ball boundedness of `f*` into the affine lower bound of
-- slope `α` by part (2). Dividing that pointwise estimate by `‖x‖` gives
-- `f x / ‖x‖ ≥ α + β / ‖x‖`, and the correction term tends to `0` along `‖x‖ → +∞`, so the
-- liminf is at least `α`.
/-- Proposition 14.14 (3): if `0 ≤ α` and the Fenchel conjugate `f*` is bounded
above on the closed ball `B(0; α)`, then the liminf of `f(x) / ‖x‖` at infinity is at least `α`. -/
theorem le_liminf_div_norm_of_conjugate_boundedAbove_on_closedBall
    (f : H → Set.Ioi (⊥ : EReal)) (α : NNReal)
    (hbounded :
      ∃ γ : ℝ,
        ∀ u ∈ closedBall (0 : H) (α : ℝ), f.asEReal∗ u ≤ (γ : EReal)) :
    ((α : ℝ) : EReal) ≤
      Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) := sorry

end Conjugation

end ERealFunction
