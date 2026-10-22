/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u

namespace ERealFunction

section ProximalAverage

variable {H : Type u} [NormedAddCommGroup H] [Module ℝ H]

-- Proof sketch: Corollary 14.8(ii) identifies the conjugate of `pav(f, g)` with the proximal
-- average of two `Γ₀(H)` functions, so taking the conjugate again and using
-- Corollary 13.38 gives `(pav(f, g))** = pav(f, g)`. Proposition 14.7(4) and Proposition 13.13
-- then show that its canonical Chapter 9 representative `properIoi (pav(f, g))
-- (isProper_proximalAverage f g hf hg)` lies in `Γ₀(H)`.
/-- Corollary 14.8 (1): if `f, g ∈ Γ₀(H)`, then the proximal average `pav(f, g)`, viewed as a
`]-∞, +∞]`-valued function, also belongs to `Γ₀(H)`. -/
theorem proximalAverage_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg) ∈ Γ₀(H) := sorry

end ProximalAverage

section ProximalAverageConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: rewrite `pav(f, g)` as `Θ(f, g) - q`, compute the conjugate of `Θ(f, g)` by the
-- conjugation rules for scaling, composition with `2 • id`, and infimal convolution with the
-- quadratic kernel, and then compare the result with the same decomposition of `pav(f*, g*)`.
/-- Corollary 14.8 (2): the Fenchel conjugate of the proximal average is the proximal average of
the Fenchel conjugates. -/
theorem gammaZeroConjugate_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g)∗ =
      pav(gammaZeroConjugate f hf, gammaZeroConjugate g hg) := sorry

end ProximalAverageConjugation

section ProximalAverageMoreauDecomposition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply clause (2), then use the unit-parameter case of the Moreau-envelope
-- identity from Proposition 14.1 to rewrite the unit Moreau envelope of `pav(f, g)` and of the
-- two conjugates with the quadratic kernel `q(x) = ‖x‖² / 2`.
/-- Corollary 14.8 (3): the unit Moreau envelope of the proximal average, equivalently its
infimal convolution with `q(x) = (1 / 2) ‖x‖²`, equals the arithmetic mean of the corresponding
unit Moreau envelopes of `f` and `g`. -/
theorem proximalAverage_infimalConvolution_unitMoreauQuadraticKernel
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    ({}^[(1 : PosReal)] (pav(f, g))) =
      fun x : H ↦
        ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] f) x +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] g) x := sorry

-- Proof sketch: use the standard identity `Prox_h = ∇ (h* □ q)` for `h ∈ Γ₀(H)`, apply it to
-- `h = pav(f, g)`, insert clause (3), and then differentiate the affine combination pointwise.
/-- Corollary 14.8 (4): the proximity operator of the proximal average is the arithmetic mean of
the proximity operators of `f` and `g`. -/
theorem proximityOperator_proximalAverage_eq_arithmeticMean
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    Prox[
      properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg),
      proximalAverage_mem_gammaZero f g hf hg] =
      fun x : H ↦
        (1 / 2 : ℝ) • Prox[f, hf] x +
          (1 / 2 : ℝ) • Prox[g, hg] x := sorry

end ProximalAverageMoreauDecomposition

end ERealFunction
