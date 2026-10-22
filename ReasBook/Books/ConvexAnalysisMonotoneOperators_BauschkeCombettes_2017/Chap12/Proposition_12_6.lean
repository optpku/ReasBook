/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace
open ERealFunction

universe u

namespace ERealFunction

section Domain

variable {H : Type u} [AddGroup H]

/-- Proposition 12.6 (ii): for extended-real-valued functions that never take the value `-∞`, the
domain of the infimal convolution is the Minkowski sum of the domains. -/
-- Proof sketch: rewrite `(f □ g) x` as an infimum over decompositions `x = y + z`. A finite
-- decomposition shows `x ∈ dom (f □ g)`, while a finite infimal-convolution value together with the
-- no-`⊥` hypotheses yields a decomposition with both summands in the corresponding domains.
theorem dom_infimalConvolution
    (f g : H → Set.Ioi (⊥ : EReal)) :
    dom (f □ g) =
      effectiveDomain f + effectiveDomain g := sorry

end Domain

section Commutative

variable {H : Type u} [AddCommGroup H]

/-- Proposition 12.6 (iii): infimal convolution is commutative. -/
-- Proof sketch: reindex the infimum by swapping a decomposition `x = y + z` with `x = z + y`.
theorem infimalConvolution_comm (f g : H → EReal) :
    infimalConvolution f g = infimalConvolution g f := sorry

end Commutative

section AffineMinorants

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 12.6 (i): if `f` and `g` admit continuous affine minorants with slope `u`, then
their infimal convolution admits one with the same slope. -/
-- Proof sketch: combine the two affine lower bounds in the defining infimum
-- `(f □ g) x = inf_y (f y + g (x - y))` to obtain the affine lower bound
-- `⟪x, u⟫ + η + μ`.
theorem hasContinuousAffineMinorantWithSlope_infimalConvolution
    (f g : H → EReal) (u : H)
    (hf : HasContinuousAffineMinorantWithSlope f u)
    (hg : HasContinuousAffineMinorantWithSlope g u) :
    HasContinuousAffineMinorantWithSlope (f □ g) u := sorry

/-- Under the hypotheses of Proposition 12.6 (i), the infimal convolution never attains `-∞`. -/
-- Proof sketch: apply Proposition 12.6 (i) to get a continuous affine minorant of `f □ g`, then
-- evaluate that minorant at `x` to bound `(f □ g) x` strictly above `⊥`.
theorem infimalConvolution_ne_bot_of_hasContinuousAffineMinorantWithSlope
    (f g : H → EReal) (u : H)
    (hf : HasContinuousAffineMinorantWithSlope f u)
    (hg : HasContinuousAffineMinorantWithSlope g u) (x : H) :
    (f □ g) x ≠ ⊥ := sorry

/-- Proposition 12.6 (iv): if `f`, `g`, and `h` admit continuous affine minorants with the same
slope, then infimal convolution is associative on `f`, `g`, and `h`. -/
-- Proof sketch: part (i) gives affine minorants for `g □ h` and `f □ g`, so both iterated
-- infimal convolutions are well defined. Then rewrite both sides as the infimum of
-- `f u + g v + h w` over triples satisfying `u + v + w = x`.
theorem infimalConvolution_assoc_of_commonSlopeMinorants
    (f g h : H → EReal) (u : H)
    (hf : HasContinuousAffineMinorantWithSlope f u)
    (hg : HasContinuousAffineMinorantWithSlope g u)
    (hh : HasContinuousAffineMinorantWithSlope h u) :
    infimalConvolution f (infimalConvolution g h) =
      infimalConvolution (infimalConvolution f g) h := sorry

end AffineMinorants

end ERealFunction
