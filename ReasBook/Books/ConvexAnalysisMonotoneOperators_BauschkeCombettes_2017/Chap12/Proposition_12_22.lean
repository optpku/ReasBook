/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section GammaZero

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]

-- Proof sketch: combine the convexity result for `γ • f` with the standard facts
-- that properness and lower semicontinuity are preserved by multiplication by a strictly positive
-- scalar.
/-- Positive pointwise scaling by a positive real preserves membership in `Γ₀(H)`. -/
theorem smul_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    γ • f ∈ Γ₀(H) := sorry

end GammaZero

section MoreauEnvelope

variable {H : Type u} [NormedAddCommGroup H]

-- Proof sketch: unfold `moreauEnvelope_apply`, factor the positive scalar `γ` out of the defining
-- infimum, and rewrite the quadratic coefficient `1 / (2 * μ)` as `γ / (2 * (γ * μ))`.
/-- Proposition 12.22 (1): clause (i), scaling `f` by the positive real `γ` scales its
`μ`-Moreau envelope, with the envelope parameter changing from `μ` to `γμ`. -/
theorem moreauEnvelope_smul_eq_smul_moreauEnvelope
    (f : H → Set.Ioi (⊥ : EReal)) (γ μ : PosReal) :
    {}^[μ] (γ • f) = (γ : EReal) • {}^[(γ * μ)] f :=
  sorry

-- Proof sketch: expand both Moreau envelopes, exchange the two infima, and apply Corollary 2.15 to
-- compute the inner infimum of the weighted sum of squared distances.
/-- Proposition 12.22 (2): clause (ii), taking the `γ`-Moreau envelope of the `μ`-Moreau envelope
yields the `(γ + μ)`-Moreau envelope. -/
theorem iterated_moreauEnvelope_eq_moreauEnvelope_add
    (f : H → Set.Ioi (⊥ : EReal)) (γ μ : PosReal) :
    {}^[γ] ({}^[μ] f) = {}^[(γ + μ)] f := sorry

end MoreauEnvelope

end ERealFunction
