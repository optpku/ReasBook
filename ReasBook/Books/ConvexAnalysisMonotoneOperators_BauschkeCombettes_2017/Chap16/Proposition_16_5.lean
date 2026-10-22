/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_60

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section BiconjugationAndSubdifferentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (x : H)

-- Proof sketch: choose a subgradient `u ∈ (∂ f) x`. The supporting affine minorant through
-- `(x, f x)` shows that `f.asEReal` admits a continuous affine minorant, so
-- Proposition 13.45 identifies its biconjugate with the lower semicontinuous convex envelope.
-- Proposition 16.4 gives lower semicontinuity at `x`, and Corollary 9.10 together with
-- Lemma 1.32 turns that local lower semicontinuity into the pointwise equality
-- `f** x = f x`.
/-- Proposition 16.5 (1): if an `]-∞,+∞]`-valued function is subdifferentiable at `x`, then its
Fenchel biconjugate agrees with `f` at `x`. -/
theorem biconjugate_eq_self_at_of_subdifferentiableAt
    (hxsub : SubdifferentiableAt f x) :
    f.asEReal∗∗ x = f.asEReal x := sorry

-- Proof sketch: Proposition 16.4 gives lower semicontinuity of `f` at `x`, and
-- `SubdifferentiableAt.mem_effectiveDomain` makes `f x` finite above. The biconjugate is convex,
-- and clause (1) identifies its value at `x` with the finite value `f x`. The upstream Chapter 13
-- owner theorem `biconjugate_isProper_of_lscAt_of_convex_at_finite_point` is the correct
-- properness bridge once the needed local lower-semicontinuity and convexity hypotheses have been
-- established at `x`.
-- Proof sketch: choose `u ∈ (∂ f) x` from `hxsub`. Proposition 16.10 applied to `f` identifies
-- `x ∈ ∂ f* u`, and applying it again to the packaged Fenchel conjugate identifies
-- `u ∈ ∂ f** x`. Clause (1) supplies the pointwise equality `f** x = f x`, so the
-- Fenchel--Young equalities for `f` and `f**` coincide at `x`.
/-- Proposition 16.5 (2): if an `]-∞,+∞]`-valued function is subdifferentiable at `x`, then the
subdifferential of the Fenchel biconjugate `f^{**}` at `x` coincides with the subdifferential of
`f` at `x`. -/
theorem biconjugate_subdifferential_eq_subdifferential_at_of_subdifferentiableAt
    (hxsub : SubdifferentiableAt f x) :
    (∂ (f.asEReal∗∗)) x = (∂ f) x := sorry

end BiconjugationAndSubdifferentials

end ERealFunction
