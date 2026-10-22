/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Corollary_9_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Lemma 1.32 rewrites lower semicontinuity at `x` as
-- `lowerSemicontinuousEnvelope f x = f x`, while Corollary 9.10 identifies
-- `lowerSemicontinuousConvexEnvelope f` with `lowerSemicontinuousEnvelope f` for convex `f`.
/-- Proposition 13.44, clause `(i)`: for a convex extended-real-valued function, lower
semicontinuity at `x` is equivalent to the lower semicontinuous convex envelope agreeing with `f`
at `x`. -/
theorem lscAt_iff_lowerSemicontinuousConvexEnvelope_eq_self_of_convex
    {f : H → EReal} (hconv : IsConvex f) {x : H} :
    LowerSemicontinuousAt f x ↔ lowerSemicontinuousConvexEnvelope f x = f x := sorry

-- Proof sketch: Lemma 1.32 rewrites lower semicontinuity at `x` as
-- `lowerSemicontinuousEnvelope f x = f x`, Corollary 9.10 identifies
-- `lowerSemicontinuousConvexEnvelope f` with `lowerSemicontinuousEnvelope f` for convex `f`,
-- and membership of `x` in `effectiveDom f` gives the needed finite-point hypothesis.
/-- Proposition 13.44, clause `(ii)`: for a convex extended-real-valued function on a real
Hilbert space, at a point `x` of the effective domain lower semicontinuity is equivalent to the
textbook chain `f∗∗ x = lowerSemicontinuousConvexEnvelope f x =
lowerSemicontinuousEnvelope f x = f x`. -/
theorem lscAt_iff_biconjugate_chain_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f) :
    LowerSemicontinuousAt f x ↔
      f∗∗ x = lowerSemicontinuousConvexEnvelope f x ∧
        lowerSemicontinuousConvexEnvelope f x = lowerSemicontinuousEnvelope f x ∧
        lowerSemicontinuousEnvelope f x = f x := sorry

-- Proof sketch: clause `(ii)` already contains the full pointwise chain, so clause `(iii)` is its
-- endpoint equality.
/-- Proposition 13.44, clause `(iii)`: for a convex extended-real-valued function on a real
Hilbert space, at a point `x` of the effective domain the function is lower semicontinuous if and
only if its Fenchel biconjugate agrees with `f` at `x`. -/
theorem lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f) :
    LowerSemicontinuousAt f x ↔ f∗∗ x = f x := sorry

-- Proof sketch: clause `(iii)` provides a finite point of `f∗∗`, Proposition 13.13 places
-- `f∗∗` in `Γ(H)`, and Proposition 9.6 rules out the `⊥` branch globally for any member of
-- `Γ(H)` that is finite somewhere.
/-- Companion bridge: under the hypotheses of Proposition 13.44, the Fenchel biconjugate is a
proper extended-real-valued function. -/
theorem biconjugate_isProper_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    IsProper (f∗∗) := sorry

-- Proof sketch: apply the generic implication `Γ(H) → Γ₀(H)` for proper functions to the
-- canonical Chapter 9 owner `properIoi` of the proper function `f∗∗`.
/-- Companion bridge: the canonical `Γ₀(H)`-valued representative of the Fenchel biconjugate
belongs to `Γ₀(H)` under the hypotheses of Proposition 13.44. -/
theorem biconjugate_mem_gammaZero_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    properIoi (f∗∗)
      (biconjugate_isProper_of_lscAt_of_convex_at_finite_point hconv hx hlsc) ∈ Γ₀(H) := sorry

-- Proof sketch: clause `(ii)` supplies the pointwise chain
-- `f∗∗ x = lowerSemicontinuousConvexEnvelope f x = lowerSemicontinuousEnvelope f x = f x`,
-- Proposition 13.16 gives `f∗∗ ≤ f`, and Proposition 13.13 places `f∗∗` in `Γ(H)`. Since the
-- value at `x` lies in the effective domain, Proposition 9.6 rules out the `⊥` branch for `f∗∗`,
-- yielding the Chapter 9 owner-level conclusion that the packaged biconjugate belongs to
-- `Γ₀(H)`.
/-- Proposition 13.44, moreover: if a convex extended-real-valued function is lower
semicontinuous at a point `x` of the effective domain, then globally
`f ≥ lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f = f∗∗`, and the
canonical `Γ₀(H)`-valued representative `properIoi (f∗∗)
(biconjugate_isProper_of_lscAt_of_convex_at_finite_point hconv hx hlsc)` of `f∗∗` belongs to
`Γ₀(H)`. -/
theorem convexEnvelope_hull_biconjugate_chain_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    f∗∗ ≤ f ∧
      lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f ∧
      lowerSemicontinuousEnvelope f = f∗∗ ∧
      properIoi (f∗∗)
        (biconjugate_isProper_of_lscAt_of_convex_at_finite_point hconv hx hlsc) ∈ Γ₀(H) := sorry

end Conjugation

end ERealFunction
