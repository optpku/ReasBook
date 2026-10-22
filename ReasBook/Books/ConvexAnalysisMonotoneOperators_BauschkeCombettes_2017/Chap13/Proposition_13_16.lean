/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply `fenchel_young_inequality` with the outer conjugation variable in place of
-- `u`, then take the supremum over the primal variable to show each value of `f∗∗` is bounded
-- above by the corresponding value of `f`.
/-- Proposition 13.16 (1): clause (i). Every extended-real-valued function dominates its
biconjugate. -/
theorem biconjugate_le (f : H → EReal) :
    f∗∗ ≤ f := sorry

-- Proof sketch: compare the defining suprema of `f∗` and `g∗`. If `f ≤ g`, then each affine
-- defect `⟪x, u⟫ - g x` is bounded above by `⟪x, u⟫ - f x`, so taking suprema reverses the
-- order.
/-- Proposition 13.16 (2): clause (ii), first conclusion. Fenchel conjugation reverses the
pointwise order on extended-real-valued functions. -/
theorem conjugate_antitone :
    Antitone (conjugate : (H → EReal) → H → EReal) := sorry

-- Proof sketch: apply `conjugate_antitone` twice, first to `f ≤ g` and then to the induced
-- inequality `g∗ ≤ f∗`.
/-- Proposition 13.16 (3): clause (ii), second conclusion. Taking biconjugates preserves the
pointwise order. -/
theorem biconjugate_mono :
    Monotone (fun f : H → EReal ↦ f∗∗) := sorry

-- Proof sketch: `biconjugate_le (f := f∗)` gives `f∗∗∗ ≤ f∗`, while `conjugate_antitone`
-- applied to `biconjugate_le (f := f)` yields the reverse inequality `f∗ ≤ f∗∗∗`.
/-- Proposition 13.16 (4): clause (iii). The triple Fenchel conjugate of a function equals its
single conjugate. -/
theorem triple_conjugate_eq_conjugate
    (f : H → EReal) :
    f∗∗∗ = f∗ := sorry

-- Proof sketch: `conjugate_mem_gamma` places `f∗` in `gamma H`, and Proposition 9.8 identifies
-- `lowerSemicontinuousConvexEnvelope f` as the largest lower semicontinuous convex minorant of
-- `f`. Hence `biconjugate_le f` and `lowerSemicontinuousConvexEnvelope_le f` give
-- `f∗∗ ≤ lowerSemicontinuousConvexEnvelope f ≤ f`, and `conjugate_antitone` together with
-- `triple_conjugate_eq_conjugate` forces the conjugates of `f` and of its envelope to coincide.
/-- Proposition 13.16 (5): clause (iv). Passing to the lower semicontinuous convex envelope does
not change the Fenchel conjugate. -/
theorem conjugate_lowerSemicontinuousConvexEnvelope_eq
    (f : H → EReal) :
    (lowerSemicontinuousConvexEnvelope f)∗ = f∗ := sorry

end Conjugation

end ERealFunction
