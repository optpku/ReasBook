/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: if `f** = f`, then `f` is a Fenchel conjugate by Definition 13.1, so
-- Proposition 13.13 puts it in `Γ(H)`. Conversely, if `f ∈ Γ(H)`, apply the supporting
-- hyperplane argument of the Fenchel--Moreau theorem to get `f ≤ f**`, then combine with
-- Proposition 13.16(i), which always gives `f** ≤ f`.
/-- Theorem 13.37: for a proper extended-real-valued function on a real Hilbert space, being lower
semicontinuous and convex, equivalently belonging to `Γ(H)`, is equivalent to coinciding with its
Fenchel biconjugate. -/
theorem mem_gamma_iff_eq_biconjugate_of_is_proper
    {f : H → EReal} (hproper : IsProper f) :
    f ∈ Γ(H) ↔ f∗∗ = f := sorry

-- Proof sketch: Theorem 13.37 identifies `f**` with `f`, so `f*` has proper conjugate. Applying
-- Proposition 13.10(iii) to `f*` therefore upgrades the properness of `f** = f` to properness of
-- `f*`.
/-- If a proper extended-real-valued function on a real Hilbert space is lower semicontinuous and
convex, equivalently lies in `Γ(H)`, then its Fenchel conjugate is proper. -/
theorem conjugate_is_proper_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    IsProper f∗ := sorry

end FenchelMoreau

end ERealFunction
