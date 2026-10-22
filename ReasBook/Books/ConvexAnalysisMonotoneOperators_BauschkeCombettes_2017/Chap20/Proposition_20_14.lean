/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

universe u v

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- `source-facing`: Proposition 20.14 is the textbook equivalence between monotonicity, the finite
-- Jensen inequality on `gra A`, and the corresponding two-point convexity statement on `gra A`.
-- `core/canonical`: Lemma 2.14 is the owner identity turning the Jensen defect of
-- `p ↦ ⟪p.1, p.2⟫_ℝ` into a weighted sum of monotonicity pairings.
-- `bridge/view`: a `ConvexOn` statement on `convexHull ℝ (gra A)` is a useful ambient reformulation
-- via `ConvexOn.map_sum_le`, but it is companion-only and not the main source-facing theorem.
-- Proof sketch: Lemma 2.14 rewrites the finite Jensen defect of the pairing on graph points as a
-- half-weighted sum of terms `⟪x i - x j, u i - u j⟫_ℝ`. Clause `(i)` makes each summand
-- nonnegative, yielding clause `(ii)`. The two-point statement in clause `(iii)` is the special
-- case of clause `(ii)`, and expanding its defect gives
-- `-α * (1 - α) * ⟪x - y, u - v⟫_ℝ`, recovering monotonicity.
/-- Proposition 20.14: for a set-valued operator `A`, the following are equivalent:
(i) `A` is monotone; (ii) the pairing `F(x, u) = ⟪x, u⟫_ℝ` satisfies the finite Jensen inequality
on graph points of `A`; (iii) `F` is convex along two-point combinations of graph points of `A`. -/
theorem tfae_isMonotone_graph_pairing_convexity (A : SetValuedOperator H H) :
    List.TFAE
      [A.IsMonotone,
        (∀ {ι : Type v} (s : Finset ι) (α : ι → ℝ) (p : ι → gra A),
          (∀ i ∈ s, 0 ≤ α i) →
            (∑ i ∈ s, α i) = 1 →
              ⟪(∑ i ∈ s, α i • (p i : H × H)).1, (∑ i ∈ s, α i • (p i : H × H)).2⟫_ℝ ≤
                ∑ i ∈ s, α i * ⟪(p i : H × H).1, (p i : H × H).2⟫_ℝ),
        (∀ ⦃p q : gra A⦄ ⦃α : ℝ⦄, 0 < α → α < 1 →
          ⟪(α • (p : H × H) + (1 - α) • (q : H × H)).1,
            (α • (p : H × H) + (1 - α) • (q : H × H)).2⟫_ℝ ≤
            α * ⟪(p : H × H).1, (p : H × H).2⟫_ℝ +
              (1 - α) * ⟪(q : H × H).1, (q : H × H).2⟫_ℝ)] := sorry

end SetValuedOperator
