/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

/-- Theorem 1.46 (Ekeland): on a complete metric space, a proper lower semicontinuous
extended-real-valued function that is bounded below satisfies Ekeland's variational principle.
If `y ∈ ERealFunction.dom f` and `f y ≤ α + inf f(X)` with `α ≥ 0` and `β > 0`, then there
exists `z` such that
`f z + (α / β) d(y, z) ≤ f y`, `d(y, z) ≤ β`, and
`f z < f x + (α / β) d(x, z)` for every `x ≠ z`. -/
-- Proof sketch: follow the textbook construction of the inductive minimizing sequence
-- `x₀ = y`, `xₙ₊₁ ∈ Cₙ`; use the descent inequality along the sequence to prove it is Cauchy,
-- pass to the limit `z` by completeness, apply lower semicontinuity to obtain the first
-- inequality, deduce the distance bound from the approximate minimality of `y`, and then prove
-- the strict variational inequality by contradiction using the nested sets `Cₙ`.
theorem exists_ekeland_variational_point {X : Type u} [MetricSpace X] [CompleteSpace X]
    (f : X → EReal) (hf_proper : ERealFunction.IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_bddBelow : BddBelow (Set.range f)) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) {y : X}
    (hy : y ∈ ERealFunction.dom f) (hy_approx : f y ≤ (α : EReal) + sInf (Set.range f)) :
    ∃ z : X,
      f z + ((α / β) * dist y z : ℝ) ≤ f y ∧
        dist y z ≤ β ∧
          ∀ ⦃x : X⦄, x ≠ z → f z < f x + ((α / β) * dist x z : ℝ) := sorry
