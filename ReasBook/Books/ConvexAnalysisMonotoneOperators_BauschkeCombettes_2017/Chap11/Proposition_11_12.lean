/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [SeminormedAddCommGroup H]

-- Proof sketch: if some lower level set is unbounded, choose a sequence in it with norms tending
-- to `+∞`; along that sequence the function values stay below the same real threshold, so `f` is
-- not coercive. Conversely, if every real lower level set is bounded and `‖xₙ‖ → +∞`, then for
-- each real threshold `ξ` the tail of `xₙ` eventually leaves `lowerLevelSet f ξ`, which forces
-- `f xₙ → +∞`.
/-- Proposition 11.12: an extended-real-valued function is coercive if and only if each of its
real lower level sets is bounded. -/
theorem coercive_iff_bounded_lowerLevelSet (f : H → EReal) :
    Coercive f ↔ ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet f ξ) := by
  rw [Coercive, EReal.tendsto_nhds_top_iff_real]
  constructor
  · intro hf ξ
    refine (Bornology.isBounded_def).2 ?_
    change {x : H | ¬f x ≤ (ξ : EReal)} ∈ Bornology.cobounded H
    simpa [not_le] using hf ξ
  · intro h ξ
    have hξ : (lowerLevelSet f ξ)ᶜ ∈ Bornology.cobounded H :=
      (Bornology.isBounded_def).1 (h ξ)
    change {x : H | ¬f x ≤ (ξ : EReal)} ∈ Bornology.cobounded H at hξ
    change {x : H | (ξ : EReal) < f x} ∈ Bornology.cobounded H
    simpa [not_le] using hξ

end ERealFunction
