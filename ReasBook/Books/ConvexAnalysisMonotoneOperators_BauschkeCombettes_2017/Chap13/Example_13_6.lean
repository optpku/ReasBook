/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: specialize Example 13.5 to `C = univ`, use that `univ` is nonempty and that
-- `Metric.infDist u univ = 0`, then rewrite the resulting right-hand side as `‖u‖² / 2`.
/-- Example 13.6: for `f = (1 / 2)‖·‖²`, the Fenchel conjugate `f*` equals `f`. -/
theorem fenchelConjugate_halfSquaredNorm :
    ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal)∗ =
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal := by
  have hadd :
      ((ι[(univ : Set H)] + halfSquaredNorm).asEReal) =
        (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal := by
    funext u
    simp [Function.asEReal, indicator]
  calc
    ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal)∗
        = fun u : H ↦ ((((‖u‖ ^ 2 - Metric.infDist u univ ^ 2) / 2 : ℝ) : EReal)) := by
            simpa [hadd] using
              (fenchelConjugate_indicator_add_halfSquaredNorm_eq_sqNorm_sub_sqInfDist_div_two
                (univ : Set H) Set.univ_nonempty)
    _ = fun u : H ↦ ((((‖u‖ ^ 2) / 2 : ℝ) : EReal)) := by
          funext u
          simp [Metric.infDist_zero_of_mem (by simp : u ∈ (univ : Set H))]
    _ = (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal := by
          funext u
          rw [Function.asEReal_apply, halfSquaredNorm_apply]

end

end ERealFunction
