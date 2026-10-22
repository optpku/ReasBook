/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

variable (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)

/- Proposition 15.21 (1): the weak duality inequality for the composite primal-dual pair is
exactly the owner theorem already established in Proposition 15.18. -/
recall compositePrimalOptimalValue_ge_neg_compositeDualOptimalValue

-- Proof sketch: unfold `compositeDualityGap`; in the exceptional branch the gap is `0`, and in
-- the non-exceptional branch it is `μ + μ*`, which is nonnegative by clause (1).
/-- Proposition 15.21 (2): the composite duality gap lies in `[0, +∞]`, equivalently it is
nonnegative. -/
theorem compositeDualityGap_nonnegative : 0 ≤ compositeDualityGap f g L := by
  rw [compositeDualityGap_def]
  split_ifs with hExceptional
  · simp
  · by_cases hDualTop : compositeDualOptimalValue f g L = ⊤
    · have hPrimalNeBot : compositePrimalOptimalValue f g L ≠ ⊥ := by
        intro hPrimalBot
        apply hExceptional
        refine ⟨?_, Or.inl hPrimalBot⟩
        simpa [hDualTop] using hPrimalBot
      simp [hDualTop, EReal.add_top_of_ne_bot hPrimalNeBot]
    · have hDualNeBot : compositeDualOptimalValue f g L ≠ ⊥ := by
        intro hDualBot
        have hWeak := compositePrimalOptimalValue_ge_neg_compositeDualOptimalValue f g L
        have hPrimalTop : compositePrimalOptimalValue f g L = ⊤ := by
          apply le_antisymm le_top
          simpa [hDualBot] using hWeak
        exact hExceptional ⟨by simpa [hDualBot] using hPrimalTop, Or.inr hPrimalTop⟩
      have hWeak := compositePrimalOptimalValue_ge_neg_compositeDualOptimalValue f g L
      have hGapNonneg :
          0 ≤ compositePrimalOptimalValue f g L - -compositeDualOptimalValue f g L :=
        (EReal.sub_nonneg
          (Or.inr <| by simpa using hDualNeBot)
          (Or.inr <| by simpa using hDualTop)).2 hWeak
      simpa [sub_eq_add_neg, neg_neg] using hGapNonneg

-- Proof sketch: split on the exceptional branch in Definition 15.19; there the gap is
-- definitionally `0`, while in the ordinary branch `Δ = μ + μ*`, so clause (1) identifies
-- vanishing of the gap with the equality `μ = -μ*`.
/-- Proposition 15.21 (3): the equality `μ = -μ*` holds exactly when the composite duality gap
vanishes. -/
theorem compositePrimalOptimalValue_eq_neg_compositeDualOptimalValue_iff_compositeDualityGap_eq_zero
    :
    compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L ↔
      compositeDualityGap f g L = 0 := by
  rw [compositeDualityGap_def]
  by_cases hExceptional : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L ∧
      (compositePrimalOptimalValue f g L = (⊥ : EReal) ∨
        compositePrimalOptimalValue f g L = ⊤)
  · rw [if_pos hExceptional]
    simp [hExceptional.1]
  · rw [if_neg hExceptional]
    constructor
    · intro hEq
      have hPrimalNeBot : compositePrimalOptimalValue f g L ≠ ⊥ := by
        intro hPrimalBot
        exact hExceptional ⟨hEq, Or.inl hPrimalBot⟩
      have hPrimalNeTop : compositePrimalOptimalValue f g L ≠ ⊤ := by
        intro hPrimalTop
        exact hExceptional ⟨hEq, Or.inr hPrimalTop⟩
      have hZero : compositePrimalOptimalValue f g L - compositePrimalOptimalValue f g L = 0 :=
        EReal.sub_self hPrimalNeTop hPrimalNeBot
      have hDiff :
          compositePrimalOptimalValue f g L - -compositeDualOptimalValue f g L = 0 := by
        simpa [hEq] using hZero
      simpa [sub_eq_add_neg, neg_neg] using hDiff
    · intro hGap
      have hWeak := compositePrimalOptimalValue_ge_neg_compositeDualOptimalValue f g L
      have hLe : compositePrimalOptimalValue f g L ≤ -compositeDualOptimalValue f g L := by
        exact (EReal.sub_nonpos).1 <| by simpa [sub_eq_add_neg, neg_neg] using hGap.le
      exact le_antisymm hLe hWeak

end FenchelRockafellarDuality

end ERealFunction
