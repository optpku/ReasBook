/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Remark_4_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_40

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Corollary 4.41: on a subset `D` of a real Hilbert space, `T` is firmly nonexpansive if and
only if its relaxation `x ↦ (1 - λ) • x + λ • T x` is `(λ / 2)`-averaged for `λ ∈ (0, 2)`. -/
theorem firmlyNonexpansiveOn_iff_relaxation_averagedWith {D : Set H} (T : D → H)
    {lam : ℝ} (hlam : lam ∈ Set.Ioo (0 : ℝ) 2) :
    FirmlyNonexpansiveOn D T ↔
      AveragedWith (lam / 2) (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num
  have hlam' : lam ∈ Set.Ioo (0 : ℝ) (1 / (1 / 2 : ℝ)) := by
    simpa using hlam
  calc
    FirmlyNonexpansiveOn D T ↔ AveragedWith (1 / 2 : ℝ) T := by
      exact firmlyNonexpansiveOn_iff_averagedWith_half T
    _ ↔ AveragedWith (lam * (1 / 2 : ℝ)) (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) := by
      exact averagedWith_iff_averagedWith_relaxedMap hhalf hlam'
    _ ↔ AveragedWith (lam / 2) (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) := by
      simp [div_eq_mul_inv]

end
