/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Lemma_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped unitInterval

/-- Lemma 1.5.7: homotopic loops in `S¹` based at `1` have canonical lifts through
`Real.fourierChar : ℝ → S¹` starting at `0`, and these lifts end at the same point of `ℝ`. -/
-- Proof sketch: unpack `γ₀.Homotopic γ₁` as an endpoint-fixed homotopy of continuous maps and
-- apply `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` to the covering map
-- `real_fourierChar_isCoveringMap` with initial lift `0`.
theorem fourierChar_lift_endpoint_eq_of_homotopic_loops
    (γ₀ γ₁ : Path (1 : Circle) 1) (h : γ₀.Homotopic γ₁) :
    real_fourierChar_isCoveringMap.liftPath γ₀.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ₀) 1 =
      real_fourierChar_isCoveringMap.liftPath γ₁.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ₁) 1 := by
  obtain ⟨H⟩ := h
  exact real_fourierChar_isCoveringMap.liftPath_apply_one_eq_of_homotopicRel ⟨H⟩ 0
    (circle_path_start_eq_fourierChar_zero γ₀) (circle_path_start_eq_fourierChar_zero γ₁)
