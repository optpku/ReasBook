/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

/-- The map `x ↦ e^{2πix}` from `ℝ` to `S¹`, represented by `Real.fourierChar`, is a covering
map. -/
-- Proof sketch: identify `Real.fourierChar` with the textbook map `x ↦ Circle.exp (2 * π * x)`
-- and obtain the covering-map property from `Circle.isCoveringMap_exp` by composing with the
-- homeomorphism of `ℝ` given by multiplication by `2 * π`.
theorem real_fourierChar_isCoveringMap : IsCoveringMap Real.fourierChar := by
  -- The scaling factor `2 * π` is nonzero, so multiplication by it is a homeomorphism of `ℝ`.
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
    positivity
  -- Transfer the covering-map property of `Circle.exp` along this homeomorphism.
  simpa [Real.fourierChar_apply', Function.comp_def, smul_eq_mul] using
    Circle.isCoveringMap_exp.comp_homeomorph (Homeomorph.smulOfNeZero (2 * Real.pi) h2pi)

/-- A path in `S¹` starting at `1` starts at the same point as the canonical base lift `0 : ℝ`
through `Real.fourierChar`. -/
-- Proof sketch: use the source condition `γ.source : γ 0 = 1` and identify
-- `Real.fourierChar 0` with `1 : Circle`.
theorem circle_path_start_eq_fourierChar_zero {y : Circle} (γ : Path (1 : Circle) y) :
    γ.toContinuousMap 0 = Real.fourierChar 0 := by
  simp [γ.source]

/-- Lemma 1.5.6: every path in `S^1` starting at `1` has a unique lift to `ℝ` starting at `0`
through the covering map `Real.fourierChar x = e^{2πix}`. -/
-- Proof sketch: apply the unique lifting theorem for the covering map
-- `real_fourierChar_isCoveringMap` to the path `f`, with the prescribed initial lift `0`.
theorem existsUnique_fourierChar_lift_of_circle_path {y : Circle} (f : Path (1 : Circle) y) :
    ∃! g : C(I, ℝ), (Real.fourierChar ∘ g : I → Circle) = f ∧ g 0 = 0 := by
  have hf0 := circle_path_start_eq_fourierChar_zero f
  refine
    ⟨real_fourierChar_isCoveringMap.liftPath f.toContinuousMap 0 hf0, ?_, ?_⟩
  · constructor
    · change
        Real.fourierChar ∘ ⇑(real_fourierChar_isCoveringMap.liftPath f.toContinuousMap 0 hf0) =
          ⇑f.toContinuousMap
      exact real_fourierChar_isCoveringMap.liftPath_lifts f.toContinuousMap 0 hf0
    · exact real_fourierChar_isCoveringMap.liftPath_zero f.toContinuousMap 0 hf0
  · intro g hg
    refine (real_fourierChar_isCoveringMap.eq_liftPath_iff' hf0).2 ?_
    refine ⟨?_, hg.2⟩
    change Real.fourierChar ∘ ⇑g = ⇑f.toContinuousMap
    simpa using hg.1
