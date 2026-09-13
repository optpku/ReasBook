/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import RockafellarSum_2026.ReasLib.Analysis.Sequence.L1

/-!
# Paper transposes on `L1Seq`

This module defines precomposition transposes of continuous maps out of the
real summable-sequence space.
-/

public section

universe u v

namespace ContinuousLinearMap

/-- The transpose of a continuous linear map from `L1Seq`, defined by precomposition on
continuous linear functionals. -/
noncomputable def paperTranspose {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : L1Seq →L[ℝ] E) : StrongDual ℝ E →L[ℝ] StrongDual ℝ L1Seq :=
  ContinuousLinearMap.precomp ℝ T

/-- Evaluating the transpose of a continuous linear map amounts to precomposing the
functional with that map. -/
@[simp]
theorem paperTranspose_apply {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : L1Seq →L[ℝ] E) (φ : StrongDual ℝ E) (a : L1Seq) :
    T.paperTranspose φ a = φ (T a) := by
  -- Unfolding precomposition reduces evaluation to ordinary function composition.
  rfl

end ContinuousLinearMap
