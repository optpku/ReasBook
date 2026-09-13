/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.L1.Transpose
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Dual

/-!
# Reindexed transposes on `C0Seq`

This module defines the transpose of an `L1Seq`-to-`C0Seq` map under the
canonical dual identification.
-/

public section

namespace ContinuousLinearMap

/-- The transpose of a continuous linear map from `L1Seq` to `C0Seq`, with its domain
reindexed through the canonical identification of the strong dual of `C0Seq` with `L1Seq`. -/
noncomputable def reindexedTranspose (A : L1Seq →L[ℝ] C0Seq) :
    L1Seq →L[ℝ] StrongDual ℝ L1Seq :=
  A.paperTranspose.comp C0Seq.l1ToDual.toContinuousLinearMap

/-- The reindexed transpose first identifies an `L1Seq` with its corresponding continuous
linear functional on `C0Seq`. -/
theorem reindexedTranspose_apply (A : L1Seq →L[ℝ] C0Seq) (a : L1Seq) :
    A.reindexedTranspose a = A.paperTranspose (C0Seq.dualEquivL1.symm a) := by
  -- Evaluate the composition and normalize the canonical dual identification.
  simp [reindexedTranspose, C0Seq.dualEquivL1_symm_apply]

/-- Evaluating the reindexed transpose gives the coordinatewise `C0Seq`–`L1Seq` pairing. -/
theorem reindexedTranspose_apply_apply (A : L1Seq →L[ℝ] C0Seq) (a b : L1Seq) :
    A.reindexedTranspose a b = ∑' n : ℕ, A b n * a n := by
  -- Reduce transpose evaluation to the established coordinate pairing formula.
  rw [reindexedTranspose_apply, paperTranspose_apply, C0Seq.dualEquivL1_symm_apply,
    C0Seq.l1ToDual_apply]

end ContinuousLinearMap
