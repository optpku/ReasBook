/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0

/-!
# C0Seq coordinate functionals

This module records continuity and continuous-linear-map representations of
coordinate evaluation.
-/

public section

namespace C0Seq

/-- Evaluation at a fixed coordinate is continuous on `C0Seq`. -/
theorem continuous_apply (n : ℕ) :
    Continuous (fun x : C0Seq ↦ x n) := by
  -- Control coordinate distances by the uniform distance inherited from bounded functions.
  refine LipschitzWith.continuous (LipschitzWith.mk_one fun x y ↦ ?_)
  calc
    dist (x n) (y n) = dist (x.toBCF n) (y.toBCF n) := rfl
    _ ≤ dist x.toBCF y.toBCF := BoundedContinuousFunction.dist_coe_le_dist n
    _ = dist x y := ZeroAtInftyContinuousMap.dist_toBCF_eq_dist

/-- Evaluation at a fixed coordinate as a continuous real-linear functional on `C0Seq`. -/
def evalCLM (n : ℕ) : C0Seq →L[ℝ] ℝ where
  toFun x := x n
  map_add' x y := ZeroAtInftyContinuousMap.add_apply n x y
  map_smul' c x := ZeroAtInftyContinuousMap.smul_apply c x n
  cont := continuous_apply n

/-- Applying the coordinate evaluation functional returns the selected coordinate. -/
@[simp]
theorem evalCLM_apply (n : ℕ) (x : C0Seq) : evalCLM n x = x n := by
  -- The bundled functional retains coordinate evaluation as its underlying function.
  rfl

/-- The absolute value of each coordinate of a `C0Seq` is bounded by its norm. -/
theorem abs_apply_le_norm (x : C0Seq) (n : ℕ) : |x n| ≤ ‖x‖ := by
  -- Bound the coordinate in the bounded-function model, then transport its norm back.
  calc
    |x n| = ‖x.toBCF n‖ := (Real.norm_eq_abs (x n)).symm
    _ ≤ ‖x.toBCF‖ := BoundedContinuousFunction.norm_coe_le_norm x.toBCF n
    _ = ‖x‖ := ZeroAtInftyContinuousMap.norm_toBCF_eq_norm

/-- The norm on `C0Seq` is the supremum of the absolute values of its coordinates. -/
theorem norm_eq_iSup_abs (x : C0Seq) :
    ‖x‖ = ⨆ n : ℕ, |x n| := by
  -- Expand the bounded-function norm as a coordinate supremum and normalize real norms.
  calc
    ‖x‖ = ‖x.toBCF‖ := ZeroAtInftyContinuousMap.norm_toBCF_eq_norm.symm
    _ = ⨆ n : ℕ, ‖x.toBCF n‖ := BoundedContinuousFunction.norm_eq_iSup_norm x.toBCF
    _ = ⨆ n : ℕ, |x n| := by
      congr 1

end C0Seq
