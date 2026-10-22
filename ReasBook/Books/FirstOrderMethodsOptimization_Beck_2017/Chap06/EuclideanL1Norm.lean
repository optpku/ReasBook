/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

noncomputable section

open WithLp (toLp)
open scoped BigOperators

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

namespace EuclideanSpace

/-- The Euclidean `ℓ¹` norm on a finite product, specializing to `ℝ^n` when `ι = Fin n`. -/
abbrev l1Norm (x : E) : ℝ :=
  ‖toLp 1 fun i ↦ x i‖

/-- The Euclidean `ℓ¹` norm is the finite sum of the coordinate absolute values. -/
@[simp] theorem l1Norm_eq_sum_abs (x : E) :
    l1Norm x = ∑ i, |x i| := by
  rw [l1Norm, PiLp.norm_eq_sum]
  · simp
  · norm_num

end EuclideanSpace

/-- Textbook notation for the Euclidean `ℓ¹` norm on a finite product. -/
notation "‖" x "‖₁" => EuclideanSpace.l1Norm x

end
