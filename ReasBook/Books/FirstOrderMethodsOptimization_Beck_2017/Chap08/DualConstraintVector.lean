/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

open WithLp (toLp)

universe u

section

variable {E : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- The coordinatewise constraint family `g i x` viewed as the Euclidean constraint vector used
by the Chapter 8 Lagrangian dual objective. -/
def dual_constraint_vector (g : Fin m → E → ℝ) : E → Λ :=
  fun x ↦ toLp 2 (fun i ↦ g i x)

/-- Evaluating `dual_constraint_vector g x` at coordinate `i` returns `g i x`. -/
@[simp] theorem dual_constraint_vector_apply
    (g : Fin m → E → ℝ) (x : E) (i : Fin m) :
    dual_constraint_vector g x i = g i x := by
  simp [dual_constraint_vector]

end
