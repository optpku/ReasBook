/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 6.8 is `source-facing`: the new owner here is the Huber loss itself. The chapter's
canonical smoothing-parameter owner is `PosReal` from Definition 6.7, so the Huber owner should
use that positive parameter directly rather than a bare real together with a separate positivity
proof. Although the text states the Euclidean formula, the defining expression only depends on
the norm, so the ambient abstraction level stays at the chapter's canonical normed-additive-space
layer rather than a coordinate model such as `ℝ^n`. -/

/-- Definition 6.8: for a positive smoothing parameter `μ`, the Huber function is the radial
piecewise function that equals `(1 / (2 * μ)) ‖x‖²` on the closed ball `‖x‖ ≤ μ` and
`‖x‖ - μ / 2` outside that ball. -/
def huber_function (μ : PosReal) : E → ℝ :=
  fun x ↦ if ‖x‖ ≤ μ then (1 / (2 * μ)) * ‖x‖ ^ (2 : ℕ) else ‖x‖ - μ / 2

@[inherit_doc] notation "H[" μ "]" => huber_function μ

-- Proof sketch: unfold `huber_function`; the displayed piecewise formula is exactly the defining
-- expression.
/-- Evaluating the Huber function at `x` gives its defining piecewise radial formula. -/
@[simp] theorem huber_function_apply (μ : PosReal) (x : E) :
    H[μ] x =
      if ‖x‖ ≤ μ then (1 / (2 * μ)) * ‖x‖ ^ (2 : ℕ) else ‖x‖ - μ / 2 :=
  rfl

-- Proof sketch: extensionality reduces the equality of functions to
-- `huber_function_apply` at each point.
/-- The notation `H[μ]` denotes the Huber function with parameter `μ`, written in its defining
piecewise radial form. -/
@[simp] theorem huber_function_def (μ : PosReal) :
    (H[μ] : E → ℝ) =
      fun x ↦ if ‖x‖ ≤ μ then (1 / (2 * μ)) * ‖x‖ ^ (2 : ℕ) else ‖x‖ - μ / 2 :=
  rfl

-- Proof sketch: in the branch `‖x‖ ≤ μ`, the defining `if` in `huber_function_apply` simplifies
-- by `if_pos hx`.
/-- On the closed ball `‖x‖ ≤ μ`, the Huber function agrees with its quadratic branch. -/
theorem huber_function_of_norm_le (μ : PosReal) {x : E} (hx : ‖x‖ ≤ μ) :
    H[μ] x = (1 / (2 * μ)) * ‖x‖ ^ (2 : ℕ) := by
  simp [huber_function, hx]

-- Proof sketch: in the branch `μ < ‖x‖`, the defining `if` in `huber_function_apply`
-- simplifies by `if_neg hx.not_le`.
/-- Outside the closed ball `‖x‖ ≤ μ`, the Huber function agrees with its affine branch. -/
theorem huber_function_of_mu_lt_norm (μ : PosReal) {x : E} (hx : μ < ‖x‖) :
    H[μ] x = ‖x‖ - μ / 2 := by
  simp [huber_function, not_le_of_gt hx]

end
