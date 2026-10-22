/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

universe u

/- Chapter 9 reuses two explicit mirror-descent stepsize sequences across the asymptotic-rate
items. They are not a second owner for mirror descent itself; they are source-facing named step
rules attached to the existing trajectory predicates. Keeping them in a small support owner avoids
importing a theorem file merely to reuse the canonical sequence. -/

section

/-- The predefined diminishing mirror-descent stepsize family
`t_k = √(2σ) / (L_f √(k + 1))`. -/
def mirror_descent_predefined_diminishing_stepsize (Lf σ : ℝ) : ℕ → ℝ :=
  fun k ↦ Real.sqrt (2 * σ) / (Lf * Real.sqrt ((k : ℝ) + 1))

/-- Evaluating the predefined diminishing stepsize family at iteration `k` gives the textbook
closed form `√(2σ) / (L_f √(k + 1))`. -/
@[simp] theorem mirror_descent_predefined_diminishing_stepsize_apply (Lf σ : ℝ) (k : ℕ) :
    mirror_descent_predefined_diminishing_stepsize Lf σ k =
      Real.sqrt (2 * σ) / (Lf * Real.sqrt ((k : ℝ) + 1)) := rfl

end

section

variable {E : Type u} [NormedAddCommGroup E]

/-- The adaptive mirror-descent stepsize family from Theorem 9.18: it uses the fallback bound
`L_f` when the chosen subgradient vanishes and otherwise uses the realized norm `‖g_k‖`. -/
def mirror_descent_adaptive_stepsize (Lf σ : ℝ) (g : ℕ → E) : ℕ → ℝ :=
  fun k ↦
    if _ : ‖g k‖ = 0 then
      Real.sqrt (2 * σ) / (Lf * Real.sqrt ((k : ℝ) + 1))
    else
      Real.sqrt (2 * σ) / (‖g k‖ * Real.sqrt ((k : ℝ) + 1))

/- If the chosen subgradient vanishes at iteration `k`, the adaptive stepsize rule agrees with the
fallback formula `√(2σ) / (L_f √(k + 1))`. -/
@[simp] theorem mirror_descent_adaptive_stepsize_apply_zero
    (Lf σ : ℝ) (g : ℕ → E) {k : ℕ} (hg : g k = 0) :
    mirror_descent_adaptive_stepsize Lf σ g k =
      Real.sqrt (2 * σ) / (Lf * Real.sqrt ((k : ℝ) + 1)) := by
  simp [mirror_descent_adaptive_stepsize, hg]

/- If the chosen subgradient is nonzero at iteration `k`, the adaptive stepsize rule is
`√(2σ) / (‖g_k‖ √(k + 1))`. -/
@[simp] theorem mirror_descent_adaptive_stepsize_apply_nonzero
    (Lf σ : ℝ) (g : ℕ → E) {k : ℕ} (hg : g k ≠ 0) :
    mirror_descent_adaptive_stepsize Lf σ g k =
      Real.sqrt (2 * σ) / (‖g k‖ * Real.sqrt ((k : ℝ) + 1)) := by
  have hnorm : ‖g k‖ ≠ 0 := by
    intro hzero
    exact hg (by simpa [norm_eq_zero] using hzero)
  simp [mirror_descent_adaptive_stepsize, hnorm]

end
