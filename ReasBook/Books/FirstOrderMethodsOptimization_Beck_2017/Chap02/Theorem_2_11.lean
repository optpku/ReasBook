/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: apply `geometric_hahn_banach_closed_point` to the closed convex set `C` and the
-- point `y ∉ C`, obtaining a continuous linear functional `p` and a real number `α` with
-- `p x < α < p y` for all `x ∈ C`. Choose `x₀ ∈ C`; if `p = 0`, then `0 < α < 0`, impossible, so
-- `p ≠ 0`. Finally weaken the strict inequality on `C` to `p x ≤ α`.
/-- Theorem 2.11: strict separation theorem. A nonempty closed convex set in a real inner product
space and a point outside it can be strictly separated by a nonzero continuous linear functional. -/
theorem strict_separation_closed_convex_point {C : Set E} {y : E} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hy : y ∉ C) :
    ∃ p : StrongDual ℝ E, p ≠ 0 ∧ ∃ α : ℝ, p y > α ∧ ∀ x ∈ C, p x ≤ α := by
  obtain ⟨p, α, hpC, hpy⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hy
  obtain ⟨x₀, hx₀⟩ := hC_nonempty
  refine ⟨p, ?_, α, hpy, fun x hx ↦ (hpC x hx).le⟩
  intro hp0
  have hx₀_lt : (0 : ℝ) < α := by simpa [hp0] using hpC x₀ hx₀
  have hα_lt : α < 0 := by simpa [hp0] using hpy
  exact (not_lt_of_ge hx₀_lt.le hα_lt).elim

end
