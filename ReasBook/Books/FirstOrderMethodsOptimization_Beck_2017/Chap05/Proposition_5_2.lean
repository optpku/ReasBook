/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 5.2 is `source-facing`: the mathematical object is the affine functional
`x ↦ b x + c`. The `core/canonical` owners already live upstream as Chapter 5's
`is_l_smooth_on` and mathlib's calculus API for continuous linear maps, so the derivative field is
derived directly from `ContinuousLinearMap.fderiv` and `fderiv_add_const` rather than through any
local wrapper. -/

-- Proof sketch: the Fréchet derivative of `x ↦ b x + c` is the constant map `fun _ ↦ b`, so the
-- derivative field is `0`-Lipschitz on `Set.univ`; differentiability at every point follows from
-- the standard derivative formula for continuous linear maps and addition of a constant.
/-- Proposition 5.2: every affine functional `x ↦ b x + c` on a real normed space is globally
`0`-smooth. -/
theorem is_l_smooth_affine_functional (b : E →L[ℝ] ℝ) (c : ℝ) :
    is_l_smooth_on (fun x ↦ b x + c) Set.univ 0 := by
  rw [is_l_smooth_on_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact b.differentiableAt.add_const c
  · intro x hx y hy
    simp

end
