/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

public section

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A gradient witness identifies the line derivative of `J` at `f` in direction `h`
with `inner ℝ g h`. -/
theorem HasGradientAt.hasLineDerivAt {J : H → ℝ} {f g : H} (hJ : HasGradientAt J g f) (h : H) :
    HasLineDerivAt ℝ J (inner ℝ g h) f h := by
  simpa [hJ.fderiv_apply] using hJ.hasFDerivAt.hasLineDerivAt h

/-- Proposition 2.34. If `J : H → ℝ` is Fréchet differentiable at `f`, then for every
`h : H` the map `τ ↦ J (f + τ • h)` is differentiable at `0` with derivative
`inner ℝ (gradient J f) h`. -/
theorem hasDerivAt_line_inner_gradient (J : H → ℝ) (f h : H)
    (hJ : DifferentiableAt ℝ J f) :
    HasDerivAt (fun τ : ℝ ↦ J (f + τ • h)) (inner ℝ (gradient J f) h) 0 := by
  simpa [HasLineDerivAt] using hJ.hasGradientAt.hasLineDerivAt h

/-- Under differentiability at `f`, the line derivative of `J` in direction `h` is
`inner ℝ (gradient J f) h`. -/
theorem lineDeriv_eq_inner_gradient (J : H → ℝ) (f h : H)
    (hJ : DifferentiableAt ℝ J f) :
    lineDeriv ℝ J f h = inner ℝ (gradient J f) h := by
  simpa using (hJ.hasGradientAt.hasLineDerivAt h).lineDeriv
