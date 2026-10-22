/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Sqrt

public section

noncomputable section

namespace ProbabilityTheory

/-- Item-owned Wright--Fisher support for Exercise 26.2.1: the scalar diffusion coefficient of
`dX_t = sqrt (γ X_t (1 - X_t)) dW_t + c (θ - X_t) dt`, extended by `0` outside `[0,1]`. -/
def wrightFisherScalarDiffusionCoeff (γ : ℝ) : NNReal → ℝ → ℝ :=
  fun _ x ↦ if x ∈ Set.Icc (0 : ℝ) 1 then Real.sqrt (γ * x * (1 - x)) else 0

/-- Evaluating the Wright--Fisher scalar diffusion coefficient unfolds the defining truncation to
the unit interval. -/
theorem wrightFisherScalarDiffusionCoeff_apply
    (γ : ℝ) (t : NNReal) (x : ℝ) :
    wrightFisherScalarDiffusionCoeff γ t x =
      if x ∈ Set.Icc (0 : ℝ) 1 then Real.sqrt (γ * x * (1 - x)) else 0 := by
  simp [wrightFisherScalarDiffusionCoeff]

/-- Outside `[0,1]`, the Wright--Fisher scalar diffusion coefficient vanishes. -/
theorem wrightFisherScalarDiffusionCoeff_eq_zero_of_not_mem_unitInterval
    (γ : ℝ) {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) (t : NNReal) :
    wrightFisherScalarDiffusionCoeff γ t x = 0 := by
  simp [wrightFisherScalarDiffusionCoeff, hx]

end ProbabilityTheory
