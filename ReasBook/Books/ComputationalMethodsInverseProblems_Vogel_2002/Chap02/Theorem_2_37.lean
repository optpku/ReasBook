/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

public section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 2.37. The source states this for Fréchet-differentiable `J`, but the
conclusion already follows from `IsLocalMin J fStar` because `gradient` is defined
from `fderiv`, which is `0` at a local minimizer by Fermat's theorem. -/
theorem gradient_eq_zero_of_isLocalMin (J : H → ℝ) {fStar : H}
    (hmin : IsLocalMin J fStar) :
    gradient J fStar = 0 := by
  apply (InnerProductSpace.toDual ℝ H).injective
  rw [toDual_gradient, hmin.fderiv_eq_zero, map_zero]
