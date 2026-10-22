/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section

namespace SpectralFilter

/-- The TSVD scalar filter `w_α(λ)` keeps the spectral component when `α ≤ λ`
and truncates it otherwise. -/
@[expose]
def tsvd (α lam : ℝ) : ℝ :=
  if α ≤ lam then 1 else 0

/-- The Tikhonov scalar filter `w_α(λ) = λ / (α + λ)`. -/
@[expose]
def tikhonov (α lam : ℝ) : ℝ :=
  lam / (α + lam)

end SpectralFilter
