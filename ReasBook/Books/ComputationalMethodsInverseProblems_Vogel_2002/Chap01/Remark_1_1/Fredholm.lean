/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

public section

open scoped Interval

noncomputable section

namespace Fredholm1D

/-- The one-dimensional Fredholm first-kind blur operator on `[0, 1]`. -/
@[expose] def operator (k f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t in (0 : ℝ)..1, k (x - t) * f t

/-- Pointwise formula for `Fredholm1D.operator`. -/
theorem operator_apply (k f : ℝ → ℝ) (x : ℝ) :
    operator k f x = ∫ t in (0 : ℝ)..1, k (x - t) * f t := rfl

/-- The Gaussian blur kernel from the source model. -/
@[expose] def gaussianKernel (C γ : ℝ) : ℝ → ℝ :=
  fun x ↦ C * Real.exp (-(x ^ 2) / (2 * γ ^ 2))

/-- Pointwise formula for `Fredholm1D.gaussianKernel`. -/
theorem gaussianKernel_apply (C γ x : ℝ) :
    gaussianKernel C γ x = C * Real.exp (-(x ^ 2) / (2 * γ ^ 2)) := rfl

/-- The midpoint-quadrature matrix associated with the Gaussian blur kernel. -/
@[expose] def midpointMatrix (n : ℕ) (C γ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    let h : ℝ := 1 / n
    h * C * Real.exp (-((((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) ^ 2) / (2 * γ ^ 2)))

/-- Entrywise formula for `Fredholm1D.midpointMatrix`. -/
theorem midpointMatrix_apply (n : ℕ) (C γ : ℝ) (i j : Fin n) :
    midpointMatrix n C γ i j =
      let h : ℝ := 1 / n
      h * C * Real.exp (-((((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) ^ 2) / (2 * γ ^ 2))) := rfl

end Fredholm1D
