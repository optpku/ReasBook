/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Convolution
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Poisson.Basic

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Convolution NNReal

noncomputable section

namespace Blur2D

/-- The continuous two-dimensional blur operator with a four-variable point spread function. -/
def operator
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (f : (ℝ × ℝ) → ℝ) : (ℝ × ℝ) → ℝ :=
  fun p ↦ ∫ q : ℝ × ℝ, k p q * f q

/-- Pointwise formula for `Blur2D.operator`. -/
theorem operator_apply
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (f : (ℝ × ℝ) → ℝ)
    (p : ℝ × ℝ) :
    operator k f p = ∫ q : ℝ × ℝ, k p q * f q := sorry

/-- The pixel-integrated energy of a continuous image over a measurable region. -/
def pixelEnergy (Ω : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ) : ℝ :=
  ∫ p in Ω, g p

/-- Defining formula for `Blur2D.pixelEnergy`. -/
theorem pixelEnergy_def (Ω : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ) :
    pixelEnergy Ω g = ∫ p in Ω, g p := sorry

/-- The single-pixel Poisson-plus-Gaussian noise law on `ℝ`. -/
def pixelNoiseLaw (gij σ2 : ℝ≥0) : Measure ℝ :=
  (ProbabilityTheory.poissonMeasure gij).map (Nat.cast : ℕ → ℝ) ∗
    ProbabilityTheory.gaussianReal 0 σ2

/-- Defining formula for `Blur2D.pixelNoiseLaw`. -/
theorem pixelNoiseLaw_def (gij σ2 : ℝ≥0) :
    pixelNoiseLaw gij σ2 =
      (ProbabilityTheory.poissonMeasure gij).map (Nat.cast : ℕ → ℝ) ∗
        ProbabilityTheory.gaussianReal 0 σ2 := sorry

/-- The sampled four-index discrete point spread function obtained from midpoint quadrature. -/
def sampledPSF {n_x n_y : ℕ}
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    (xcoord : Fin n_x → ℝ)
    (ycoord : Fin n_y → ℝ) :
    Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ :=
  fun i μ j ν ↦ k (xcoord i, ycoord j) (xcoord μ, ycoord ν) * Δx * Δy

/-- Entrywise formula for `Blur2D.sampledPSF`. -/
theorem sampledPSF_apply {n_x n_y : ℕ}
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    (xcoord : Fin n_x → ℝ)
    (ycoord : Fin n_y → ℝ)
    (i μ : Fin n_x)
    (j ν : Fin n_y) :
    sampledPSF k Δx Δy xcoord ycoord i μ j ν =
      k (xcoord i, ycoord j) (xcoord μ, ycoord ν) * Δx * Δy := sorry

/-- The deterministic discrete blur associated with a four-index discrete point spread function. -/
def discreteBlur {n_x n_y : ℕ}
    (t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (f : Matrix (Fin n_x) (Fin n_y) ℝ) : Matrix (Fin n_x) (Fin n_y) ℝ :=
  fun i j ↦ ∑ μ, ∑ ν, t i μ j ν * f μ ν

/-- Entrywise formula for `Blur2D.discreteBlur`. -/
theorem discreteBlur_apply {n_x n_y : ℕ}
    (t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (f : Matrix (Fin n_x) (Fin n_y) ℝ)
    (i : Fin n_x)
    (j : Fin n_y) :
    discreteBlur t f i j = ∑ μ, ∑ ν, t i μ j ν * f μ ν := sorry

/-- The noisy discrete image obtained by adding an explicit error array to the discrete blur. -/
def observedImage {n_x n_y : ℕ}
    (t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (f η : Matrix (Fin n_x) (Fin n_y) ℝ) : Matrix (Fin n_x) (Fin n_y) ℝ :=
  fun i j ↦ discreteBlur t f i j + η i j

/-- Entrywise formula for `Blur2D.observedImage`. -/
theorem observedImage_apply {n_x n_y : ℕ}
    (t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (f η : Matrix (Fin n_x) (Fin n_y) ℝ)
    (i : Fin n_x)
    (j : Fin n_y) :
    observedImage t f η i j = discreteBlur t f i j + η i j := sorry

/-- The sampled noisy datum obtained by first discretizing the point spread
function with midpoint quadrature and then adding an explicit noise image. -/
def sampledObservedImage {n_x n_y : ℕ}
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    (xcoord : Fin n_x → ℝ)
    (ycoord : Fin n_y → ℝ)
    (f η : Matrix (Fin n_x) (Fin n_y) ℝ) : Matrix (Fin n_x) (Fin n_y) ℝ :=
  observedImage (sampledPSF k Δx Δy xcoord ycoord) f η

/-- The reduced two-variable kernel corresponding to spatial translation invariance. -/
def translationInvariantKernel (κ : (ℝ × ℝ) → ℝ) :
    (ℝ × ℝ) → (ℝ × ℝ) → ℝ :=
  fun p q ↦ κ (p - q)

/-- Entrywise formula for `Blur2D.translationInvariantKernel`. -/
theorem translationInvariantKernel_apply
    (κ : (ℝ × ℝ) → ℝ)
    (p q : ℝ × ℝ) :
    translationInvariantKernel κ p q = κ (p - q) := sorry

/-- The translation-invariant blur operator is the convolution of the image with the reduced PSF. -/
theorem operator_eq_convolution
    (κ f : (ℝ × ℝ) → ℝ) :
    operator (translationInvariantKernel κ) f =
      MeasureTheory.convolution f κ (ContinuousLinearMap.mul ℝ ℝ) MeasureSpace.volume := sorry

/-- The offset-indexed discrete point spread function for a translation-invariant blur model. -/
def translationInvariantDiscretePSF
    (κ : (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ) : ℤ → ℤ → ℝ :=
  fun i j ↦ κ (((i : ℝ) * Δx), ((j : ℝ) * Δy)) * Δx * Δy

/-- Entrywise formula for `Blur2D.translationInvariantDiscretePSF`. -/
theorem translationInvariantDiscretePSF_apply
    (κ : (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    (i j : ℤ) :
    translationInvariantDiscretePSF κ Δx Δy i j =
      κ (((i : ℝ) * Δx), ((j : ℝ) * Δy)) * Δx * Δy := sorry

end Blur2D
