/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ProbabilityTheory

/-- The positive part `x⁺ = max (x, 0)` of a real number. -/
def realPosPart (x : ℝ) : ℝ :=
  max x 0

-- Proof sketch: unfold `realPosPart`; it is defined to be the maximum of `x` and `0`.
/-- Evaluating `realPosPart` gives the maximum of `x` and `0`. -/
theorem realPosPart_eq_max (x : ℝ) :
    realPosPart x = max x 0 := by
  -- Unfold the definition to expose the maximum directly.
  rfl

/-- The diffusion coefficient `σ(t, x) = sqrt (γ x⁺)` of the one-dimensional
Cox--Ingersoll--Ross / Feller branching SDE from Example 26.11. -/
def cirDiffusionCoeff (γ : NNReal) : NNReal → ℝ → ℝ :=
  fun _ x ↦ Real.sqrt ((γ : ℝ) * realPosPart x)

-- Proof sketch: unfold `cirDiffusionCoeff`; it is time-independent and equals
-- `sqrt (γ realPosPart x)` at the state value `x`.
/-- Evaluating the CIR diffusion coefficient gives `sqrt (γ x⁺)`. -/
theorem cirDiffusionCoeff_apply (γ : NNReal) (t : NNReal) (x : ℝ) :
    cirDiffusionCoeff γ t x = Real.sqrt ((γ : ℝ) * realPosPart x) := by
  -- Unfold the time-independent coefficient at the evaluation point `(t, x)`.
  rfl

/-- The drift coefficient `β(t, x) = a (b - x⁺)` of the one-dimensional
Cox--Ingersoll--Ross / Feller branching SDE from Example 26.11. -/
def cirDriftCoeff (a b : NNReal) : NNReal → ℝ → ℝ :=
  fun _ x ↦ (a : ℝ) * ((b : ℝ) - realPosPart x)

-- Proof sketch: unfold `cirDriftCoeff`; it is time-independent and equals `a (b - x⁺)` at the
-- state value `x`.
/-- Evaluating the CIR drift coefficient gives `a (b - x⁺)`. -/
theorem cirDriftCoeff_apply (a b : NNReal) (t : NNReal) (x : ℝ) :
    cirDriftCoeff a b t x = (a : ℝ) * ((b : ℝ) - realPosPart x) := by
  -- Unfold the time-independent drift coefficient at the evaluation point `(t, x)`.
  rfl

/-- Example 26.11: in the case `a = b = 0`, the Laplace transform of the nonnegative square-root
diffusion started from `x ≥ 0` is
`φ(t, λ, x) = exp (- λ x / ((γ / 2) λ t + 1))`. -/
def cirLaplaceTransform (γ t x : NNReal) : ℝ → ℝ :=
  fun l ↦ Real.exp (-(((x : ℝ) * l) / ((((γ : ℝ) / 2) * l * (t : ℝ)) + 1)))

-- Proof sketch: unfold `cirLaplaceTransform`; this is exactly the explicit exponential formula
-- displayed in Example 26.11.
/-- Evaluating `cirLaplaceTransform γ t x` gives the textbook exponential formula
`exp (- λ x / ((γ / 2) λ t + 1))`. -/
theorem cirLaplaceTransform_apply (γ t x : NNReal) (l : ℝ) :
    cirLaplaceTransform γ t x l =
      Real.exp (-(((x : ℝ) * l) / ((((γ : ℝ) / 2) * l * (t : ℝ)) + 1))) := by
  -- Unfold the explicit formula packaged in `cirLaplaceTransform`.
  rfl

-- Proof sketch: specialize the explicit formula at `t = 0` and simplify the denominator to `1`.
/-- At time `0`, the CIR Laplace transform is the initial value `exp (- λ x)`. -/
theorem cirLaplaceTransform_zero_time (γ x : NNReal) (l : ℝ) :
    cirLaplaceTransform γ 0 x l = Real.exp (-((x : ℝ) * l)) := by
  -- Specialize the explicit formula at `t = 0` and simplify the denominator to `1`.
  simp [cirLaplaceTransform]

-- Proof sketch: specialize the explicit formula to `γ = 2`, so `(γ : ℝ) / 2 = 1`, and simplify
-- the denominator to `λ t + 1`.
/-- For `γ = 2`, the CIR Laplace transform becomes `exp (- λ x / (λ t + 1))`, the Chapter 21
Feller branching-diffusion Laplace-transform formula. -/
theorem cirLaplaceTransform_gamma_two (t x : NNReal) (l : ℝ) :
    cirLaplaceTransform 2 t x l =
      Real.exp (-(((x : ℝ) * l) / (l * (t : ℝ) + 1))) := by
  -- Rewrite to the explicit formula so only the scalar normalization remains.
  rw [cirLaplaceTransform_apply]
  -- Simplify `(2 : ℝ) / 2` to `1` and clean the denominator.
  norm_num

end ProbabilityTheory
