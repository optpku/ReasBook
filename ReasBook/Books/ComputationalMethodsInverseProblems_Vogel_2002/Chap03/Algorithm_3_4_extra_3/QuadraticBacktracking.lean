/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

public section

noncomputable section

namespace LineSearch

/-- The quadratic backtracking candidate determined by the source formula `(3.30)`. -/
@[expose] def quadraticBacktrackingStep (φ : ℝ → ℝ) (τ₀ : ℝ) : ℝ :=
  -(deriv φ 0) * τ₀ ^ 2 / (2 * (φ τ₀ - φ 0 - deriv φ 0 * τ₀))

/-- Expands `quadraticBacktrackingStep` into its closed-form expression. -/
theorem quadraticBacktrackingStep_def (φ : ℝ → ℝ) (τ₀ : ℝ) :
    quadraticBacktrackingStep φ τ₀ =
      -(deriv φ 0) * τ₀ ^ 2 / (2 * (φ τ₀ - φ 0 - deriv φ 0 * τ₀)) := rfl

end LineSearch
