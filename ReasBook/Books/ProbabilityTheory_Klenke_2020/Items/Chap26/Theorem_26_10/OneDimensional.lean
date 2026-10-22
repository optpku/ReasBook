/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_8.CoefficientConditions

noncomputable section

namespace ProbabilityTheory

/-- Shared support API for Theorem 26.10: the chapter's one-dimensional state space. -/
abbrev OneDimensionalSDEState := SDEState 1

/-- Shared support API for Theorem 26.10: view a scalar state as the chapter's one-dimensional
state space. -/
abbrev oneDimensionalState (x : ℝ) : OneDimensionalSDEState :=
  fun _ ↦ x

/-- Evaluating `oneDimensionalState x` at its unique coordinate recovers the scalar `x`. -/
theorem oneDimensionalState_apply (x : ℝ) (i : Fin 1) :
    oneDimensionalState x i = x :=
  rfl

/-- Shared support API for Theorem 26.10: lift a scalar drift coefficient to the chapter's
one-dimensional drift surface. -/
abbrev oneDimensionalDrift (b : NNReal → ℝ → ℝ) : SDEDriftCoeff 1 :=
  fun t x _ ↦ b t (x 0)

/-- Evaluating the lifted one-dimensional drift recovers the original scalar coefficient. -/
theorem oneDimensionalDrift_apply
    (b : NNReal → ℝ → ℝ) (t : NNReal) (x : SDEState 1) (i : Fin 1) :
    oneDimensionalDrift b t x i = b t (x 0) :=
  rfl

/-- Shared support API for Theorem 26.10: lift a scalar diffusion coefficient to the chapter's
one-dimensional diffusion surface. -/
abbrev oneDimensionalDiffusion (σ : NNReal → ℝ → ℝ) : SDEDiffusionCoeff 1 1 :=
  fun t x _ _ ↦ σ t (x 0)

/-- Evaluating the lifted one-dimensional diffusion recovers the original scalar coefficient. -/
theorem oneDimensionalDiffusion_apply
    (σ : NNReal → ℝ → ℝ) (t : NNReal) (x : SDEState 1) (i j : Fin 1) :
    oneDimensionalDiffusion σ t x i j = σ t (x 0) :=
  rfl

/-- Shared support API for Theorem 26.10: a one-dimensional state is determined by its unique
coordinate. -/
theorem state_eq_oneDimensionalState (x : SDEState 1) :
    x = oneDimensionalState (x 0) := by
  ext i
  fin_cases i
  rfl

/-- Shared support API for Theorem 26.10: shifting time preserves the scalar drift Lipschitz
estimate. -/
theorem oneDimensionalShiftedDrift_lipschitz
    {b : NNReal → ℝ → ℝ} {K : ℝ}
    (hb_lipschitz :
      ∀ t : NNReal, ∀ x x' : ℝ, |b t x - b t x'| ≤ K * |x - x'|)
    (s : NNReal) :
    ∀ t : NNReal, ∀ x x' : ℝ, |b (s + t) x - b (s + t) x'| ≤ K * |x - x'| := by
  intro t x x'
  exact hb_lipschitz (s + t) x x'

/-- Shared support API for Theorem 26.10: shifting time preserves the scalar H\"older diffusion
estimate. -/
theorem oneDimensionalShiftedDiffusion_holder
    {σ : NNReal → ℝ → ℝ} {α : ℝ}
    (hσ_holder :
      ∀ t : NNReal, ∀ x x' : ℝ, |σ t x - σ t x'| ≤ Real.rpow (|x - x'|) α)
    (s : NNReal) :
    ∀ t : NNReal, ∀ x x' : ℝ, |σ (s + t) x - σ (s + t) x'| ≤ Real.rpow (|x - x'|) α := by
  intro t x x'
  exact hσ_holder (s + t) x x'

end ProbabilityTheory
