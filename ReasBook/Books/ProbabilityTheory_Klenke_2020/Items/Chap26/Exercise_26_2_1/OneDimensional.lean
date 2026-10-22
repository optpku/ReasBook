/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.Basic

public section

noncomputable section

namespace ProbabilityTheory

/-- Item-owned one-dimensional state space for Exercise 26.2.1. -/
abbrev OneDimensionalStateSpace := Fin 1 → ℝ

/-- Item-owned one-dimensional bridge for Exercise 26.2.1: the scalar state `x` as the chapter's
`Fin 1 → ℝ` state. -/
abbrev oneDimensionalState (x : ℝ) : OneDimensionalStateSpace :=
  fun _ ↦ x

/-- Evaluating `oneDimensionalState x` at the unique coordinate recovers `x`. -/
theorem oneDimensionalState_apply (x : ℝ) (i : Fin 1) :
    oneDimensionalState x i = x :=
  rfl

/-- Item-owned one-dimensional bridge for Exercise 26.2.1: a scalar drift coefficient as a
`Fin 1`-valued drift field on `ℝ¹`. -/
abbrev oneDimensionalDrift
    (b : NNReal → ℝ → ℝ) : NNReal → OneDimensionalStateSpace → Fin 1 → ℝ :=
  fun t x _ ↦ b t (x 0)

/-- Evaluating the lifted one-dimensional drift recovers the scalar coefficient. -/
theorem oneDimensionalDrift_apply
    (b : NNReal → ℝ → ℝ) (t : NNReal) (x : OneDimensionalStateSpace) (i : Fin 1) :
    oneDimensionalDrift b t x i = b t (x 0) :=
  rfl

/-- Item-owned one-dimensional bridge for Exercise 26.2.1: a scalar diffusion coefficient as a
`1 × 1` diffusion matrix field on `ℝ¹`. -/
abbrev oneDimensionalDiffusion (σ : NNReal → ℝ → ℝ) :
    NNReal → OneDimensionalStateSpace → Fin 1 → Fin 1 → ℝ :=
  fun t x _ _ ↦ σ t (x 0)

/-- Evaluating the lifted one-dimensional diffusion recovers the scalar coefficient. -/
theorem oneDimensionalDiffusion_apply
    (σ : NNReal → ℝ → ℝ) (t : NNReal) (x : OneDimensionalStateSpace) (i j : Fin 1) :
    oneDimensionalDiffusion σ t x i j = σ t (x 0) :=
  rfl

end ProbabilityTheory
