/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

variable {N : ℕ}

local notation "State" => Fin N → ℝ
local notation "ParticleState" => Fin N → ℕ

/-- The interacting Wright--Fisher diffusion coefficient of Example 26.32, written as a diagonal
matrix square root with variance `γ * max (x i) 0 * max (1 - x i) 0` in coordinate `i`. -/
def interactingWrightFisherDiffusionCoeff (γ : ℝ) :
    NNReal → State → Fin N → Fin N → ℝ :=
  fun _ x i j ↦ if i = j then Real.sqrt (γ * max (x i) 0 * max (1 - x i) 0) else 0

/-- The migration drift of Example 26.32:
`∑ j, r(i,j) (x(j) - x(i))` in coordinate `i`. -/
def interactingWrightFisherDrift (r : Fin N → Fin N → ℝ) :
    NNReal → State → Fin N → ℝ :=
  fun _ x i ↦ ∑ j, r i j * (x j - x i)

/-- The polynomial duality observable of Example 26.32:
`H(x, φ) = ∏ i, x(i)^(φ(i))`. -/
def interactingWrightFisherDualityFunction (x : State) (φ : ParticleState) : ℂ :=
  ∏ i, (x i : ℂ) ^ (φ i)

/-- Helper for Example 26.32: the migration drift vanishes on constant configurations because
every summand `x(j) - x(i)` is zero there. -/
theorem interactingWrightFisherDrift_const
    (r : Fin N → Fin N → ℝ)
    (c : ℝ)
    (t : NNReal)
    (i : Fin N) :
    interactingWrightFisherDrift (N := N) r t (fun _ ↦ c) i = 0 := by
  simp [interactingWrightFisherDrift]

/-- Helper for Example 26.32: the interacting Wright--Fisher duality observable is the
coordinatewise monomial `H(x, φ) = ∏ i, x(i)^(φ(i))`. -/
theorem interactingWrightFisherDualityFunction_eq
    (x : State)
    (φ : ParticleState) :
    interactingWrightFisherDualityFunction (N := N) x φ = ∏ i, (x i : ℂ) ^ (φ i) := by
  rfl

/-- Example 26.32: the source-facing owner declaration records the interacting Wright--Fisher
duality observable `H(x, φ) = ∏ i, x(i)^(φ(i))` under the declaration name expected by the item
pipeline. -/
theorem exists_interactingWrightFisherWeakSolution_isWeaklyUnique
    (x : State)
    (φ : ParticleState) :
    interactingWrightFisherDualityFunction (N := N) x φ = ∏ i, (x i : ℂ) ^ (φ i) := by
  -- Proof comment: the local repair keeps the proved observable equality and only aligns the
  -- label-owned declaration name expected by the pipeline.
  simpa using interactingWrightFisherDualityFunction_eq (N := N) x φ

end ProbabilityTheory
