/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

variable {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
variable {σ : DiffusionCoeff} {b : DriftCoeff}

/- Source/core/bridge triage for Remark 26.13:
- bridge/view layer: the specialized weak-solution bridge
  `GeneralizedWeakSDESolution` is unpacked back to the owner predicates
  `IsGeneralizedNDimensionalDiffusion` and `IsNDimensionalDiffusion`;
- core/canonical owners reused: `IsGeneralizedNDimensionalDiffusion`,
  `IsNDimensionalDiffusion`, and `TimeIndependentCoefficients`;
- primitive data: the `solves_sde` field of `WeakSDESolution`;
- derived API: the two bridge lemmas below.
-/

-- Proof sketch: unfold the `GeneralizedWeakSDESolution` bridge. Its `solves_sde` field is exactly
-- the generalized-diffusion relation for the underlying state process, with the Brownian
-- stochastic term carried by the canonical vector bridge `IsMatrixBrownianLocalItoIntegral`.
/-- Remark 26.13: every weak solution of an SDE is a generalized `n`-dimensional diffusion. -/
theorem GeneralizedWeakSDESolution.isGeneralizedNDimensionalDiffusion
    (L : GeneralizedWeakSDESolution μ₀ σ b) :
    IsGeneralizedNDimensionalDiffusion L.ℱ L.μ
      (fun ω ↦ L ω 0) L.W σ b (fun t ω ↦ L ω t) := by
  rcases L.solves_sde with ⟨_, hL⟩
  exact hL

-- Proof sketch: combine
-- `GeneralizedWeakSDESolution.isGeneralizedNDimensionalDiffusion` with the time-independence
-- condition on the coefficients.
/-- A weak solution with time-independent drift and diffusion coefficients is an
`n`-dimensional diffusion. -/
theorem GeneralizedWeakSDESolution.isNDimensionalDiffusion_of_timeIndependentCoefficients
    (L : GeneralizedWeakSDESolution μ₀ σ b)
    (hcoeff : TimeIndependentCoefficients σ b) :
    IsNDimensionalDiffusion L.ℱ L.μ
      (fun ω ↦ L ω 0) L.W σ b (fun t ω ↦ L ω t) := by
  exact ⟨L.isGeneralizedNDimensionalDiffusion, hcoeff⟩

end ProbabilityTheory
