/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_2

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "StatePath" => EuclideanPathSpace n
local notation "NoisePath" => EuclideanPathSpace m
local notation "BrownianProcess" => NNReal → Ω → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ

/-- Shared Chapter 26 API: the process obtained by evaluating a path-valued random variable at
time `t`. -/
abbrev pathProcess {d : ℕ} (Y : Ω → EuclideanPathSpace d) : NNReal → Ω → Fin d → ℝ :=
  fun t ω ↦ Y ω t

/-- Shared Chapter 26 API: the path-valued Brownian-driver condition paired with the canonical
strong-solution owner for generalized SDEs. -/
abbrev GeneralizedSDEBrownianMotion :
    {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) →
      (Ω → NoisePath) → Prop :=
  fun {_} _ P ℱ W ↦
    ∃ _ : IsProbabilityMeasure P,
      IsBrownianMotionWithFiltration ℱ P (pathProcess W)

/-- Shared Chapter 26 API: the path-valued strong-solution relation for generalized SDE
coefficients `(σ, b)`. -/
def SolvesStrongGeneralizedSDE (σ : DiffusionCoeff) (b : DriftCoeff) :
    {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) →
      (Ω → State) → (Ω → NoisePath) → (Ω → StatePath) → Prop :=
  fun {_} _ P ℱ ξ W X ↦
    ∃ _ : IsProbabilityMeasure P,
      IsGeneralizedNDimensionalDiffusion ℱ P ξ (pathProcess W) σ b (pathProcess X)

end ProbabilityTheory
