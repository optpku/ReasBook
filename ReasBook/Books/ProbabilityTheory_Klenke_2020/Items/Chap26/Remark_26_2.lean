/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Lemma_26_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {n m : ℕ}

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => Fin n → ℝ
local notation "StateProcess" => NNReal → Ω → State
local notation "BrownianProcess" => NNReal → Ω → Fin m → ℝ
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

variable {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An `m`-dimensional Brownian process with filtration `ℱ` is a standard vector Brownian motion
whose coordinates are adapted to `ℱ`. -/
def IsBrownianMotionWithFiltration
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : BrownianProcess) : Prop :=
  IsStandardBrownianMotionVector μ W.toEuclidean ∧
    Adapted ℱ W

/-- The coefficients of the SDE are time-independent when their values depend only on the state
variable and not on the time parameter. -/
def TimeIndependentCoefficients (σ : DiffusionCoeff) (b : DriftCoeff) : Prop :=
  (∀ t₁ t₂ x, σ t₁ x = σ t₂ x) ∧
    ∀ t₁ t₂ x, b t₁ x = b t₂ x

/-- Helper for Remark 26.2: the matrix-valued Brownian Itô bridge from Lemma 26.7 is
structure-valued data, so the diffusion predicate records only the existence of such a
realization. -/
def hasMatrixBrownianLocalItoIntegralRealization
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : BrownianProcess)
    (H : NNReal → Ω → Fin n → Fin m → ℝ)
    (N : StateProcess) : Prop :=
  Nonempty
    (ProbabilityTheory.IsMatrixBrownianLocalItoIntegral
      ℱ
      μ
      W.toEuclidean
      H
      N.toEuclidean)

/-- A generalized `n`-dimensional diffusion with initial state `ξ` is an `n`-dimensional process
driven by an `m`-dimensional Brownian motion whose coordinates admit the Itô decomposition with
coefficients `σ(t, X_t)` and `b(t, X_t)`. The Brownian martingale term is expressed through the
canonical vector bridge `IsMatrixBrownianLocalItoIntegral`, so the auxiliary scalar coordinate
realizations remain internal. -/
def IsGeneralizedNDimensionalDiffusion
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → State) (W : BrownianProcess) (σ : DiffusionCoeff) (b : DriftCoeff)
    (X : StateProcess) : Prop :=
  IsBrownianMotionWithFiltration ℱ μ W ∧
    ∃ N : StateProcess,
      hasMatrixBrownianLocalItoIntegralRealization
        ℱ
        μ
        W
        (fun t ω i j ↦ σ t (X t ω) i j)
        N ∧
      (∀ i, ProgMeasurable ℱ (fun t ω ↦ b t (X t ω) i)) ∧
      (∀ i T, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦ |b s.toNNReal (X s.toNNReal ω) i|)
          (Set.Icc (0 : ℝ) (T : ℝ))) ∧
      X =
        fun t ω i ↦
          ξ ω i +
            N t ω i +
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X s.toNNReal ω) i

/-- An `n`-dimensional diffusion is a generalized `n`-dimensional diffusion whose coefficients are
time-independent. -/
def IsNDimensionalDiffusion
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → State) (W : BrownianProcess) (σ : DiffusionCoeff) (b : DriftCoeff)
    (X : StateProcess) : Prop :=
  IsGeneralizedNDimensionalDiffusion ℱ μ ξ W σ b X ∧
    TimeIndependentCoefficients σ b

section StrongSolutionRealization

variable {ξ : Ω → State} {W : BrownianProcess} {σ : DiffusionCoeff} {b : DriftCoeff}
variable {X : StateProcess}

local notation "SolvesGeneralizedDiffusion" =>
  fun ξ' W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ μ ξ' W' σ b X'

/- Source/core/bridge triage for Remark 26.2:
- source-facing owner declarations in this file: `IsBrownianMotionWithFiltration`,
  `TimeIndependentCoefficients`, `IsGeneralizedNDimensionalDiffusion`, and
  `IsNDimensionalDiffusion`;
- core/canonical owner reused in the remark: `HasPathwiseStrongSolutionRealization`;
- derived API reused from `Remark_26_14`: `HasPathwiseStrongSolutionRealization.solvesSDE`,
  which is the direct canonical recall for the generalized-diffusion clause and avoids a duplicate
  local theorem shell.
-/

/- Remark 26.2: every strong-solution realization of the SDE determines a generalized
`n`-dimensional diffusion with initial state `ξ`; this is the specialization of the canonical
owner theorem `HasPathwiseStrongSolutionRealization.solvesSDE` to
`SolvesGeneralizedDiffusion`. -/
recall HasPathwiseStrongSolutionRealization.solvesSDE

-- Proof sketch: combine the canonical recall
-- `HasPathwiseStrongSolutionRealization.solvesSDE` with the time-independence assumption on the
-- coefficients.
/- A strong solution with time-independent diffusion and drift coefficients is an
`n`-dimensional diffusion in the autonomous sense. -/
set_option linter.unusedVariables false in
theorem strongSolution_is_n_dimensional_diffusion_of_timeIndependentCoefficients
    (hX : HasPathwiseStrongSolutionRealization
      (fun _ : BrownianProcess ↦ True)
      SolvesGeneralizedDiffusion
      ℱ ξ W X)
    (hcoeff : TimeIndependentCoefficients σ b) :
    IsNDimensionalDiffusion ℱ μ ξ W σ b X :=
  ⟨HasPathwiseStrongSolutionRealization.solvesSDE hX, hcoeff⟩

end StrongSolutionRealization

end ProbabilityTheory
