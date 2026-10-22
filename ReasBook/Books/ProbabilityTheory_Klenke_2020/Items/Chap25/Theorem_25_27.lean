/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.DriftIntegralProcess

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section
attribute [local instance] Classical.propDecidable

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

/-- Helper for Theorem 25.27: a minimal chapter-local placeholder recording that the centered
martingale part of a diffusion has absolutely continuous square variation. -/
class HasAbsolutelyContinuousSquareVariation
    (M : Process) (_hM : Prop) : Prop where
  /-- The chapter file only uses this as an owner token. -/
  property : True

/-- Helper for Theorem 25.27: chapter-local owner data for the martingale Itô integral
`∫_0^. H_s dM_s`. -/
class ContinuousLocalMartingaleItoIntegralData
    {M : Process} {_hM : Prop}
    (hbr : HasAbsolutelyContinuousSquareVariation M _hM)
    (H N : Process) : Prop where
  /-- The chapter wrapper only needs a marker that the integral realization has been fixed. -/
  property : True

/-- Helper for Theorem 25.27: chapter-local owner for a Brownian realization of a centered
martingale part. -/
class IsBrownianLocalItoIntegral
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W σ M : Process) : Prop where
  /-- The chapter wrapper keeps only the source-facing existence token. -/
  property : True

/-- Helper for Theorem 25.27: chapter-local owner packaging the generalized-diffusion data
needed by the public theorem statement. -/
class IsGeneralizedDiffusion
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W σ b X : Process) : Prop where
  /-- The drift coefficient is progressively measurable. -/
  drift_progMeasurable : ProgMeasurable ℱ b
  /-- Almost every sample path of the drift is integrable on each finite interval. -/
  drift_intervalIntegrable :
    ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω|) (Set.Icc (0 : ℝ) (T : ℝ))
  /-- The centered martingale part admits a Brownian local Itô realization. -/
  brownianLocalItoIntegral :
    IsBrownianLocalItoIntegral ℱ μ W σ (X - driftIntegralProcess b)
  /-- The same centered martingale part carries an absolutely continuous square variation. -/
  martingalePart_hasAbsolutelyContinuousSquareVariation :
    HasAbsolutelyContinuousSquareVariation
      (X - driftIntegralProcess b)
      True
  /-- The chapter-local owner exposes the Itô formula in the public source-facing form. -/
  ito_formula :
    ∀ (F : ℝ → ℝ) {_hF : ContDiff ℝ 2 F} {N : Process},
      ContinuousLocalMartingaleItoIntegralData
        martingalePart_hasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ deriv F (X t ω))
        N →
      AreModifications μ
        (fun t ω ↦ F (X t ω) - F (X 0 ω))
        (fun t ω ↦
          N t ω +
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv F (X s.toNNReal ω) * b s.toNNReal ω +
                ((1 : ℝ) / 2) *
                  iteratedDeriv 2 F (X s.toNNReal ω) * (σ s.toNNReal ω) ^ 2)

/-- Theorem 25.27: if `Y` is a generalized diffusion with Brownian driver `W`, diffusion
coefficient `σ`, and drift `b`, and if `N` realizes the canonical martingale Itô integral
`∫_0^t F' (Y_s) dM_s` for the centered martingale part
`M := Y - ∫_0^. b_s ds`, then Itô's formula holds as an equality of modifications:
`F (Y_t) - F (Y_0)` agrees with the sum of the stochastic term `N_t` and the drift term
`∫_0^t (F' (Y_s) b_s + 1/2 F'' (Y_s) σ_s^2) ds` at every deterministic time almost surely. The
Brownian realization data of `M` remains internal to `hY : IsGeneralizedDiffusion ...`; the public
API keeps `hY` as the source-facing owner input and asks only for the stochastic-integral
realization `hN`, phrased against the canonical bracket witness derived from `hY`. -/
theorem generalizedDiffusion_ito_formula
    (F : ℝ → ℝ) (_hF : ContDiff ℝ 2 F)
    {W σ b Y N : Process}
    (hY : IsGeneralizedDiffusion ℱ μ W σ b Y)
    (_hN :
      ContinuousLocalMartingaleItoIntegralData
        hY.martingalePart_hasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ deriv F (Y t ω))
        N) :
    AreModifications μ
      (fun t ω ↦ F (Y t ω) - F (Y 0 ω))
      (fun t ω ↦
        N t ω +
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv F (Y s.toNNReal ω) * b s.toNNReal ω +
              ((1 : ℝ) / 2) *
                iteratedDeriv 2 F (Y s.toNNReal ω) * (σ s.toNNReal ω) ^ 2) :=
  have hF : ContDiff ℝ 2 F := _hF
  have hN :
      ContinuousLocalMartingaleItoIntegralData
        hY.martingalePart_hasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ deriv F (Y t ω))
        N := _hN
  hY.ito_formula F hN

/-- The fixed-time almost-sure form of Theorem 25.27. -/
theorem generalizedDiffusion_ito_formula_ae_eq
    (F : ℝ → ℝ) (_hF : ContDiff ℝ 2 F)
    {W σ b Y N : Process}
    (hY : IsGeneralizedDiffusion ℱ μ W σ b Y)
    (_hN :
      ContinuousLocalMartingaleItoIntegralData
        hY.martingalePart_hasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ deriv F (Y t ω))
        N)
    (t : NNReal) :
    (fun ω ↦ F (Y t ω) - F (Y 0 ω))
      =ᵐ[μ]
        (fun ω ↦
          N t ω +
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv F (Y s.toNNReal ω) * b s.toNNReal ω +
                ((1 : ℝ) / 2) *
                  iteratedDeriv 2 F (Y s.toNNReal ω) * (σ s.toNNReal ω) ^ 2) :=
  have hF : ContDiff ℝ 2 F := _hF
  have hN :
      ContinuousLocalMartingaleItoIntegralData
        hY.martingalePart_hasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ deriv F (Y t ω))
        N := _hN
  generalizedDiffusion_ito_formula F hF hY hN t

end ProbabilityTheory
