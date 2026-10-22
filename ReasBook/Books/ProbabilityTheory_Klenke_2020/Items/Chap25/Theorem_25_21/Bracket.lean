/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_75
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {ℱ : Filtration NNReal mΩ}

/-- A continuous local martingale has absolutely continuous square variation if it comes with a
continuous square-variation process and a progressively measurable density whose integral on
`[0, t]` recovers that square variation. -/
structure HasAbsolutelyContinuousSquareVariation
    (M : NNReal → Ω → ℝ) (hM : IsContinuousLocalMartingale ℱ μ M) where
  density : NNReal → Ω → NNReal
  squareVariation : NNReal → Ω → ℝ
  squareVariation_owner : IsContinuousSquareVariationProcess ℱ μ M squareVariation
  density_progMeasurable : ProgMeasurable ℱ fun t ω ↦ (density t ω : ℝ)
  squareVariation_eq :
    ∀ t : NNReal, ∀ ω : Ω,
      squareVariation t ω =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (density s.toNNReal ω : ℝ)

/-- Convenience projection for the density in an absolutely continuous square-variation witness. -/
abbrev squareVariationDensity
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    NNReal → Ω → NNReal :=
  hbr.density

/-- The bracket-density integral `∫₀ᵗ H_s² d⟨M⟩_s`, written using the chosen density of `⟨M⟩`. -/
def bracketDensityIntegralUpTo
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H : NNReal → Ω → ℝ) :
    NNReal → Ω → ℝ :=
  fun t ω ↦
    ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      (H s.toNNReal ω) ^ 2 * (squareVariationDensity hbr s.toNNReal ω : ℝ)

/-- The coefficient `sqrt (d⟨M⟩ / dt)` used in the textbook `‖·‖_M` norm. -/
def squareVariationDensityRoot
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    NNReal → Ω → ℝ :=
  fun t ω ↦ Real.sqrt (squareVariationDensity hbr t ω : ℝ)

/-- The Brownian-side coefficient corresponding to the Itô integrand `H` against `M`. -/
def brownianRepresentationItoIntegrand
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H : NNReal → Ω → ℝ) :
    NNReal → Ω → ℝ :=
  fun t ω ↦ H t ω * squareVariationDensityRoot hbr t ω

/-- The textbook `‖H‖_M` norm of an integrand against a continuous local martingale `M`. -/
noncomputable def itoIntegrandNorm
    (M : NNReal → Ω → ℝ) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H : NNReal → Ω → ℝ) : ℝ≥0∞ :=
  eLpNorm
    (MeasureTheory.processToTimeSpaceFun (brownianRepresentationItoIntegrand hbr H))
    2
    (MeasureTheory.processMeasure μ)

/-- The integrand `H` has finite textbook norm `‖H‖_M`. -/
def HasFiniteItoIntegrandNorm
    (M : NNReal → Ω → ℝ) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) (H : NNReal → Ω → ℝ) : Prop :=
  itoIntegrandNorm M hbr H < ∞

/-- Convergence in the textbook norm `‖·‖_M`. -/
def TendstoInItoIntegrandNorm
    (M : NNReal → Ω → ℝ) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (Hs : ℕ → NNReal → Ω → ℝ) (H : NNReal → Ω → ℝ) : Prop :=
  Tendsto
    (fun n ↦ itoIntegrandNorm M hbr (fun t ω ↦ Hs n t ω - H t ω))
    atTop
    (𝓝 (0 : ℝ≥0∞))

/-- A localizing sequence for `∫ H dM` is a stopping-time approximation to `∞` along which the
truncated integrands have finite `M`-norm. -/
def IsItoLocalizingSequence
    (M : NNReal → Ω → ℝ) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) (τSeq : ℕ → Ω → NNReal) : Prop :=
  IsStoppingTimeApproximationUpTo ℱ μ
      (fun n ω ↦ (τSeq n ω : ENNReal)) (fun _ ↦ ∞) ∧
    ∀ n : ℕ,
      HasFiniteItoIntegrandNorm M hbr
        (processBeforeStoppingTime H fun ω ↦ (τSeq n ω : ENNReal))

/-- A family of predictable simple processes approximates `H` in `‖·‖_M` if every stage has
finite `M`-norm and the norms of the differences tend to `0`. -/
def IsPredictableSimpleItoApproximation
    (M : NNReal → Ω → ℝ) {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) (Hs : ℕ → PredictableSimpleProcess ℱ) : Prop :=
  (∀ m : ℕ, HasFiniteItoIntegrandNorm M hbr (Hs m : NNReal → Ω → ℝ)) ∧
    TendstoInItoIntegrandNorm M hbr (fun m ↦ (Hs m : NNReal → Ω → ℝ)) H

end ProbabilityTheory
