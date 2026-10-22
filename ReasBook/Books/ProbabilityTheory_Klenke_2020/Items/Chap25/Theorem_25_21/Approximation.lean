/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21.Integral
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {ℱ : Filtration NNReal mΩ}

/-- Theorem 25.21's double-approximation clause, stated with the canonical dyadic pathwise Itô
realizations of the predictable-simple approximants on the original sample space. -/
def HasApproximationFormula
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H N : NNReal → Ω → ℝ) : Prop :=
  ∀ τSeq : ℕ → Ω → NNReal,
    IsItoLocalizingSequence M hbr H τSeq →
    ∀ Hs : ℕ → ℕ → PredictableSimpleProcess ℱ,
      ∀ _ :
        ∀ n : ℕ,
          IsPredictableSimpleItoApproximation M hbr
            (processBeforeStoppingTime H fun ω ↦ (τSeq n ω : ENNReal))
            (Hs n),
      ∀ t : NNReal,
        ∃ rowLimit : ℕ → Ω → ℝ,
          TendstoInMeasure μ rowLimit atTop (N t) ∧
            ∀ n : ℕ,
              TendstoInMeasure μ
                (fun m ω ↦
                  continuousLocalMartingaleItoIntegralProcess hM
                    (Hs n m : NNReal → Ω → ℝ) t ω)
                atTop
                (rowLimit n)

/-- Source-facing owner clause for Theorem 25.21: the selected Itô integral process agrees with
the canonical dyadic pathwise realization outside one measurable null set, uniformly in time. -/
structure IsContinuousLocalMartingaleItoIntegralSourceOwner
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (H N : NNReal → Ω → ℝ) : Prop where
  indistinguishable_canonical :
    AreIndistinguishable μ N (continuousLocalMartingaleItoIntegralProcess hM H)

/-- Source-faithful output package for Theorem 25.21. The theorem exposes the selected Itô
integral process together with the textbook double-approximation clause, the canonical-owner
relation to the dyadic pathwise realization, the continuous local martingale clause, and the
square-variation formula up to indistinguishability on each finite horizon. -/
structure ContinuousLocalMartingaleItoIntegralSourceSpec
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) where
  process : NNReal → Ω → ℝ
  itoIntegral :
    IsContinuousLocalMartingaleItoIntegralSourceOwner (hM := hM) H process
  approximationFormula :
    HasApproximationFormula hM hbr H process
  continuousLocalMartingale :
    IsContinuousLocalMartingale ℱ μ process
  squareVariationUpTo :
    ∀ T : NNReal,
      ∃ squareVariationVersion : NNReal → Ω → ℝ,
        IsContinuousSquareVariationProcess ℱ μ process squareVariationVersion ∧
          AreIndistinguishable μ
            (stoppedProcess squareVariationVersion (fun _ ↦ (T : ENNReal)))
            (stoppedProcess (bracketDensityIntegralUpTo hbr H) (fun _ ↦ (T : ENNReal)))

/-- Companion constructor for the source-facing Theorem 25.21 specification bundle. -/
def ContinuousLocalMartingaleItoIntegralSourceSpec.ofClauses
    {M : NNReal → Ω → ℝ} {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    {H : NNReal → Ω → ℝ}
    (N : NNReal → Ω → ℝ)
    (hIto : IsContinuousLocalMartingaleItoIntegralSourceOwner (hM := hM) H N)
    (hApprox : HasApproximationFormula hM hbr H N)
    (hLocal : IsContinuousLocalMartingale ℱ μ N)
    (hSquare :
      ∀ T : NNReal,
        ∃ squareVariationVersion : NNReal → Ω → ℝ,
          IsContinuousSquareVariationProcess ℱ μ N squareVariationVersion ∧
            AreIndistinguishable μ
              (stoppedProcess squareVariationVersion (fun _ ↦ (T : ENNReal)))
              (stoppedProcess (bracketDensityIntegralUpTo hbr H) (fun _ ↦ (T : ENNReal)))) :
    ContinuousLocalMartingaleItoIntegralSourceSpec hbr H :=
  ⟨N, hIto, hApprox, hLocal, hSquare⟩

end ProbabilityTheory
