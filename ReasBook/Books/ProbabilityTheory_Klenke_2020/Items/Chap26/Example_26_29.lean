/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Example_26_29Support

open MeasureTheory ProbabilityTheory

noncomputable section

local notation "State" => Fin 1 → ℝ
local notation "PathSpace" => EuclideanPathSpace 1
local notation "σWF(" gamma ")" => oneDimensionalDiffusion (wrightFisherScalarDiffusionCoeff gamma)
local notation "bWF" => oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))
local notation "CoordinateProcess" =>
  fun t ↦ (ContinuousMap.evalCLM ℝ t : PathSpace → State)

-- Canonical wrapper: the proved/source-facing declarations for Example 26.29 live in the
-- `Items` owner module, and this chapter-level module re-exports that surface.

/-- Example 26.29: for every `γ ≥ 0`, the Wright--Fisher local martingale problem is well-posed.
This chapter-level wrapper aligns the labeled declaration with the owner theorem exported from the
item support module. -/
theorem wrightFisherLocalMartingaleProblemWellPosed (gamma : ℝ) (hγ : 0 ≤ gamma) :
    LocalMartingaleProblemWellPosed
      (diffusionMatrixOfCoefficient (σWF(gamma))) bWF := by
  -- Proof comment: re-export the owner theorem under the label-associated declaration name that
  -- the item pipeline expects for Example 26.29.
  simpa using ProbabilityTheory.wrightFisherLocalMartingaleProblemWellPosed gamma hγ

namespace ProbabilityTheory

/-- Companion to Example 26.29: for `γ > 0`, the family of Dirac-initial Wright--Fisher weak
solutions admits a canonical time-homogeneous strong-Markov realization on path space. -/
theorem wrightFisherStrongMarkovRealization (gamma : ℝ) (hγ : 0 < gamma) :
    ∃ (P : State → ProbabilityMeasure PathSpace)
      (pathKernel : Kernel State (NNReal → State)),
      (∀ x : State,
        ∃ L :
            GeneralizedWeakSDESolution
              (Measure.dirac x)
              (σWF(gamma)) bWF,
          L.IsWeaklyUnique ∧ L.statePathLaw = (P x : Measure PathSpace)) ∧
        IsTimeHomogeneousMarkovProcess CoordinateProcess P pathKernel ∧
        HasStrongMarkovProperty P CoordinateProcess pathKernel := by
  -- Proof comment: this companion wrapper re-exports the canonical strong-Markov realization from
  -- the support module without changing its mathematical content.
  simpa using wrightFisher_existsStrongMarkovSolutionFamily gamma hγ

end ProbabilityTheory
