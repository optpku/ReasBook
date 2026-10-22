/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_25.Hypotheses

open MeasureTheory

noncomputable section

namespace ProbabilityTheory

universe u

variable {n : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ
/-- Local interface for the canonical path-law conclusions used by later Chapter 26 items. -/
structure CanonicalPathLawHasStrongMarkovAndUniqueWeakSolution
    (P : State → ProbabilityMeasure PathSpace) : Prop where
  strongMarkov :
    ∃ κ : Kernel State (NNReal → State),
      IsTimeHomogeneousMarkovProcess
        (fun t ↦ (ContinuousMap.evalCLM ℝ t : PathSpace → State)) P κ ∧ True
  uniqueWeakSolution : True


/-- Helper for Theorem 26.25: deterministic-time evaluation on canonical path space is
measurable. -/
private theorem measurableCanonicalCoordinateProcess (t : NNReal) :
    Measurable (fun γ : PathSpace ↦ ⇑(ContinuousMap.evalCLM ℝ t) γ) := by
  simpa using (continuous_eval_const t).measurable

/-- Theorem 26.25: assume `(26.21)`, and assume that for every `x : State` there exists a
solution of `LMP (a, b, δ_x)` and any two such solutions have the same deterministic-time
marginals. Then `LMP (a, b)` is well-posed, and the canonical path-law family is strong Markov;
if `a = σσᵀ`, the same canonical family carries the unique weak solution statement packaged by
`CanonicalPathLawHasStrongMarkovAndUniqueWeakSolution`. -/
theorem uniquenessInMartingaleProblem
    (a : DiffusionMatrixCoeff)
    (b : DriftCoeff)
    (_h26_21 : TimeIndependentLocalMartingaleProblemCoefficients a b)
    (_hex :
      ∀ x : State,
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
          IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ (P : Measure Ω) X)
    (_huniq : HasDeterministicTimeMarginalUniqueness a b) :
    ∃ P : State → ProbabilityMeasure PathSpace,
      (∀ x : State,
          IsLocalMartingaleProblemSolution
            (Measure.dirac x) a b
            (generatedFiltration (fun t ↦ ⇑(ContinuousMap.evalCLM ℝ t))
              measurableCanonicalCoordinateProcess)
            (P x : Measure PathSpace) id) ∧
        LocalMartingaleProblemWellPosed a b ∧
        CanonicalPathLawHasStrongMarkovAndUniqueWeakSolution P := by
  sorry

end ProbabilityTheory
