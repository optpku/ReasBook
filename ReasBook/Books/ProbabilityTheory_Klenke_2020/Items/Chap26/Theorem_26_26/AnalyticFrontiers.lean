/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.GeneralizedStrongSolutionAPI
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Coefficients
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Evaluation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Growth
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_8.StrongMarkovAtStart

open MeasureTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n m : ℕ}

/-! These are the analytic frontier interfaces used by the Theorem 26.26 owner file.

The old project loaded them from a legacy cached module. Their statements are kept in this
dependency-closed `Items` module; the unavailable analytic proofs are explicit `sorry`s.
-/

theorem stroockVaradhan_diracLocalMartingaleProblemDataFrontier
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (hTimeIndependent : TimeIndependentLocalMartingaleProblemCoefficients a b)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b) :
    ∀ x : StroockVaradhanState n,
      (∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
        (P : ProbabilityMeasure Ω) (X : Ω → StroockVaradhanPathSpace n),
        IsLocalMartingaleProblemSolution
          (Measure.dirac x) a b ℱ (P : Measure Ω) X) ∧
        LocalMartingaleProblemHasUniqueLaw.{u, v}
          (Measure.dirac x) a b := by
  sorry

theorem stroockVaradhan_diracStrongMarkovRealizationFrontier
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (σ : NNReal → StroockVaradhanState n → Fin n → Fin m → ℝ)
    (haσ : a = diffusionMatrixOfCoefficient σ)
    (hcoeff : TimeIndependentCoefficients σ b)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b)
    (x : StroockVaradhanState n) :
    ∃ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal inferInstance)
      (P : ProbabilityMeasure Ω) (W : NNReal → Ω → Fin m → ℝ)
      (X : NNReal → Ω → StroockVaradhanState n)
      (κ : Kernel (StroockVaradhanState n) (NNReal → StroockVaradhanState n)),
      HasPathwiseStrongSolutionRealization
          (IsBrownianMotionWithFiltration ℱ (P : Measure Ω))
          (fun ξ W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ (P : Measure Ω) ξ W' σ b X')
          ℱ
          (fun _ ↦ x)
          W
          X ∧
        HasStrongMarkovPropertyAtStartNDim P X κ := by
  sorry

theorem stroockVaradhan_positiveTimeTransitionKernelExpectationContinuousFrontier
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (hTimeIndependent : TimeIndependentLocalMartingaleProblemCoefficients a b)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b)
    (Pref : StroockVaradhanState n → ProbabilityMeasure (StroockVaradhanPathSpace n))
    (κ : Kernel (StroockVaradhanState n) (NNReal → StroockVaradhanState n))
    (hPrefGenerated :
      ∀ x : StroockVaradhanState n,
        IsLocalMartingaleProblemSolution
          (Measure.dirac x)
          a
          b
          (generatedFiltration
            (fun t ↦
              (ContinuousMap.evalCLM ℝ t :
                StroockVaradhanPathSpace n → StroockVaradhanState n))
            (measurable_path_eval (n := n)))
          (Pref x : Measure (StroockVaradhanPathSpace n))
          id)
    (hMarkov :
      IsTimeHomogeneousMarkovProcess
        (fun t ↦
          (ContinuousMap.evalCLM ℝ t :
            StroockVaradhanPathSpace n → StroockVaradhanState n))
        Pref
        κ)
    (t : NNReal)
    (ht : 0 < t)
    (f : StroockVaradhanState n → ℝ)
    (hf : Measurable f)
    (hf_bdd : ∃ C : ℝ, ∀ y : StroockVaradhanState n, |f y| ≤ C) :
    Continuous (fun x : StroockVaradhanState n ↦
      ∫ y, f y ∂ transitionKernel κ t x) := by
  sorry

end ProbabilityTheory
