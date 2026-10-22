/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7.OptimalFamily
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective

public section

universe u

/-- Notation 7.7-extra-1 (1). For a fixed regularization method and admissible
parameter set `S`, the expected estimation-optimal parameter family `αₑ`
consists exactly of the families whose `n`th term minimizes the `n`th expected
estimation objective on `S`. -/
theorem expectedEstimationOptimalFamily_iff {τ : Type u}
    (expectedEstimationObjective : ℕ → τ → ℝ) (S : Set τ) (alphaE : ℕ → τ) :
    ParameterChoice.IsOptimalParameterFamily expectedEstimationObjective (fun _ ↦ S) alphaE ↔
      ∀ n, IsMinOn (expectedEstimationObjective n) S (alphaE n) := by
  simpa using
    ParameterChoice.isOptimalParameterFamily_const_iff expectedEstimationObjective S alphaE

/-- Notation 7.7-extra-1 (2). For a fixed regularization method and admissible
parameter set `S`, the expected prediction-optimal parameter family `αₚ`
consists exactly of the families whose `n`th term minimizes the `n`th expected
prediction objective on `S`. -/
theorem expectedPredictionOptimalFamily_iff {τ : Type u}
    (expectedPredictionObjective : ℕ → τ → ℝ) (S : Set τ) (alphaP : ℕ → τ) :
    ParameterChoice.IsOptimalParameterFamily expectedPredictionObjective (fun _ ↦ S) alphaP ↔
      ∀ n, IsMinOn (expectedPredictionObjective n) S (alphaP n) := by
  simpa using
    ParameterChoice.isOptimalParameterFamily_const_iff expectedPredictionObjective S alphaP

/-- Notation 7.7-extra-1 (3). For a fixed regularization method and admissible
parameter set `S`, the expected parameter family `α` selected by a particular
method consists exactly of the families whose `n`th term minimizes the `n`th
expected selection objective on `S`; for example, `α_V` is obtained by taking
the expected GCV objective as the selection objective. -/
theorem expectedMethodParameterFamily_iff {τ : Type u}
    (selectionObjective : ℕ → τ → ℝ) (S : Set τ) (alpha : ℕ → τ) :
    ParameterChoice.IsOptimalParameterFamily selectionObjective (fun _ ↦ S) alpha ↔
      ∀ n, IsMinOn (selectionObjective n) S (alpha n) := by
  simpa using
    ParameterChoice.isOptimalParameterFamily_const_iff selectionObjective S alpha
