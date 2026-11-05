/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_definition_1_7.Optimality
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_2_algorithm_1_3.MixedCut

section Algorithm13

variable {m n p : ℕ}

/-- A stage-indexed execution of the cutting-plane method records the stage relaxations, the
optimal basic solutions returned by those relaxations, and the generated cuts. -/
structure MixedIntegerCuttingPlaneExecution (n p : ℕ) where
  relaxation : ℕ → Set (MixedRealPoint n p)
  basicSolution : ℕ → MixedRealPoint n p
  generatedCut : ℕ → MixedCut n p

namespace MixedIntegerCuttingPlaneExecution

/-- `ofStages` builds an execution record from its stage-indexed relaxations, basic solutions,
and generated cuts. -/
def ofStages
    (relaxation : ℕ → Set (MixedRealPoint n p))
    (basicSolution : ℕ → MixedRealPoint n p)
    (generatedCut : ℕ → MixedCut n p) :
    MixedIntegerCuttingPlaneExecution n p where
  relaxation := relaxation
  basicSolution := basicSolution
  generatedCut := generatedCut

@[simp] theorem relaxation_ofStages
    (relaxation : ℕ → Set (MixedRealPoint n p))
    (basicSolution : ℕ → MixedRealPoint n p)
    (generatedCut : ℕ → MixedCut n p)
    (k : ℕ) :
    (ofStages relaxation basicSolution generatedCut).relaxation k = relaxation k :=
  rfl

@[simp] theorem basicSolution_ofStages
    (relaxation : ℕ → Set (MixedRealPoint n p))
    (basicSolution : ℕ → MixedRealPoint n p)
    (generatedCut : ℕ → MixedCut n p)
    (k : ℕ) :
    (ofStages relaxation basicSolution generatedCut).basicSolution k = basicSolution k :=
  rfl

@[simp] theorem generatedCut_ofStages
    (relaxation : ℕ → Set (MixedRealPoint n p))
    (basicSolution : ℕ → MixedRealPoint n p)
    (generatedCut : ℕ → MixedCut n p)
    (k : ℕ) :
    (ofStages relaxation basicSolution generatedCut).generatedCut k = generatedCut k :=
  rfl

section

variable (execution : MixedIntegerCuttingPlaneExecution n p)

/-- The execution stops at stage `k` exactly when the recorded basic solution already belongs to
the mixed-integer feasible set of `P`. -/
def stopsAt
    (P : MixedIntegerLinearProgram m n p)
    (k : ℕ) : Prop :=
  execution.basicSolution k ∈ P.feasibleSet

/-- Source-facing expansion of the stopping test `execution.stopsAt P k`. -/
@[simp]
theorem stopsAt_iff
    {P : MixedIntegerLinearProgram m n p}
    {k : ℕ} :
    execution.stopsAt P k ↔ execution.basicSolution k ∈ P.feasibleSet :=
  Iff.rfl

/-- The stage-`k` clause of the cutting-plane method: solve the current relaxation, stop if the
basic solution is already feasible for the original MILP, otherwise add a Definition 1.9 cutting
plane for the feasible set at the current basic solution and update the next relaxation by
intersecting with its halfspace. -/
def stagewiseClause
    (P : MixedIntegerLinearProgram m n p)
    (isOptimalBasicSolutionOfRelaxation :
      ℕ → Set (MixedRealPoint n p) → (MixedRealPoint n p → ℝ) → MixedRealPoint n p → Prop)
    (k : ℕ) : Prop :=
  isOptimalBasicSolutionOfRelaxation k (execution.relaxation k) P.objectiveValue
      (execution.basicSolution k) ∧
    (execution.stopsAt P k →
      P.isOptimalSolution (execution.basicSolution k)) ∧
    (¬ execution.stopsAt P k →
      (execution.generatedCut k).cutsAt
        P.feasibleSet
        (execution.basicSolution k) ∧
        execution.relaxation (k + 1) =
          execution.relaxation k ∩ (execution.generatedCut k).halfspace)

/-- `execution.stagewiseClause ... k` unfolds to the stagewise optimization, stopping, and
cut-generation clauses from Algorithm 1.3. -/
theorem stagewiseClause_iff
    {P : MixedIntegerLinearProgram m n p}
    {isOptimalBasicSolutionOfRelaxation :
      ℕ → Set (MixedRealPoint n p) → (MixedRealPoint n p → ℝ) → MixedRealPoint n p → Prop}
    {k : ℕ} :
    execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k ↔
      isOptimalBasicSolutionOfRelaxation k (execution.relaxation k) P.objectiveValue
          (execution.basicSolution k) ∧
        (execution.stopsAt P k →
          P.isOptimalSolution (execution.basicSolution k)) ∧
        (¬ execution.stopsAt P k →
          (execution.generatedCut k).cutsAt
            P.feasibleSet
            (execution.basicSolution k) ∧
            execution.relaxation (k + 1) =
              execution.relaxation k ∩ (execution.generatedCut k).halfspace) :=
  Iff.rfl

namespace stagewiseClause

variable
    {execution : MixedIntegerCuttingPlaneExecution n p}
    {P : MixedIntegerLinearProgram m n p}
    {isOptimalBasicSolutionOfRelaxation :
      ℕ → Set (MixedRealPoint n p) → (MixedRealPoint n p → ℝ) → MixedRealPoint n p → Prop}
    {k : ℕ}

/-- The stage-`k` clause first records optimality of the chosen basic solution for the current
relaxation. -/
theorem optimalBasicSolution
    (hClause : execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k) :
    isOptimalBasicSolutionOfRelaxation
      k (execution.relaxation k) P.objectiveValue (execution.basicSolution k) :=
  hClause.1

/-- If the execution stops at stage `k`, the recorded basic solution is optimal for `P`. -/
theorem stopsAt_imp_isOptimalSolution
    (hClause : execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k) :
    execution.stopsAt P k →
      P.isOptimalSolution (execution.basicSolution k) :=
  hClause.2.1

/-- If the execution does not stop at stage `k`, the generated cut cuts `P.feasibleSet` at the
current basic solution. -/
theorem not_stopsAt_imp_cutsAt
    (hClause : execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k)
    (hNotStop : ¬ execution.stopsAt P k) :
    (execution.generatedCut k).cutsAt P.feasibleSet (execution.basicSolution k) :=
  (hClause.2.2 hNotStop).1

/-- If the execution does not stop at stage `k`, the next relaxation is the intersection of the
current relaxation with the generated-cut halfspace. -/
theorem not_stopsAt_imp_relaxation_eq_inter
    (hClause : execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k)
    (hNotStop : ¬ execution.stopsAt P k) :
    execution.relaxation (k + 1) =
      execution.relaxation k ∩ (execution.generatedCut k).halfspace :=
  (hClause.2.2 hNotStop).2

end stagewiseClause

/-- Algorithm 1.3. A recorded stage-indexed execution satisfies the textbook cutting-plane method
for a mixed-integer linear program `P` when the initial relaxation contains `P.feasibleSet` and
every stage satisfies the source clause. -/
structure IsAlgorithm
    (P : MixedIntegerLinearProgram m n p)
    (isOptimalBasicSolutionOfRelaxation :
      ℕ → Set (MixedRealPoint n p) → (MixedRealPoint n p → ℝ) → MixedRealPoint n p → Prop) :
    Prop where
  initial_contains_feasibleSet :
    P.feasibleSet ⊆ execution.relaxation 0
  stagewise :
    ∀ k,
      execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k

/-- `IsAlgorithm.ofClauses` packages the initial feasible-set containment and the stagewise
transition clause into the source-faithful execution owner for Algorithm 1.3. -/
def IsAlgorithm.ofClauses
    {P : MixedIntegerLinearProgram m n p}
    {isOptimalBasicSolutionOfRelaxation :
      ℕ → Set (MixedRealPoint n p) → (MixedRealPoint n p → ℝ) → MixedRealPoint n p → Prop}
    (h_initial_contains_feasibleSet :
      P.feasibleSet ⊆ execution.relaxation 0)
    (h_stagewise :
      ∀ k,
        execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k) :
    execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation where
  initial_contains_feasibleSet := h_initial_contains_feasibleSet
  stagewise := h_stagewise

/-- `execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation` expands to the initial
feasible-set containment together with the stagewise clause at every stage. -/
theorem isAlgorithm_iff
    (P : MixedIntegerLinearProgram m n p)
    (isOptimalBasicSolutionOfRelaxation :
      ℕ → Set (MixedRealPoint n p) → (MixedRealPoint n p → ℝ) → MixedRealPoint n p → Prop) :
    execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation ↔
      P.feasibleSet ⊆ execution.relaxation 0 ∧
        (∀ k, execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k) := by
  constructor
  · intro hAlgorithm
    exact ⟨hAlgorithm.initial_contains_feasibleSet, hAlgorithm.stagewise⟩
  · rintro ⟨h_initial_contains_feasibleSet, h_stagewise⟩
    exact
      { initial_contains_feasibleSet := h_initial_contains_feasibleSet
        stagewise := h_stagewise }

variable
    {P : MixedIntegerLinearProgram m n p}
    {isOptimalBasicSolutionOfRelaxation :
      ℕ → Set (MixedRealPoint n p) → (MixedRealPoint n p → ℝ) → MixedRealPoint n p → Prop}

namespace IsAlgorithm

/-- An Algorithm 1.3 execution starts from a relaxation containing `P.feasibleSet`. -/
theorem initialRelaxation_contains_feasibleSet
    (hAlgorithm :
      execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation) :
    P.feasibleSet ⊆ execution.relaxation 0 :=
  hAlgorithm.initial_contains_feasibleSet

/-- Every feasible point of `P` lies in the initial relaxation of an Algorithm 1.3 execution. -/
theorem mem_initialRelaxation
    (hAlgorithm :
      execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation)
    {xy : MixedRealPoint n p}
    (hxy : xy ∈ P.feasibleSet) :
    xy ∈ execution.relaxation 0 :=
  hAlgorithm.initial_contains_feasibleSet hxy

/-- At every stage of an Algorithm 1.3 execution, the recorded basic solution satisfies the
stagewise optimality predicate for the current relaxation. -/
theorem optimalBasicSolution
    (hAlgorithm :
      execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation)
    {k : ℕ} :
    isOptimalBasicSolutionOfRelaxation
      k (execution.relaxation k) P.objectiveValue (execution.basicSolution k) :=
  stagewiseClause.optimalBasicSolution (hAlgorithm.stagewise k)

/-- If an Algorithm 1.3 execution stops at stage `k`, the recorded basic solution is optimal for
`P`. -/
theorem stopsAt_imp_isOptimalSolution
    (hAlgorithm :
      execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation)
    {k : ℕ} :
    execution.stopsAt P k →
      P.isOptimalSolution (execution.basicSolution k) :=
  stagewiseClause.stopsAt_imp_isOptimalSolution (hAlgorithm.stagewise k)

/-- If an Algorithm 1.3 execution does not stop at stage `k`, the generated cut cuts
`P.feasibleSet` at the current basic solution. -/
theorem not_stopsAt_imp_cutsAt
    (hAlgorithm :
      execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation)
    {k : ℕ}
    (hNotStop : ¬ execution.stopsAt P k) :
    (execution.generatedCut k).cutsAt P.feasibleSet (execution.basicSolution k) :=
  stagewiseClause.not_stopsAt_imp_cutsAt (hAlgorithm.stagewise k) hNotStop

/-- If an Algorithm 1.3 execution does not stop at stage `k`, the next relaxation is obtained by
intersecting the current relaxation with the generated-cut halfspace. -/
theorem not_stopsAt_imp_relaxation_eq_inter
    (hAlgorithm :
      execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation)
    {k : ℕ}
    (hNotStop : ¬ execution.stopsAt P k) :
    execution.relaxation (k + 1) =
      execution.relaxation k ∩ (execution.generatedCut k).halfspace :=
  stagewiseClause.not_stopsAt_imp_relaxation_eq_inter (hAlgorithm.stagewise k) hNotStop

end IsAlgorithm

/-- An execution satisfying `IsAlgorithm` satisfies the source stagewise clause at every stage. -/
theorem stagewise
    (hAlgorithm :
      execution.IsAlgorithm P isOptimalBasicSolutionOfRelaxation)
    (k : ℕ) :
    execution.stagewiseClause P isOptimalBasicSolutionOfRelaxation k :=
  hAlgorithm.stagewise k

end

end MixedIntegerCuttingPlaneExecution

end Algorithm13
