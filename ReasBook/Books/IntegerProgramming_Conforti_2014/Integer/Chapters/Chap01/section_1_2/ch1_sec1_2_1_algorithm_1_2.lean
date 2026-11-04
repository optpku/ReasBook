/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_algorithm_1_2.Transition

namespace MilpBranchAndBound

variable {m n p : ℕ}

/-- Algorithm 1.2. `IsLpBoundingAlgorithm P run` is the source-faithful stage-indexed execution
specification of branch-and-bound with linear-programming bounding for the MILP `P`: the run
starts from the root LP relaxation with lower bound `⊥` and no incumbent, preserves the incumbent
consistency invariant, and each nonterminal stage satisfies one of the four LP-bounding cases. -/
structure IsLpBoundingAlgorithm
    (P : MixedIntegerLinearProgram m n p)
    (run : ℕ → State n p) : Prop where
  initialRun : run 0 = initial P.lpRelaxation ⊥ none
  incumbentInvariant :
    ∀ k,
      incumbentSpec P.feasibleSet P.integerObjective P.continuousObjective
        (run k).lowerBound (run k).incumbent
  stagewiseStep :
    ∀ k, (run k).activeNodes ≠ [] → lpBoundingClause P (run k) (run (k + 1))

namespace IsLpBoundingAlgorithm

/-- The initial active-node list of an Algorithm 1.2 run is the singleton list containing the
root LP relaxation. -/
@[simp] theorem initialActiveNodes
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (hAlgorithm : IsLpBoundingAlgorithm P run) :
    (run 0).activeNodes = [P.lpRelaxation] := by
  -- Project the initialization equality onto the active-node field.
  have h := congrArg State.activeNodes hAlgorithm.initialRun
  simpa using h

/-- The initial lower bound of an Algorithm 1.2 run is `⊥`. -/
@[simp] theorem initialLowerBound
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (hAlgorithm : IsLpBoundingAlgorithm P run) :
    (run 0).lowerBound = ⊥ := by
  -- Project the initialization equality onto the stored lower bound.
  have h := congrArg State.lowerBound hAlgorithm.initialRun
  simpa using h

/-- The initial incumbent stored by an Algorithm 1.2 run is `none`. -/
@[simp] theorem initialIncumbent_eq
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (hAlgorithm : IsLpBoundingAlgorithm P run) :
    (run 0).incumbent = none := by
  -- Project the initialization equality onto the incumbent field.
  have h := congrArg State.incumbent hAlgorithm.initialRun
  simpa using h

/-- The stage-`0` invariant recovers the initial incumbent specification from `initialRun`. -/
theorem initialIncumbent
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (hAlgorithm : IsLpBoundingAlgorithm P run) :
    incumbentSpec P.feasibleSet P.integerObjective P.continuousObjective ⊥ none := by
  -- Re-express the stage-`0` invariant using the initial state's projections.
  have hInvariant := hAlgorithm.incumbentInvariant 0
  rw [hAlgorithm.initialLowerBound, hAlgorithm.initialIncumbent_eq] at hInvariant
  exact hInvariant

end IsLpBoundingAlgorithm

/-- `IsLpBoundingAlgorithm.ofClauses` packages the defining initialization, invariant, and
transition clauses into the source-faithful LP-bounding branch-and-bound execution owner. -/
def IsLpBoundingAlgorithm.ofClauses
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (h_initialRun : run 0 = initial P.lpRelaxation ⊥ none)
    (h_incumbentInvariant :
      ∀ k,
        incumbentSpec P.feasibleSet P.integerObjective P.continuousObjective
          (run k).lowerBound (run k).incumbent)
    (h_stagewiseStep :
      ∀ k, (run k).activeNodes ≠ [] → lpBoundingClause P (run k) (run (k + 1))) :
    IsLpBoundingAlgorithm P run where
  initialRun := h_initialRun
  incumbentInvariant := h_incumbentInvariant
  stagewiseStep := h_stagewiseStep

/-- The execution-specification predicate expands to initialization at the root LP relaxation, the
incumbent invariant, and the nonterminal LP-bounding transition clause. -/
theorem isLpBoundingAlgorithm_iff
    (P : MixedIntegerLinearProgram m n p)
    (run : ℕ → State n p) :
    IsLpBoundingAlgorithm P run ↔
      run 0 = initial P.lpRelaxation ⊥ none ∧
        (∀ k,
          incumbentSpec P.feasibleSet P.integerObjective P.continuousObjective
            (run k).lowerBound (run k).incumbent) ∧
        (∀ k, (run k).activeNodes ≠ [] → lpBoundingClause P (run k) (run (k + 1))) := by
  constructor
  · intro hAlgorithm
    exact ⟨hAlgorithm.initialRun, hAlgorithm.incumbentInvariant, hAlgorithm.stagewiseStep⟩
  · rintro ⟨h_initialRun, h_incumbentInvariant, h_stagewiseStep⟩
    exact IsLpBoundingAlgorithm.ofClauses h_initialRun h_incumbentInvariant h_stagewiseStep

end MilpBranchAndBound
