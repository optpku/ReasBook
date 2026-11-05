/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_3_algorithm_1_4.Transition

namespace MilpBranchAndCut

open MilpBranchAndBound

variable {m n p : ℕ}

/-- Algorithm 1.4. `IsBranchAndCutAlgorithm P run` is the source-faithful stage-indexed execution
specification of branch-and-cut for the MILP `P`: the run starts from the root LP relaxation with
lower bound `⊥` and no incumbent, preserves the incumbent-consistency invariant, and each
nonterminal stage satisfies the branch-and-cut stagewise clause. -/
structure IsBranchAndCutAlgorithm
    (P : MixedIntegerLinearProgram m n p)
    (run : ℕ → State n p) : Prop
where
  initialRun : run 0 = initial P.lpRelaxation ⊥ none
  incumbentInvariant :
    ∀ k,
      incumbentSpec
        P.feasibleSet P.integerObjective P.continuousObjective
        (run k).lowerBound (run k).incumbent
  stagewiseStep :
    ∀ k, (run k).activeNodes ≠ [] → stagewiseClause P (run k) (run (k + 1))

namespace IsBranchAndCutAlgorithm

/-- The initial active-node list of an Algorithm 1.4 run is the singleton list containing the
root LP relaxation. -/
@[simp] theorem initialActiveNodes
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (hAlgorithm : IsBranchAndCutAlgorithm P run) :
    (run 0).activeNodes = [P.lpRelaxation] := by
  simp [hAlgorithm.initialRun]

/-- The initial lower bound of an Algorithm 1.4 run is `⊥`. -/
@[simp] theorem initialLowerBound
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (hAlgorithm : IsBranchAndCutAlgorithm P run) :
    (run 0).lowerBound = ⊥ := by
  simp [hAlgorithm.initialRun]

/-- The initial incumbent stored by an Algorithm 1.4 run is `none`. -/
@[simp] theorem initialIncumbent_eq
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (hAlgorithm : IsBranchAndCutAlgorithm P run) :
    (run 0).incumbent = none := by
  simp [hAlgorithm.initialRun]

/-- The run invariant at `k = 0` recovers the initial incumbent specification from
`initialRun`. -/
theorem initialIncumbent
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (hAlgorithm : IsBranchAndCutAlgorithm P run) :
    incumbentSpec P.feasibleSet P.integerObjective P.continuousObjective ⊥ none := by
  rw [← hAlgorithm.initialLowerBound, ← hAlgorithm.initialIncumbent_eq]
  exact hAlgorithm.incumbentInvariant 0

end IsBranchAndCutAlgorithm

/-- `IsBranchAndCutAlgorithm.ofClauses` packages the defining initialization, invariant, and
clauses into the source-faithful branch-and-cut execution owner. -/
def IsBranchAndCutAlgorithm.ofClauses
    {P : MixedIntegerLinearProgram m n p}
    {run : ℕ → State n p}
    (h_initialRun : run 0 = initial P.lpRelaxation ⊥ none)
    (h_incumbentInvariant :
      ∀ k,
        incumbentSpec
          P.feasibleSet P.integerObjective P.continuousObjective
          (run k).lowerBound (run k).incumbent)
    (h_stagewiseStep :
      ∀ k, (run k).activeNodes ≠ [] → stagewiseClause P (run k) (run (k + 1))) :
    IsBranchAndCutAlgorithm P run where
  initialRun := h_initialRun
  incumbentInvariant := h_incumbentInvariant
  stagewiseStep := h_stagewiseStep

/-- The execution predicate for Algorithm 1.4 unfolds to root initialization, the incumbent
invariant, and the branch-and-cut stagewise transition clause; the stage-`0` incumbent clause is
recovered by `IsBranchAndCutAlgorithm.initialIncumbent`. -/
theorem isBranchAndCutAlgorithm_iff
    (P : MixedIntegerLinearProgram m n p)
    (run : ℕ → State n p) :
    IsBranchAndCutAlgorithm P run ↔
      run 0 = initial P.lpRelaxation ⊥ none ∧
        (∀ k,
          incumbentSpec
            P.feasibleSet P.integerObjective P.continuousObjective
            (run k).lowerBound (run k).incumbent) ∧
        (∀ k, (run k).activeNodes ≠ [] → stagewiseClause P (run k) (run (k + 1))) := by
  constructor
  · intro hAlgorithm
    exact ⟨hAlgorithm.initialRun, hAlgorithm.incumbentInvariant, hAlgorithm.stagewiseStep⟩
  · rintro ⟨h_initialRun, h_incumbentInvariant, h_stagewiseStep⟩
    exact IsBranchAndCutAlgorithm.ofClauses h_initialRun h_incumbentInvariant h_stagewiseStep

end MilpBranchAndCut
