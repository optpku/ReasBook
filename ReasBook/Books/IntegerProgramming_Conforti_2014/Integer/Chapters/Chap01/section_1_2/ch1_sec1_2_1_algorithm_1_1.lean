/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_algorithm_1_1.Transition

public section

namespace MilpBranchAndBound

/-- Algorithm 1.1. `isAlgorithm S P₀ c h L₀ incumbent₀ run` is the source-faithful execution
specification of branch-and-bound for the MILP feasible set `S ⊆ ℤ^n × ℝ^m`: the run starts from
the root relaxation `P₀`, stores a lower bound and associated incumbent, and every nonterminal
state advances by one of the four stagewise cases from the textbook algorithm. -/
structure isAlgorithm
    {n m : ℕ}
    (S : Set (MixedRealPoint n m))
    (P₀ : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (L₀ : WithBot ℝ)
    (incumbent₀ : Option (MixedRealPoint n m))
    (run : ℕ → State n m) : Prop where
  subsetLattice : S ⊆ mixed_integer_lattice n m
  subsetRoot : S ⊆ P₀
  initialRun : run 0 = initial P₀ L₀ incumbent₀
  incumbentInvariant : ∀ k, incumbentSpec S c h (run k).lowerBound (run k).incumbent
  stagewiseStep : ∀ k, (run k).activeNodes ≠ [] → stagewiseClause S c h (run k) (run (k + 1))

namespace isAlgorithm

/-- The initial active-node list of an Algorithm 1.1 run is the singleton list containing the
root relaxation `P₀`. -/
@[simp] theorem initialActiveNodes
    {n m : ℕ}
    {S : Set (MixedRealPoint n m)}
    {P₀ : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {L₀ : WithBot ℝ}
    {incumbent₀ : Option (MixedRealPoint n m)}
    {run : ℕ → State n m}
    (hAlgorithm : isAlgorithm S P₀ c h L₀ incumbent₀ run) :
    (run 0).activeNodes = [P₀] := by
  simp [hAlgorithm.initialRun]

/-- The initial lower bound of an Algorithm 1.1 run is the prescribed starting bound `L₀`. -/
@[simp] theorem initialLowerBound
    {n m : ℕ}
    {S : Set (MixedRealPoint n m)}
    {P₀ : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {L₀ : WithBot ℝ}
    {incumbent₀ : Option (MixedRealPoint n m)}
    {run : ℕ → State n m}
    (hAlgorithm : isAlgorithm S P₀ c h L₀ incumbent₀ run) :
    (run 0).lowerBound = L₀ := by
  simp [hAlgorithm.initialRun]

/-- The initial incumbent stored by an Algorithm 1.1 run is the prescribed starting incumbent
`incumbent₀`. -/
@[simp] theorem initialIncumbent_eq
    {n m : ℕ}
    {S : Set (MixedRealPoint n m)}
    {P₀ : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {L₀ : WithBot ℝ}
    {incumbent₀ : Option (MixedRealPoint n m)}
    {run : ℕ → State n m}
    (hAlgorithm : isAlgorithm S P₀ c h L₀ incumbent₀ run) :
    (run 0).incumbent = incumbent₀ := by
  simp [hAlgorithm.initialRun]

/-- The run invariant at `k = 0` recovers the initial incumbent specification from
`initialRun`. -/
theorem initialIncumbent
    {n m : ℕ}
    {S : Set (MixedRealPoint n m)}
    {P₀ : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {L₀ : WithBot ℝ}
    {incumbent₀ : Option (MixedRealPoint n m)}
    {run : ℕ → State n m}
    (hAlgorithm : isAlgorithm S P₀ c h L₀ incumbent₀ run) :
    incumbentSpec S c h L₀ incumbent₀ := by
  rw [← hAlgorithm.initialLowerBound, ← hAlgorithm.initialIncumbent_eq]
  exact hAlgorithm.incumbentInvariant 0

end isAlgorithm

/-- `isAlgorithm.ofClauses` packages the defining initialization, invariant, and transition clauses
into the source-faithful branch-and-bound execution owner. -/
def isAlgorithm.ofClauses
    {n m : ℕ}
    {S : Set (MixedRealPoint n m)}
    {P₀ : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {L₀ : WithBot ℝ}
    {incumbent₀ : Option (MixedRealPoint n m)}
    {run : ℕ → State n m}
    (h_subsetLattice : S ⊆ mixed_integer_lattice n m)
    (h_subsetRoot : S ⊆ P₀)
    (h_initialRun : run 0 = initial P₀ L₀ incumbent₀)
    (h_incumbentInvariant : ∀ k, incumbentSpec S c h (run k).lowerBound (run k).incumbent)
    (h_stagewiseStep :
      ∀ k, (run k).activeNodes ≠ [] → stagewiseClause S c h (run k) (run (k + 1))) :
    isAlgorithm S P₀ c h L₀ incumbent₀ run where
  subsetLattice := h_subsetLattice
  subsetRoot := h_subsetRoot
  initialRun := h_initialRun
  incumbentInvariant := h_incumbentInvariant
  stagewiseStep := h_stagewiseStep

/-- `isAlgorithm S P₀ c h L₀ incumbent₀ run` expands to the initialization clauses, the incumbent
consistency invariant, and the stagewise transition clause at every nonterminal state; the stage-0
incumbent clause is recovered by `isAlgorithm.initialIncumbent`. -/
theorem isAlgorithm_iff
    {n m : ℕ}
    (S : Set (MixedRealPoint n m))
    (P₀ : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (L₀ : WithBot ℝ)
    (incumbent₀ : Option (MixedRealPoint n m))
    (run : ℕ → State n m) :
    isAlgorithm S P₀ c h L₀ incumbent₀ run ↔
      S ⊆ mixed_integer_lattice n m ∧
        S ⊆ P₀ ∧
        run 0 = initial P₀ L₀ incumbent₀ ∧
        (∀ k, incumbentSpec S c h (run k).lowerBound (run k).incumbent) ∧
        (∀ k, (run k).activeNodes ≠ [] → stagewiseClause S c h (run k) (run (k + 1))) := by
  constructor
  · intro hAlgorithm
    exact ⟨hAlgorithm.subsetLattice, hAlgorithm.subsetRoot, hAlgorithm.initialRun,
      hAlgorithm.incumbentInvariant, hAlgorithm.stagewiseStep⟩
  · rintro ⟨h_subsetLattice, h_subsetRoot, h_initialRun, h_incumbentInvariant, h_stagewiseStep⟩
    exact isAlgorithm.ofClauses h_subsetLattice h_subsetRoot h_initialRun h_incumbentInvariant
      h_stagewiseStep

end MilpBranchAndBound
