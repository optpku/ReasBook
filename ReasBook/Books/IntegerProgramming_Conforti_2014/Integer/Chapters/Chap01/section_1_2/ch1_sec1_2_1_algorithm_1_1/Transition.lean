module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_algorithm_1_1.Execution
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_definition_1_8.Children

public section

namespace MilpBranchAndBound

/-- Pruning by infeasibility removes an active node whose relaxation polyhedron is empty and leaves
the lower bound and incumbent unchanged. -/
def pruneByInfeasibility
    {n m : ℕ}
    (σ τ : State n m) : Prop :=
  ∃ pre P suffix,
    σ.activeNodes = pre ++ P :: suffix ∧
      P = ∅ ∧
      τ.activeNodes = pre ++ suffix ∧
      τ.lowerBound = σ.lowerBound ∧
      τ.incumbent = σ.incumbent

/-- Pruning by integrality removes an active node whose LP optimum is attained at a feasible mixed
integer point, updates the lower bound to `max {L, z}`, and records the optimum as the incumbent
when it strictly improves the bound. -/
def pruneByIntegrality
    {n m : ℕ}
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (σ τ : State n m) : Prop :=
  ∃ pre P suffix xy z,
    σ.activeNodes = pre ++ P :: suffix ∧
      xy ∈ P ∧
      IsGreatest (mixed_linear_objective c h '' P) z ∧
      mixed_linear_objective c h xy = z ∧
      xy ∈ mixed_integer_lattice n m ∧
      xy ∈ S ∧
      τ.activeNodes = pre ++ suffix ∧
      τ.lowerBound = max σ.lowerBound (z : WithBot ℝ) ∧
      (σ.lowerBound < (z : WithBot ℝ) ∧ τ.incumbent = some xy ∨
        (z : WithBot ℝ) ≤ σ.lowerBound ∧ τ.incumbent = σ.incumbent)

/-- Pruning by bound removes an active node whose LP optimum value `z` does not improve the
current lower bound `L`, after the mixed-integer incumbent case has already failed. -/
def pruneByBound
    {n m : ℕ}
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (σ τ : State n m) : Prop :=
  ∃ pre P suffix xy z,
    σ.activeNodes = pre ++ P :: suffix ∧
      xy ∈ P ∧
      IsGreatest (mixed_linear_objective c h '' P) z ∧
      mixed_linear_objective c h xy = z ∧
      ¬ (xy ∈ mixed_integer_lattice n m ∧ xy ∈ S) ∧
      (z : WithBot ℝ) ≤ σ.lowerBound ∧
      τ.activeNodes = pre ++ suffix ∧
      τ.lowerBound = σ.lowerBound ∧
      τ.incumbent = σ.incumbent

/-- Branching on a fractional coordinate removes the selected active node, chooses a fractional
integer-variable index `j`, and inserts the two split children from `(1.u26)` while leaving the
lower bound and incumbent unchanged. -/
def branchOnFractional
    {n m : ℕ}
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (σ τ : State n m) : Prop :=
  ∃ pre P suffix xy z j,
    σ.activeNodes = pre ++ P :: suffix ∧
      xy ∈ P ∧
      IsGreatest (mixed_linear_objective c h '' P) z ∧
      mixed_linear_objective c h xy = z ∧
      ¬ (xy ∈ mixed_integer_lattice n m ∧ xy ∈ S) ∧
      σ.lowerBound < (z : WithBot ℝ) ∧
      Int.fract (xy.1 j) ≠ 0 ∧
      List.Perm τ.activeNodes
        (leftChild P j (xy.1 j) :: rightChild P j (xy.1 j) :: (pre ++ suffix)) ∧
      τ.lowerBound = σ.lowerBound ∧
      τ.incumbent = σ.incumbent

/-- The stagewise clause for one transition of the generic MILP branch-and-bound algorithm is the
disjunction of the source's four cases: infeasibility, integrality, bound pruning, or branching on
a fractional integer coordinate. -/
def stagewiseClause
    {n m : ℕ}
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (σ τ : State n m) : Prop :=
  pruneByInfeasibility σ τ ∨
    pruneByIntegrality S c h σ τ ∨
    pruneByBound S c h σ τ ∨
    branchOnFractional S c h σ τ

/-- `stagewiseClause S c h σ τ` unfolds to the four source-faithful branch-and-bound transition
cases. -/
theorem stagewiseClause_iff
    {n m : ℕ}
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (σ τ : State n m) :
    stagewiseClause S c h σ τ ↔
      pruneByInfeasibility σ τ ∨
        pruneByIntegrality S c h σ τ ∨
        pruneByBound S c h σ τ ∨
        branchOnFractional S c h σ τ :=
  Iff.rfl

end MilpBranchAndBound

end
