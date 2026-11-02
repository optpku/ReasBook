import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_algorithm_1_1.Transition
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_algorithm_1_2.Children

namespace MilpBranchAndBound

variable {m n p : ℕ}

/-- A child family for a selected LP node is admissible when it has at least two children, each
child satisfies the named added-linear-constraint predicate from Step 5(a),
the current LP-optimal point is excluded from every child, and every MILP-feasible point of the
parent node is covered by some child. -/
def admissibleChildren
    (P : MixedIntegerLinearProgram m n p)
    (node : Set (MixedRealPoint n p))
    (xy : MixedRealPoint n p)
    (children : List (Set (MixedRealPoint n p))) : Prop :=
  2 ≤ children.length ∧
    (∀ child ∈ children, linearConstraintChild node child) ∧
    (∀ child ∈ children, xy ∉ child) ∧
    ∀ z, z ∈ P.feasibleSet → z ∈ node → ∃ child ∈ children, z ∈ child

/-- The admissible-child predicate expands to the smaller named child-shape interface used in the
branching clause. -/
@[simp] theorem admissibleChildren_iff_linearConstraintChild
    (P : MixedIntegerLinearProgram m n p)
    (node : Set (MixedRealPoint n p))
    (xy : MixedRealPoint n p)
    (children : List (Set (MixedRealPoint n p))) :
    admissibleChildren P node xy children ↔
      2 ≤ children.length ∧
        (∀ child ∈ children, linearConstraintChild node child) ∧
        (∀ child ∈ children, xy ∉ child) ∧
        (∀ z, z ∈ P.feasibleSet → z ∈ node → ∃ child ∈ children, z ∈ child) := by
  -- Unfold `admissibleChildren` only to the normalized child predicate interface.
  exact Iff.rfl

/-- The admissible-child predicate also expands back to the explicit matrix witness from Step 5(a)
when a downstream argument needs the raw added-constraint data. -/
theorem admissibleChildren_iff
    (P : MixedIntegerLinearProgram m n p)
    (node : Set (MixedRealPoint n p))
    (xy : MixedRealPoint n p)
    (children : List (Set (MixedRealPoint n p))) :
    admissibleChildren P node xy children ↔
      2 ≤ children.length ∧
        (∀ child ∈ children,
          ∃ q : ℕ,
            ∃ A : Matrix (Fin q) (Fin (n + p)) ℝ,
              ∃ b : Fin q → ℝ,
                child = node ∩ ((Fin.appendEquiv n p).symm '' polyhedron_le_set A b)) ∧
        (∀ child ∈ children, xy ∉ child) ∧
        (∀ z, z ∈ P.feasibleSet → z ∈ node → ∃ child ∈ children, z ∈ child) := by
  -- Route correction: keep the main branch interface in the named child predicate normal form,
  -- and reopen the explicit LP-child witness only in this compatibility theorem.
  rw [admissibleChildren_iff_linearConstraintChild]
  rw [forall_mem_linearConstraintChild_iff]

/-- Pruning by an LP bound removes a selected node whose LP optimum value does not exceed the
current incumbent value stored in the state. -/
def pruneByLpBound
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) : Prop :=
  ∃ pre node suffix xy z,
    σ.activeNodes = pre ++ node :: suffix ∧
      xy ∈ node ∧
      IsGreatest (P.objectiveValue '' node) z ∧
      P.objectiveValue xy = z ∧
      z ≤ σ.lowerBound ∧
      τ.activeNodes = pre ++ suffix ∧
      τ.lowerBound = σ.lowerBound ∧
      τ.incumbent = σ.incumbent

/-- Updating the incumbent removes a selected node whose LP optimum is already feasible for the
MILP and strictly improves the currently stored incumbent value. -/
def updateIncumbent
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) : Prop :=
  ∃ pre node suffix xy z,
    σ.activeNodes = pre ++ node :: suffix ∧
      xy ∈ node ∧
      IsGreatest (P.objectiveValue '' node) z ∧
      P.objectiveValue xy = z ∧
      xy ∈ P.feasibleSet ∧
      σ.lowerBound < z ∧
      τ.activeNodes = pre ++ suffix ∧
      τ.lowerBound = z ∧
      τ.incumbent = some xy

/-- Branching by additional linear constraints removes a selected node, keeps the stored lower
bound and incumbent, and replaces that node by an admissible family of at least two LP children. -/
def branchByAdditionalConstraints
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) : Prop :=
  ∃ pre node suffix xy z children,
    σ.activeNodes = pre ++ node :: suffix ∧
      xy ∈ node ∧
      IsGreatest (P.objectiveValue '' node) z ∧
      P.objectiveValue xy = z ∧
      xy ∉ P.feasibleSet ∧
      σ.lowerBound < z ∧
      admissibleChildren P node xy children ∧
      List.Perm τ.activeNodes (children ++ pre ++ suffix) ∧
      τ.lowerBound = σ.lowerBound ∧
      τ.incumbent = σ.incumbent

/-- The nonterminal LP-bounding step is exactly one of the four source cases: infeasible-node
pruning, incumbent-dominated-node pruning, incumbent update, or branching by added constraints. -/
def lpBoundingClause
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) : Prop :=
  pruneByInfeasibility σ τ ∨
    pruneByLpBound P σ τ ∨
    updateIncumbent P σ τ ∨
    branchByAdditionalConstraints P σ τ

/-- The LP-bounding clause unfolds to the four branch-and-bound transition cases. -/
@[simp] theorem lpBoundingClause_iff
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) :
    lpBoundingClause P σ τ ↔
      pruneByInfeasibility σ τ ∨
        pruneByLpBound P σ τ ∨
        updateIncumbent P σ τ ∨
        branchByAdditionalConstraints P σ τ :=
  Iff.rfl

end MilpBranchAndBound
