/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_algorithm_1_2.Transition
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_2_algorithm_1_3.MixedCut

namespace MilpBranchAndCut

open MilpBranchAndBound

variable {m n p : ℕ}

/-- Intersecting an LP node with a cut family keeps the parent node and imposes every cut
halfspace in that family. -/
def applyCuts
    (node : Set (MixedRealPoint n p))
    (cuts : Set (MixedCut n p)) : Set (MixedRealPoint n p) :=
  {xy | xy ∈ node ∧ ∀ cut ∈ cuts, cut.satisfied xy}

/-- Membership in `applyCuts node cuts` means membership in the parent node together with
satisfaction of every listed cut. -/
theorem mem_applyCuts_iff
    {node : Set (MixedRealPoint n p)}
    {cuts : Set (MixedCut n p)}
    {xy : MixedRealPoint n p} :
    xy ∈ applyCuts node cuts ↔ xy ∈ node ∧ ∀ cut ∈ cuts, cut.satisfied xy :=
  Iff.rfl

/-- Cut strengthening is available at `xy` exactly when there is a Definition 1.9 cutting plane
for `P.feasibleSet` at `xy`. -/
def cutStrengtheningAvailable
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) : Prop :=
  ∃ cut : MixedCut n p, cut.cutsAt P.feasibleSet xy

/-- The availability of cut strengthening at `xy` is equivalent to the existence of a nonempty
finite cut family whose members all cut `P.feasibleSet` at `xy`. -/
theorem cutStrengtheningAvailable_iff_exists_nonemptyCuts
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) :
    cutStrengtheningAvailable P xy ↔
      ∃ cuts : Set (MixedCut n p), cuts.Finite ∧ cuts.Nonempty ∧
        ∀ cut ∈ cuts, cut.cutsAt P.feasibleSet xy := by
  constructor
  · rintro ⟨cut, hcut⟩
    refine ⟨{cut}, Set.finite_singleton cut, Set.singleton_nonempty cut, ?_⟩
    intro cut' hmem
    simpa using hmem ▸ hcut
  · rintro ⟨cuts, -, hcuts_nonempty, hcuts⟩
    rcases hcuts_nonempty with ⟨cut, hmem⟩
    exact ⟨cut, hcuts cut hmem⟩

/-- Strengthening by cuts removes a selected active node, keeps the current LP optimum data, and
replaces that node by the explicit cut-refined node obtained from a finite nonempty cut family whose
members are Definition 1.9 cutting planes for `P.feasibleSet` at the current LP optimum, after
the current LP bound has strictly improved the stored incumbent bound. -/
def strengthenByCuts
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) : Prop :=
  ∃ pre node suffix xy z cuts,
    σ.activeNodes = pre ++ node :: suffix ∧
      xy ∈ node ∧
      IsGreatest (P.objectiveValue '' node) z ∧
      P.objectiveValue xy = z ∧
      σ.lowerBound < z ∧
      cuts.Finite ∧
      cuts.Nonempty ∧
      (∀ cut ∈ cuts, cut.cutsAt P.feasibleSet xy) ∧
      List.Perm τ.activeNodes (applyCuts node cuts :: pre ++ suffix) ∧
      τ.lowerBound = σ.lowerBound ∧
      τ.incumbent = σ.incumbent

/-- The cut-strengthening clause unfolds to selection of an active node with LP optimum data, a
nonempty finite cut family of Definition 1.9 cutting planes for `P.feasibleSet` at the current LP
optimum,
replacement by `applyCuts`, and
unchanged lower-bound/incumbent data. -/
theorem strengthenByCuts_iff
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) :
    strengthenByCuts P σ τ ↔
      ∃ pre node suffix xy z cuts,
        σ.activeNodes = pre ++ node :: suffix ∧
          xy ∈ node ∧
          IsGreatest (P.objectiveValue '' node) z ∧
          P.objectiveValue xy = z ∧
          σ.lowerBound < z ∧
          cuts.Finite ∧
          cuts.Nonempty ∧
          (∀ cut ∈ cuts, cut.cutsAt P.feasibleSet xy) ∧
          List.Perm τ.activeNodes (applyCuts node cuts :: pre ++ suffix) ∧
          τ.lowerBound = σ.lowerBound ∧
          τ.incumbent = σ.incumbent :=
  Iff.rfl

/-- Branching by additional constraints is permitted only when the selected LP-optimal point
admits no Definition 1.9 cutting plane for `P.feasibleSet`. -/
def branchByAdditionalConstraintsWhenNoCut
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) : Prop :=
  ∃ pre node suffix xy z children,
    σ.activeNodes = pre ++ node :: suffix ∧
      xy ∈ node ∧
      IsGreatest (P.objectiveValue '' node) z ∧
      P.objectiveValue xy = z ∧
      xy ∉ P.feasibleSet ∧
      σ.lowerBound < z ∧
      ¬ cutStrengtheningAvailable P xy ∧
      admissibleChildren P node xy children ∧
      List.Perm τ.activeNodes (children ++ pre ++ suffix) ∧
      τ.lowerBound = σ.lowerBound ∧
      τ.incumbent = σ.incumbent

/-- The branch fallback clause unfolds to the ordinary Algorithm 1.2 branching data together with
the priority condition that no cut strengthening is available at the current LP optimum. -/
theorem branchByAdditionalConstraintsWhenNoCut_iff
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) :
    branchByAdditionalConstraintsWhenNoCut P σ τ ↔
      ∃ pre node suffix xy z children,
        σ.activeNodes = pre ++ node :: suffix ∧
          xy ∈ node ∧
          IsGreatest (P.objectiveValue '' node) z ∧
          P.objectiveValue xy = z ∧
          xy ∉ P.feasibleSet ∧
          σ.lowerBound < z ∧
          ¬ cutStrengtheningAvailable P xy ∧
          admissibleChildren P node xy children ∧
          List.Perm τ.activeNodes (children ++ pre ++ suffix) ∧
          τ.lowerBound = σ.lowerBound ∧
          τ.incumbent = σ.incumbent :=
  Iff.rfl

/-- The branch fallback of Algorithm 1.4 is in particular a branch-by-additional-constraints step
from Algorithm 1.2. -/
theorem branchByAdditionalConstraintsWhenNoCut_imp_branchByAdditionalConstraints
    {P : MixedIntegerLinearProgram m n p}
    {σ τ : State n p}
    (h : branchByAdditionalConstraintsWhenNoCut P σ τ) :
    branchByAdditionalConstraints P σ τ := by
  rcases h with ⟨pre, node, suffix, xy, z, children, hNodes, hxy, hz, hObj, hNotFeasible,
    hLower, _, hChildren, hPerm, hτLower, hτIncumbent⟩
  exact ⟨pre, node, suffix, xy, z, children, hNodes, hxy, hz, hObj, hNotFeasible, hLower,
    hChildren, hPerm, hτLower, hτIncumbent⟩

/-- One nonterminal branch-and-cut transition is exactly one of the source-faithful cases:
infeasibility pruning, LP-bound pruning, incumbent update, cut strengthening, or branching by
additional constraints when no cut strengthening is available. -/
def stagewiseClause
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) : Prop :=
  pruneByInfeasibility σ τ ∨
    pruneByLpBound P σ τ ∨
    updateIncumbent P σ τ ∨
    strengthenByCuts P σ τ ∨
    branchByAdditionalConstraintsWhenNoCut P σ τ

/-- The one-step branch-and-cut clause unfolds to the five source-order transition cases, with
branching available only as the fallback after cut strengthening is unavailable. -/
theorem stagewiseClause_iff
    (P : MixedIntegerLinearProgram m n p)
    (σ τ : State n p) :
    stagewiseClause P σ τ ↔
      pruneByInfeasibility σ τ ∨
        pruneByLpBound P σ τ ∨
        updateIncumbent P σ τ ∨
        strengthenByCuts P σ τ ∨
        branchByAdditionalConstraintsWhenNoCut P σ τ :=
  Iff.rfl

end MilpBranchAndCut
