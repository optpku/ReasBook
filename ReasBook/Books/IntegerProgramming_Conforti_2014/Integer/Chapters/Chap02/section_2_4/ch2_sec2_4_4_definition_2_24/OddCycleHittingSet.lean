/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image

open scoped BigOperators

public section

namespace SimpleGraph.OddCycleHittingSet

universe u

variable {V : Type u}

/-- An edge set `H` is feasible for the odd-cycle hitting-set formulation on `G` when it is
contained in `G.edgeSet` and meets every odd cycle of `G`. -/
def feasible (G : SimpleGraph V) (H : Set (Sym2 V)) : Prop :=
  H ⊆ G.edgeSet ∧
    ∀ u : V, ∀ p : G.Walk u u, p.IsCycle → Odd p.length → ∃ e, e ∈ p.edges ∧ e ∈ H

/-- Membership in `feasible G H` means that `H` is an edge subset of `G` meeting every odd cycle.
-/
theorem feasible_iff
    {G : SimpleGraph V} {H : Set (Sym2 V)} :
    feasible G H ↔
      H ⊆ G.edgeSet ∧
        ∀ u : V, ∀ p : G.Walk u u, p.IsCycle → Odd p.length → ∃ e, e ∈ p.edges ∧ e ∈ H := by
  -- This is the defining conjunction of `feasible`.
  rfl

/-- The weighted objective of the odd-cycle hitting-set formulation, obtained by summing `w` over
the selected graph edges in `H`. -/
noncomputable def objective
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (H : Set (Sym2 V)) : ℝ := by
  classical
  exact (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ H).sum w

/-- `objective G w H` is the sum of `w` over the edges of `G` that lie in `H`. -/
theorem objective_def
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (H : Set (Sym2 V)) :
    objective G w H =
      (by
        classical
        exact (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ H).sum w) := by
  -- Unfold the definition of the filtered edge-weight sum.
  rfl

/-- The objective values attained by feasible odd-cycle hitting sets of `G`. -/
def objectiveValues
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) : Set ℝ :=
  objective G w '' {H | feasible G H}

/-- Membership in `objectiveValues G w` means that some feasible odd-cycle hitting set attains
that value. -/
theorem mem_objectiveValues_iff
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {w : G.edgeSet → ℝ} {z : ℝ} :
    z ∈ objectiveValues G w ↔
      ∃ H : Set (Sym2 V), feasible G H ∧ objective G w H = z := by
  constructor
  · intro hz
    -- Unpack the image/set-builder description of attained objective values.
    rcases hz with ⟨H, hH, rfl⟩
    exact ⟨H, hH, rfl⟩
  · rintro ⟨H, hH, rfl⟩
    -- Repackage a feasible witness into the image of `objective`.
    exact ⟨H, hH, rfl⟩

/-- `H` is optimal for the odd-cycle hitting-set formulation when it is feasible and has minimum
objective value among all feasible odd-cycle hitting sets. -/
def IsOptimal
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (H : Set (Sym2 V)) : Prop :=
  feasible G H ∧ ∀ H' : Set (Sym2 V), feasible G H' → objective G w H ≤ objective G w H'

/-- Unfolding characterization of optimality for the odd-cycle hitting-set formulation. -/
theorem isOptimal_iff
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {w : G.edgeSet → ℝ} {H : Set (Sym2 V)} :
    IsOptimal G w H ↔
      feasible G H ∧
        ∀ H' : Set (Sym2 V), feasible G H' → objective G w H ≤ objective G w H' := by
  -- This is the defining conjunction of `IsOptimal`.
  rfl

end SimpleGraph.OddCycleHittingSet
