/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Bridge

open scoped BigOperators

public section

namespace SimpleGraph.ShortestPathCutLP

universe u

variable {V : Type u}

section

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The sum of the edge coordinates `x` over the edges crossing the cut side `S`. -/
noncomputable def cutEdgeSum (x : G.edgeSet → ℝ) (S : Finset V) : ℝ :=
  Finset.sum (SimpleGraph.MinimumCut.cutEdges G S) x

/-- `cutEdgeSum G x S` is the sum of `x` over `SimpleGraph.MinimumCut.cutEdges G S`. -/
theorem cutEdgeSum_def
    (x : G.edgeSet → ℝ) (S : Finset V) :
    cutEdgeSum G x S = Finset.sum (SimpleGraph.MinimumCut.cutEdges G S) x := by
  -- This is the defining equation of `cutEdgeSum`.
  rfl

/-- The cut-constraint and box-constraint feasible region for the undirected shortest
`s,t`-path linear program on `G`.

This declaration belongs to the item
`remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_22/ShortestPathCutLP.lean`.
-/
def feasible (s t : V) (x : G.edgeSet → ℝ) : Prop :=
  (∀ S : Finset V, SimpleGraph.IsSTCutSide s t S → 1 ≤ cutEdgeSum G x S) ∧
    (∀ e : G.edgeSet, 0 ≤ x e) ∧
      ∀ e : G.edgeSet, x e ≤ 1

/-- Membership in `feasible G s t x` means that every `s,t`-cut side has cut sum at least `1`
and every edge coordinate lies in the interval `[0, 1]`. -/
theorem feasible_iff
    {s t : V} {x : G.edgeSet → ℝ} :
    feasible G s t x ↔
      (∀ S : Finset V, SimpleGraph.IsSTCutSide s t S → 1 ≤ cutEdgeSum G x S) ∧
        (∀ e : G.edgeSet, 0 ≤ x e) ∧
          ∀ e : G.edgeSet, x e ≤ 1 := by
  -- This theorem only exposes the conjunction stored in `feasible`.
  rfl

/-- The `s,t`-cut inequality extracted from `feasible G s t x`. -/
theorem feasible_cut_ge_one
    {s t : V} {x : G.edgeSet → ℝ} (hx : feasible G s t x)
    {S : Finset V} (hS : SimpleGraph.IsSTCutSide s t S) :
    1 ≤ cutEdgeSum G x S := by
  -- The first feasibility conjunct is exactly the family of cut inequalities.
  exact hx.1 S hS

/-- The nonnegativity constraint extracted from `feasible G s t x`. -/
theorem feasible_nonneg
    {s t : V} {x : G.edgeSet → ℝ} (hx : feasible G s t x) (e : G.edgeSet) :
    0 ≤ x e := by
  -- The second feasibility conjunct records coordinatewise nonnegativity.
  exact hx.2.1 e

/-- The upper box constraint extracted from `feasible G s t x`. -/
theorem feasible_le_one
    {s t : V} {x : G.edgeSet → ℝ} (hx : feasible G s t x) (e : G.edgeSet) :
    x e ≤ 1 := by
  -- The final feasibility conjunct records the upper box bound.
  exact hx.2.2 e

/-- The weighted objective of the undirected shortest `s,t`-path cut formulation on `G`. -/
def objective (w x : G.edgeSet → ℝ) : ℝ :=
  ∑ e : G.edgeSet, w e * x e

omit [DecidableEq V] in
/-- `objective G w x` is the sum `∑ e, w e * x e` over the ambient edge coordinates of `G`. -/
theorem objective_def
    (w x : G.edgeSet → ℝ) :
    objective G w x = (∑ e : G.edgeSet, w e * x e) := by
  -- This is the defining equation of `objective`.
  rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_22/ShortestPathCutLP.lean.
Definition 2.22. `objectiveValues G s t w` is the set of objective values attained by feasible
solutions of the undirected shortest `s,t`-path cut formulation on `G`. -/
def objectiveValues (s t : V) (w : G.edgeSet → ℝ) : Set ℝ :=
  {r | ∃ x : G.edgeSet → ℝ, feasible G s t x ∧ objective G w x = r}

/-- `objectiveValues G s t w` is definitionally the set of real numbers attained by feasible
edge assignments through the objective. -/
theorem objectiveValues_def
    (s t : V) (w : G.edgeSet → ℝ) :
    objectiveValues G s t w =
      {r | ∃ x : G.edgeSet → ℝ, feasible G s t x ∧ objective G w x = r} := by
  -- This companion theorem exposes the defining set-builder of `objectiveValues`.
  rfl

/-- Membership in `objectiveValues G s t w` means that some feasible edge assignment attains the
objective value `r`. -/
theorem mem_objectiveValues_iff
    {s t : V} {w : G.edgeSet → ℝ} {r : ℝ} :
    r ∈ objectiveValues G s t w ↔
      ∃ x : G.edgeSet → ℝ, feasible G s t x ∧ objective G w x = r := by
  -- Unfold `objectiveValues` and simplify set membership to the defining existential.
  simp [objectiveValues_def]

end

end SimpleGraph.ShortestPathCutLP
