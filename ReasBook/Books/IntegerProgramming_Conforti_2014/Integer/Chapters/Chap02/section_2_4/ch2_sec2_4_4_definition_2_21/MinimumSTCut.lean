/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Real.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Cuts
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Weight

open scoped BigOperators

public section

namespace SimpleGraph.MinimumSTCut

universe u

variable {V : Type u}

section CutObjectiveValues

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The attained cut weights of `s,t`-cut sides in `G` with respect to the edge weights `w`. -/
def cutObjectiveValues (s t : V) (w : G.edgeSet → ℝ) : Set ℝ :=
  {r | ∃ S : Finset V, SimpleGraph.IsSTCutSide s t S ∧ G.cutWeight w S = r}

/-- Membership in `cutObjectiveValues G s t w` means that some `s,t`-cut side has cut weight `r`.
-/
theorem mem_cutObjectiveValues_iff
    {s t : V} {w : G.edgeSet → ℝ} {r : ℝ} :
    r ∈ cutObjectiveValues G s t w ↔
      ∃ S : Finset V, SimpleGraph.IsSTCutSide s t S ∧ G.cutWeight w S = r := by
  -- Unfold the set-builder definition to expose its existential membership condition.
  rfl

/-- The weight of every `s,t`-cut side belongs to `cutObjectiveValues G s t w`. -/
theorem cutWeight_mem_cutObjectiveValues
    {s t : V} (w : G.edgeSet → ℝ) {S : Finset V} (hS : SimpleGraph.IsSTCutSide s t S) :
    G.cutWeight w S ∈ cutObjectiveValues G s t w := by
  -- Use the given cut side as the witness for the attained cut weight.
  rw [mem_cutObjectiveValues_iff]
  have hweight : G.cutWeight w S = G.cutWeight w S := rfl
  exact ⟨S, hS, hweight⟩

end CutObjectiveValues

section

variable (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

/-- The sum of the edge variables `x` over the edges used by the path `p`, expressed in the
ambient edge coordinates of `G`. -/
noncomputable def pathEdgeSum (x : G.edgeSet → ℝ) {s t : V} (p : G.Path s t) : ℝ :=
  open scoped Classical in
    ∑ e : G.edgeSet, if e.1 ∈ (p : G.Walk s t).edgeSet then x e else 0

/-- `pathEdgeSum G x p` unfolds as the ambient edge sum filtered by membership in
`(p : G.Walk s t).edgeSet`. -/
theorem pathEdgeSum_def
    (x : G.edgeSet → ℝ) {s t : V} (p : G.Path s t) :
    pathEdgeSum G x p =
      (open scoped Classical in
        ∑ e : G.edgeSet, if e.1 ∈ (p : G.Walk s t).edgeSet then x e else 0) := by
  -- Unfold only the named path-edge sum; the path representation remains opaque.
  rfl

/-- The binary `s,t`-path-cover feasible region for the minimum-weight `s,t`-cut formulation on
`G`. -/
def feasible (s t : V) (x : G.edgeSet → ℝ) : Prop :=
  (∀ p : G.Path s t, 1 ≤ pathEdgeSum G x p) ∧
    ∀ e : G.edgeSet, x e = 0 ∨ x e = 1

/-- Membership in `feasible G s t x` means that every `s,t`-path has edge sum at least `1` and
that `x` is binary on each edge. -/
theorem feasible_iff
    {s t : V} {x : G.edgeSet → ℝ} :
    feasible G s t x ↔
      (∀ p : G.Path s t, 1 ≤ pathEdgeSum G x p) ∧
        ∀ e : G.edgeSet, x e = 0 ∨ x e = 1 := by
  -- Unfold feasibility into its path-cover and binary-coordinate conditions.
  rfl

/-- The `s,t`-path covering inequality extracted from `feasible G s t x`. -/
theorem feasible_path_ge_one
    {s t : V} {x : G.edgeSet → ℝ} (hx : feasible G s t x) (p : G.Path s t) :
    1 ≤ pathEdgeSum G x p := by
  -- Normalize feasibility once, then project its path-cover component.
  rw [feasible_iff] at hx
  exact hx.1 p

/-- The binary edge-coordinate condition extracted from `feasible G s t x`. -/
theorem feasible_binary
    {s t : V} {x : G.edgeSet → ℝ} (hx : feasible G s t x) (e : G.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  -- Normalize feasibility once, then project its binary-coordinate component.
  rw [feasible_iff] at hx
  exact hx.2 e

/-- The weighted objective of the binary `s,t`-path-cover formulation on `G`. -/
def objective (w : G.edgeSet → ℝ) (x : G.edgeSet → ℝ) : ℝ :=
  ∑ e : G.edgeSet, w e * x e

/-- `objective G w x` unfolds as `∑ e : G.edgeSet, w e * x e`. -/
theorem objective_def
    (w : G.edgeSet → ℝ) (x : G.edgeSet → ℝ) :
    objective G w x = ∑ e : G.edgeSet, w e * x e := by
  -- Unfold the named objective to its finite weighted sum.
  rfl

/-- The attained objective values of the binary `s,t`-path-cover formulation on `G`. -/
def objectiveValues (s t : V) (w : G.edgeSet → ℝ) : Set ℝ :=
  {r | ∃ x : G.edgeSet → ℝ, feasible G s t x ∧ objective G w x = r}

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_21/MinimumSTCut.lean: <!-- http -->
Membership in `objectiveValues G s t w` means that some feasible binary edge assignment attains
the objective value `r`. -/
theorem mem_objectiveValues_iff
    {s t : V} {w : G.edgeSet → ℝ} {r : ℝ} :
    r ∈ objectiveValues G s t w ↔
      ∃ x : G.edgeSet → ℝ, feasible G s t x ∧ objective G w x = r := by
  -- Unfold the attained-value set to expose its feasible witness and objective equation.
  rfl

end

end SimpleGraph.MinimumSTCut

end
