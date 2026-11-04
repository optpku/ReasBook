/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Bridge

public section

/-!
Minimum cut and spanning tree formulation.

This item uses the canonical spanning-tree condition `T.spanningCoe.IsTree` on subgraphs and the
reusable formulation API in `SimpleGraph.MinimumCut` for the corresponding `0`-`1` minimum-cut
model.
-/

/- Definition 2.23 (1). The textbook notion of a spanning tree of `G` is formalized by the
canonical condition `T.spanningCoe.IsTree` on subgraphs `T : G.Subgraph`. -/
#check fun {V : Type _} (G : SimpleGraph V) (T : G.Subgraph) ↦ T.spanningCoe.IsTree

/- The canonical owners for Definition 2.23 (2) are the attained-value sets below. -/
#check SimpleGraph.MinimumCut.cutObjectiveValues
#check SimpleGraph.MinimumCut.objectiveValues

namespace SimpleGraph
namespace MinimumCut

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Definition 2.23 (2). For a finite connected undirected graph `G` with nonnegative edge
weights `w`, the minimum-cut problem has the same least objective values as the `0`-`1`
spanning-tree-cover formulation `SimpleGraph.MinimumCut.objectiveValues G w`. -/
theorem isLeast_cutObjectiveValues_iff_isLeast_objectiveValues
    (w : G.edgeSet → ℝ) (hG : G.Connected) (hw : ∀ e : G.edgeSet, 0 ≤ w e) {r : ℝ} :
    IsLeast (cutObjectiveValues G w) r ↔ IsLeast (objectiveValues G w) r := by
  classical
  constructor
  · intro hr
    rcases hr with ⟨hrMem, hrMin⟩
    rcases (mem_cutObjectiveValues_iff G).1 hrMem with
      ⟨S, hS, hObj⟩
    refine ⟨?_, ?_⟩
    · -- A least cut value is attained by its cut indicator.
      refine (mem_objectiveValues_iff G).2 ?_
      refine ⟨cutIndicator G S, cutIndicator_feasible_of_isProperCutSide G hS, ?_⟩
      rw [objective_cutIndicator_eq_cutWeight]
      exact hObj
    · intro r' hr'
      rcases (mem_objectiveValues_iff G).1 hr' with ⟨x, hx, hxr⟩
      rcases existsProperCutSide_le_objective_of_feasible G hG w hw hx with ⟨S', hS', hle⟩
      have hrCut : G.cutWeight w S' ∈ cutObjectiveValues G w :=
        cutWeight_mem_cutObjectiveValues G w hS'
      calc
        r ≤ G.cutWeight w S' := hrMin hrCut
        _ ≤ objective G w x := hle
        _ = r' := hxr
  · intro hr
    rcases hr with ⟨hrMem, hrMin⟩
    rcases (mem_objectiveValues_iff G).1 hrMem with
      ⟨x, hx, hObj⟩
    rcases existsProperCutSide_le_objective_of_feasible G hG w hw hx with ⟨S, hS, hle⟩
    have hcutMem : G.cutWeight w S ∈ cutObjectiveValues G w :=
      cutWeight_mem_cutObjectiveValues G w hS
    refine ⟨?_, ?_⟩
    · -- The dominating cut must attain the same least value.
      have hObjMem : objective G w (cutIndicator G S) ∈ objectiveValues G w :=
        (mem_objectiveValues_iff G).2
          ⟨cutIndicator G S, cutIndicator_feasible_of_isProperCutSide G hS, rfl⟩
      have hUpper : r ≤ objective G w (cutIndicator G S) := hrMin hObjMem
      have hLower : G.cutWeight w S ≤ r := by
        calc
          G.cutWeight w S ≤ objective G w x := hle
          _ = r := hObj
      have hEq : G.cutWeight w S = r := by
        rw [objective_cutIndicator_eq_cutWeight G] at hUpper
        exact le_antisymm hLower hUpper
      exact (mem_cutObjectiveValues_iff G).2 ⟨S, hS, hEq⟩
    · intro r' hr'
      rcases (mem_cutObjectiveValues_iff G).1 hr' with ⟨S', hS', hS'r⟩
      have hrObj : objective G w (cutIndicator G S') ∈ objectiveValues G w :=
        (mem_objectiveValues_iff G).2
          ⟨cutIndicator G S', cutIndicator_feasible_of_isProperCutSide G hS', rfl⟩
      calc
        r ≤ objective G w (cutIndicator G S') := hrMin hrObj
        _ = G.cutWeight w S' := objective_cutIndicator_eq_cutWeight G w S'
        _ = r' := hS'r

end MinimumCut
end SimpleGraph
