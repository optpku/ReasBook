module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_21.MinimumSTCut
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_21.MinimumSTCut.Bridge

public section

/-!
Minimum-weight `s,t`-cut and its binary path formulation.

The reusable owner is `SimpleGraph.MinimumSTCut`; the declarations below record the canonical
cut-side and path-cover API for Definition 2.21.
-/

/- Definition 2.21 (1): the textbook notion of an
`s,t`-cut side is formalized by `SimpleGraph.IsSTCutSide`, and the canonical attained-value owners
for the cut formulation and its equivalent binary path formulation are the declarations below. -/
#check SimpleGraph.IsSTCutSide
#check SimpleGraph.MinimumSTCut.cutObjectiveValues
#check SimpleGraph.MinimumSTCut.feasible
#check SimpleGraph.MinimumSTCut.objectiveValues

namespace SimpleGraph.MinimumSTCut

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Helper for Definition 2.21: the path-cover objective of a cut indicator equals the weight of
the corresponding cut. -/
private theorem objective_cutIndicator_eq_cutWeight
    (w : G.edgeSet → ℝ) (S : Finset V) :
    objective G w (SimpleGraph.MinimumCut.cutIndicator G S) = G.cutWeight w S := by
  -- Both formulations use the same weighted edge sum, so the minimum-cut computation applies.
  simpa only [objective_def, SimpleGraph.MinimumCut.objective_def] using
    SimpleGraph.MinimumCut.objective_cutIndicator_eq_cutWeight G w S

/-- Helper for Definition 2.21: a cut side's indicator attains a feasible path-cover objective
value. -/
private theorem objective_cutIndicator_mem_objectiveValues
    {s t : V} (w : G.edgeSet → ℝ) {S : Finset V} (hS : SimpleGraph.IsSTCutSide s t S) :
    objective G w (SimpleGraph.MinimumCut.cutIndicator G S) ∈ objectiveValues G s t w := by
  -- Feasibility of the indicator supplies the witness for attained objective membership.
  refine (mem_objectiveValues_iff G).2 ?_
  refine ⟨SimpleGraph.MinimumCut.cutIndicator G S, ?_, ?_⟩
  · exact cutIndicator_feasible_of_isSTCutSide G hS
  · rfl

/-- Definition 2.21 (2). For a finite connected undirected graph `G` with distinct vertices `s` and
`t` and nonnegative edge weights `w`, the least attained `s,t`-cut value is exactly the least
attained value of the equivalent binary `s,t`-path-cover formulation
`SimpleGraph.MinimumSTCut.objectiveValues G s t w`. -/
theorem isLeast_cutObjectiveValues_iff_isLeast_objectiveValues
    (s t : V) (w : G.edgeSet → ℝ) (hG : G.Connected) (hst : s ≠ t)
    (hw : ∀ e : G.edgeSet, 0 ≤ w e) {r : ℝ} :
    IsLeast (cutObjectiveValues G s t w) r ↔ IsLeast (objectiveValues G s t w) r := by
  classical
  constructor
  · intro hr
    rcases hr with ⟨hrMem, hrMin⟩
    rcases (mem_cutObjectiveValues_iff G).1 hrMem with ⟨S, hS, hObj⟩
    refine ⟨?_, ?_⟩
    · -- The indicator of an attaining cut realizes the same path-cover objective value.
      refine (mem_objectiveValues_iff G).2 ?_
      refine ⟨SimpleGraph.MinimumCut.cutIndicator G S, ?_, ?_⟩
      · exact cutIndicator_feasible_of_isSTCutSide G hS
      · rw [objective_cutIndicator_eq_cutWeight G]
        exact hObj
    · -- Every feasible value dominates a cut value, hence also the least cut value.
      intro r' hr'
      rcases (mem_objectiveValues_iff G).1 hr' with ⟨x, hx, hxr⟩
      rcases existsSTCutSide_le_objective_of_feasible G hG hst w hw hx with
        ⟨S', hS', hle⟩
      have hrCut : G.cutWeight w S' ∈ cutObjectiveValues G s t w :=
        cutWeight_mem_cutObjectiveValues G w hS'
      calc
        r ≤ G.cutWeight w S' := hrMin hrCut
        _ ≤ objective G w x := hle
        _ = r' := hxr
  · intro hr
    rcases hr with ⟨hrMem, hrMin⟩
    rcases (mem_objectiveValues_iff G).1 hrMem with ⟨x, hx, hObj⟩
    rcases existsSTCutSide_le_objective_of_feasible G hG hst w hw hx with ⟨S, hS, hle⟩
    refine ⟨?_, ?_⟩
    · -- A dominated cut indicator and leastness force equality with the attained optimum.
      have hIndicatorMem :
          objective G w (SimpleGraph.MinimumCut.cutIndicator G S) ∈
            objectiveValues G s t w :=
        objective_cutIndicator_mem_objectiveValues G w hS
      have hUpper :
          r ≤ objective G w (SimpleGraph.MinimumCut.cutIndicator G S) := hrMin hIndicatorMem
      have hLower : G.cutWeight w S ≤ r := hle.trans_eq hObj
      rw [objective_cutIndicator_eq_cutWeight G] at hUpper
      have hEq : G.cutWeight w S = r := le_antisymm hLower hUpper
      refine (mem_cutObjectiveValues_iff G).2 ?_
      refine ⟨S, ?_, ?_⟩
      · exact hS
      · exact hEq
    · -- Each cut value is realized by its feasible indicator, so objective leastness applies.
      intro r' hr'
      rcases (mem_cutObjectiveValues_iff G).1 hr' with ⟨S', hS', hS'r⟩
      have hrObj :
          objective G w (SimpleGraph.MinimumCut.cutIndicator G S') ∈
            objectiveValues G s t w :=
        objective_cutIndicator_mem_objectiveValues G w hS'
      calc
        r ≤ objective G w (SimpleGraph.MinimumCut.cutIndicator G S') := hrMin hrObj
        _ = G.cutWeight w S' := objective_cutIndicator_eq_cutWeight G w S'
        _ = r' := hS'r

end SimpleGraph.MinimumSTCut
