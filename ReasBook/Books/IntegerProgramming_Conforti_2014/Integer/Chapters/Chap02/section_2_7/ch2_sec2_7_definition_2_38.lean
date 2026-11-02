module

public import Mathlib.Order.Bounds.Defs
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_38.Problem

public section

/-!
Symmetric traveling salesman problem on an undirected graph.

This item is formalized by the reusable owner
`SymmetricTravelingSalesmanProblem`, its feasible-tour predicate
`SymmetricTravelingSalesmanProblem.IsHamiltonianTour`, the closed-walk carrier
`SymmetricTravelingSalesmanProblem.ClosedWalk`, the feasible-set owner
`SymmetricTravelingSalesmanProblem.feasibleSet`, the cost functional
`SymmetricTravelingSalesmanProblem.objective`, and the attained-value set
`SymmetricTravelingSalesmanProblem.objectiveValues`.
-/

/- The canonical owners for Definition 2.38 are the reusable STSP declarations below. -/
#check SymmetricTravelingSalesmanProblem
#check SymmetricTravelingSalesmanProblem.ClosedWalk
#check SymmetricTravelingSalesmanProblem.IsHamiltonianTour
#check SymmetricTravelingSalesmanProblem.feasibleSet
#check SymmetricTravelingSalesmanProblem.mem_feasibleSet_iff
#check SymmetricTravelingSalesmanProblem.objective
#check SymmetricTravelingSalesmanProblem.objectiveValues

namespace SymmetricTravelingSalesmanProblem

universe u

section Definition_2_38

variable {V : Type u} [DecidableEq V]
variable (P : SymmetricTravelingSalesmanProblem V)

/-- Definition 2.38. The symmetric traveling salesman problem on `P` is the problem of finding a
Hamiltonian tour whose total cost is a least element of `P.objectiveValues`. -/
theorem isLeast_objectiveValues_iff
    {r : ℝ} :
    IsLeast P.objectiveValues r ↔
      ∃ t : P.ClosedWalk, P.IsHamiltonianTour t ∧
        P.objective t = r ∧
          ∀ t' : P.ClosedWalk, P.IsHamiltonianTour t' → r ≤ P.objective t' := by
  constructor
  · rintro ⟨hr, hlb⟩
    -- Extract the witnessing optimal Hamiltonian tour from the least attained value.
    rcases P.mem_objectiveValues_iff.1 hr with ⟨t, ht, hobj⟩
    refine ⟨t, ht, hobj, ?_⟩
    -- Any Hamiltonian tour contributes an attained value, so the `IsLeast` lower bound applies.
    intro t' ht'
    exact hlb (P.mem_objectiveValues_iff.2 ⟨t', ht', rfl⟩)
  · rintro ⟨t, ht, hobj, hmin⟩
    refine ⟨P.mem_objectiveValues_iff.2 ⟨t, ht, hobj⟩, ?_⟩
    -- Convert an arbitrary attained value back to a feasible tour and compare objectives.
    intro r' hr'
    rcases P.mem_objectiveValues_iff.1 hr' with ⟨t', ht', hobj'⟩
    rw [← hobj']
    exact hmin t' ht'

/-- Definition 2.38 companion: the least attained value is realized by a member of
`P.feasibleSet`, and it is bounded above by the objective value of every other feasible tour. -/
theorem isLeast_objectiveValues_iff_exists_mem_feasibleSet
    {r : ℝ} :
    IsLeast P.objectiveValues r ↔
      ∃ t : P.ClosedWalk, t ∈ P.feasibleSet ∧
        P.objective t = r ∧
          ∀ t' : P.ClosedWalk, t' ∈ P.feasibleSet → r ≤ P.objective t' := by
  constructor
  · rintro h
    rcases P.isLeast_objectiveValues_iff.1 h with ⟨t, ht, hobj, hmin⟩
    refine ⟨t, (P.mem_feasibleSet_iff.2 ht), hobj, ?_⟩
    intro t' ht'
    exact hmin t' (P.mem_feasibleSet_iff.1 ht')
  · rintro ⟨t, ht, hobj, hmin⟩
    refine P.isLeast_objectiveValues_iff.2 ?_
    refine ⟨t, (P.mem_feasibleSet_iff.1 ht), hobj, ?_⟩
    intro t' ht'
    exact hmin t' (P.mem_feasibleSet_iff.2 ht')

end Definition_2_38

end SymmetricTravelingSalesmanProblem
