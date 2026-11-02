import Mathlib.Order.Bounds.Defs
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_34.Problem

/-!
Asymmetric traveling salesman problem on a digraph.

This item is formalized by the reusable owner
`AsymmetricTravelingSalesmanProblem`, its feasible-tour predicate
`AsymmetricTravelingSalesmanProblem.IsHamiltonianTour`, the feasible-set owner
`AsymmetricTravelingSalesmanProblem.feasibleSet`, the cost functional
`AsymmetricTravelingSalesmanProblem.objective`, and the attained-value set
`AsymmetricTravelingSalesmanProblem.objectiveValues`.
-/

/- The canonical owners for Definition 2.34 are the reusable ATSP declarations below. -/
#check AsymmetricTravelingSalesmanProblem
#check AsymmetricTravelingSalesmanProblem.IsHamiltonianTour
#check AsymmetricTravelingSalesmanProblem.feasibleSet
#check AsymmetricTravelingSalesmanProblem.mem_feasibleSet_iff
#check AsymmetricTravelingSalesmanProblem.objective
#check AsymmetricTravelingSalesmanProblem.objectiveValues

namespace AsymmetricTravelingSalesmanProblem

universe u w

section Definition_2_34

variable {V : Type u} {A : Type w}
variable (P : AsymmetricTravelingSalesmanProblem V A)

/-- Definition 2.34. The asymmetric traveling salesman problem on `P` is the problem of finding a
Hamiltonian tour whose total cost is a least element of `P.objectiveValues`. -/
theorem isLeast_objectiveValues_iff
    {r : ℝ} :
    IsLeast P.objectiveValues r ↔
      ∃ C : Finset A, P.IsHamiltonianTour C ∧
        P.objective C = r ∧
          ∀ C' : Finset A, P.IsHamiltonianTour C' → r ≤ P.objective C' := by
  constructor
  · intro hr
    rcases hr with ⟨hr_mem, hr_lower⟩
    -- Convert least-value membership into a Hamiltonian-tour witness attaining `r`.
    rcases (P.mem_objectiveValues_iff.mp hr_mem) with ⟨C, hC, hObj⟩
    -- Re-express the lower-bound clause pointwise on Hamiltonian tours.
    have hr_lower' : ∀ ⦃r' : ℝ⦄, r' ∈ P.objectiveValues → r ≤ r' := by
      simpa [lowerBounds] using hr_lower
    refine ⟨C, hC, hObj, ?_⟩
    intro C' hC'
    have hmem : P.objective C' ∈ P.objectiveValues := by
      exact P.mem_objectiveValues_iff.mpr ⟨C', hC', rfl⟩
    exact hr_lower' hmem
  · rintro ⟨C, hC, hObj, hOpt⟩
    refine ⟨?_, ?_⟩
    -- Package the chosen optimal tour back into the attained-value set.
    · exact P.mem_objectiveValues_iff.mpr ⟨C, hC, hObj⟩
    -- Every attained value comes from some Hamiltonian tour.
    -- The tourwise optimum therefore yields the needed lower bound.
    · have hLower : ∀ ⦃r' : ℝ⦄, r' ∈ P.objectiveValues → r ≤ r' := by
        intro r' hr'
        rcases (P.mem_objectiveValues_iff.mp hr') with ⟨C', hC', hObj'⟩
        have hOpt' : r ≤ P.objective C' := hOpt C' hC'
        simpa [hObj'] using hOpt'
      simpa [lowerBounds] using hLower

/-- Definition 2.34 companion: the least attained value is realized by a member of
`P.feasibleSet`, and it is bounded above by the objective value of every other feasible tour. -/
theorem isLeast_objectiveValues_iff_exists_mem_feasibleSet
    {r : ℝ} :
    IsLeast P.objectiveValues r ↔
      ∃ C : Finset A, C ∈ P.feasibleSet ∧
        P.objective C = r ∧
          ∀ C' : Finset A, C' ∈ P.feasibleSet → r ≤ P.objective C' := by
  constructor
  · intro hr
    rcases P.isLeast_objectiveValues_iff.mp hr with ⟨C, hC, hObj, hOpt⟩
    refine ⟨C, P.mem_feasibleSet_iff.mpr hC, hObj, ?_⟩
    intro C' hC'
    exact hOpt C' (P.mem_feasibleSet_iff.mp hC')
  · rintro ⟨C, hC, hObj, hOpt⟩
    refine P.isLeast_objectiveValues_iff.mpr ?_
    refine ⟨C, P.mem_feasibleSet_iff.mp hC, hObj, ?_⟩
    intro C' hC'
    exact hOpt C' (P.mem_feasibleSet_iff.mpr hC')

end Definition_2_34

end AsymmetricTravelingSalesmanProblem
