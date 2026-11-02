module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Defs
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_2_definition_2_14.CliqueMatrix

public section

open scoped BigOperators

namespace SimpleGraph
namespace StableSetColoring

universe u

variable {V : Type u} [Fintype V]

/-- The finite family of all maximal stable sets of the finite graph `G`. -/
noncomputable def maximalStableSets (G : SimpleGraph V) : Finset (Finset V) :=
  Gᶜ.maximalCliques

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_55/StableSetCovering.lean

Membership in `maximalStableSets G` means being a maximal stable set of `G`. -/
theorem mem_maximalStableSets_iff
    (G : SimpleGraph V)
    (S : Finset V) :
    S ∈ maximalStableSets G ↔ Maximal G.IsIndepSet (S : Set V) := by
  -- View a stable set in `G` as a clique in the complement and use maximality there.
  simp only [maximalStableSets, SimpleGraph.mem_maximalCliques_iff,
    SimpleGraph.isMaximalClique_compl]

/-- The maximal stable sets of `G` that contain the chosen vertex `v`. -/
noncomputable def maximalStableSetsContaining
    (G : SimpleGraph V)
    (v : V) :
    Finset (maximalStableSets G) :=
  open scoped Classical in
    (maximalStableSets G).attach.filter fun S ↦ v ∈ (S : Finset V)

/-- Membership in `maximalStableSetsContaining G v` means that the indexed maximal stable set
contains `v`. -/
theorem mem_maximalStableSetsContaining_iff
    {G : SimpleGraph V}
    {v : V}
    {S : maximalStableSets G} :
    S ∈ maximalStableSetsContaining G v ↔ v ∈ (S : Finset V) := by
  classical
  -- Membership in the attached finset is automatic, so the filter leaves only containment of `v`.
  simp only [maximalStableSetsContaining, Finset.mem_filter, Finset.mem_attach, true_and]

/-- The stable-set formulation objective is the sum of the variables indexed by maximal stable
sets. -/
noncomputable def objective
    {G : SimpleGraph V}
    (x : maximalStableSets G → ℤ) :
    ℤ :=
  ∑ S, x S

/-- Unfolding equation for `objective`. -/
theorem objective_def
    {G : SimpleGraph V}
    (x : maximalStableSets G → ℤ) :
    objective x = ∑ S, x S := by
  -- The displayed finite sum is the defining expression for the objective.
  rfl

/-- A stable-set formulation solution is feasible when every maximal-stable-set variable is binary
and the maximal stable sets covering each vertex have total weight at least `1`. -/
noncomputable def feasible
  (G : SimpleGraph V)
  (x : maximalStableSets G → ℤ) :
  Prop :=
  (∀ S : maximalStableSets G, x S = 0 ∨ x S = 1) ∧
    ∀ v : V, 1 ≤ Finset.sum (maximalStableSetsContaining G v) x

/-- Membership in `feasible G x` is exactly the binary condition together with the vertex-covering
inequalities of the stable-set formulation. -/
theorem feasible_iff
    {G : SimpleGraph V}
    {x : maximalStableSets G → ℤ} :
    feasible G x ↔
      (∀ S : maximalStableSets G, x S = 0 ∨ x S = 1) ∧
        ∀ v : V, 1 ≤ Finset.sum (maximalStableSetsContaining G v) x := by
  -- Both conjuncts are precisely the defining feasibility conditions.
  rfl

/-- The objective values attained by feasible stable-set covering solutions on `G`. -/
noncomputable def objectiveValues
    (G : SimpleGraph V) :
    Set ℤ :=
  {r | ∃ x : maximalStableSets G → ℤ, feasible G x ∧ objective x = r}

/-- Membership in `objectiveValues G` means that some feasible stable-set covering solution attains
the value `r`. -/
theorem mem_objectiveValues_iff
    {G : SimpleGraph V}
    {r : ℤ} :
    r ∈ objectiveValues G ↔
      ∃ x : maximalStableSets G → ℤ, feasible G x ∧ objective x = r := by
  -- Set-builder membership unfolds to the stated feasible witness and objective equation.
  rfl

end StableSetColoring
end SimpleGraph

end

#print axioms SimpleGraph.StableSetColoring.mem_maximalStableSets_iff
