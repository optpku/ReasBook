/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1

open scoped BigOperators

universe u w

/-- The weighted directed-network data underlying an asymmetric traveling salesman problem. -/
structure AsymmetricTravelingSalesmanProblem (V : Type u) (A : Type w) where
  tail : A → V
  head : A → V
  cost : A → ℝ

namespace AsymmetricTravelingSalesmanProblem

variable {V : Type u} {A : Type w}

/-- The digraph determined by the endpoint maps of `P`, forgetting arc labels and costs. -/
def toDigraph (P : AsymmetricTravelingSalesmanProblem V A) : Digraph V where
  Adj u v := ∃ a : A, P.tail a = u ∧ P.head a = v

/-- A directed Hamiltonian tour in `P` is a simple directed circuit whose incident-vertex set
contains every vertex. -/
structure IsHamiltonianTour (P : AsymmetricTravelingSalesmanProblem V A) (C : Finset A) : Prop
    extends IsSimpleCircuit P.tail P.head C where
  visits_all : ∀ v : V, v ∈ circuit_vertex_set P.tail P.head C

/-- Build a Hamiltonian tour from a simple circuit together with the proof that every vertex is
incident to one of its arcs. -/
def ofIsSimpleCircuit
    {P : AsymmetricTravelingSalesmanProblem V A} {C : Finset A}
    (hC : IsSimpleCircuit P.tail P.head C)
    (h_visits_all : ∀ v : V, v ∈ circuit_vertex_set P.tail P.head C) :
    P.IsHamiltonianTour C :=
  { toIsSimpleCircuit := hC
    visits_all := h_visits_all }

/-- Membership in `P.IsHamiltonianTour C` is exactly the conjunction of the simple-circuit
condition and the requirement that every vertex is visited. -/
theorem isHamiltonianTour_iff
    {P : AsymmetricTravelingSalesmanProblem V A} {C : Finset A} :
    P.IsHamiltonianTour C ↔
      IsSimpleCircuit P.tail P.head C ∧
        ∀ v : V, v ∈ circuit_vertex_set P.tail P.head C := by
  constructor
  · intro hC
    exact ⟨hC.toIsSimpleCircuit, hC.visits_all⟩
  · rintro ⟨hC, h_visits_all⟩
    exact ⟨hC, h_visits_all⟩

/-- The feasible tours of `P` are the arc sets that form Hamiltonian tours. -/
def feasibleSet (P : AsymmetricTravelingSalesmanProblem V A) : Set (Finset A) :=
  {C | P.IsHamiltonianTour C}

/-- Membership in `P.feasibleSet` means that the chosen arc set is a Hamiltonian tour. -/
theorem mem_feasibleSet_iff
    {P : AsymmetricTravelingSalesmanProblem V A} {C : Finset A} :
    C ∈ P.feasibleSet ↔ P.IsHamiltonianTour C := by
  rfl

/-- The total cost of the arc set `C` is the sum of the arc costs of `P` over `C`. -/
def objective (P : AsymmetricTravelingSalesmanProblem V A) (C : Finset A) : ℝ :=
  C.sum P.cost

/-- Unfolding equation for `P.objective`. -/
theorem objective_def
    (P : AsymmetricTravelingSalesmanProblem V A) (C : Finset A) :
    P.objective C = C.sum P.cost := by
  rfl

/-- The attained objective values of the asymmetric traveling salesman problem `P`. -/
def objectiveValues (P : AsymmetricTravelingSalesmanProblem V A) : Set ℝ :=
  P.objective '' P.feasibleSet

/-- Membership in `P.objectiveValues` means that some Hamiltonian tour attains the value `r`. -/
theorem mem_objectiveValues_iff
    {P : AsymmetricTravelingSalesmanProblem V A} {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ C : Finset A, P.IsHamiltonianTour C ∧ P.objective C = r := by
  constructor
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, (mem_feasibleSet_iff.mp hC), rfl⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, (mem_feasibleSet_iff.mpr hC), rfl⟩

end AsymmetricTravelingSalesmanProblem
