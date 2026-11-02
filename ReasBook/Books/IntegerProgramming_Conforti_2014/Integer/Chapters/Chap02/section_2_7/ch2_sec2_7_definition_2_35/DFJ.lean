import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_definition_2_34.Problem
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_definition_4_3_3_extra_1

open scoped BigOperators

namespace AsymmetricTravelingSalesmanProblem
namespace DFJ

variable {V A : Type} [Fintype A]

/-- The DFJ feasibility constraints on the arc variables `x` require one outgoing arc and one
incoming arc at each vertex, at least one outgoing arc across every nonempty proper cut, and
binary arc values. -/
def feasible (P : AsymmetricTravelingSalesmanProblem V A) (x : A → ℝ) : Prop :=
  (∀ v : V, Finset.sum (outgoing_arcs P.tail v) (fun a ↦ x a) = (1 : ℝ)) ∧
    (∀ v : V, Finset.sum (incoming_arcs P.head v) (fun a ↦ x a) = (1 : ℝ)) ∧
      (∀ S : Set V, S.Nonempty → S ≠ Set.univ →
        (1 : ℝ) ≤ Finset.sum (δ⁺[P.tail, P.head] S) (fun a ↦ x a)) ∧
        ∀ a : A, x a = 0 ∨ x a = 1

/-- Membership in `feasible P x` is exactly the conjunction of the DFJ out-degree, in-degree,
cut, and binary constraints. -/
theorem feasible_iff
    {P : AsymmetricTravelingSalesmanProblem V A} {x : A → ℝ} :
    feasible P x ↔
      (∀ v : V, Finset.sum (outgoing_arcs P.tail v) (fun a ↦ x a) = (1 : ℝ)) ∧
        (∀ v : V, Finset.sum (incoming_arcs P.head v) (fun a ↦ x a) = (1 : ℝ)) ∧
          (∀ S : Set V, S.Nonempty → S ≠ Set.univ →
            (1 : ℝ) ≤ Finset.sum (δ⁺[P.tail, P.head] S) (fun a ↦ x a)) ∧
            ∀ a : A, x a = 0 ∨ x a = 1 := by
  -- This is the defining conjunction for `feasible`.
  rfl

/-- The outgoing-degree equation extracted from `feasible P x`. -/
theorem feasible_outgoing_eq_one
    {P : AsymmetricTravelingSalesmanProblem V A} {x : A → ℝ}
    (h_feasible : feasible P x) (v : V) :
    Finset.sum (outgoing_arcs P.tail v) (fun a ↦ x a) = (1 : ℝ) := by
  -- Project the outgoing-degree constraint from the normalized feasibility data.
  exact (feasible_iff.mp h_feasible).1 v

/-- The incoming-degree equation extracted from `feasible P x`. -/
theorem feasible_incoming_eq_one
    {P : AsymmetricTravelingSalesmanProblem V A} {x : A → ℝ}
    (h_feasible : feasible P x) (v : V) :
    Finset.sum (incoming_arcs P.head v) (fun a ↦ x a) = (1 : ℝ) := by
  -- Project the incoming-degree constraint from the normalized feasibility data.
  exact (feasible_iff.mp h_feasible).2.1 v

/-- The nonempty proper-cut inequality extracted from `feasible P x`. -/
theorem feasible_cut_ge_one
    {P : AsymmetricTravelingSalesmanProblem V A} {x : A → ℝ}
    (h_feasible : feasible P x) {S : Set V}
    (hS_nonempty : S.Nonempty) (hS_proper : S ≠ Set.univ) :
    (1 : ℝ) ≤ Finset.sum (δ⁺[P.tail, P.head] S) (fun a ↦ x a) := by
  -- Project the proper-cut inequality and apply it to the chosen cut `S`.
  exact (feasible_iff.mp h_feasible).2.2.1 S hS_nonempty hS_proper

/-- The binary arc-variable condition extracted from `feasible P x`. -/
theorem feasible_binary
    {P : AsymmetricTravelingSalesmanProblem V A} {x : A → ℝ}
    (h_feasible : feasible P x) (a : A) :
    x a = 0 ∨ x a = 1 := by
  -- Project the binary-variable constraint from the normalized feasibility data.
  exact (feasible_iff.mp h_feasible).2.2.2 a

/-- The DFJ objective is the total arc cost weighted by the arc variables `x`. -/
def objective (P : AsymmetricTravelingSalesmanProblem V A) (x : A → ℝ) : ℝ :=
  ∑ a : A, P.cost a * x a

/-- Unfolding equation for `objective P x`. -/
theorem objective_def
    (P : AsymmetricTravelingSalesmanProblem V A) (x : A → ℝ) :
    objective P x = ∑ a : A, P.cost a * x a := by
  -- This is the defining equation for `objective`.
  rfl

/-- The attained objective values of the DFJ formulation on `P`. -/
def objectiveValues (P : AsymmetricTravelingSalesmanProblem V A) : Set ℝ :=
  {r | ∃ x : A → ℝ, feasible P x ∧ objective P x = r}

/-- Membership in `objectiveValues P` means that some DFJ-feasible arc vector attains `r`. -/
theorem mem_objectiveValues_iff
    {P : AsymmetricTravelingSalesmanProblem V A} {r : ℝ} :
    r ∈ objectiveValues P ↔
      ∃ x : A → ℝ, feasible P x ∧ objective P x = r := by
  -- Membership unfolds to existence of a feasible arc vector attaining `r`.
  rfl

end DFJ
end AsymmetricTravelingSalesmanProblem
