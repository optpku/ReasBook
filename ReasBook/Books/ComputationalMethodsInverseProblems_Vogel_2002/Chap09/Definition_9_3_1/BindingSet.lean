/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_2.IndexSets
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-- The binding set of `f` for `J` consists of the coordinates where `f`
vanishes and the corresponding gradient component is strictly positive. -/
def bindingSet
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) : Set (Fin n) :=
  {i | f i = 0 ∧ 0 < gradient J f i}

/-- Membership in `bindingSet J f` is equivalent to vanishing of the
corresponding coordinate of `f` together with strict positivity of the matching
gradient component. -/
@[simp] theorem mem_bindingSet
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    i ∈ bindingSet J f ↔ f i = 0 ∧ 0 < gradient J f i :=
  Iff.rfl

/-- The binding set is the intersection of the active set for the orthant
constraints with the indices where the gradient component is strictly
positive. -/
theorem bindingSet_eq_active_inter
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    bindingSet J f =
      ActiveSet.active (fun i x ↦ x i) f ∩ {i | 0 < gradient J f i} := by
  ext i
  constructor
  · intro hi
    rcases (mem_bindingSet J f i).1 hi with ⟨hzero, hgrad⟩
    exact ⟨(ActiveSet.mem_active (fun j x ↦ x j) f i).2 hzero, hgrad⟩
  · rintro ⟨hi, hgrad⟩
    exact (mem_bindingSet J f i).2
      ⟨(ActiveSet.mem_active (fun j x ↦ x j) f i).1 hi, hgrad⟩

/-- Every index in `bindingSet J f` belongs to the active set of the coordinate
constraints `x i ≥ 0`. -/
theorem bindingSet_subset_active
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    bindingSet J f ⊆ ActiveSet.active (fun i x ↦ x i) f := by
  intro i hi
  exact (ActiveSet.mem_active (fun j x ↦ x j) f i).2 ((mem_bindingSet J f i).1 hi).1

end NonnegativeOrthant
