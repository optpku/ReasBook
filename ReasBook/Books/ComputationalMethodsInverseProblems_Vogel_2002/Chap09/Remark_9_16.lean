/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs

public section

/-! Statement-stage canonical anchors for Remark 9.16.

The source remark is qualitative: it records that coordinatewise nonnegativity
constraints are a special case of coordinatewise lower and box constraints, and
then gives numerical-method motivation. The mathematical content needed
downstream is a bridge from the Chapter 9 feasible-set owner
`NonnegativeOrthant.feasibleSet` to the canonical set language for lower and
box constraints.
-/

/-
Remark 9.16.

Nonnegativity constraints are a special case of bound constraints, or box
constraints. In Lean's canonical set language, coordinatewise lower bounds use
`Set.Ici`, coordinatewise box bounds use `Set.Icc`, and coordinatewise feasible
regions are expressed with products such as `Set.pi Set.univ (fun i ↦ Set.Ici
(0 : ℝ))` or `Set.pi Set.univ (fun i ↦ Set.Icc (a i) (b i))`. The remaining
sentences about efficient numerical methods are motivation rather than a source
theorem, so this item records the source-facing identification of the
nonnegative-orthant feasible set with the canonical product-of-intervals
description, together with the box-constraint backend notions.
-/
namespace NonnegativeOrthant

variable {n : ℕ}

/-- Remark 9.16. The feasible set for problem `(9.16)` is the coordinatewise
product of the lower intervals `Set.Ici (0 : ℝ)` after transporting
`EuclideanSpace ℝ (Fin n)` to plain coordinate functions via
`EuclideanSpace.equiv`. This is the source remark's canonical reformulation of
nonnegativity constraints as coordinatewise lower constraints. -/
@[simp] theorem equiv_mem_pi_Ici_iff
    {f : EuclideanSpace ℝ (Fin n)} :
    EuclideanSpace.equiv (Fin n) ℝ f ∈ Set.pi Set.univ (fun _ : Fin n ↦ Set.Ici (0 : ℝ)) ↔
      f ∈ feasibleSet n := by
  rw [mem_feasibleSet]
  simp only [Set.mem_pi, Set.mem_Ici, Set.mem_univ, forall_true_left]
  rfl

/-- Remark 9.16. The nonnegative orthant is the preimage of the canonical
coordinatewise product region `Set.pi Set.univ (fun i ↦ Set.Ici (0 : ℝ))` under
the coordinate equivalence `EuclideanSpace.equiv`. -/
theorem feasibleSet_eq_preimage_pi_Ici (n : ℕ) :
    feasibleSet n =
      (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Set.pi Set.univ (fun _ : Fin n ↦ Set.Ici (0 : ℝ)) := by
  ext f
  exact equiv_mem_pi_Ici_iff.symm

end NonnegativeOrthant

/- Canonical backend notions for the surrounding coordinatewise box language. -/
#check Set.Icc
#check Set.mem_pi
