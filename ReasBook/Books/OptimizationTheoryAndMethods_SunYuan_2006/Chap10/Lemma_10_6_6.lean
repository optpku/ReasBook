/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Layer choice:
-- * source-facing owner: `StandardPenaltyProblem.nonsmoothExactPenalty`;
-- * core/canonical owner: `PenaltyFunction`;
-- * bridge/view: `PenaltyFunction.nonsmoothExact`.
-- This lemma keeps the source-facing objective as the main surface and adds only the minimal
-- bridge API needed to pass from `h (c⁽-⁾[problem] x) = 0` to feasibility.

namespace StandardPenaltyProblem

/-- If a strong distance function vanishes on the source violation vector `c⁽-⁾[problem] x`,
then that violation vector is `0`. -/
theorem constraintViolation_eq_zero_of_strongDistanceFunction_eq_zero
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ)
    [hh : IsStrongDistanceFunction h] {x : Point}
    (hx : h (c⁽-⁾[problem] x) = 0) :
    c⁽-⁾[problem] x = 0 := by
  rcases hh.exists_pos_le_mul_l1Norm with ⟨δ, hδ_pos, hδ_le⟩
  have h_norm_nonneg : 0 ≤ ‖c⁽-⁾[problem] x‖₁ := by
    rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have h_mul_nonneg : 0 ≤ δ * ‖c⁽-⁾[problem] x‖₁ :=
    mul_nonneg hδ_pos.le h_norm_nonneg
  have h_mul_le_zero : δ * ‖c⁽-⁾[problem] x‖₁ ≤ 0 := by
    simpa [hx] using hδ_le (c⁽-⁾[problem] x)
  have h_mul_zero : δ * ‖c⁽-⁾[problem] x‖₁ = 0 :=
    le_antisymm h_mul_le_zero h_mul_nonneg
  have h_norm_zero : ‖c⁽-⁾[problem] x‖₁ = 0 := by
    rcases mul_eq_zero.mp h_mul_zero with hδ_zero | h_norm_zero
    · exact (hδ_pos.ne' hδ_zero).elim
    · exact h_norm_zero
  have h_sum_abs_zero : ∑ j, |(c⁽-⁾[problem] x) j| = 0 := by
    rw [← EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
    exact h_norm_zero
  refine PiLp.ext fun i ↦ ?_
  have h_abs_zero :
      |(c⁽-⁾[problem] x) i| = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ abs_nonneg ((c⁽-⁾[problem] x) j)).mp ?_ i
      (Finset.mem_univ i)
    exact h_sum_abs_zero
  exact abs_eq_zero.mp h_abs_zero

/-- If a strong distance function vanishes on `c⁽-⁾[problem] x`, then `x` is feasible for
`problem`. -/
theorem mem_of_strongDistanceFunction_eq_zero
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ)
    [IsStrongDistanceFunction h] {x : Point} (hx : h (c⁽-⁾[problem] x) = 0) :
    x ∈ problem := by
  exact (problem.mem_iff_constraintViolation_eq_zero x).2
    (problem.constraintViolation_eq_zero_of_strongDistanceFunction_eq_zero h hx)

/-- On feasible points, the nonsmooth exact penalty objective agrees with the original
objective. -/
theorem nonsmoothExactPenalty_eq_objective_of_mem_feasibleSet
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ)
    [hh : IsStrongDistanceFunction h] (σ : ℝ) {x : Point} (hx : x ∈ problem) :
    problem.nonsmoothExactPenalty h σ x = problem.objective x := by
  rw [problem.nonsmoothExactPenalty_apply]
  rw [(problem.mem_iff_constraintViolation_eq_zero x).mp hx, hh.map_zero, mul_zero, add_zero]

end StandardPenaltyProblem

/-- Chapter10 Lemma 10.6.6: if `h (c⁽-⁾[problem] xBar) = 0` and `xBar` is a local minimizer of
the nonsmooth exact penalty objective `problem.nonsmoothExactPenalty h σ`, then `xBar` is also a
local minimizer of the constrained optimization problem, i.e. of `problem.objective` on
`problem.feasibleSet`. The source's positivity assumption `σ > 0` is redundant for this
implication, so the source-facing statement omits it. -/
theorem isLocalMinOn_objective_on_feasibleSet_of_isLocalMinOn_nonsmoothExactPenalty
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ)
    [IsStrongDistanceFunction h] {σ : ℝ} {xBar : Point}
    (h_zero : h (c⁽-⁾[problem] xBar) = 0)
    (h_localMin : IsLocalMinOn (problem.nonsmoothExactPenalty h σ) Set.univ xBar) :
    IsLocalMinOn problem.objective problem.feasibleSet xBar := by
  have hxBar : xBar ∈ problem :=
    problem.mem_of_strongDistanceFunction_eq_zero h h_zero
  have h_localMin_feasible :
      IsLocalMinOn (problem.nonsmoothExactPenalty h σ) problem.feasibleSet xBar :=
    h_localMin.on_subset (Set.subset_univ _)
  refine h_localMin_feasible.congr ?_ (show xBar ∈ problem.feasibleSet from hxBar)
  show problem.nonsmoothExactPenalty h σ =ᶠ[nhdsWithin xBar problem.feasibleSet] problem.objective
  exact Filter.mem_of_superset self_mem_nhdsWithin fun x hx ↦
    problem.nonsmoothExactPenalty_eq_objective_of_mem_feasibleSet h σ hx

/-- The bundled penalty-function view of Lemma 10.6.6. -/
theorem isLocalMinOn_objective_on_feasibleSet_of_isLocalMinOn_nonsmoothExact
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ)
    [IsStrongDistanceFunction h] {σ : ℝ} (hσ : 0 < σ) {xBar : Point}
    (h_zero : h (c⁽-⁾[problem] xBar) = 0)
    (h_localMin : IsLocalMinOn (PenaltyFunction.nonsmoothExact problem h σ hσ) Set.univ xBar) :
    IsLocalMinOn problem.objective problem.feasibleSet xBar := by
  simpa [PenaltyFunction.nonsmoothExact_apply] using
    isLocalMinOn_objective_on_feasibleSet_of_isLocalMinOn_nonsmoothExactPenalty
      problem h h_zero h_localMin

#print axioms StandardPenaltyProblem.constraintViolation_eq_zero_of_strongDistanceFunction_eq_zero
#print axioms isLocalMinOn_objective_on_feasibleSet_of_isLocalMinOn_nonsmoothExactPenalty

end
