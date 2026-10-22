/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * `StandardPenaltyProblem` from `Definition_10_1_extra_1` is the chapter's source-facing owner
--   for mixed equality/inequality constrained problems.
-- * `StandardPenaltyProblem.nonsmoothExactPenalty` and
--   `StandardPenaltyProblem.nonsmoothExactPenaltySublevelSet` from
--   `Definition_10_6_extra_1` are the source-facing exact-penalty owner and its sublevel-set
--   view.
-- * `IsMinOn` is the canonical mathlib minimizer predicate.
-- This lemma therefore reuses the Chapter 10 exact-penalty owner directly instead of restating
-- the problem, violation, and kernel API locally.

/-- Chapter10 Lemma 10.6.3: if `xσ` solves the nonsmooth exact penalty subproblem
`min_x problem.objective x + σ * h (c⁽-⁾[problem] x)` on `ℝ^n`, and
`η = h (c⁽-⁾[problem] xσ)`, then `xσ` also solves the constrained problem
`min_x problem.objective x` subject to `h (c⁽-⁾[problem] x) ≤ η`, for any `σ ≥ 0`. -/
theorem isMinOnObjectiveOnNonsmoothExactPenaltySublevelSet
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (xσ : Point)
    (hxσ : IsMinOn (problem.nonsmoothExactPenalty h σ) Set.univ xσ) :
    IsMinOn
      problem.objective
      (problem.nonsmoothExactPenaltySublevelSet h (h (c⁽-⁾[problem] xσ)))
      xσ := by
  let penalty : Point → ℝ := fun x ↦ σ * h (c⁽-⁾[problem] x)
  let s := problem.nonsmoothExactPenaltySublevelSet h (h (c⁽-⁾[problem] xσ))
  have hpenalty_max : IsMaxOn penalty s xσ := by
    refine isMaxOn_iff.mpr ?_
    intro x hx
    have hx' : h (c⁽-⁾[problem] x) ≤ h (c⁽-⁾[problem] xσ) :=
      (problem.mem_nonsmoothExactPenaltySublevelSet h (h (c⁽-⁾[problem] xσ)) x).mp hx
    exact mul_le_mul_of_nonneg_left hx' hσ
  have hxσ' : IsMinOn (fun x ↦ problem.objective x + penalty x) Set.univ xσ := by
    have hxσ'' := hxσ
    change IsMinOn (fun x ↦ problem.objective x + σ * h (c⁽-⁾[problem] x)) Set.univ xσ at hxσ''
    simpa [penalty] using hxσ''
  have hxσ'' : IsMinOn (fun x ↦ problem.objective x + penalty x) s xσ :=
    hxσ'.on_subset (by intro x _; simp)
  simpa [penalty, sub_eq_add_neg] using hxσ''.sub hpenalty_max

#print axioms isMinOnObjectiveOnNonsmoothExactPenaltySublevelSet

end
