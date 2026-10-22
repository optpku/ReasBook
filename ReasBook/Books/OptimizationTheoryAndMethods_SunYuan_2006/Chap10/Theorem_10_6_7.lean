/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Theorem_10_6_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * `StandardPenaltyProblem.nonsmoothExactPenalty` and `IsStrongDistanceFunction` in
--   `Definition_10_6_extra_1` are the canonical Chapter 10 exact-penalty owners.
-- * `StandardPenaltyProblem.activeConstraintSet`, `StandardPenaltyProblem.LicqAt`, and
--   `StandardPenaltyProblem.toConstrainedOptimizationProblem` in
--   `StandardPenaltyProblemBridge` are the chapter's canonical active-set, LICQ, and bridge
--   owners.
-- * `StandardPenaltyProblem.IsLagrangeMultiplier` in `Theorem_10_6_1` is the chapter's
--   mixed-constraint KKT owner.
-- * `IsLocalMin` in Chapter 1 is the canonical unconstrained local-minimum owner, while
--   `IsLocalMinOn` remains the constrained owner for the source hypothesis on
--   `problem.feasibleSet`.
-- This file therefore uses the consolidated Chapter 10 source-facing bridge surface and states
-- Theorem 10.6.7 with the canonical Chapter 1 local-minimum owners and the canonical Chapter 10
-- LICQ owner.

/-- Chapter10 Theorem 10.6.7: let `xStar` be a local minimizer of the constrained problem
`problem.objective` on `problem.feasibleSet` and let `lamStar` be a corresponding Lagrange
multiplier. If LICQ holds at `xStar` for the active constraint gradients, if `h` is a strong
distance function with lower `ℓ₁` bound constant `δ`, and if `σ * δ > ‖lamStar‖∞`, then
`xStar` is also a local minimizer of the nonsmooth exact penalty function
`problem.nonsmoothExactPenalty h σ`. -/
theorem isLocalMin_nonsmoothExactPenalty_of_isLagrangeMultiplier_of_licq
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : ConstraintPoint)
    (σ δ : ℝ) (h : ConstraintPoint → ℝ) [IsStrongDistanceFunction h]
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_multiplier : problem.IsLagrangeMultiplier xStar lamStar)
    (h_licq : problem.LicqAt xStar)
    (hδ : 0 < δ)
    (h_lower_l1 : ∀ c : ConstraintPoint, δ * ‖c‖₁ ≤ h c)
    (h_sigma : σ * δ > ‖lamStar‖∞) :
    IsLocalMin (problem.nonsmoothExactPenalty h σ) xStar := sorry

#print axioms StandardPenaltyProblem.activeConstraintSet
#print axioms isLocalMin_nonsmoothExactPenalty_of_isLagrangeMultiplier_of_licq

end
