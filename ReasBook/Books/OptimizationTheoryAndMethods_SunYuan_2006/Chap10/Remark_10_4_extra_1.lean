/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Algorithm_10_4_1

open scoped BigOperators

noncomputable section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

namespace StandardPenaltyProblem

/-- If every constraint is an equality constraint, the chapter's augmented Lagrangian reduces to
the quadratic-penalty-corrected Lagrangian from the equality-only case. -/
theorem augmentedLagrangian_eq_of_eqCount_eq
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint) (x : Point)
    (hEq : problem.eqCount = m) :
    problem.augmentedLagrangian lam σ x =
      problem.objective x +
        ∑ i : Fin m, (-(lam i) * problem.constraint i x +
          (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ)) := by
  simpa [hEq] using problem.augmentedLagrangian_eq lam σ x

/-- On an equality-block coordinate, the chapter's multiplier update is
`λ i - σ i * problem.constraint i x`. -/
theorem multiplierUpdate_apply_of_lt_eqCount
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) (i : Fin m) (hi : i.1 < problem.eqCount) :
    problem.multiplierUpdate lam σ x i = lam i - σ i * problem.constraint i x := by
  rw [StandardPenaltyProblem.multiplierUpdate, PiLp.toLp_apply, if_pos hi]

/-- On an inequality-block coordinate, the chapter's multiplier update is
`max (λ i - σ i * problem.constraint i x) 0`. -/
theorem multiplierUpdate_apply_of_eqCount_le
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) (i : Fin m) (hi : problem.eqCount ≤ i.1) :
    problem.multiplierUpdate lam σ x i =
      max (lam i - σ i * problem.constraint i x) 0 := by
  rw [StandardPenaltyProblem.multiplierUpdate, PiLp.toLp_apply, if_neg (not_lt_of_ge hi)]

/-- If every constraint is an equality constraint, the chapter's multiplier update is exactly the
coordinatewise rule `λ i - σ i * problem.constraint i x`. -/
theorem multiplierUpdate_apply_of_eqCount_eq
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (x : Point) (i : Fin m) (hEq : problem.eqCount = m) :
    problem.multiplierUpdate lam σ x i = lam i - σ i * problem.constraint i x := by
  have hi : i.1 < problem.eqCount := by
    simp [hEq]
  exact problem.multiplierUpdate_apply_of_lt_eqCount lam σ x i hi

/-- Helper for Chapter10 Remark 10.4-extra-1: a family of `HasGradientAt` witnesses identifies
the canonical gradients of the constraint functions at the current point. -/
theorem constraint_gradient_eq_of_hasGradientAt
    (problem : StandardPenaltyProblem n m) (x : Point) (constraintGradient : Fin m → Point)
    (hConstraintGradient :
      ∀ i : Fin m, HasGradientAt (problem.constraint i) (constraintGradient i) x) :
    ∀ i : Fin m, gradient (problem.constraint i) x = constraintGradient i := by
  intro i
  -- Each supplied witness pins down the canonical gradient at `x`.
  exact (hConstraintGradient i).gradient

/-- The source post-update stationarity identity `(10.4.9)` says that if `objectiveGradient` and
`constraintGradient i` are the actual gradients of `problem.objective` and `problem.constraint i`
at the subproblem point `xNext`, and these gradients satisfy the `(10.4.6)` balance with the
updated multipliers, then the corresponding Lagrangian stationarity residual is `0`. -/
theorem postUpdateStationarityResidual_eq_zero
    (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
    (xNext : Point) (objectiveGradient : Point) (constraintGradient : Fin m → Point)
    (hObjectiveGradient : HasGradientAt problem.objective objectiveGradient xNext)
    (hConstraintGradient :
      ∀ i : Fin m, HasGradientAt (problem.constraint i) (constraintGradient i) xNext)
    (hstationary :
      objectiveGradient =
        ∑ i : Fin m, (problem.multiplierUpdate lam σ xNext i) • constraintGradient i) :
    gradient problem.objective xNext -
        ∑ i : Fin m,
          (problem.multiplierUpdate lam σ xNext i) • gradient (problem.constraint i) xNext =
      0 := by
  have hConstraintGradient' :
      ∀ i : Fin m, gradient (problem.constraint i) xNext = constraintGradient i :=
    problem.constraint_gradient_eq_of_hasGradientAt xNext constraintGradient hConstraintGradient
  -- Rewrite the canonical gradients to the recorded source gradients from `(10.4.6)`.
  rw [hObjectiveGradient.gradient]
  -- The assumed balance is exactly the post-update residual identity after substitution.
  calc
    objectiveGradient -
        ∑ i : Fin m,
          (problem.multiplierUpdate lam σ xNext i) • gradient (problem.constraint i) xNext
      = objectiveGradient -
          ∑ i : Fin m,
            (problem.multiplierUpdate lam σ xNext i) • constraintGradient i := by
              simp [hConstraintGradient']
    _ = 0 := by
      rw [hstationary]
      simp

end StandardPenaltyProblem

namespace AugmentedLagrangianMethod

/-- If the `k`th stage does not terminate, evaluating the Step 3 penalty-parameter update at
coordinate `i` gives the source rule `(10.4.13)`: the previous parameter is kept when the
test `(10.4.11)` succeeds, and otherwise it is raised to
`max (10 * σᵢ⁽k⁾) (k²)`. -/
theorem penaltyParameter_update_apply
    (method : _root_.AugmentedLagrangianMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hstop : ¬ terminatedAt method k) (i : Fin m) :
    method.penaltyParameter (k + 1) i =
      if penaltyUpdateTestAt method k i then
        method.penaltyParameter k i
      else
        max (10 * method.penaltyParameter k i) ((k : ℝ) ^ (2 : ℕ)) := by
  exact method.penaltyParameter_update_eq hk hstop i

/-- If the source Step 3 condition `(10.4.11)` holds at coordinate `i`, then the next
penalty parameter keeps the previous value `σᵢ⁽k⁾`. -/
theorem penaltyParameter_update_apply_of_condition
    (method : _root_.AugmentedLagrangianMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hstop : ¬ terminatedAt method k) (i : Fin m)
    (htest : penaltyUpdateConditionAt method k i) :
    method.penaltyParameter (k + 1) i = method.penaltyParameter k i := by
  have htest' : penaltyUpdateTestAt method k i = true :=
    (method.penaltyUpdateTestAt_eq_true_iff k i).2 htest
  simp [method.penaltyParameter_update_apply hk hstop i, htest']

/-- If the source Step 3 condition `(10.4.11)` fails at coordinate `i`, then the next
penalty parameter is updated by the remaining branch of `(10.4.13)`,
`max (10 * σᵢ⁽k⁾) (k²)`. -/
theorem penaltyParameter_update_apply_of_not_condition
    (method : _root_.AugmentedLagrangianMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hstop : ¬ terminatedAt method k) (i : Fin m)
    (htest : ¬ penaltyUpdateConditionAt method k i) :
    method.penaltyParameter (k + 1) i =
      max (10 * method.penaltyParameter k i) ((k : ℝ) ^ (2 : ℕ)) := by
  cases hbool : penaltyUpdateTestAt method k i with
  | false =>
      simp [method.penaltyParameter_update_apply hk hstop i, hbool]
  | true =>
      exact (htest ((method.penaltyUpdateTestAt_eq_true_iff k i).1 hbool)).elim

end AugmentedLagrangianMethod

/-- Chapter10 Remark 10.4-extra-1: the Section 10.4 augmented-Lagrangian discussion is captured
by four formal identities already developed above: in the equality-only case the augmented
Lagrangian reduces to the quadratic-penalty-corrected Lagrangian `(10.4.1)`, the multiplier
update reduces to `(10.4.3)`, the post-update balance `(10.4.6)` yields the stationarity
residual `(10.4.9)`, and on every nonterminating stage of Algorithm 10.4.1 the penalty
parameter update is the Step 3 branch formula `(10.4.13)`. -/
theorem augmentedLagrangian_remark_formulas :
    (∀ (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint) (x : Point)
        (_ : problem.eqCount = m),
      problem.augmentedLagrangian lam σ x =
        problem.objective x +
          ∑ i : Fin m, (-(lam i) * problem.constraint i x +
            (1 / 2 : ℝ) * σ i * (problem.constraint i x) ^ (2 : ℕ))) ∧
    (∀ (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
        (x : Point) (i : Fin m) (_ : problem.eqCount = m),
      problem.multiplierUpdate lam σ x i = lam i - σ i * problem.constraint i x) ∧
    (∀ (problem : StandardPenaltyProblem n m) (lam σ : ConstraintPoint)
        (xNext : Point) (objectiveGradient : Point) (constraintGradient : Fin m → Point)
        (_ : HasGradientAt problem.objective objectiveGradient xNext)
        (_ :
          ∀ i : Fin m, HasGradientAt (problem.constraint i) (constraintGradient i) xNext)
        (_ :
          objectiveGradient =
            ∑ i : Fin m, (problem.multiplierUpdate lam σ xNext i) • constraintGradient i),
      gradient problem.objective xNext -
          ∑ i : Fin m,
            (problem.multiplierUpdate lam σ xNext i) • gradient (problem.constraint i) xNext =
        0) ∧
    (∀ (method : _root_.AugmentedLagrangianMethod n m) {k : ℕ} (_ : 1 ≤ k)
        (_ : ¬ AugmentedLagrangianMethod.terminatedAt method k) (i : Fin m),
      method.penaltyParameter (k + 1) i =
        if AugmentedLagrangianMethod.penaltyUpdateTestAt method k i then
          method.penaltyParameter k i
        else
          max (10 * method.penaltyParameter k i) ((k : ℝ) ^ (2 : ℕ))) := by
  constructor
  · intro problem lam σ x hEq
    -- In the equality-only regime, every coordinate uses the equality branch.
    exact problem.augmentedLagrangian_eq_of_eqCount_eq lam σ x hEq
  constructor
  · intro problem lam σ x i hEq
    -- The coordinatewise multiplier update collapses to `(10.4.3)`.
    exact problem.multiplierUpdate_apply_of_eqCount_eq lam σ x i hEq
  constructor
  · intro problem lam σ xNext objectiveGradient constraintGradient
      hObjectiveGradient hConstraintGradient hstationary
    -- The recorded gradient balance is exactly the post-update stationarity identity.
    exact problem.postUpdateStationarityResidual_eq_zero
      lam σ xNext objectiveGradient constraintGradient
      hObjectiveGradient hConstraintGradient hstationary
  · intro method k hk hstop i
    -- On nonterminating stages, Step 3 exposes the explicit penalty-parameter branch.
    exact method.penaltyParameter_update_apply hk hstop i

#print axioms AugmentedLagrangianMethod.penaltyParameter_update_apply
#print axioms StandardPenaltyProblem.augmentedLagrangian
#print axioms StandardPenaltyProblem.multiplierUpdate
