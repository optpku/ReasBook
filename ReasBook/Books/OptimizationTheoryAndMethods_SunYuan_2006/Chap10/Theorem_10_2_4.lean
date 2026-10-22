/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Theorem_10_2_5

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: Chapter 10 already owns the simple penalty method in
-- `Algorithm_10_2_3`, while `Theorem_10_2_5` owns the canonical minimal-violation value
-- `method.problem.minimalViolationValue`. This file keeps Theorem 10.2.4 source-facing through
-- the explicit minimizing-point hypothesis and adds only a thin bridge to that canonical owner.

namespace SimplePenaltyFunctionMethod

/-- Helper for Chapter10 Theorem 10.2.4: if the violation norm
`x ↦ ‖c⁽-⁾[method.problem] x‖` attains a global minimum strictly below the tolerance `ε`, then
the canonical minimal-violation value is also strictly below `ε`. -/
theorem minimalViolationValue_lt_tolerance_of_exists_isMinOn_constraintViolationNorm
    (method : SimplePenaltyFunctionMethod n m)
    (hTol :
      ∃ xHat : Point,
        IsMinOn (fun x : Point ↦ ‖c⁽-⁾[method.problem] x‖) Set.univ xHat ∧
          ‖c⁽-⁾[method.problem] xHat‖ < method.tolerance) :
    method.problem.minimalViolationValue < method.tolerance := by
  rcases hTol with ⟨xHat, hxHatMin, hxHatTol⟩
  -- Convert the source-facing global minimizer into the canonical minimal-violation set.
  have hxHatMem : xHat ∈ method.problem.minimalViolationSet :=
    (StandardPenaltyProblem.mem_minimalViolationSet_iff_isMinOn_constraintViolationNorm
      method.problem xHat).2 hxHatMin
  -- Re-express that membership as the defining equality for the minimal violation value.
  have hxHatEq :
      ‖c⁽-⁾[method.problem] xHat‖ = method.problem.minimalViolationValue :=
    (StandardPenaltyProblem.mem_minimalViolationSet_iff method.problem xHat).1 hxHatMem
  -- Substitute the attained minimum value and inherit the strict tolerance bound.
  rw [← hxHatEq]
  exact hxHatTol

/-- Helper for Chapter10 Theorem 10.2.4: if no reached stage satisfies the stopping test, then
Algorithm 10.2.3 is in the canonical nontermination regime. -/
lemma doesNotTerminateFinitely_of_no_reached_terminating_stage
    (method : SimplePenaltyFunctionMethod n m)
    (hNoStage : ¬ ∃ k : ℕ, 1 ≤ k ∧ method.reached k ∧ method.terminatedAt k) :
    method.doesNotTerminateFinitely := by
  -- Repackage the missing terminating stage into the pointwise nontermination predicate.
  refine (method.doesNotTerminateFinitely_iff_forall_reached_not_terminatedAt).2 ?_
  intro k hk hreached hterminated
  exact hNoStage ⟨k, hk, hreached, hterminated⟩

/-- Helper for Chapter10 Theorem 10.2.4: if the canonical minimal violation value already lies
strictly below the tolerance, then some reached stage must satisfy the stopping test. -/
lemma exists_reached_terminatedAt_of_minimalViolationValue_lt_tolerance
    (method : SimplePenaltyFunctionMethod n m)
    (hLt : method.problem.minimalViolationValue < method.tolerance) :
    ∃ k : ℕ, 1 ≤ k ∧ method.reached k ∧ method.terminatedAt k := by
  classical
  -- Argue by contradiction so that Theorem 10.2.5 can supply the nontermination inequality.
  by_contra hNoStage
  have hNoTerminate : method.doesNotTerminateFinitely :=
    method.doesNotTerminateFinitely_of_no_reached_terminating_stage hNoStage
  -- Nontermination forces the tolerance below the minimal violation value, contradicting `hLt`.
  have hGe : method.tolerance ≤ method.problem.minimalViolationValue :=
    simplePenaltyFunctionMethod_minimalViolationValue_ge_tolerance method hNoTerminate
  exact (not_lt_of_ge hGe) hLt

end SimplePenaltyFunctionMethod

/-- Chapter10 Theorem 10.2.4: if the tolerance `ε` in Algorithm 10.2.3 is strictly larger than
the minimum of `x ↦ ‖c⁽-⁾[method.problem] x‖` on the ambient decision space, encoded here by a
global minimizer `xHat` of the violation norm with `‖c⁽-⁾[method.problem] xHat‖ < ε`, then the
simple penalty function method terminates at some reached stage. -/
theorem simplePenaltyFunctionMethod_finiteTermination
    (method : SimplePenaltyFunctionMethod n m)
    (hTol :
      ∃ xHat : Point,
        IsMinOn (fun x : Point ↦ ‖c⁽-⁾[method.problem] x‖) Set.univ xHat ∧
          ‖c⁽-⁾[method.problem] xHat‖ < method.tolerance) :
    ∃ k : ℕ, 1 ≤ k ∧ method.reached k ∧ method.terminatedAt k := by
  -- First translate the source minimizing-point hypothesis into the canonical strict inequality.
  have hMinimal :
      method.problem.minimalViolationValue < method.tolerance :=
    method.minimalViolationValue_lt_tolerance_of_exists_isMinOn_constraintViolationNorm hTol
  -- Then invoke the contradiction lemma that rules out nontermination under this strict gap.
  exact method.exists_reached_terminatedAt_of_minimalViolationValue_lt_tolerance hMinimal
