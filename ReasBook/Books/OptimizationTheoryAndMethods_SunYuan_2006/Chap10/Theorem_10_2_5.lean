/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Algorithm_10_2_3

noncomputable section

open Filter

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: `Algorithm_10_2_3` already owns the source-facing simple penalty method and
-- its stagewise stopping/minimizer API, while `StandardPenaltyProblem` owns the underlying
-- constraint-violation norm. This theorem file therefore keeps nontermination method-level, but
-- lifts the minimal-violation objects to the problem-level owner they actually depend on.

namespace StandardPenaltyProblem

/-- The minimal violation value of the Chapter 10 constraint norm, encoding the source quantity
`min_x ‖c⁽-⁾(x)‖` as `sInf (Set.range fun x ↦ ‖c⁽-⁾(x)‖)` on `ℝ`. -/
def minimalViolationValue (problem : StandardPenaltyProblem n m) : ℝ :=
  sInf (Set.range fun x : Point ↦ ‖c⁽-⁾[problem] x‖)

/-- The minimizing set for the Chapter 10 violation norm consists of the points where
`‖c⁽-⁾(x)‖ = problem.minimalViolationValue`. -/
def minimalViolationSet (problem : StandardPenaltyProblem n m) : Set Point :=
  {x | ‖c⁽-⁾[problem] x‖ = problem.minimalViolationValue}

/-- Membership in `problem.minimalViolationSet` is exactly the equation
`‖c⁽-⁾(x)‖ = problem.minimalViolationValue`. -/
theorem mem_minimalViolationSet_iff
    (problem : StandardPenaltyProblem n m) (x : Point) :
    x ∈ problem.minimalViolationSet ↔
      ‖c⁽-⁾[problem] x‖ = problem.minimalViolationValue :=
  Iff.rfl

/-- The Chapter 10 minimal violation value is bounded above by every attained violation norm. -/
theorem minimalViolationValue_le_constraintViolationNorm
    (problem : StandardPenaltyProblem n m) (x : Point) :
    problem.minimalViolationValue ≤ ‖c⁽-⁾[problem] x‖ := by
  unfold minimalViolationValue
  refine csInf_le ?_ ⟨x, rfl⟩
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨z, rfl⟩
  exact norm_nonneg _

/-- The Chapter 10 minimal violation value is nonnegative. -/
theorem minimalViolationValue_nonneg
    (problem : StandardPenaltyProblem n m) :
    0 ≤ problem.minimalViolationValue := by
  unfold minimalViolationValue
  refine le_csInf ?_ ?_
  · exact Set.range_nonempty _
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    exact norm_nonneg _

/-- Membership in `problem.minimalViolationSet` is equivalent to minimizing the Chapter 10
violation norm on the ambient decision space. -/
theorem mem_minimalViolationSet_iff_isMinOn_constraintViolationNorm
    (problem : StandardPenaltyProblem n m) (x : Point) :
    x ∈ problem.minimalViolationSet ↔
      IsMinOn (fun y : Point ↦ ‖c⁽-⁾[problem] y‖) Set.univ x := by
  constructor
  · intro hx
    rw [mem_minimalViolationSet_iff] at hx
    rw [isMinOn_univ_iff]
    intro y
    rw [hx]
    exact problem.minimalViolationValue_le_constraintViolationNorm y
  · intro hx
    rw [mem_minimalViolationSet_iff]
    refine le_antisymm ?_ (problem.minimalViolationValue_le_constraintViolationNorm x)
    refine le_csInf (Set.range_nonempty (fun y : Point ↦ ‖c⁽-⁾[problem] y‖)) ?_
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact (isMinOn_univ_iff.mp hx) z

end StandardPenaltyProblem

namespace SimplePenaltyFunctionMethod

/-- `method.doesNotTerminateFinitely` means that every stage `k ≥ 1` is reached, so Algorithm
10.2.3 never stops after finitely many stages. -/
def doesNotTerminateFinitely (method : SimplePenaltyFunctionMethod n m) : Prop :=
  ∀ k, 1 ≤ k → method.reached k

/-- `method.doesNotTerminateFinitely` unfolds to the source nontermination condition that every
stage `k ≥ 1` is reached. -/
theorem doesNotTerminateFinitely_iff
    (method : SimplePenaltyFunctionMethod n m) :
    method.doesNotTerminateFinitely ↔
      ∀ k, 1 ≤ k → method.reached k :=
  Iff.rfl

/-- If Algorithm 10.2.3 does not terminate finitely, then every stage `k ≥ 1` is reached. -/
theorem reached_of_doesNotTerminateFinitely
    (method : SimplePenaltyFunctionMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely) (k : ℕ) (hk : 1 ≤ k) :
    method.reached k :=
  method.doesNotTerminateFinitely_iff.mp hNoTerminate k hk

/-- If Algorithm 10.2.3 does not terminate finitely, then every reached stage `k ≥ 1` fails the
source stopping test. -/
theorem not_terminatedAt_of_doesNotTerminateFinitely
    (method : SimplePenaltyFunctionMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely) {k : ℕ} (hk : 1 ≤ k) :
    ¬ method.terminatedAt k := by
  have hreachedSucc : method.reached (k + 1) :=
    method.reached_of_doesNotTerminateFinitely hNoTerminate (k + 1)
      (Nat.succ_le_succ (Nat.zero_le k))
  exact ((method.reached_succ_iff_not_terminatedAt hk).1 hreachedSucc).2

/-- Algorithm 10.2.3 does not terminate finitely exactly when every stage `k ≥ 1` fails the
source stopping test. -/
theorem doesNotTerminateFinitely_iff_forall_not_terminatedAt
    (method : SimplePenaltyFunctionMethod n m) :
    method.doesNotTerminateFinitely ↔
      ∀ k, 1 ≤ k → ¬ method.terminatedAt k := by
  constructor
  · intro h k hk
    exact method.not_terminatedAt_of_doesNotTerminateFinitely h hk
  · intro h k hk
    have hReachedAll : ∀ t : ℕ, method.reached (t + 1) := by
      intro t
      induction t with
      | zero =>
          simpa using method.reached_one
      | succ t ht =>
          have htk : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
          exact (method.reached_succ_iff_not_terminatedAt htk).2 ⟨ht, h (t + 1) htk⟩
    rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
    simpa [Nat.add_comm] using hReachedAll t

/-- Algorithm 10.2.3 does not terminate finitely exactly when every reached stage `k ≥ 1` fails
the source stopping test. -/
theorem doesNotTerminateFinitely_iff_forall_reached_not_terminatedAt
    (method : SimplePenaltyFunctionMethod n m) :
    method.doesNotTerminateFinitely ↔
      ∀ k, 1 ≤ k → method.reached k → ¬ method.terminatedAt k := by
  constructor
  · intro h k hk _hreached
    exact method.not_terminatedAt_of_doesNotTerminateFinitely h hk
  · intro h
    rw [method.doesNotTerminateFinitely_iff]
    intro k hk
    have hReachedAll : ∀ t : ℕ, method.reached (t + 1) := by
      intro t
      induction t with
      | zero =>
          simpa using method.reached_one
      | succ t ht =>
          have htk : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
          exact (method.reached_succ_iff_not_terminatedAt htk).2 ⟨ht, h (t + 1) htk ht⟩
    rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
    simpa [Nat.add_comm] using hReachedAll t

end SimplePenaltyFunctionMethod

/-- Chapter10 Theorem 10.2.5 (1): if Algorithm 10.2.3 does not terminate finitely, then the
minimal violation value of `x ↦ ‖c⁽-⁾[method.problem] x‖` is at least the tolerance `ε`. -/
theorem simplePenaltyFunctionMethod_minimalViolationValue_ge_tolerance
    (method : SimplePenaltyFunctionMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely) :
    method.tolerance ≤ method.problem.minimalViolationValue := sorry

/-- Chapter10 Theorem 10.2.5 (2): if Algorithm 10.2.3 does not terminate finitely, then the
violation norms of the stage solutions `x(σ_k)` converge to the minimal violation value. -/
theorem simplePenaltyFunctionMethod_violationNorm_tendsto_minimalViolationValue
    (method : SimplePenaltyFunctionMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely) :
    Tendsto
      (fun k : ℕ ↦ ‖c⁽-⁾[method.problem] (method.subproblemSolution k)‖)
      atTop
      (nhds method.problem.minimalViolationValue) := sorry

/-- Chapter10 Theorem 10.2.5 (3): if Algorithm 10.2.3 does not terminate finitely, then any
accumulation point `xStar` of the stage-solution sequence `x(σ_k)` solves the problem
`min_x method.problem.objective x` subject to
`‖c⁽-⁾[method.problem] x‖ = method.problem.minimalViolationValue`. -/
theorem simplePenaltyFunctionMethod_accumulationPoint_isMinOn_minimalViolationSet
    (method : SimplePenaltyFunctionMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (method.subproblemSolution ∘ φ) atTop (nhds xStar)) :
    xStar ∈ method.problem.minimalViolationSet ∧
      IsMinOn method.problem.objective method.problem.minimalViolationSet xStar := sorry

#print axioms StandardPenaltyProblem.minimalViolationValue
#print axioms StandardPenaltyProblem.minimalViolationSet

end
