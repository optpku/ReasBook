/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Algorithm_10_3_3
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

open Filter

section

-- Domain sampling:
-- * `InteriorPointPenaltyProblem` in `Definition_10_3_extra_1` is the Chapter 10 core owner for
--   the feasible-set, strict-feasible-set, barrier-sum, and penalty-function surfaces.
-- * `InteriorPointPenaltyFunctionMethod` in `Algorithm_10_3_3` is the source-facing owner for
--   Algorithm 10.3.3 itself, already extending that penalty-problem owner.
-- * `IsMinOn`, `Tendsto`, and `nhds` are the canonical mathlib minimizer/asymptotic surfaces for
--   the theorem-level consequences below.
-- This file therefore stays at the theorem layer: it adds only theorem-specific derived API to
-- the existing method owner and states Theorem 10.3.4 directly in terms of that owner.

variable {Point : Type*} {ι : Type*} [Fintype ι]

namespace InteriorPointPenaltyProblem

/-- The source quantity `inf_{x ∈ int(X)} f(x)` is encoded as the infimum of the objective values
on the strict feasible region `problem.strictFeasibleSet = int(X)`. -/
def strictFeasibleObjectiveInfimum (problem : InteriorPointPenaltyProblem Point ι) : ℝ :=
  sInf (problem.objective '' problem.strictFeasibleSet)

/-- Evaluating `problem.strictFeasibleObjectiveInfimum` expands to the infimum of the objective
values on the source strict feasible region. -/
theorem strictFeasibleObjectiveInfimum_eq
    (problem : InteriorPointPenaltyProblem Point ι) :
    problem.strictFeasibleObjectiveInfimum =
      sInf (problem.objective '' problem.strictFeasibleSet) :=
  rfl

end InteriorPointPenaltyProblem

namespace InteriorPointPenaltyFunctionMethod

/-- `method.terminatesFinitely` means that Algorithm 10.3.3 reaches an active stage `k ≥ 1`
at which the source stopping test holds. -/
def terminatesFinitely (method : InteriorPointPenaltyFunctionMethod Point ι) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ method.active k ∧ method.terminatedAt k

/-- Unfolding `method.terminatesFinitely` gives the source finite-termination condition in terms
of an active stopping stage. -/
theorem terminatesFinitely_iff
    (method : InteriorPointPenaltyFunctionMethod Point ι) :
    method.terminatesFinitely ↔
      ∃ k : ℕ, 1 ≤ k ∧ method.active k ∧ method.terminatedAt k :=
  Iff.rfl

/-- `method.doesNotTerminateFinitely` means that every stage `k ≥ 1` fails the source stopping
test, so Algorithm 10.3.3 never terminates after finitely many stages. -/
def doesNotTerminateFinitely (method : InteriorPointPenaltyFunctionMethod Point ι) : Prop :=
  ∀ k, 1 ≤ k → ¬ method.terminatedAt k

/-- Unfolding `method.doesNotTerminateFinitely` gives the source nontermination condition that
every stage `k ≥ 1` fails the stopping test. -/
theorem doesNotTerminateFinitely_iff
    (method : InteriorPointPenaltyFunctionMethod Point ι) :
    method.doesNotTerminateFinitely ↔
      ∀ k, 1 ≤ k → ¬ method.terminatedAt k :=
  Iff.rfl

/-- Algorithm 10.3.3 does not terminate finitely exactly when every stage `k ≥ 1` remains
active. This is the source-facing active-stage reformulation of the canonical nontermination
owner. -/
theorem doesNotTerminateFinitely_iff_forall_active
    (method : InteriorPointPenaltyFunctionMethod Point ι) :
    method.doesNotTerminateFinitely ↔
      ∀ k, 1 ≤ k → method.active k := by
  constructor
  · intro h k hk
    have hActiveAll : ∀ t : ℕ, method.active (t + 1) := by
      intro t
      induction t with
      | zero =>
          simpa using method.active_one
      | succ t ht =>
          have htk : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
          exact (method.active_succ_iff_not_terminatedAt htk ht).2 (h (t + 1) htk)
    rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
    simpa [Nat.add_comm] using hActiveAll t
  · intro h k hk
    have hactive : method.active k := h k hk
    have hactive_succ : method.active (k + 1) :=
      h (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
    exact (method.active_succ_iff_not_terminatedAt hk hactive).1 hactive_succ

/-- If Algorithm 10.3.3 does not terminate finitely, then every stage `k ≥ 1` remains active. -/
theorem active_of_doesNotTerminateFinitely
    (method : InteriorPointPenaltyFunctionMethod Point ι)
    (hNoTerminate : method.doesNotTerminateFinitely) :
    ∀ k, 1 ≤ k → method.active k :=
  Iff.mp method.doesNotTerminateFinitely_iff_forall_active hNoTerminate

/-- If Algorithm 10.3.3 does not terminate finitely, then every stage `k ≥ 1` fails the source
stopping test. -/
theorem not_terminatedAt_of_doesNotTerminateFinitely
    (method : InteriorPointPenaltyFunctionMethod Point ι)
    (hNoTerminate : method.doesNotTerminateFinitely) {k : ℕ} (hk : 1 ≤ k) :
    ¬ method.terminatedAt k :=
  hNoTerminate k hk

/-- Algorithm 10.3.3 does not terminate finitely exactly when every active stage `k ≥ 1` fails
the source stopping test. -/
theorem doesNotTerminateFinitely_iff_forall_active_not_terminatedAt
    (method : InteriorPointPenaltyFunctionMethod Point ι) :
    method.doesNotTerminateFinitely ↔
      ∀ k, 1 ≤ k → method.active k → ¬ method.terminatedAt k := by
  constructor
  · intro h k hk _
    exact method.not_terminatedAt_of_doesNotTerminateFinitely h hk
  · intro h
    rw [method.doesNotTerminateFinitely_iff]
    intro k hk
    have hActiveAll : ∀ t : ℕ, method.active (t + 1) := by
      intro t
      induction t with
      | zero =>
          simpa using method.active_one
      | succ t ht =>
          have htk : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
          exact (method.active_succ_iff_not_terminatedAt htk ht).2 (h (t + 1) htk ht)
    rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
    simpa [Nat.add_comm] using
      h (t + 1) (Nat.succ_le_succ (Nat.zero_le t)) (hActiveAll t)

/-- The stage-`k` scaled barrier contribution of the `i`th constraint is the source term
`(1 / σ_k) * h (cᵢ(x_(k+1)))`. -/
def barrierTermAt
    (method : InteriorPointPenaltyFunctionMethod Point ι) (i : ι) (k : ℕ) : ℝ :=
  (1 / method.penaltyParameter k) *
    method.barrier (method.constraint i (method.iterate (k + 1)))

/-- Evaluating `method.barrierTermAt i k` expands to the source term
`(1 / σ_k) * h (cᵢ(x_(k+1)))`. -/
theorem barrierTermAt_eq
    (method : InteriorPointPenaltyFunctionMethod Point ι) (i : ι) (k : ℕ) :
    method.barrierTermAt i k =
      (1 / method.penaltyParameter k) *
        method.barrier (method.constraint i (method.iterate (k + 1))) :=
  rfl

/-- The stage-`k` objective value is the source quantity `f(x_k)`. -/
def objectiveValueAt (method : InteriorPointPenaltyFunctionMethod Point ι) (k : ℕ) : ℝ :=
  method.objective (method.iterate k)

/-- Evaluating `method.objectiveValueAt k` expands to the source objective value `f(x_k)`. -/
theorem objectiveValueAt_eq
    (method : InteriorPointPenaltyFunctionMethod Point ι) (k : ℕ) :
    method.objectiveValueAt k = method.objective (method.iterate k) :=
  rfl

end InteriorPointPenaltyFunctionMethod

/-- Chapter10 Theorem 10.3.4 (1): if `f` is bounded below on the feasible region `X` and
`ε > 0`, then Algorithm 10.3.3 terminates finitely at an active stage. -/
theorem interiorPointPenaltyFunctionMethod_terminatesFinitely
    (method : InteriorPointPenaltyFunctionMethod Point ι)
    (hTolerance : 0 < method.tolerance)
    (hBoundedBelow :
      BddBelow (method.objective '' method.toInteriorPointPenaltyProblem.feasibleSet)) :
    method.terminatesFinitely := sorry

/-- Chapter10 Theorem 10.3.4 (2): if `f` is bounded below on the feasible region `X` and
Algorithm 10.3.3 does not terminate finitely, then for each constraint index `i` the scaled
barrier term `(1 / σ_k) * h (cᵢ(x_(k+1)))` tends to `0`, and `method.barrierTermAt i k`
already encodes that source indexing. -/
theorem interiorPointPenaltyFunctionMethod_barrierTerm_tendsto_zero
    (method : InteriorPointPenaltyFunctionMethod Point ι)
    (hBoundedBelow :
      BddBelow (method.objective '' method.toInteriorPointPenaltyProblem.feasibleSet))
    (hNoTerminate : method.doesNotTerminateFinitely) :
    ∀ i : ι, Tendsto (fun k : ℕ ↦ method.barrierTermAt i k) atTop (nhds 0) := sorry

/-- Chapter10 Theorem 10.3.4 (3): if `f` is bounded below on the feasible region `X` and
Algorithm 10.3.3 does not terminate finitely, then the objective values `f(x_k)` tend to
`inf_{x ∈ int(X)} f(x)`, encoded here by the inherited problem-level owner
`method.toInteriorPointPenaltyProblem.strictFeasibleObjectiveInfimum`. The tail encoding
`k + 1` represents the source sequence indexed from stage `1`. -/
theorem interiorPointPenaltyFunctionMethod_objectiveValue_tendsto_strictFeasibleObjectiveInfimum
    (method : InteriorPointPenaltyFunctionMethod Point ι)
    (hBoundedBelow :
      BddBelow (method.objective '' method.toInteriorPointPenaltyProblem.feasibleSet))
    (hNoTerminate : method.doesNotTerminateFinitely) :
    Tendsto
      (fun k : ℕ ↦ method.objectiveValueAt (k + 1))
      atTop
      (nhds method.toInteriorPointPenaltyProblem.strictFeasibleObjectiveInfimum) := sorry

variable [TopologicalSpace Point]

/-- Chapter10 Theorem 10.3.4 (4): under the same feasible-region lower-bound hypothesis, any
accumulation point of the iterate sequence `x_k` in the nonterminating case solves the original
problem `(10.3.1)-(10.3.2)`, represented here as belonging to
`method.toInteriorPointPenaltyProblem.feasibleSet` and minimizing `method.objective` there. The
tail encoding `φ k + 1` represents the source sequence indexed from stage `1`. -/
theorem interiorPointPenaltyFunctionMethod_accumulationPoint_isMinOn_feasibleSet
    (method : InteriorPointPenaltyFunctionMethod Point ι)
    (hBoundedBelow :
      BddBelow (method.objective '' method.toInteriorPointPenaltyProblem.feasibleSet))
    (hNoTerminate : method.doesNotTerminateFinitely)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    xStar ∈ method.toInteriorPointPenaltyProblem.feasibleSet ∧
      IsMinOn method.objective method.toInteriorPointPenaltyProblem.feasibleSet xStar := sorry

#print axioms InteriorPointPenaltyFunctionMethod.terminatesFinitely
#print axioms InteriorPointPenaltyFunctionMethod.doesNotTerminateFinitely
#print axioms InteriorPointPenaltyProblem.strictFeasibleObjectiveInfimum
#print axioms InteriorPointPenaltyFunctionMethod.barrierTermAt
#print axioms InteriorPointPenaltyFunctionMethod.objectiveValueAt

end
