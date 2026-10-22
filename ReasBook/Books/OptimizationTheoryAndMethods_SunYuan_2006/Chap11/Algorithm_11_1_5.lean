/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_3

noncomputable section

-- Domain sampling:
-- * primary domain: feasible-direction methods in real Hilbert spaces, specialized here to
--   `EuclideanSpace ℝ (Fin n)`
-- * core/canonical owner reused from earlier Chapter 11: `IsFeasibleDescentDirection`
-- * bridge/view reused for positive feasible steplengths: `feasiblePointLineSearchDomain`
-- * source-facing layer retained here: the stagewise run data of Algorithm 11.1.5

/-- Chapter11 Algorithm 11.1.5: a feasible point method for minimizing `objective` on
`feasibleSet` starts from `x₁ ∈ feasibleSet`. Step 2 stops when no vector satisfies the concrete
conditions `IsFeasibleDescentDirection objective x_k feasibleSet d`; otherwise it chooses `d_k`
with that property. Step 3 produces a positive feasible steplength
`stepSize k ∈ feasiblePointLineSearchDomain x_k d_k feasibleSet`, and Step 4 updates
`x_(k + 1) = x_k + α_k • d_k`. Here `continues k` means that Step 2 succeeds at stage `k`, so
the method carries out Steps 3-4 from `x_k`; after that, stage `k + 1` is continuing exactly
when the new iterate `x_(k + 1)` again admits a Step-2 direction. -/
structure FeasiblePointMethod (n : ℕ) where
  feasibleSet : Set (EuclideanSpace ℝ (Fin n))
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  initialPoint : EuclideanSpace ℝ (Fin n)
  continues : ℕ → Prop
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  direction : ℕ → EuclideanSpace ℝ (Fin n)
  stepSize : ℕ → ℝ
  initialPoint_mem : initialPoint ∈ feasibleSet
  iterate_one : iterate 1 = initialPoint
  continues_one_iff :
    continues 1 ↔
      ∃ d : EuclideanSpace ℝ (Fin n),
        IsFeasibleDescentDirection objective initialPoint feasibleSet d
  feasible (k : ℕ) (hk : 1 ≤ k) (hcontinues : continues k) :
    iterate k ∈ feasibleSet
  direction_spec (k : ℕ) (hk : 1 ≤ k) (hcontinues : continues k) :
    IsFeasibleDescentDirection objective (iterate k) feasibleSet (direction k)
  step_search (k : ℕ) (hk : 1 ≤ k) (hcontinues : continues k) :
    stepSize k ∈ feasiblePointLineSearchDomain (iterate k) (direction k) feasibleSet
  iterate_succ (k : ℕ) (hk : 1 ≤ k) (hcontinues : continues k) :
    iterate (k + 1) = iterate k + stepSize k • direction k
  continues_succ_iff (k : ℕ) (hk : 1 ≤ k) :
    continues (k + 1) ↔
      continues k ∧
        ∃ d : EuclideanSpace ℝ (Fin n),
          IsFeasibleDescentDirection objective (iterate (k + 1)) feasibleSet d

namespace FeasiblePointMethod

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Method" => @_root_.FeasiblePointMethod n

/-- A point belongs to `method` when it lies in the feasible set encoded by the method. -/
instance instMembershipPoint :
    Membership Point Method where
  mem method x := x ∈ method.feasibleSet

/-- Membership in `method` is exactly membership in the feasible set recorded by `method`. -/
theorem mem_feasibleSet_iff
    (method : Method) (x : Point) :
    x ∈ method ↔ x ∈ method.feasibleSet :=
  Iff.rfl

/-- Algorithm 11.1.5 is terminated at stage `k` when the current iterate `x_k` has no
admissible Step-2 search direction. -/
def terminatedAt (method : Method) (k : ℕ) : Prop :=
  ¬ ∃ d : Point,
      IsFeasibleDescentDirection
        method.objective (method.iterate k) method.feasibleSet d

/-- Unfolding `method.terminatedAt k` gives the failure of the Step-2 direction-existence
condition at `x_k`. -/
theorem terminatedAt_iff
    (method : Method) (k : ℕ) :
    method.terminatedAt k ↔
      ¬ ∃ d : Point,
        IsFeasibleDescentDirection
          method.objective (method.iterate k) method.feasibleSet d :=
  Iff.rfl

/-- The initial point recorded by `method` lies in the feasible set of `method`. -/
theorem initialPoint_mem_feasibleSet
    (method : Method) :
    method.initialPoint ∈ method.feasibleSet :=
  method.initialPoint_mem

/-- The first iterate of `method` is the recorded initial point `x₁`. -/
theorem iterate_one_eq_initialPoint
    (method : Method) :
    method.iterate 1 = method.initialPoint :=
  method.iterate_one

/-- The initial iterate of `method` is the recorded feasible initial point. -/
theorem iterate_one_mem_feasibleSet
    (method : Method) :
    method.iterate 1 ∈ method.feasibleSet := by
  simpa [method.iterate_one_eq_initialPoint] using method.initialPoint_mem_feasibleSet

/-- The initial stage is continuing exactly when the initial point admits a Step-2 search
direction. -/
theorem continues_one_iff_exists_feasibleDescentDirection
    (method : Method) :
    method.continues 1 ↔
      ∃ d : Point,
        IsFeasibleDescentDirection
          method.objective (method.iterate 1) method.feasibleSet d := by
  simpa [method.iterate_one] using method.continues_one_iff

/-- If stage `k` is continuing, then the recorded step size `α_k` is positive. -/
theorem stepSize_pos
    (method : Method) (k : ℕ) (hk : 1 ≤ k)
    (hcontinues : method.continues k) :
    0 < method.stepSize k := by
  exact
    (mem_feasiblePointLineSearchDomain_iff
      (method.iterate k) (method.direction k) method.feasibleSet (method.stepSize k)).1
      (method.step_search k hk hcontinues) |>.1

/-- If stage `k` is continuing, then the Step-3 feasible point search keeps the next iterate
`x_(k + 1)` in the feasible set. -/
theorem iterate_succ_mem_feasibleSet
    (method : Method) (k : ℕ) (hk : 1 ≤ k)
    (hcontinues : method.continues k) :
    method.iterate (k + 1) ∈ method.feasibleSet := by
  rw [method.iterate_succ k hk hcontinues]
  exact
    (mem_feasiblePointLineSearchDomain_iff
      (method.iterate k) (method.direction k) method.feasibleSet (method.stepSize k)).1
      (method.step_search k hk hcontinues) |>.2

/-- After a continuing stage `k`, the algorithm continues past Step 2 at stage `k + 1`
exactly when the new iterate `x_(k + 1)` is not a termination point. -/
theorem continues_succ_iff_not_terminatedAt
    (method : Method) (k : ℕ) (hk : 1 ≤ k)
    (hcontinues : method.continues k) :
    method.continues (k + 1) ↔ ¬ method.terminatedAt (k + 1) := by
  classical
  have hsucc' := method.continues_succ_iff k hk
  simpa [terminatedAt, hcontinues] using hsucc'

end FeasiblePointMethod
