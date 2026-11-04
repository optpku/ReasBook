/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_3.ch2_sec2_3_algorithm_2_1.Pricing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Order.Bounds.Basic

open scoped BigOperators

public section

namespace CuttingStockColumnGeneration

variable {m : ℕ}

/-- The restricted master problem attached to the active pattern family `S'` is feasible at `x`
when the covering inequalities hold, every variable is nonnegative, and all coefficients outside
`S'` vanish. -/
def master_feasible
    (S' : Finset (Fin m → ℕ)) (b : Fin m → ℝ) (x : (Fin m → ℕ) → ℝ) : Prop :=
  (∀ i, b i ≤ Finset.sum S' (fun s ↦ (s i : ℝ) * x s)) ∧
    (∀ s, 0 ≤ x s) ∧
      ∀ s ∉ S', x s = 0

/-- Unfolding characterization of `master_feasible`. -/
theorem master_feasible_iff
    (S' : Finset (Fin m → ℕ)) (b : Fin m → ℝ) (x : (Fin m → ℕ) → ℝ) :
    master_feasible S' b x ↔
      (∀ i, b i ≤ Finset.sum S' (fun s ↦ (s i : ℝ) * x s)) ∧
        (∀ s, 0 ≤ x s) ∧
        ∀ s ∉ S', x s = 0 :=
  Iff.rfl

/-- The feasible set of the restricted master problem attached to the active pattern family `S'`.
-/
def master_feasible_set
    (S' : Finset (Fin m → ℕ)) (b : Fin m → ℝ) : Set ((Fin m → ℕ) → ℝ) :=
  {x | master_feasible S' b x}

/-- Membership in `master_feasible_set S' b` is exactly restricted-master feasibility. -/
@[simp] theorem mem_master_feasible_set_iff
    {S' : Finset (Fin m → ℕ)} {b : Fin m → ℝ} {x : (Fin m → ℕ) → ℝ} :
    x ∈ master_feasible_set S' b ↔ master_feasible S' b x :=
  Iff.rfl

/-- The restricted dual attached to the active pattern family `S'` is feasible at `u` when every
active pattern satisfies its reduced-cost inequality and `u` is coordinatewise nonnegative. -/
def master_dual_feasible
    (S' : Finset (Fin m → ℕ)) (u : Fin m → ℝ) : Prop :=
  (∀ s ∈ S', ∑ i, (s i : ℝ) * u i ≤ 1) ∧
    ∀ i, 0 ≤ u i

/-- Unfolding characterization of `master_dual_feasible`. -/
theorem master_dual_feasible_iff
    (S' : Finset (Fin m → ℕ)) (u : Fin m → ℝ) :
    master_dual_feasible S' u ↔
      (∀ s ∈ S', ∑ i, (s i : ℝ) * u i ≤ 1) ∧
        ∀ i, 0 ≤ u i :=
  Iff.rfl

/-- The feasible set of the restricted dual attached to the active pattern family `S'`. -/
def master_dual_feasible_set
    (S' : Finset (Fin m → ℕ)) : Set (Fin m → ℝ) :=
  {u | master_dual_feasible S' u}

/-- Membership in `master_dual_feasible_set S'` is exactly restricted-dual feasibility. -/
@[simp] theorem mem_master_dual_feasible_set_iff
    {S' : Finset (Fin m → ℕ)} {u : Fin m → ℝ} :
    u ∈ master_dual_feasible_set S' ↔ master_dual_feasible S' u :=
  Iff.rfl

/-- The restricted primal objective is the total weight assigned to the active pattern family
`S'`. -/
def master_objective
    (S' : Finset (Fin m → ℕ)) (x : (Fin m → ℕ) → ℝ) : ℝ :=
  Finset.sum S' x

/-- The restricted dual objective is `∑ i, b_i u_i`. -/
def master_dual_objective
    (b : Fin m → ℝ) (u : Fin m → ℝ) : ℝ :=
  ∑ i, b i * u i

/-- The restricted primal objective values attained on the active pattern family `S'`. -/
def master_objective_values
    (S' : Finset (Fin m → ℕ)) (b : Fin m → ℝ) : Set ℝ :=
  master_objective S' '' master_feasible_set S' b

/-- Membership in `master_objective_values S' b` means that the restricted primal objective is
attained by some restricted-master feasible point. -/
@[simp] theorem mem_master_objective_values_iff
    {S' : Finset (Fin m → ℕ)} {b : Fin m → ℝ} {r : ℝ} :
    r ∈ master_objective_values S' b ↔
      ∃ x : (Fin m → ℕ) → ℝ, master_feasible S' b x ∧ master_objective S' x = r :=
  Iff.rfl

/-- The restricted dual objective values attained on the active pattern family `S'`. -/
def master_dual_objective_values
    (S' : Finset (Fin m → ℕ)) (b : Fin m → ℝ) : Set ℝ :=
  master_dual_objective b '' master_dual_feasible_set S'

/-- Membership in `master_dual_objective_values S' b` means that the restricted dual objective is
attained by some restricted-dual feasible point. -/
@[simp] theorem mem_master_dual_objective_values_iff
    {S' : Finset (Fin m → ℕ)} {b : Fin m → ℝ} {r : ℝ} :
    r ∈ master_dual_objective_values S' b ↔
      ∃ u : Fin m → ℝ, master_dual_feasible S' u ∧ master_dual_objective b u = r :=
  Iff.rfl

/-- A recorded stage of the column-generation method stores the current active pattern family, a
restricted primal solution, a restricted dual solution, and an optimal pricing pattern/value
candidate. -/
structure State (m : ℕ) where
  activePatterns : Finset (Fin m → ℕ)
  primalSolution : (Fin m → ℕ) → ℝ
  dualSolution : Fin m → ℝ
  pricingPattern : Fin m → ℕ
  pricingValue : ℝ

namespace State

/-- `State.record` packages the explicit active set, primal solution, dual solution, and pricing
data into one recorded column-generation stage. -/
def record
    (activePatterns : Finset (Fin m → ℕ))
    (primalSolution : (Fin m → ℕ) → ℝ)
    (dualSolution : Fin m → ℝ)
    (pricingPattern : Fin m → ℕ)
    (pricingValue : ℝ) :
    State m :=
  { activePatterns := activePatterns
    primalSolution := primalSolution
    dualSolution := dualSolution
    pricingPattern := pricingPattern
    pricingValue := pricingValue }

end State

/-- The stagewise clause of column generation says that the current active family `S'` is solved
to restricted primal and dual optimality, the pricing problem over the full pattern family `S` is
solved by `s*` with value `v*`, and either `v* ≤ 1` certifies full-master optimality or the next
active family is obtained by adjoining `s*`. -/
def stagewiseClause
    (S : Finset (Fin m → ℕ)) (b : Fin m → ℝ)
    (σ τ : State m) : Prop :=
  σ.activePatterns ⊆ S ∧
    master_feasible σ.activePatterns b σ.primalSolution ∧
    IsLeast (master_objective_values σ.activePatterns b)
      (master_objective σ.activePatterns σ.primalSolution) ∧
    master_dual_feasible σ.activePatterns σ.dualSolution ∧
    IsGreatest (master_dual_objective_values σ.activePatterns b)
      (master_dual_objective b σ.dualSolution) ∧
    σ.pricingPattern ∈ S ∧
    IsGreatest (pricing_objective_values S σ.dualSolution) σ.pricingValue ∧
    pricing_objective σ.dualSolution σ.pricingPattern = σ.pricingValue ∧
    ((σ.pricingValue ≤ 1 ∧
        τ = σ ∧
        master_feasible S b σ.primalSolution ∧
        IsLeast (master_objective_values S b)
          (master_objective S σ.primalSolution)) ∨
      (1 < σ.pricingValue ∧
        τ.activePatterns = insert σ.pricingPattern σ.activePatterns))

/-- The stagewise clause expands to restricted-master primal and dual optimality, pricing
optimality, and the textbook termination-or-augmentation alternative. -/
theorem stagewiseClause_iff
    (S : Finset (Fin m → ℕ)) (b : Fin m → ℝ)
    (σ τ : State m) :
    stagewiseClause S b σ τ ↔
      σ.activePatterns ⊆ S ∧
        master_feasible σ.activePatterns b σ.primalSolution ∧
        IsLeast (master_objective_values σ.activePatterns b)
          (master_objective σ.activePatterns σ.primalSolution) ∧
        master_dual_feasible σ.activePatterns σ.dualSolution ∧
        IsGreatest (master_dual_objective_values σ.activePatterns b)
          (master_dual_objective b σ.dualSolution) ∧
        σ.pricingPattern ∈ S ∧
        IsGreatest (pricing_objective_values S σ.dualSolution) σ.pricingValue ∧
        pricing_objective σ.dualSolution σ.pricingPattern = σ.pricingValue ∧
        ((σ.pricingValue ≤ 1 ∧
            τ = σ ∧
            master_feasible S b σ.primalSolution ∧
            IsLeast (master_objective_values S b)
              (master_objective S σ.primalSolution)) ∨
          (1 < σ.pricingValue ∧
            τ.activePatterns = insert σ.pricingPattern σ.activePatterns)) :=
  Iff.rfl

/-- Algorithm 2.1. `isAlgorithm S b run` is the source-faithful stage-indexed execution
specification of column generation for the LP relaxation of the pattern-based cutting-stock model
over the actual pattern family `S`: every stage solves the restricted primal and dual LPs, solves
the pricing knapsack problem, and either terminates with a full-master optimum when `v* ≤ 1` or
augments the active family by the pricing pattern `s*`. The initial-subset condition is recovered
from the `k = 0` stage clause. -/
@[mk_iff isAlgorithm_iff]
structure isAlgorithm
    (S : Finset (Fin m → ℕ)) (b : Fin m → ℝ)
    (run : ℕ → State m) : Prop
where
  stagewiseStep : ∀ k, stagewiseClause S b (run k) (run (k + 1))

/-- Every recorded active pattern family in an algorithm run is a subset of the ambient pattern
family `S`. -/
theorem isAlgorithm.activePatterns_subset
    {S : Finset (Fin m → ℕ)} {b : Fin m → ℝ}
    {run : ℕ → State m} (h : isAlgorithm S b run) (k : ℕ) :
    (run k).activePatterns ⊆ S :=
  (h.stagewiseStep k).1

/-- The initial active pattern family in an algorithm run is a subset of `S`. -/
theorem isAlgorithm.initialSubset
    {S : Finset (Fin m → ℕ)} {b : Fin m → ℝ}
    {run : ℕ → State m} (h : isAlgorithm S b run) :
    (run 0).activePatterns ⊆ S :=
  h.activePatterns_subset 0

/-- `isAlgorithm.ofClauses` packages the repeated column-generation stagewise clause into the
source-faithful execution owner. -/
def isAlgorithm.ofClauses
    {S : Finset (Fin m → ℕ)} {b : Fin m → ℝ}
    {run : ℕ → State m}
    (h_stagewiseStep : ∀ k, stagewiseClause S b (run k) (run (k + 1))) :
    isAlgorithm S b run where
  stagewiseStep := h_stagewiseStep

end CuttingStockColumnGeneration
