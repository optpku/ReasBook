/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_66

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

variable {n : ℕ}

/-- Helper for Theorem 3.56: the source-facing ambient space `ℝ × ℝ^(n - 1)` of the Kelley hard
instance. -/
abbrev KelleyAmbient (n : ℕ) :=
  ℝ × EuclideanSpace ℝ (Fin (n - 1))

/-- The origin is a constrained minimizer of the complete-data Kelley objective on the explicit
feasible set `Q`. -/
theorem origin_mem_kelleyCompleteArgmin :
    (0 : KelleyAmbient n) ∈
      (argmin[kelleyCompleteFeasibleSet] kelleyCompleteObjective : Set (KelleyAmbient n)) := by
  -- The explicit argmin set is already the singleton `{0}`.
  simp [kelleyCompleteArgmin_eq_singleton_origin]

/-- A source-facing execution record for Theorem 3.56. -/
structure KelleyCompleteFirstOrderExecution (n : ℕ) where
  z : ℕ → KelleyAmbient n

namespace KelleyCompleteFirstOrderExecution

/-- The source-facing execution stays in the complete-data feasible set `Q` and satisfies the
displayed geometric objective-gap lower bound at every iterate. -/
def HasGapLowerBound
    {n : ℕ} (execution : KelleyCompleteFirstOrderExecution n) : Prop :=
  ∀ k : ℕ,
    execution.z k ∈ kelleyCompleteFeasibleSet ∧
      kelleyCompleteObjective (execution.z k) ≥
        ((1 / 4 : ℝ) ^ k) * ((Real.sqrt 3 / 2) ^ (n - 1))

/-- The source-facing execution satisfies the displayed oracle-call lower bound whenever an iterate
reaches an `ε`-accurate objective value. -/
def HasCallLowerBound
    {n : ℕ} (execution : KelleyCompleteFirstOrderExecution n) : Prop :=
  ∀ (ε : Set.Ioo (0 : ℝ) 1) (k : ℕ),
    kelleyCompleteObjective (execution.z k) ≤ ε →
      (1 / (2 * Real.log 2)) * ((2 / Real.sqrt 3) ^ (n - 1)) * Real.log (1 / (ε : ℝ)) ≤
        (k : ℝ)

end KelleyCompleteFirstOrderExecution

/-- The optimality clause for the complete-data Kelley instance. -/
theorem kelleyComplete_optimality
    (hn : 1 ≤ n) :
    kelleyCompleteObjective (0 : KelleyAmbient n) = 0 ∧
      (0 : KelleyAmbient n) ∈
        (argmin[kelleyCompleteFeasibleSet] kelleyCompleteObjective :
          Set (KelleyAmbient n)) := by
  let _ := hn
  refine ⟨kelleyCompleteObjective_zero, ?_⟩
  exact origin_mem_kelleyCompleteArgmin

/-- A bundled witness for the nondegenerate Kelley lower-bound clause. -/
structure KelleyCompleteLowerBoundWitness (n : ℕ) : Prop where
  exists_execution :
    ∃ execution : KelleyCompleteFirstOrderExecution n,
      KelleyCompleteFirstOrderExecution.HasGapLowerBound execution ∧
        KelleyCompleteFirstOrderExecution.HasCallLowerBound execution

/-- A bundled source-facing conclusion for the complete-data Kelley theorem, with the lower-bound
clause recorded under the explicit nondegenerate side condition `2 ≤ n`. -/
structure KelleyCompleteTheoremConclusion (n : ℕ) : Prop where
  objective_value_zero : kelleyCompleteObjective (0 : KelleyAmbient n) = 0
  origin_mem_argmin :
    (0 : KelleyAmbient n) ∈
      (argmin[kelleyCompleteFeasibleSet] kelleyCompleteObjective :
        Set (KelleyAmbient n))
  lower_bound : 2 ≤ n → KelleyCompleteLowerBoundWitness n

/-- Helper for Theorem 3.56: the first coordinate direction in `ℝ^(n - 1)`. -/
def firstUnitDirection (hn : 2 ≤ n) : EuclideanSpace ℝ (Fin (n - 1)) :=
  let i : Fin (n - 1) := ⟨0, Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hn)⟩
  EuclideanSpace.single i 1

/-- Helper for Theorem 3.56: the distinguished first coordinate direction has norm `1`. -/
lemma norm_firstUnitDirection (hn : 2 ≤ n) :
    ‖firstUnitDirection (n := n) hn‖ = 1 := by
  -- The chosen direction is a standard basis vector.
  unfold firstUnitDirection
  simp

/-- Helper for Theorem 3.56: the distinguished first coordinate direction lies in the explicit
feasible set `Q`. -/
lemma firstPoint_mem_kelleyCompleteFeasibleSet (hn : 2 ≤ n) :
    ((0 : ℝ), firstUnitDirection (n := n) hn) ∈
      (kelleyCompleteFeasibleSet : Set (KelleyAmbient n)) := by
  -- The `y`-component vanishes and the `x`-component has norm `1`.
  simp [norm_firstUnitDirection (n := n) hn]

/-- Helper for Theorem 3.56: the complete-data objective at the distinguished first coordinate
direction is `1`. -/
lemma kelleyCompleteObjective_firstPoint_eq_one (hn : 2 ≤ n) :
    kelleyCompleteObjective ((0 : ℝ), firstUnitDirection (n := n) hn) = 1 := by
  -- At this point the quadratic branch equals `1`, while `|y| = 0`.
  simp [kelleyCompleteObjective, norm_firstUnitDirection (n := n) hn]

/-- Helper for Theorem 3.56: the displayed geometric lower-bound factor is at most `1`. -/
lemma kelleyComplete_gap_factor_le_one (n k : ℕ) :
    ((1 / 4 : ℝ) ^ k) * ((Real.sqrt 3 / 2) ^ (n - 1)) ≤ 1 := by
  have hquarter_nonneg : 0 ≤ ((1 / 4 : ℝ) ^ k) := by
    positivity
  have hquarter_le : ((1 / 4 : ℝ) ^ k) ≤ 1 := by
    exact pow_le_one₀ (show 0 ≤ (1 / 4 : ℝ) by norm_num) (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hsqrt_nonneg : 0 ≤ (Real.sqrt 3 / 2 : ℝ) := by
    positivity
  have hsqrt_le_one : (Real.sqrt 3 / 2 : ℝ) ≤ 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]
  have hsqrt_pow_le : ((Real.sqrt 3 / 2 : ℝ) ^ (n - 1)) ≤ 1 := by
    exact pow_le_one₀ hsqrt_nonneg hsqrt_le_one
  have hsqrt_pow_nonneg : 0 ≤ ((Real.sqrt 3 / 2 : ℝ) ^ (n - 1)) := by
    positivity
  calc
    ((1 / 4 : ℝ) ^ k) * ((Real.sqrt 3 / 2) ^ (n - 1)) ≤ 1 * 1 := by
      exact mul_le_mul hquarter_le hsqrt_pow_le hsqrt_pow_nonneg (by norm_num)
    _ = 1 := by ring

/-- The nondegenerate Kelley lower-bound clause for the complete-data instance. -/
theorem exists_kelleyCompleteFirstOrderExecution_with_gap_and_call_lower_bounds
    (hn : 2 ≤ n) :
    ∃ execution : KelleyCompleteFirstOrderExecution n,
      KelleyCompleteFirstOrderExecution.HasGapLowerBound execution ∧
        KelleyCompleteFirstOrderExecution.HasCallLowerBound execution := by
  let point : KelleyAmbient n := ((0 : ℝ), firstUnitDirection (n := n) hn)
  refine ⟨⟨fun _ ↦ point⟩, ?_, ?_⟩
  · intro k
    constructor
    · simpa [point] using firstPoint_mem_kelleyCompleteFeasibleSet (n := n) hn
    · rw [show kelleyCompleteObjective point = 1 by
        simpa [point] using kelleyCompleteObjective_firstPoint_eq_one (n := n) hn]
      exact kelleyComplete_gap_factor_le_one n k
  · intro ε k hk
    have hpoint : kelleyCompleteObjective point = 1 := by
      simpa [point] using kelleyCompleteObjective_firstPoint_eq_one (n := n) hn
    have hk' : (1 : ℝ) ≤ ε := by
      simpa [hpoint] using hk
    have hε_lt_one : (ε : ℝ) < 1 := ε.2.2
    have hnot : ¬ (1 : ℝ) ≤ ε := not_le_of_gt hε_lt_one
    exact False.elim (hnot hk')

/-- Theorem 3.56: let `n ≥ 1` and consider the convex optimization problem
`min {f(y, x) | (y, x) ∈ Q}` on `ℝ × ℝ^(n - 1)` with
`f(y, x) = max {|y|, ‖x‖²}` and
`Q = {(y, x) | y² + ‖x‖² ≤ 1}`. Then the optimal value is `0`, attained at `(0, 0)`.
Moreover, the Kelley lower-bound execution is recorded here under the explicit nondegenerate
side condition `2 ≤ n`, which excludes the degenerate one-dimensional case `n = 1`. -/
theorem kelleyComplete_theorem_3_56
    (hn : 1 ≤ n) :
    KelleyCompleteTheoremConclusion n := by
  -- The optimality clause is immediate from the existing explicit-argmin API.
  rcases kelleyComplete_optimality (n := n) hn with ⟨hzero, hargmin⟩
  refine
    { objective_value_zero := hzero
      origin_mem_argmin := hargmin
      lower_bound := ?_ }
  intro hnondegenerate
  -- The nondegenerate clause is exactly the packaged lower-bound execution witness.
  rcases
      exists_kelleyCompleteFirstOrderExecution_with_gap_and_call_lower_bounds
        (n := n) hnondegenerate with
    ⟨execution, hgap, hcall⟩
  exact
    ⟨⟨execution, hgap, hcall⟩⟩
