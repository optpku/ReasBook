/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_11

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain note: this item lies in the Chapter 5 explicit-structure path-following complexity domain.

Sampled owner declarations in this domain:
* `BarrierPathFollowingScheme` in `Definition_5_3_4_1`, the chapter owner for short-step
  path-following data;
* `barrierPathFollowingStoppingThreshold` and `barrierPathFollowingTerminationBound` in
  `Theorem_5_3_11`, the generic Chapter 5 owners governing short-step complexity;
* `Matrix.mulVec`-free scalar `O(...)` predicates elsewhere in the project, the standard source-
  facing bridge pattern when a textbook asymptotic estimate is read off from a more canonical
  owner theorem.

Best owner abstraction:
* source-facing: the textbook short-step iteration-count asymptotic
  `HasLpBarrierShortStepIterationBound ε N_it` with fixed accuracy `ε ∈ (0, 1)`;
* core/canonical: `BarrierPathFollowingScheme` together with
  `barrierPathFollowingTerminationBound`;
* bridge/view: the equivalence below between the canonical owner plus the fixed-accuracy side
  condition and the explicit `ν = 4m + n + 1` formula.

Primitive data:
* the fixed accuracy `ε`;
* the iteration-count family `N_it`.

Derived API:
* the source-facing Chapter 5 owner `HasLpBarrierShortStepIterationBound ε N_it`;
* the positive-dimension guard `0 < n`, matching the surrounding Chapter 5 complexity owners;
* the source-facing explicit template theorem specialized to `ν = 4m + n + 1`.

The previous version imported a nearby theorem file for a source-facing asymptotic predicate.
This refinement makes Definition 5.4.9.6 the owner of that source-facing `O(...)` bound, while
keeping the chapter’s path-following termination-bound layer as the canonical background owner.
For an existential-constant `O(...)` predicate, replacing `√(m + n)` by `√(4m + n + 1)` changes
the bound only by a universal constant factor on `ℕ`, so the remaining theorem stays a thin
explicit-template bridge. -/

section

variable (ε : ℝ) (N_it : ℕ → ℕ → ℕ)

/- This item is a source-facing bridge over the canonical Chapter 5 path-following
termination-bound layer. -/
recall barrierPathFollowingTerminationBound

/-- Definition 5.4.9.6: a short-step iteration model with count `N_it` satisfies the textbook
`O(√(m + n) log ((m + n) / ε))` bound at the fixed small accuracy `ε ∈ (0, 1)` if it is
controlled by a positive constant independent of `m` and `n` on positive variable dimension
`n`. -/
def HasLpBarrierShortStepIterationBound : Prop :=
  ε ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ C_it : ℝ,
      0 < C_it ∧
        ∀ m n : ℕ, 0 < n →
          (N_it m n : ℝ) ≤
            C_it * Real.sqrt ((m : ℝ) + (n : ℝ)) *
              Real.log (((m + n : ℕ) : ℝ) / ε)

private theorem iterationLog_nonneg
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (m n : ℕ) (hn : 0 < n) :
    0 ≤ Real.log (((m + n : ℕ) : ℝ) / ε) := by
  have hone_le_sum : (1 : ℝ) ≤ ((m + n : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ m + n by omega)
  have hε_le_sum : ε ≤ ((m + n : ℕ) : ℝ) := by
    exact le_trans (le_of_lt hε.2) hone_le_sum
  have hratio_ge_one : (1 : ℝ) ≤ ((m + n : ℕ) : ℝ) / ε := by
    exact (one_le_div₀ hε.1).2 hε_le_sum
  exact Real.log_nonneg hratio_ge_one

private theorem sqrt_sum_le_sqrt_explicit (m n : ℕ) :
    Real.sqrt (((m + n : ℕ) : ℝ)) ≤ Real.sqrt (4 * m + n + 1 : ℝ) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast (show m + n ≤ 4 * m + n + 1 by omega)

private theorem sqrt_explicit_le_three_mul_sqrt_sum
    (m n : ℕ) (hn : 0 < n) :
    Real.sqrt (4 * m + n + 1 : ℝ) ≤ 3 * Real.sqrt (((m + n : ℕ) : ℝ)) := by
  have hbound : (4 * m + n + 1 : ℝ) ≤ 9 * (((m + n : ℕ) : ℝ)) := by
    exact_mod_cast (show 4 * m + n + 1 ≤ 9 * (m + n) by
      have hmn_one : 1 ≤ m + n := by omega
      omega)
  refine le_trans (Real.sqrt_le_sqrt hbound) ?_
  rw [Real.sqrt_mul (by positivity)]
  norm_num

/-- The Chapter 5 owner `HasLpBarrierShortStepIterationBound ε N_it` is equivalent to the
explicit source-facing constant-factor bound with `ν = 4m + n + 1`, together with the fixed
small-accuracy hypothesis `ε ∈ (0, 1)` and the positive-dimension guard `0 < n`. -/
theorem hasLpBarrierShortStepIterationBound_iff_explicitTemplate
    : HasLpBarrierShortStepIterationBound ε N_it ↔
      ε ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 0 < n →
          (N_it m n : ℝ) ≤
            C * Real.sqrt (4 * m + n + 1 : ℝ) *
              Real.log (((m + n : ℕ) : ℝ) / ε) := by
  constructor
  · rintro ⟨hε, C, hC, hbound⟩
    refine ⟨hε, C, hC, ?_⟩
    intro m n hn
    have h₁ :
        (N_it m n : ℝ) ≤
          C * Real.sqrt (((m + n : ℕ) : ℝ)) *
            Real.log (((m + n : ℕ) : ℝ) / ε) := by
      simpa [Nat.cast_add, mul_assoc] using hbound m n hn
    have hlog_nonneg := iterationLog_nonneg hε m n hn
    have h₂ :
        C * Real.sqrt (((m + n : ℕ) : ℝ)) *
            Real.log (((m + n : ℕ) : ℝ) / ε) ≤
          C * Real.sqrt (4 * m + n + 1 : ℝ) *
            Real.log (((m + n : ℕ) : ℝ) / ε) := by
      have htemplate :=
        mul_le_mul_of_nonneg_right (sqrt_sum_le_sqrt_explicit m n) hlog_nonneg
      have hscaled := mul_le_mul_of_nonneg_left htemplate hC.le
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans h₁ h₂
  · rintro ⟨hε, C, hC, hbound⟩
    refine ⟨hε, 3 * C, by positivity, ?_⟩
    intro m n hn
    have h₁ :
        (N_it m n : ℝ) ≤
          C * Real.sqrt (4 * m + n + 1 : ℝ) *
            Real.log (((m + n : ℕ) : ℝ) / ε) := by
      simpa [mul_assoc] using hbound m n hn
    have hlog_nonneg := iterationLog_nonneg hε m n hn
    have h₂ :
        C * Real.sqrt (4 * m + n + 1 : ℝ) *
            Real.log (((m + n : ℕ) : ℝ) / ε) ≤
          (3 * C) * Real.sqrt ((m : ℝ) + (n : ℝ)) *
            Real.log (((m + n : ℕ) : ℝ) / ε) := by
      have htemplate :=
        mul_le_mul_of_nonneg_right
          (sqrt_explicit_le_three_mul_sqrt_sum m n hn) hlog_nonneg
      have hscaled := mul_le_mul_of_nonneg_left htemplate hC.le
      simpa [Nat.cast_add, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans h₁ h₂

end
