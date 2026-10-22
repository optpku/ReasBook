/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

-- Semantic recall: `lean_leansearch` found `Pi.basisFun_apply`, confirming that
-- `Pi.single t 1` is the canonical term for the unit vector `e_t`.

/-- The unit vector `e_t` with `1` in the `t`-th component and `0` elsewhere. -/
def negativeCurvatureUnitVector {n : ℕ} (t : Fin n) : Fin n → ℝ :=
  Pi.single t 1

/-- Evaluate `negativeCurvatureUnitVector` componentwise. -/
@[simp] theorem negativeCurvatureUnitVector_apply {n : ℕ} (t j : Fin n) :
    negativeCurvatureUnitVector t j = if j = t then 1 else 0 := by
  by_cases h : j = t
  · simp [negativeCurvatureUnitVector, h]
  · simp [negativeCurvatureUnitVector, h]

/-- The score function `ψ_j = d_jj - e_jj` used to select the pivot index in the
negative curvature direction method. -/
def negativeCurvaturePivotScores {n : ℕ} (dDiag eDiag : Fin n → ℝ) : Fin n → ℝ :=
  fun j ↦ dDiag j - eDiag j

/-- Expand `negativeCurvaturePivotScores` at a single index. -/
@[simp] theorem negativeCurvaturePivotScores_apply {n : ℕ}
    (dDiag eDiag : Fin n → ℝ) (j : Fin n) :
    negativeCurvaturePivotScores dDiag eDiag j = dDiag j - eDiag j := rfl

/-- Step 2 chooses `t` so that `ψ t` is minimal among all indices. -/
def negativeCurvaturePivotIsMinimal {n : ℕ} (dDiag eDiag : Fin n → ℝ) (t : Fin n) : Prop :=
  ∀ j : Fin n,
    negativeCurvaturePivotScores dDiag eDiag t ≤ negativeCurvaturePivotScores dDiag eDiag j

/-- Step 3 either stops when `ψ t` is nonnegative or returns a concrete direction `dk`
solving `L_kᵀ d = e_t`. -/
inductive NegativeCurvaturePivotOutcome {n : ℕ}
    (Lk : Matrix (Fin n) (Fin n) ℝ) (dDiag eDiag : Fin n → ℝ) (t : Fin n) : Type where
  /-- The algorithm stops because the minimizing score is nonnegative. -/
  | stop
      (nonnegative : 0 ≤ negativeCurvaturePivotScores dDiag eDiag t) :
      NegativeCurvaturePivotOutcome Lk dDiag eDiag t
  /-- The algorithm returns a direction `dk` solving `L_kᵀ d = e_t` because the
  minimizing score is negative. -/
  | direction
      (negative : negativeCurvaturePivotScores dDiag eDiag t < 0)
      (dk : Fin n → ℝ)
      (solve_eq : (Matrix.transpose Lk).mulVec dk = negativeCurvatureUnitVector t) :
      NegativeCurvaturePivotOutcome Lk dDiag eDiag t

/-- Chapter03 Algorithm 3.5.2: with `ψ j = dDiag j - eDiag j`, choose an index `t`
minimizing `ψ`; if `0 ≤ ψ t`, stop, and otherwise return a concrete direction `dk`
solving `(Matrix.transpose Lk).mulVec dk = e_t`, where
`e_t = negativeCurvatureUnitVector t`. -/
structure NegativeCurvaturePivotStep {n : ℕ}
    (Lk : Matrix (Fin n) (Fin n) ℝ) (dDiag eDiag : Fin n → ℝ) where
  /-- Step 2 chooses the pivot index `t` minimizing `ψ`. -/
  t : Fin n
  /-- Step 2 chooses `t` so that `ψ t` is minimal among all indices. -/
  minimal : negativeCurvaturePivotIsMinimal dDiag eDiag t
  /-- Step 3 records whether the algorithm stops or returns a concrete direction. -/
  outcome : NegativeCurvaturePivotOutcome Lk dDiag eDiag t

/-- A `NegativeCurvaturePivotStep` canonically yields its Step 3 outcome. -/
instance {n : ℕ} {Lk : Matrix (Fin n) (Fin n) ℝ} {dDiag eDiag : Fin n → ℝ}
    (step : NegativeCurvaturePivotStep Lk dDiag eDiag) :
    CoeDep (NegativeCurvaturePivotStep Lk dDiag eDiag) step
      (NegativeCurvaturePivotOutcome Lk dDiag eDiag step.t) where
  coe := step.outcome

/-- The selected pivot score is at most every other score. -/
theorem NegativeCurvaturePivotStep.pivotScore_le {n : ℕ}
    {Lk : Matrix (Fin n) (Fin n) ℝ} {dDiag eDiag : Fin n → ℝ}
    (step : NegativeCurvaturePivotStep Lk dDiag eDiag) (j : Fin n) :
    negativeCurvaturePivotScores dDiag eDiag step.t ≤ negativeCurvaturePivotScores dDiag eDiag j :=
  step.minimal j
