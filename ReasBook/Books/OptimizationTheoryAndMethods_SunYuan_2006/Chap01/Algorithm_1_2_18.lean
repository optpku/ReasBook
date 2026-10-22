/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OptimizationTheoryAndMethods_SunYuan_2006.Matrix.UnitLowerTriangular

noncomputable section

open Matrix
open scoped BigOperators

-- Domain sampling:
-- * `Matrix.IsUnitLowerTriangular` is the project owner for the unit-lower hypothesis on the LDL
--   factor.
-- * `Matrix.mulVec` is the canonical owner for the solve equation `L.mulVec p = y`.
-- * `Matrix.inv_mulVec_eq_vec` and `Matrix.mulVec_mulVec` are the canonical bridge lemmas for the
--   inverse-based solve `L⁻¹ *ᵥ y`.
-- * `Theorem_1_2_15` and `Exercise_1_6` keep nearby Chapter 1 rank-one matrix updates over a
--   field-valued matrix owner rather than fixing `ℝ`; this file should live at the same algebraic
--   owner level.
-- * `NegativeRankOneCholeskyUpdate` in `Algorithm_1_2_19` keeps the textbook algorithm owner
--   separate from its inverse-based solve bridge; the same source/core/bridge split is used here.
-- * `Matrix.vecMulVec` is the canonical rank-one update owner for `α y yᵀ`.
-- * `Fin n` already carries the canonical order on stage/row indices, so strict lower-triangular
--   positions should be expressed as `j < r` rather than through projection arithmetic.
-- Source/core/bridge triage:
-- * source-facing: Algorithm 1.2.18 outputs `α_j`, `barD_j`, `β_j`, `w^(j)`, and `barL`.
-- * core/canonical: `Matrix.IsUnitLowerTriangular`, `Matrix.mulVec`, `Matrix.diagonal`,
--   `Matrix.transpose`, and `Matrix.vecMulVec`.
-- * bridge/view: the solve equation `L.mulVec p = y`, and under invertibility the specialized
--   solve vector `L⁻¹ *ᵥ y`.
-- * owner abstraction: square matrices over a field together with the canonical matrix solve and
--   rank-one update owners above; the recursive algorithm data is source-facing API derived from
--   that ambient owner.

namespace RankOneCholeskyUpdate

private structure State (𝕜 : Type*) (n : Nat) where
  alpha : Fin (n + 1) → 𝕜
  barD : Fin n → 𝕜
  beta : Fin n → 𝕜
  w : Fin (n + 1) → Fin n → 𝕜
  barL : Matrix (Fin n) (Fin n) 𝕜

section

variable {n : Nat} {𝕜 : Type*} [Field 𝕜]

local notation "Hessian" => Matrix (Fin n) (Fin n) 𝕜

section

/-- The initial state stores `α₁ = α`, `w^(1) = y`, and uses zero placeholders for the data
that are produced only after the iterative updates begin. -/
private def init (L : Hessian) (y : Fin n → 𝕜) (α : 𝕜) : State 𝕜 n where
  alpha := Function.update (fun _ ↦ 0) 0 α
  barD := fun _ ↦ 0
  beta := fun _ ↦ 0
  w := Function.update (fun _ ↦ 0) 0 y
  barL := L

/-- One step of the rank-one LDL/Cholesky update records the current pivot entry
`p_j = w_j^(j)`, updates `barD_j`, `β_j`, and `α_(j+1)`, advances the auxiliary vector
`w^(j+1)`, and modifies the `j`-th column of the lower factor. -/
private def step (L : Hessian) (d : Fin n → 𝕜) (j : Fin n) (state : State 𝕜 n) :
    State 𝕜 n :=
  let pj := state.w (Fin.castSucc j) j
  let barDj := d j + state.alpha (Fin.castSucc j) * pj ^ 2
  let betaj := pj * state.alpha (Fin.castSucc j) / barDj
  let nextAlpha := d j * state.alpha (Fin.castSucc j) / barDj
  let nextW : Fin n → 𝕜 := fun r ↦
    if j < r then
      state.w (Fin.castSucc j) r - pj * L r j
    else
      state.w (Fin.castSucc j) r
  let nextBarL : Hessian := fun r c ↦
    if c = j ∧ c < r then
      L r c + betaj * nextW r
    else
      state.barL r c
  { alpha := Function.update state.alpha j.succ nextAlpha
    barD := Function.update state.barD j barDj
    beta := Function.update state.beta j betaj
    w := Function.update state.w j.succ nextW
    barL := nextBarL }

/-- Running the first `k` steps of Algorithm 1.2.18. -/
private def stateAt (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) : Nat → State 𝕜 n
  | 0 => init L y α
  | k + 1 =>
      if hk : k < n then
        step L d ⟨k, hk⟩ (stateAt L d y α k)
      else
        stateAt L d y α k

/-- The scalar sequence `α_j` produced by Algorithm 1.2.18. -/
def alpha (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) : Fin (n + 1) → 𝕜 :=
  (stateAt L d y α n).alpha

/-- The updated diagonal sequence `barD_j` produced by Algorithm 1.2.18. -/
def barD (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) : Fin n → 𝕜 :=
  (stateAt L d y α n).barD

/-- The coefficient sequence `β_j` produced by Algorithm 1.2.18. -/
def beta (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) : Fin n → 𝕜 :=
  (stateAt L d y α n).beta

/-- The auxiliary vectors `w^(j)` produced by Algorithm 1.2.18. -/
def w (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) : Fin (n + 1) → Fin n → 𝕜 :=
  (stateAt L d y α n).w

/-- The updated lower factor `barL` produced by Algorithm 1.2.18. -/
def barL (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) : Hessian :=
  (stateAt L d y α n).barL

/-- In the textbook LDL setting, the recursive formulas are well-defined when each denominator
`barD_j = d_j + α_j p_j^2` is nonzero and the input lower factor is unit lower triangular. -/
def wellDefined (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) : Prop :=
  L.IsUnitLowerTriangular ∧ ∀ j : Fin n, barD L d y α j ≠ 0

end

section

variable (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)

theorem wellDefined_unitLowerTriangular
    {n : Nat} {𝕜 : Type*} [Field 𝕜]
    (L : Matrix (Fin n) (Fin n) 𝕜) (d y : Fin n → 𝕜) (α : 𝕜)
    (h : wellDefined L d y α) :
    L.IsUnitLowerTriangular := by
  -- Unfold the source-facing well-definedness predicate once and read off its first component.
  have h' : L.IsUnitLowerTriangular ∧ ∀ j : Fin n, barD L d y α j ≠ 0 := by
    simpa [wellDefined] using h
  exact h'.1

theorem wellDefined_barD_ne_zero
    {n : Nat} {𝕜 : Type*} [Field 𝕜]
    (L : Matrix (Fin n) (Fin n) 𝕜) (d y : Fin n → 𝕜) (α : 𝕜)
    (h : wellDefined L d y α) (j : Fin n) :
    barD L d y α j ≠ 0 := by
  -- The second component of `wellDefined` is exactly the nonvanishing denominator condition.
  have h' : L.IsUnitLowerTriangular ∧ ∀ i : Fin n, barD L d y α i ≠ 0 := by
    simpa [wellDefined] using h
  exact h'.2 j

/-- A unit lower-triangular matrix is invertible, so later solve identities can pass to the
canonical inverse solve without changing owners. -/
@[reducible] private noncomputable def invertibleOfUnitLowerTriangular {L : Hessian}
    (hL : L.IsUnitLowerTriangular) :
    Invertible L := by
  -- The determinant of a unit lower-triangular matrix is the product of its unit diagonal.
  have hUnit : IsUnit L := by
    refine L.isUnit_iff_isUnit_det.mpr ?_
    rw [det_of_lowerTriangular L hL.blockTriangular_toDual]
    simp [hL.apply_diag]
  exact hUnit.unit.invertible

/-- Helper for Chapter01 Algorithm 1.2.18: the initial `α` slot is never rewritten. -/
private theorem stateAt_alpha_zero
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    ∀ k : Nat, (stateAt L d y α k).alpha 0 = α
  | 0 => by
      -- The initial state stores `α` in slot `0`.
      simp [stateAt, init]
  | k + 1 => by
      by_cases hk : k < n
      · -- A genuine stage updates only a successor slot, never slot `0`.
        simp [stateAt, hk, step, stateAt_alpha_zero L d y α k]
      · -- After the final pivot, the recursive state is constant.
        simp [stateAt, hk, stateAt_alpha_zero L d y α k]

/-- Helper for Chapter01 Algorithm 1.2.18: the initial residual row `w^(1) = y` is never
rewritten. -/
private theorem stateAt_w_zero
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    ∀ k : Nat, (stateAt L d y α k).w 0 = y
  | 0 => by
      -- The initial state stores the source right-hand side in row `0`.
      simp [stateAt, init]
  | k + 1 => by
      by_cases hk : k < n
      · -- A genuine stage updates only the next row, never row `0`.
        simp [stateAt, hk, step, stateAt_w_zero L d y α k]
      · -- After the final pivot, the recursive state is constant.
        simp [stateAt, hk, stateAt_w_zero L d y α k]

/-- The algorithm starts from `α₁ = α`. -/
theorem alpha_zero (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    alpha L d y α 0 = α := by
  -- The public owner reads the terminal state.
  simpa [alpha] using stateAt_alpha_zero L d y α n

/-- The algorithm starts from `w^(1) = y`. -/
theorem w_zero (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    w L d y α 0 = y := by
  -- The public owner reads the terminal state.
  simpa [w] using stateAt_w_zero L d y α n

/-- Helper for Chapter01 Algorithm 1.2.18: `stateAt` at a genuine pivot stage is exactly one
`step` applied to the previous stage. -/
private theorem stateAtStepEq
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    stateAt L d y α (j.1 + 1) = step L d j (stateAt L d y α j.1) := by
  -- Unfolding the recursion at a stage strictly below `n` exposes the textbook step directly.
  simp [stateAt, j.is_lt]

/-- Helper for Chapter01 Algorithm 1.2.18: the residual after eliminating the first `k` pivots
from row `r`. -/
private def residualPrefix
    (L : Hessian) (y p : Fin n → 𝕜) (k : Nat) (hk : k ≤ n) (r : Fin n) : 𝕜 :=
  y r - ∑ i : Fin k, p (Fin.castLE hk i) * L r (Fin.castLE hk i)

/-- Helper for Chapter01 Algorithm 1.2.18: extending the eliminated prefix by one pivot subtracts
exactly the newly exposed lower-triangular term. -/
private theorem residualPrefix_succ
    (L : Hessian) (y p : Fin n → 𝕜) {k : Nat} (hk : k < n) (r : Fin n) :
    residualPrefix L y p (k + 1) (Nat.succ_le_of_lt hk) r =
      residualPrefix L y p k (Nat.le_of_lt hk) r - p ⟨k, hk⟩ * L r ⟨k, hk⟩ := by
  -- Splitting the `Fin (k + 1)` sum isolates the current pivot contribution.
  have hlast :
      Fin.castLE (Nat.succ_le_of_lt hk) (Fin.last k) = ⟨k, hk⟩ := by
    ext
    simp
  rw [residualPrefix, Fin.sum_univ_castSucc, residualPrefix]
  simp [hlast, sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Chapter01 Algorithm 1.2.18: once the sweep reaches row `j`, later stages never
rewrite that current row. -/
private theorem stateAtCurrentRowStable
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    ∀ l : Nat,
      (stateAt L d y α (j.1 + l)).w (Fin.castSucc j) =
        (stateAt L d y α j.1).w (Fin.castSucc j)
  | 0 => by
      -- At stage `j`, the current row is unchanged.
      rfl
  | l + 1 => by
      by_cases hstage : j.1 + l < n
      · have hstep :
            stateAt L d y α (j.1 + (l + 1)) =
              step L d ⟨j.1 + l, hstage⟩ (stateAt L d y α (j.1 + l)) := by
          -- Route correction: later stages rewrite only the successor row of the active pivot.
          have hadd : j.1 + (l + 1) = (j.1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hstep]
        ext r
        dsimp [step]
        let k : Fin n := ⟨j.1 + l, hstage⟩
        rw [Function.update_of_ne]
        · exact congrFun (stateAtCurrentRowStable L d y α j l) r
        · intro hEq
          have hjk : j ≤ k := by
            change j.1 ≤ k.1
            simp [k]
          have hlt : (Fin.castSucc j : Fin (n + 1)) < k.succ :=
            Fin.castSucc_lt_succ_iff.mpr hjk
          exact (ne_of_lt hlt) hEq
      · -- Once the stage counter reaches `n`, the recursive state stops changing.
        have hconst :
            stateAt L d y α (j.1 + (l + 1)) =
              stateAt L d y α (j.1 + l) := by
          have hadd : j.1 + (l + 1) = (j.1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hconst]
        exact stateAtCurrentRowStable L d y α j l

/-- Helper for Chapter01 Algorithm 1.2.18: once the sweep reaches stage `j`, later stages never
rewrite the current scalar slot `α_j`. -/
private theorem stateAtCurrentAlphaStable
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    ∀ l : Nat,
      (stateAt L d y α (j.1 + l)).alpha (Fin.castSucc j) =
        (stateAt L d y α j.1).alpha (Fin.castSucc j)
  | 0 => by
      -- At stage `j`, the current scalar slot is unchanged.
      rfl
  | l + 1 => by
      by_cases hstage : j.1 + l < n
      · have hstep :
            stateAt L d y α (j.1 + (l + 1)) =
              step L d ⟨j.1 + l, hstage⟩ (stateAt L d y α (j.1 + l)) := by
          -- A later pivot updates only its successor scalar slot.
          have hadd : j.1 + (l + 1) = (j.1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hstep]
        dsimp [step]
        let k : Fin n := ⟨j.1 + l, hstage⟩
        rw [Function.update_of_ne]
        · exact stateAtCurrentAlphaStable L d y α j l
        · intro hEq
          have hjk : j ≤ k := by
            change j.1 ≤ k.1
            simp [k]
          have hlt : (Fin.castSucc j : Fin (n + 1)) < k.succ :=
            Fin.castSucc_lt_succ_iff.mpr hjk
          exact (ne_of_lt hlt) hEq
      · -- After the final pivot, the recursive state is constant.
        have hconst :
            stateAt L d y α (j.1 + (l + 1)) =
              stateAt L d y α (j.1 + l) := by
          have hadd : j.1 + (l + 1) = (j.1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hconst]
        exact stateAtCurrentAlphaStable L d y α j l

/-- Helper for Chapter01 Algorithm 1.2.18: stage `j + 1` writes the new scalar `α_(j+1)` exactly
as in the textbook recurrence. -/
private theorem stateAtWriteNextAlpha
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    (stateAt L d y α (j.1 + 1)).alpha j.succ =
      d j * (stateAt L d y α j.1).alpha (Fin.castSucc j) /
        (stateAt L d y α (j.1 + 1)).barD j := by
  -- Unfolding the pivot stage exposes the displayed scalar update directly.
  rw [stateAtStepEq]
  simp [step]

/-- Helper for Chapter01 Algorithm 1.2.18: stage `j + 1` writes the updated diagonal entry exactly
as in the textbook recurrence. -/
private theorem stateAtWriteBarD
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    (stateAt L d y α (j.1 + 1)).barD j =
      d j + (stateAt L d y α j.1).alpha (Fin.castSucc j) *
        ((stateAt L d y α j.1).w (Fin.castSucc j) j) ^ 2 := by
  -- Unfolding the pivot stage exposes the diagonal update directly.
  rw [stateAtStepEq]
  simp [step]

/-- Helper for Chapter01 Algorithm 1.2.18: stage `j + 1` writes the coefficient `β_j` exactly as
in the textbook recurrence. -/
private theorem stateAtWriteBeta
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    (stateAt L d y α (j.1 + 1)).beta j =
      (stateAt L d y α j.1).w (Fin.castSucc j) j *
        (stateAt L d y α j.1).alpha (Fin.castSucc j) /
        (stateAt L d y α (j.1 + 1)).barD j := by
  -- Unfolding the pivot stage exposes the coefficient update directly.
  rw [stateAtStepEq]
  simp [step]

/-- Helper for Chapter01 Algorithm 1.2.18: for a later column, stage `k + 1` writes the next row
entry by subtracting the pivot correction. -/
private theorem stepLaterColumn
    (L : Hessian) (d : Fin n → 𝕜) (k : Fin n) (state : State 𝕜 n)
    (r : Fin n) (hkr : k < r) :
    (step L d k state).w k.succ r =
      state.w (Fin.castSucc k) r - state.w (Fin.castSucc k) k * L r k := by
  -- The strict-lower branch of `nextW` is the only one active at a later column.
  simp [step, hkr]

/-- Helper for Chapter01 Algorithm 1.2.18: stage `j + 1` writes the strict-lower factor entry by
the displayed `β_j w_r^(j+1)` correction. -/
private theorem stateAtWriteBarLEntry
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (r j : Fin n) (hjr : j < r) :
    (stateAt L d y α (j.1 + 1)).barL r j =
      L r j +
        (stateAt L d y α (j.1 + 1)).beta j *
          (stateAt L d y α (j.1 + 1)).w j.succ r := by
  -- The strict-lower branch of `nextBarL` is the one written at pivot `j`.
  rw [stateAtStepEq]
  simp [step, hjr]

/-- Helper for Chapter01 Algorithm 1.2.18: after stage `j + 1`, the new scalar slot `α_(j+1)` is
final and never changes again. -/
private theorem stateAtProcessedAlphaStable
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    ∀ l : Nat,
      (stateAt L d y α (j.1 + 1 + l)).alpha j.succ =
        (stateAt L d y α (j.1 + 1)).alpha j.succ
  | 0 => by
      rfl
  | l + 1 => by
      by_cases hstage : j.1 + 1 + l < n
      · have hstep :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              step L d ⟨j.1 + 1 + l, hstage⟩ (stateAt L d y α (j.1 + 1 + l)) := by
          -- Later pivots write only strictly later successor slots.
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hstep]
        dsimp [step]
        let k : Fin n := ⟨j.1 + 1 + l, hstage⟩
        rw [Function.update_of_ne]
        · exact stateAtProcessedAlphaStable L d y α j l
        · intro hEq
          have hjk : j < k := by
            change j.1 < k.1
            simp [k]
            omega
          have hlt : j.succ < k.succ := Fin.succ_lt_succ_iff.mpr hjk
          exact (ne_of_lt hlt) hEq
      · -- After the final pivot, the recursive state is constant.
        have hconst :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              stateAt L d y α (j.1 + 1 + l) := by
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hconst]
        exact stateAtProcessedAlphaStable L d y α j l

/-- Helper for Chapter01 Algorithm 1.2.18: after stage `j + 1`, the updated diagonal entry
`barD_j` is final and never changes again. -/
private theorem stateAtProcessedBarDStable
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    ∀ l : Nat,
      (stateAt L d y α (j.1 + 1 + l)).barD j =
        (stateAt L d y α (j.1 + 1)).barD j
  | 0 => by
      rfl
  | l + 1 => by
      by_cases hstage : j.1 + 1 + l < n
      · have hstep :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              step L d ⟨j.1 + 1 + l, hstage⟩ (stateAt L d y α (j.1 + 1 + l)) := by
          -- Later pivots rewrite only later diagonal slots.
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hstep]
        dsimp [step]
        let k : Fin n := ⟨j.1 + 1 + l, hstage⟩
        rw [Function.update_of_ne]
        · exact stateAtProcessedBarDStable L d y α j l
        · intro hEq
          have hjk : j < k := by
            change j.1 < k.1
            simp [k]
            omega
          exact (ne_of_lt hjk) hEq
      · -- After the final pivot, the recursive state is constant.
        have hconst :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              stateAt L d y α (j.1 + 1 + l) := by
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hconst]
        exact stateAtProcessedBarDStable L d y α j l

/-- Helper for Chapter01 Algorithm 1.2.18: after stage `j + 1`, the coefficient `β_j` is final
and never changes again. -/
private theorem stateAtProcessedBetaStable
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    ∀ l : Nat,
      (stateAt L d y α (j.1 + 1 + l)).beta j =
        (stateAt L d y α (j.1 + 1)).beta j
  | 0 => by
      rfl
  | l + 1 => by
      by_cases hstage : j.1 + 1 + l < n
      · have hstep :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              step L d ⟨j.1 + 1 + l, hstage⟩ (stateAt L d y α (j.1 + 1 + l)) := by
          -- Later pivots rewrite only later coefficient slots.
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hstep]
        dsimp [step]
        let k : Fin n := ⟨j.1 + 1 + l, hstage⟩
        rw [Function.update_of_ne]
        · exact stateAtProcessedBetaStable L d y α j l
        · intro hEq
          have hjk : j < k := by
            change j.1 < k.1
            simp [k]
            omega
          exact (ne_of_lt hjk) hEq
      · -- After the final pivot, the recursive state is constant.
        have hconst :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              stateAt L d y α (j.1 + 1 + l) := by
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hconst]
        exact stateAtProcessedBetaStable L d y α j l

/-- Helper for Chapter01 Algorithm 1.2.18: after stage `j + 1`, the newly written row
`w^(j+1)` is final and never changes again. -/
private theorem stateAtNextRowStable
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (j : Fin n) :
    ∀ l : Nat,
      (stateAt L d y α (j.1 + 1 + l)).w j.succ =
        (stateAt L d y α (j.1 + 1)).w j.succ
  | 0 => by
      rfl
  | l + 1 => by
      by_cases hstage : j.1 + 1 + l < n
      · have hstep :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              step L d ⟨j.1 + 1 + l, hstage⟩ (stateAt L d y α (j.1 + 1 + l)) := by
          -- Later pivots rewrite only strictly later rows.
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hstep]
        ext r
        dsimp [step]
        let k : Fin n := ⟨j.1 + 1 + l, hstage⟩
        rw [Function.update_of_ne]
        · exact congrFun (stateAtNextRowStable L d y α j l) r
        · intro hEq
          have hjk : j < k := by
            change j.1 < k.1
            simp [k]
            omega
          have hlt : j.succ < k.succ := Fin.succ_lt_succ_iff.mpr hjk
          exact (ne_of_lt hlt) hEq
      · -- After the final pivot, the recursive state is constant.
        have hconst :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              stateAt L d y α (j.1 + 1 + l) := by
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hconst]
        exact stateAtNextRowStable L d y α j l

/-- Helper for Chapter01 Algorithm 1.2.18: after stage `j + 1`, later pivots do not revisit the
strict-lower entry `(r, j)` that was written at pivot `j`. -/
private theorem stateAtProcessedBarLEntryStable
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (r j : Fin n) (hjr : j < r) :
    ∀ l : Nat,
      (stateAt L d y α (j.1 + 1 + l)).barL r j =
        (stateAt L d y α (j.1 + 1)).barL r j
  | 0 => by
      rfl
  | l + 1 => by
      by_cases hstage : j.1 + 1 + l < n
      · have hstep :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              step L d ⟨j.1 + 1 + l, hstage⟩ (stateAt L d y α (j.1 + 1 + l)) := by
          -- Later pivots write only later columns, never the already-processed column `j`.
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hstep]
        dsimp [step]
        let k : Fin n := ⟨j.1 + 1 + l, hstage⟩
        have hjk : j < k := by
          change j.1 < k.1
          simp [k]
          omega
        have hne : j ≠ k := ne_of_lt hjk
        simp [k, hjr, hne, stateAtProcessedBarLEntryStable L d y α r j hjr l]
      · -- After the final pivot, the recursive state is constant.
        have hconst :
            stateAt L d y α (j.1 + 1 + (l + 1)) =
              stateAt L d y α (j.1 + 1 + l) := by
          have hadd : j.1 + 1 + (l + 1) = (j.1 + 1 + l) + 1 := by omega
          rw [hadd]
          simp [stateAt, hstage]
        rw [hconst]
        exact stateAtProcessedBarLEntryStable L d y α r j hjr l

/-- Helper for Chapter01 Algorithm 1.2.18: the solve equation rewrites the current diagonal entry
as the unreduced residual tail. -/
private theorem unitLowerSolveEntry
    (L : Hessian) (y : Fin n → 𝕜)
    (hL : L.IsUnitLowerTriangular)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y)
    (j : Fin n) :
    p j = residualPrefix L y p j.1 (Nat.le_of_lt j.is_lt) j := by
  let f : ℕ → 𝕜 := fun i => if hi : i < n then L j ⟨i, hi⟩ * p ⟨i, hi⟩ else 0
  -- Read the `j`-th row of the solve equation and convert the finite-index sum to a nat-range sum.
  have hrow0 : (∑ x : Fin n, L j x * p x) = y j := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hp j
  have hsum : (∑ x : Fin n, L j x * p x) = Finset.sum (Finset.range n) f := by
    simpa [f] using
      (Fin.sum_univ_eq_sum_range
        (fun x : ℕ => if hx : x < n then L j ⟨x, hx⟩ * p ⟨x, hx⟩ else 0) n)
  rw [hsum] at hrow0
  -- Split the row sum at the diagonal pivot `j`, so the upper-triangular tail can be discarded.
  rw [← Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt), Finset.sum_range_add] at hrow0
  have htail : Finset.sum (Finset.range (n - (j.1 + 1))) (fun x => f (j.1 + 1 + x)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxrange : x < n - (j.1 + 1) := Finset.mem_range.mp hx
    have hxlt : j.1 + 1 + x < n := by
      omega
    have hjx : j < ⟨j.1 + 1 + x, hxlt⟩ := by
      change j.1 < j.1 + 1 + x
      omega
    simp [f, hxlt, hL.apply_eq_zero hjx]
  let g0 : ℕ → 𝕜 := fun x =>
    if hx : x < j.1 then
      p (Fin.castLE (Nat.le_of_lt j.is_lt) ⟨x, hx⟩) *
        L j (Fin.castLE (Nat.le_of_lt j.is_lt) ⟨x, hx⟩)
    else 0
  -- Rewrite the strict prefix of the row sum into the residual-prefix owner.
  have hbase :
      (∑ i : Fin j.1, p (Fin.castLE (Nat.le_of_lt j.is_lt) i) * L j (Fin.castLE (Nat.le_of_lt j.is_lt) i)) =
        Finset.sum (Finset.range j.1) g0 := by
    simpa [g0] using
      (Fin.sum_univ_eq_sum_range
        (fun x : ℕ =>
          if hx : x < j.1 then
            p (Fin.castLE (Nat.le_of_lt j.is_lt) ⟨x, hx⟩) *
              L j (Fin.castLE (Nat.le_of_lt j.is_lt) ⟨x, hx⟩)
          else 0)
        j.1)
  have hprefixBase : Finset.sum (Finset.range j.1) f =
      ∑ i : Fin j.1, p (Fin.castLE (Nat.le_of_lt j.is_lt) i) * L j (Fin.castLE (Nat.le_of_lt j.is_lt) i) := by
    calc
      Finset.sum (Finset.range j.1) f = Finset.sum (Finset.range j.1) g0 := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxlt : x < j.1 := Finset.mem_range.mp hx
        have hxn : x < n := by
          omega
        simp [f, g0, hxlt, hxn, mul_comm]
      _ = ∑ i : Fin j.1, p (Fin.castLE (Nat.le_of_lt j.is_lt) i) * L j (Fin.castLE (Nat.le_of_lt j.is_lt) i) := by
        simpa [g0] using hbase.symm
  -- The diagonal term contributes exactly `p j` because unit-lower matrices have `L j j = 1`.
  rw [Finset.sum_range_succ, htail, hprefixBase] at hrow0
  simp [j.is_lt, hL.apply_diag, mul_comm, add_comm, add_left_comm] at hrow0
  have hrow : p j +
      ∑ i : Fin j.1, p (Fin.castLE (Nat.le_of_lt j.is_lt) i) * L j (Fin.castLE (Nat.le_of_lt j.is_lt) i) =
        y j := by
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hrow0
  exact eq_sub_iff_add_eq.mpr (by simpa [residualPrefix, add_comm, add_left_comm, add_assoc] using hrow)

/-- Helper for Chapter01 Algorithm 1.2.18: the terminal public rows already satisfy the textbook
residual recurrence, so `w_diag` no longer needs a staged `stateAt` transport theorem. -/
private theorem w_step_self
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (j r : Fin n) (hjr : j < r) :
    w L d y α j.succ r =
      w L d y α (Fin.castSucc j) r - w L d y α (Fin.castSucc j) j * L r j := by
  -- The row written at stage `j + 1` is final, while the source row `w^(j)` was already stable.
  have hprocessed :
      (stateAt L d y α n).w j.succ r =
        (stateAt L d y α (j.1 + 1)).w j.succ r := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      congrFun (stateAtNextRowStable L d y α j (n - (j.1 + 1))) r
  have hcurrent :
      (stateAt L d y α n).w (Fin.castSucc j) r =
        (stateAt L d y α j.1).w (Fin.castSucc j) r := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      congrFun (stateAtCurrentRowStable L d y α j (n - j.1)) r
  have hcurrentDiag :
      (stateAt L d y α n).w (Fin.castSucc j) j =
        (stateAt L d y α j.1).w (Fin.castSucc j) j := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      congrFun (stateAtCurrentRowStable L d y α j (n - j.1)) j
  have hwrite :
      (stateAt L d y α (j.1 + 1)).w j.succ r =
        (stateAt L d y α j.1).w (Fin.castSucc j) r -
          (stateAt L d y α j.1).w (Fin.castSucc j) j * L r j := by
    -- Unfold the pivot stage and read the strict-lower `nextW` branch.
    rw [stateAtStepEq]
    exact stepLaterColumn L d j (stateAt L d y α j.1) r hjr
  calc
    w L d y α j.succ r
        = (stateAt L d y α (j.1 + 1)).w j.succ r := by
            simpa [w] using hprocessed
    _ = (stateAt L d y α j.1).w (Fin.castSucc j) r -
          (stateAt L d y α j.1).w (Fin.castSucc j) j * L r j := hwrite
    _ = w L d y α (Fin.castSucc j) r - w L d y α (Fin.castSucc j) j * L r j := by
          rw [← hcurrent, ← hcurrentDiag]
          rfl

/-- Helper for Chapter01 Algorithm 1.2.18: a vector whose entries equal the residual-prefix
diagonal solves the unit lower-triangular forward-substitution system. -/
private theorem unitLowerSolveResidualDiag
    (L : Hessian) (y p : Fin n → 𝕜)
    (hL : L.IsUnitLowerTriangular)
    (hp : ∀ j : Fin n, p j = residualPrefix L y p j.1 (Nat.le_of_lt j.is_lt) j) :
    L.mulVec p = y := by
  -- Read each row as a split lower-triangular sum and insert the residual formula at the pivot.
  ext j
  let f : ℕ → 𝕜 := fun i => if hi : i < n then L j ⟨i, hi⟩ * p ⟨i, hi⟩ else 0
  have hsum : (∑ x : Fin n, L j x * p x) = Finset.sum (Finset.range n) f := by
    simpa [f] using
      (Fin.sum_univ_eq_sum_range
        (fun x : ℕ => if hx : x < n then L j ⟨x, hx⟩ * p ⟨x, hx⟩ else 0) n)
  have htail : Finset.sum (Finset.range (n - (j.1 + 1))) (fun x => f (j.1 + 1 + x)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxrange : x < n - (j.1 + 1) := Finset.mem_range.mp hx
    have hxlt : j.1 + 1 + x < n := by
      omega
    have hjx : j < ⟨j.1 + 1 + x, hxlt⟩ := by
      change j.1 < j.1 + 1 + x
      omega
    simp [f, hxlt, hL.apply_eq_zero hjx]
  let g0 : ℕ → 𝕜 := fun x =>
    if hx : x < j.1 then
      p (Fin.castLE (Nat.le_of_lt j.is_lt) ⟨x, hx⟩) *
        L j (Fin.castLE (Nat.le_of_lt j.is_lt) ⟨x, hx⟩)
    else 0
  have hbase :
      (∑ i : Fin j.1, p (Fin.castLE (Nat.le_of_lt j.is_lt) i) * L j (Fin.castLE (Nat.le_of_lt j.is_lt) i)) =
        Finset.sum (Finset.range j.1) g0 := by
    simpa [g0] using
      (Fin.sum_univ_eq_sum_range
        (fun x : ℕ =>
          if hx : x < j.1 then
            p (Fin.castLE (Nat.le_of_lt j.is_lt) ⟨x, hx⟩) *
              L j (Fin.castLE (Nat.le_of_lt j.is_lt) ⟨x, hx⟩)
          else 0)
        j.1)
  have hprefixBase : Finset.sum (Finset.range j.1) f =
      ∑ i : Fin j.1, p (Fin.castLE (Nat.le_of_lt j.is_lt) i) * L j (Fin.castLE (Nat.le_of_lt j.is_lt) i) := by
    calc
      Finset.sum (Finset.range j.1) f = Finset.sum (Finset.range j.1) g0 := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxlt : x < j.1 := Finset.mem_range.mp hx
        have hxn : x < n := by
          omega
        simp [f, g0, hxlt, hxn, mul_comm]
      _ = ∑ i : Fin j.1, p (Fin.castLE (Nat.le_of_lt j.is_lt) i) * L j (Fin.castLE (Nat.le_of_lt j.is_lt) i) := by
        simpa [g0] using hbase.symm
  have hrow :
      p j +
        ∑ i : Fin j.1, p (Fin.castLE (Nat.le_of_lt j.is_lt) i) * L j (Fin.castLE (Nat.le_of_lt j.is_lt) i) =
          y j := by
    -- The residual-prefix formula contributes the diagonal term at row `j`.
    exact eq_sub_iff_add_eq.mp (hp j)
  have hsumRow : (∑ x : Fin n, L j x * p x) = y j := by
    rw [hsum]
    rw [← Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt), Finset.sum_range_add]
    rw [Finset.sum_range_succ, htail, hprefixBase]
    simpa [f, j.is_lt, hL.apply_diag, mul_comm, add_comm, add_left_comm, add_assoc] using hrow
  simpa [Matrix.mulVec, dotProduct] using hsumRow

/-- Helper for Chapter01 Algorithm 1.2.18: the diagonal entries of the public auxiliary rows form
the canonical solve vector for the unit lower-triangular system `L.mulVec q = y`. -/
private theorem diagonalAuxSolveEq
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (hL : L.IsUnitLowerTriangular) :
    let q : Fin n → 𝕜 := fun j => w L d y α (Fin.castSucc j) j
    L.mulVec q = y := by
  let q : Fin n → 𝕜 := fun j => w L d y α (Fin.castSucc j) j
  have hdiag :
      ∀ j : Fin n, q j = residualPrefix L y q j.1 (Nat.le_of_lt j.is_lt) j := by
    intro j
    have hcolumn :
        ∀ k : Nat, ∀ hk : k ≤ j.1,
          w L d y α ⟨k, Nat.lt_succ_of_lt (lt_of_le_of_lt hk j.is_lt)⟩ j =
            residualPrefix L y q k (Nat.le_trans hk (Nat.le_of_lt j.is_lt)) j := by
      intro k
      induction k with
      | zero =>
          intro hk
          -- The initial public row is exactly the source right-hand side.
          simpa [q, residualPrefix] using congrFun (w_zero L d y α) j
      | succ k ih =>
          intro hk
          have hkPrev : k ≤ j.1 := by
            omega
          have hkj : k < j.1 := by
            omega
          let kCol : Fin n := ⟨k, lt_trans hkj j.is_lt⟩
          have hkColLt : kCol < j := by
            change k < j.1
            exact hkj
          have hrowSucc :
              (⟨k + 1, Nat.lt_succ_of_lt (lt_of_le_of_lt hk j.is_lt)⟩ : Fin (n + 1)) =
                kCol.succ := by
            ext
            rfl
          have hrowCurr :
              (⟨k, Nat.lt_succ_of_lt (lt_of_le_of_lt hkPrev j.is_lt)⟩ : Fin (n + 1)) =
                Fin.castSucc kCol := by
            ext
            rfl
          calc
            w L d y α ⟨k + 1, Nat.lt_succ_of_lt (lt_of_le_of_lt hk j.is_lt)⟩ j
                = w L d y α kCol.succ j := by
                    rw [hrowSucc]
            _ = w L d y α (Fin.castSucc kCol) j -
                  w L d y α (Fin.castSucc kCol) kCol * L j kCol := by
                    exact w_step_self L d y α kCol j hkColLt
            _ = residualPrefix L y q k (Nat.le_trans hkPrev (Nat.le_of_lt j.is_lt)) j -
                  q kCol * L j kCol := by
                    have hkDiag :
                        w L d y α (Fin.castSucc kCol) kCol = q kCol := by
                      rfl
                    have hkDiagRow :
                        w L d y α ⟨k, Nat.lt_succ_of_lt (lt_of_le_of_lt hkPrev j.is_lt)⟩ kCol =
                          q kCol := by
                      simpa [hrowCurr] using hkDiag
                    rw [← hrowCurr, ih hkPrev, hkDiagRow]
            _ = residualPrefix L y q (k + 1) (Nat.le_trans hk (Nat.le_of_lt j.is_lt)) j := by
                    symm
                    simpa [kCol] using
                      residualPrefix_succ L y q (hk := lt_trans hkj j.is_lt) j
    -- Specializing the fixed-column recurrence at `k = j` identifies the diagonal term itself.
    have hdiagRow := hcolumn j.1 le_rfl
    have hrowDiag :
        (⟨j.1, Nat.lt_succ_of_lt j.is_lt⟩ : Fin (n + 1)) = Fin.castSucc j := by
      ext
      rfl
    rw [hrowDiag] at hdiagRow
    simpa [q] using hdiagRow
  -- Route correction: once the public diagonal vector satisfies the residual identity, the
  -- general forward-substitution bridge closes the solve equation without any `stateAt` transport.
  exact unitLowerSolveResidualDiag L y q hL hdiag

/-- If `p` solves the forward-substitution system `L.mulVec p = y`, then the diagonal auxiliary
entry records `p_j = w_j^(j)`. -/
-- Route correction: do not finish `stateAtActiveResidual` globally first. The next pass should
-- prove the fixed-column residual bridge inside this theorem, transport the terminal public row
-- back to stage `j` with `stateAtCurrentRowStable`, and close the last step by
-- `unitLowerSolveEntry`.
theorem w_diag
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (hL : L.IsUnitLowerTriangular)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y)
    (j : Fin n) :
    w L d y α (Fin.castSucc j) j = p j := by
  let q : Fin n → 𝕜 := fun i => w L d y α (Fin.castSucc i) i
  letI := invertibleOfUnitLowerTriangular hL
  have hq : L.mulVec q = y := by
    simpa [q] using diagonalAuxSolveEq L d y α hL
  have hqInv : q = L⁻¹ *ᵥ y := by
    -- Apply the inverse solve to the public diagonal vector.
    have h := congrArg (fun v => L⁻¹ *ᵥ v) hq
    simpa [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec] using h
  have hpInv : p = L⁻¹ *ᵥ y := by
    -- Apply the same inverse solve to the given forward-substitution solution.
    have h := congrArg (fun v => L⁻¹ *ᵥ v) hp
    simpa [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec] using h
  have hqp : q = p := hqInv.trans hpInv.symm
  -- The requested diagonal slot is exactly the `j`-th component of the public solve vector.
  exact congrFun hqp j

/-- If `L` is unit lower triangular and `p` solves `L.mulVec p = y`, then the updated diagonal
entry satisfies `barD_j = d_j + α_j p_j^2`. -/
theorem barD_apply
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (hL : L.IsUnitLowerTriangular)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y)
    (j : Fin n) :
    barD L d y α j = d j + alpha L d y α (Fin.castSucc j) * (p j) ^ 2 := by
  -- The public diagonal slot is the value written at stage `j + 1`, frozen afterwards.
  have hprocessed :
      (stateAt L d y α n).barD j =
        (stateAt L d y α (j.1 + 1)).barD j := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      stateAtProcessedBarDStable L d y α j (n - (j.1 + 1))
  -- The source scalar `α_j` and current row `w^(j)` are already stable before pivot `j`.
  have hcurrentAlpha :
      (stateAt L d y α n).alpha (Fin.castSucc j) =
        (stateAt L d y α j.1).alpha (Fin.castSucc j) := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      stateAtCurrentAlphaStable L d y α j (n - j.1)
  have hcurrentW :
      (stateAt L d y α n).w (Fin.castSucc j) j =
        (stateAt L d y α j.1).w (Fin.castSucc j) j := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      congrFun (stateAtCurrentRowStable L d y α j (n - j.1)) j
  have hwdiag : w L d y α (Fin.castSucc j) j = p j :=
    w_diag L d y α hL p hp j
  calc
    barD L d y α j
        = (stateAt L d y α (j.1 + 1)).barD j := by
            simpa [barD] using hprocessed
    _ = d j + (stateAt L d y α j.1).alpha (Fin.castSucc j) *
          ((stateAt L d y α j.1).w (Fin.castSucc j) j) ^ 2 := stateAtWriteBarD L d y α j
    _ = d j + alpha L d y α (Fin.castSucc j) * (w L d y α (Fin.castSucc j) j) ^ 2 := by
          rw [← hcurrentAlpha, ← hcurrentW]
          rfl
    _ = d j + alpha L d y α (Fin.castSucc j) * (p j) ^ 2 := by
          rw [hwdiag]

/-- If `L` is unit lower triangular and `p` solves `L.mulVec p = y`, then the step coefficient
satisfies `β_j = p_j α_j / barD_j`. -/
theorem beta_apply
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (hL : L.IsUnitLowerTriangular)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y)
    (j : Fin n) :
    beta L d y α j =
      p j * alpha L d y α (Fin.castSucc j) / barD L d y α j := by
  -- The public coefficient slot is exactly the value written at stage `j + 1`.
  have hprocessed :
      (stateAt L d y α n).beta j =
        (stateAt L d y α (j.1 + 1)).beta j := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      stateAtProcessedBetaStable L d y α j (n - (j.1 + 1))
  -- The numerator and denominator owners are both stable after the pivot write.
  have hcurrentAlpha :
      (stateAt L d y α n).alpha (Fin.castSucc j) =
        (stateAt L d y α j.1).alpha (Fin.castSucc j) := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      stateAtCurrentAlphaStable L d y α j (n - j.1)
  have hcurrentW :
      (stateAt L d y α n).w (Fin.castSucc j) j =
        (stateAt L d y α j.1).w (Fin.castSucc j) j := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      congrFun (stateAtCurrentRowStable L d y α j (n - j.1)) j
  have hbarD :
      (stateAt L d y α n).barD j =
        (stateAt L d y α (j.1 + 1)).barD j := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      stateAtProcessedBarDStable L d y α j (n - (j.1 + 1))
  have hwdiag : w L d y α (Fin.castSucc j) j = p j :=
    w_diag L d y α hL p hp j
  calc
    beta L d y α j
        = (stateAt L d y α (j.1 + 1)).beta j := by
            simpa [beta] using hprocessed
    _ = (stateAt L d y α j.1).w (Fin.castSucc j) j *
          (stateAt L d y α j.1).alpha (Fin.castSucc j) /
          (stateAt L d y α (j.1 + 1)).barD j := stateAtWriteBeta L d y α j
    _ = w L d y α (Fin.castSucc j) j * alpha L d y α (Fin.castSucc j) / barD L d y α j := by
          rw [← hcurrentW, ← hcurrentAlpha, ← hbarD]
          rfl
    _ = p j * alpha L d y α (Fin.castSucc j) / barD L d y α j := by
          simpa [w] using
            congrArg (fun z => z * alpha L d y α (Fin.castSucc j) / barD L d y α j)
              hwdiag

/-- The scalar recurrence satisfies `α_(j+1) = d_j α_j / barD_j`. -/
theorem alpha_step
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (j : Fin n) :
    alpha L d y α j.succ = d j * alpha L d y α (Fin.castSucc j) / barD L d y α j := by
  -- The successor slot is written at stage `j + 1` and then frozen for the rest of the sweep.
  have hprocessed :
      (stateAt L d y α n).alpha j.succ =
        (stateAt L d y α (j.1 + 1)).alpha j.succ := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      stateAtProcessedAlphaStable L d y α j (n - (j.1 + 1))
  -- The current scalar `α_j` is already stable before the pivot `j` is processed.
  have hcurrent :
      (stateAt L d y α n).alpha (Fin.castSucc j) =
        (stateAt L d y α j.1).alpha (Fin.castSucc j) := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      stateAtCurrentAlphaStable L d y α j (n - j.1)
  -- The denominator slot `barD_j` is also frozen immediately after stage `j + 1`.
  have hbarD :
      (stateAt L d y α n).barD j =
        (stateAt L d y α (j.1 + 1)).barD j := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      stateAtProcessedBarDStable L d y α j (n - (j.1 + 1))
  -- Route correction: use the exact stage write plus the two freeze lemmas instead of reopening
  -- a larger state-history theorem for the scalar owner.
  calc
    alpha L d y α j.succ
        = (stateAt L d y α (j.1 + 1)).alpha j.succ := by
            simpa [alpha] using hprocessed
    _ = d j * (stateAt L d y α j.1).alpha (Fin.castSucc j) /
          (stateAt L d y α (j.1 + 1)).barD j := stateAtWriteNextAlpha L d y α j
    _ = d j * alpha L d y α (Fin.castSucc j) / (stateAt L d y α n).barD j := by
          rw [← hcurrent, ← hbarD]
          rfl
    _ = d j * alpha L d y α (Fin.castSucc j) / barD L d y α j := by
          rfl

/-- If `L` is unit lower triangular and `p` solves `L.mulVec p = y`, then for `j < r` the
auxiliary vector satisfies `w_r^(j+1) = w_r^(j) - p_j l_rj`. -/
theorem w_step
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (hL : L.IsUnitLowerTriangular)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y)
    (r j : Fin n) (hjr : j < r) :
    w L d y α j.succ r = w L d y α (Fin.castSucc j) r - p j * L r j := by
  -- The row written at stage `j + 1` is final, while the source row `w^(j)` was already stable.
  have hprocessed :
      (stateAt L d y α n).w j.succ r =
        (stateAt L d y α (j.1 + 1)).w j.succ r := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      congrFun (stateAtNextRowStable L d y α j (n - (j.1 + 1))) r
  have hcurrent :
      (stateAt L d y α n).w (Fin.castSucc j) r =
        (stateAt L d y α j.1).w (Fin.castSucc j) r := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      congrFun (stateAtCurrentRowStable L d y α j (n - j.1)) r
  have hcurrentDiag :
      (stateAt L d y α n).w (Fin.castSucc j) j =
        (stateAt L d y α j.1).w (Fin.castSucc j) j := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)] using
      congrFun (stateAtCurrentRowStable L d y α j (n - j.1)) j
  have hwdiag : w L d y α (Fin.castSucc j) j = p j :=
    w_diag L d y α hL p hp j
  have hwrite :
      (stateAt L d y α (j.1 + 1)).w j.succ r =
        (stateAt L d y α j.1).w (Fin.castSucc j) r -
          (stateAt L d y α j.1).w (Fin.castSucc j) j * L r j := by
    rw [stateAtStepEq]
    exact stepLaterColumn L d j (stateAt L d y α j.1) r hjr
  calc
    w L d y α j.succ r
        = (stateAt L d y α (j.1 + 1)).w j.succ r := by
            simpa [w] using hprocessed
    _ = (stateAt L d y α j.1).w (Fin.castSucc j) r -
          (stateAt L d y α j.1).w (Fin.castSucc j) j * L r j := hwrite
    _ = w L d y α (Fin.castSucc j) r - w L d y α (Fin.castSucc j) j * L r j := by
          rw [← hcurrent, ← hcurrentDiag]
          rfl
    _ = w L d y α (Fin.castSucc j) r - p j * L r j := by
          simpa [w] using
            congrArg (fun z => w L d y α (Fin.castSucc j) r - z * L r j)
              hwdiag

/-- For `j < r`, the updated lower-factor entry satisfies `barl_rj = l_rj + β_j w_r^(j+1)`. -/
theorem barL_apply
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (r j : Fin n) (hjr : j < r) :
    barL L d y α r j = L r j + ((beta L d y α j) * w L d y α j.succ r : 𝕜) := by
  -- The strict-lower entry written at stage `j + 1` and its companion owners are frozen afterwards.
  have hprocessed :
      (stateAt L d y α n).barL r j =
        (stateAt L d y α (j.1 + 1)).barL r j := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      stateAtProcessedBarLEntryStable L d y α r j hjr (n - (j.1 + 1))
  have hbeta :
      (stateAt L d y α n).beta j =
        (stateAt L d y α (j.1 + 1)).beta j := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      stateAtProcessedBetaStable L d y α j (n - (j.1 + 1))
  have hw :
      (stateAt L d y α n).w j.succ r =
        (stateAt L d y α (j.1 + 1)).w j.succ r := by
    simpa [Nat.add_assoc, Nat.add_sub_of_le (Nat.succ_le_of_lt j.is_lt)] using
      congrFun (stateAtNextRowStable L d y α j (n - (j.1 + 1))) r
  calc
    barL L d y α r j
        = (stateAt L d y α (j.1 + 1)).barL r j := by
            simpa [barL] using hprocessed
    _ = L r j +
          (stateAt L d y α (j.1 + 1)).beta j *
            (stateAt L d y α (j.1 + 1)).w j.succ r := stateAtWriteBarLEntry L d y α r j hjr
    _ = L r j + ((beta L d y α j) * w L d y α j.succ r : 𝕜) := by
          rw [← hbeta, ← hw]
          rfl

/-- Helper for Chapter01 Algorithm 1.2.18: entries on or above the diagonal are never rewritten
by the lower-factor sweep. -/
private theorem stateAtBarLEntry_eq_of_not_lt
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (r j : Fin n) (hjr : ¬ j < r) :
    ∀ k : Nat, (stateAt L d y α k).barL r j = L r j
  | 0 => by
      -- The initial lower factor is exactly the source matrix `L`.
      simp [stateAt, init]
  | k + 1 => by
      by_cases hk : k < n
      · -- The strict-lower write condition is false here, so the entry stays unchanged.
        simp [stateAt, hk, step, hjr, stateAtBarLEntry_eq_of_not_lt L d y α r j hjr k]
      · -- After the last pivot the recursive state is constant.
        simp [stateAt, hk, stateAtBarLEntry_eq_of_not_lt L d y α r j hjr k]

/-- Helper for Chapter01 Algorithm 1.2.18: entries on or above the diagonal of `barL` still agree
with the original factor `L`. -/
private theorem barL_apply_of_not_lt
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (r j : Fin n) (hjr : ¬ j < r) :
    barL L d y α r j = L r j := by
  -- The final public factor is the terminal `stateAt` lower factor.
  simpa [barL] using stateAtBarLEntry_eq_of_not_lt L d y α r j hjr n

/-- Helper for Chapter01 Algorithm 1.2.18: the active residual vector at stage `k`, truncated to
the rows that have not yet been eliminated. -/
private def tailVector
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (k : Fin (n + 1)) : Fin n → 𝕜 :=
  fun r ↦ if k.1 ≤ r.1 then w L d y α k r else 0

/-- Helper for Chapter01 Algorithm 1.2.18: the mixed lower factor using updated columns before
stage `k` and the original factor afterwards. -/
private def sweepLower
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (k : Fin (n + 1)) : Hessian :=
  fun r c ↦ if c.1 < k.1 then barL L d y α r c else L r c

/-- Helper for Chapter01 Algorithm 1.2.18: the mixed diagonal owner using updated entries before
stage `k` and the original diagonal afterwards. -/
private def sweepDiagonal
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (k : Fin (n + 1)) : Fin n → 𝕜 :=
  fun c ↦ if c.1 < k.1 then barD L d y α c else d c

/-- Helper for Chapter01 Algorithm 1.2.18: the stagewise factorization matrix made from the
processed columns/diagonal together with the remaining rank-one residual term. -/
private def sweepMatrix
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) (k : Fin (n + 1)) : Hessian :=
  sweepLower L d y α k * diagonal (sweepDiagonal L d y α k) * transpose (sweepLower L d y α k) +
    alpha L d y α k • vecMulVec (tailVector L d y α k) (tailVector L d y α k)

/-- Helper for Chapter01 Algorithm 1.2.18: at stage `0` the truncated residual is exactly the
original vector `y`. -/
private theorem tailVector_zero
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    tailVector L d y α 0 = y := by
  -- Every row lies in the untouched tail at stage `0`.
  funext r
  simp [tailVector, w_zero]

/-- Helper for Chapter01 Algorithm 1.2.18: after the last pivot no row remains in the residual
tail. -/
private theorem tailVector_last
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    tailVector L d y α (Fin.last n) = 0 := by
  -- No `Fin n` index can satisfy the impossible inequality `n ≤ r.1`.
  funext r
  simp [tailVector]

/-- Helper for Chapter01 Algorithm 1.2.18: before any pivot is processed the mixed lower factor is
the original factor `L`. -/
private theorem sweepLower_zero
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    sweepLower L d y α 0 = L := by
  -- No column index is strictly smaller than stage `0`.
  ext r c
  simp [sweepLower]

/-- Helper for Chapter01 Algorithm 1.2.18: after all pivots are processed the mixed lower factor
coincides with `barL`. -/
private theorem sweepLower_last
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    sweepLower L d y α (Fin.last n) = barL L d y α := by
  -- Every column index of `Fin n` is strictly below the terminal stage `n`.
  ext r c
  simp [sweepLower]

/-- Helper for Chapter01 Algorithm 1.2.18: before any pivot is processed the mixed diagonal is the
original diagonal `d`. -/
private theorem sweepDiagonal_zero
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    sweepDiagonal L d y α 0 = d := by
  -- No diagonal index is strictly smaller than stage `0`.
  funext c
  simp [sweepDiagonal]

/-- Helper for Chapter01 Algorithm 1.2.18: after all pivots are processed the mixed diagonal is
the updated diagonal `barD`. -/
private theorem sweepDiagonal_last
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    sweepDiagonal L d y α (Fin.last n) = barD L d y α := by
  -- Every diagonal slot of `Fin n` lies before the terminal stage `n`.
  funext c
  simp [sweepDiagonal]

/-- Helper for Chapter01 Algorithm 1.2.18: rows at or above the current pivot are already removed
from the next residual tail. -/
private theorem tailVector_succ_eq_zero_of_le
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (j r : Fin n) (hrj : r ≤ j) :
    tailVector L d y α j.succ r = 0 := by
  -- The successor stage starts strictly after row `j`.
  simp [tailVector]
  omega

/-- Helper for Chapter01 Algorithm 1.2.18: the current truncated residual splits into the pivot
column contribution plus the next truncated residual. -/
private theorem tailVectorDecompose
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (hL : L.IsUnitLowerTriangular)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y)
    (j : Fin n) :
    tailVector L d y α (Fin.castSucc j) =
      fun r ↦ p j * L r j + tailVector L d y α j.succ r := by
  -- Split by the row position relative to the current pivot `j`.
  funext r
  by_cases hrj : r < j
  · have hLzero : L r j = 0 := hL.apply_eq_zero hrj
    have htail : tailVector L d y α j.succ r = 0 := by
      exact tailVector_succ_eq_zero_of_le L d y α j r (le_of_lt hrj)
    have hcurr : ¬ (Fin.castSucc j).1 ≤ r.1 := by
      simpa using hrj.not_ge
    have hsucc : ¬ j.succ.1 ≤ r.1 := by
      intro hle
      exact hrj.not_ge (Nat.le_trans (Nat.le_succ j.1) hle)
    rw [tailVector, if_neg hcurr, tailVector, if_neg hsucc, hLzero]
    ring
  · by_cases hEq : r = j
    · subst r
      have hdiag : w L d y α (Fin.castSucc j) j = p j := w_diag L d y α hL p hp j
      have htail : tailVector L d y α j.succ j = 0 := by
        exact tailVector_succ_eq_zero_of_le L d y α j j le_rfl
      have hcurr : (Fin.castSucc j).1 ≤ j.1 := by simp
      have hsucc : ¬ j.succ.1 ≤ j.1 := by
        simpa using Nat.not_succ_le_self j.1
      rw [tailVector, if_pos hcurr, tailVector, if_neg hsucc, hdiag]
      simp [hL.apply_diag]
    · have hjr : j < r := lt_of_not_ge <| by
          intro hle
          exact hEq (le_antisymm hle (le_of_not_gt hrj))
      have hstep : w L d y α j.succ r =
          w L d y α (Fin.castSucc j) r - p j * L r j := by
        exact w_step L d y α hL p hp r j hjr
      have hsucc : j.succ.1 ≤ r.1 := by
        exact Nat.succ_le_of_lt hjr
      have hcurr : (Fin.castSucc j).1 ≤ r.1 := by
        exact le_of_lt hjr
      rw [tailVector, if_pos hcurr, tailVector, if_pos hsucc, hstep]
      ring

/-- Helper for Chapter01 Algorithm 1.2.18: the processed pivot column in the mixed lower factor
is `L` plus the `β_j` correction against the next residual tail. -/
private theorem sweepLowerSuccColumn
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (j : Fin n) :
    (fun r ↦ sweepLower L d y α j.succ r j) =
      fun r ↦ L r j + beta L d y α j * tailVector L d y α j.succ r := by
  -- Split by whether the row is strictly below the pivot or not.
  funext r
  by_cases hjr : j < r
  · have hbar : barL L d y α r j =
        L r j + beta L d y α j * w L d y α j.succ r := by
      simpa [mul_assoc] using barL_apply L d y α r j hjr
    have htail : j.succ.1 ≤ r.1 := by
      exact Nat.succ_le_of_lt hjr
    rw [sweepLower, if_pos (by simpa using j.is_lt), hbar, tailVector, if_pos htail]
  · have hle : r ≤ j := le_of_not_gt hjr
    have hbar : barL L d y α r j = L r j := barL_apply_of_not_lt L d y α r j hjr
    have htail : tailVector L d y α j.succ r = 0 :=
      tailVector_succ_eq_zero_of_le L d y α j r hle
    rw [sweepLower, if_pos (by simpa using j.is_lt), hbar, htail]
    ring

/-- Helper for Chapter01 Algorithm 1.2.18: the pivot-local rank-one algebra closes after
substituting the textbook formulas for `barD_j`, `β_j`, and `α_(j+1)`. -/
private theorem pivotRankOneIdentity
    (u v : Fin n → 𝕜) (d α p β barD αNext : 𝕜)
    (hbarD : barD = d + α * p ^ 2)
    (hβ : β = p * α / barD)
    (hαNext : αNext = d * α / barD)
    (hbarD_ne : barD ≠ 0) :
    d • vecMulVec u u +
        α • vecMulVec (fun r ↦ p * u r + v r) (fun r ↦ p * u r + v r) =
      barD • vecMulVec (fun r ↦ u r + β * v r) (fun r ↦ u r + β * v r) +
        αNext • vecMulVec v v := by
  -- Compare both rank-one updates entrywise and clear the common denominator `barD`.
  subst barD
  subst β
  subst αNext
  ext r c
  simp [Matrix.vecMulVec]
  field_simp [hbarD_ne]
  ring

/-- Helper for Chapter01 Algorithm 1.2.18: away from the active pivot column, the mixed lower
factor is unchanged when the stage advances from `j` to `j + 1`. -/
private theorem sweepLower_succ_eq_castSucc_of_ne
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (j x : Fin n) (r : Fin n) (hx : x ≠ j) :
    sweepLower L d y α j.succ r x = sweepLower L d y α (Fin.castSucc j) r x := by
  -- Away from the pivot column, the successor cutoff `x ≤ j` is the same as `x < j`.
  have hcut : x ≤ j ↔ x < j := by
    constructor
    · intro hle
      exact lt_of_le_of_ne hle hx
    · intro hlt
      exact le_of_lt hlt
  simp [sweepLower, hcut]

/-- Helper for Chapter01 Algorithm 1.2.18: away from the active pivot index, the mixed diagonal is
unchanged when the stage advances from `j` to `j + 1`. -/
private theorem sweepDiagonal_succ_eq_castSucc_of_ne
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (j x : Fin n) (hx : x ≠ j) :
    sweepDiagonal L d y α j.succ x = sweepDiagonal L d y α (Fin.castSucc j) x := by
  -- Away from the pivot slot, the successor cutoff `x ≤ j` is the same as `x < j`.
  have hcut : x ≤ j ↔ x < j := by
    constructor
    · intro hle
      exact lt_of_le_of_ne hle hx
    · intro hlt
      exact le_of_lt hlt
  simp [sweepDiagonal, hcut]

/-- Helper for Chapter01 Algorithm 1.2.18: the mixed factor matrix is the sum of its column
rank-one contributions. -/
private theorem sweepFactorColumnSum
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (k : Fin (n + 1)) :
    sweepLower L d y α k * diagonal (sweepDiagonal L d y α k) * transpose (sweepLower L d y α k) =
      ∑ x : Fin n,
        sweepDiagonal L d y α k x •
          vecMulVec (fun r ↦ sweepLower L d y α k r x)
            (fun r ↦ sweepLower L d y α k r x) := by
  -- Compare entries and collapse the diagonal factor in the middle.
  ext r c
  rw [Matrix.mul_assoc]
  calc
    (sweepLower L d y α k * (diagonal (sweepDiagonal L d y α k) * transpose (sweepLower L d y α k)))
        r c
        = ∑ x : Fin n,
            sweepLower L d y α k r x *
              ((diagonal (sweepDiagonal L d y α k) * transpose (sweepLower L d y α k)) x c) := by
            simp [Matrix.mul_apply]
    _ = ∑ x : Fin n,
          sweepDiagonal L d y α k x *
            (sweepLower L d y α k r x * sweepLower L d y α k c x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          calc
            sweepLower L d y α k r x *
                ((diagonal (sweepDiagonal L d y α k) * transpose (sweepLower L d y α k)) x c)
                = sweepLower L d y α k r x *
                    (sweepDiagonal L d y α k x * sweepLower L d y α k c x) := by
                      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
            _ = sweepDiagonal L d y α k x *
                  (sweepLower L d y α k r x * sweepLower L d y α k c x) := by
                    ring
    _ = ∑ x : Fin n,
          (sweepDiagonal L d y α k x •
            vecMulVec (fun r ↦ sweepLower L d y α k r x)
              (fun r ↦ sweepLower L d y α k r x)) r c := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [Matrix.vecMulVec, mul_left_comm, mul_assoc]
    _ = ((∑ x : Fin n,
          sweepDiagonal L d y α k x •
            vecMulVec (fun r ↦ sweepLower L d y α k r x)
              (fun r ↦ sweepLower L d y α k r x)) r) c := by
          rw [Matrix.sum_apply r c Finset.univ]

/-- Helper for Chapter01 Algorithm 1.2.18: away from the pivot, the full column contribution is
unchanged when the sweep advances one stage. -/
private theorem sweepColumnTerm_succ_eq_castSucc_of_ne
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (j x : Fin n) (hx : x ≠ j) :
    sweepDiagonal L d y α j.succ x •
        vecMulVec (fun r ↦ sweepLower L d y α j.succ r x)
          (fun r ↦ sweepLower L d y α j.succ r x) =
      sweepDiagonal L d y α (Fin.castSucc j) x •
        vecMulVec (fun r ↦ sweepLower L d y α (Fin.castSucc j) r x)
          (fun r ↦ sweepLower L d y α (Fin.castSucc j) r x) := by
  -- Rewrite the scalar owner and the entire column vector together.
  have hcolumn :
      (fun r ↦ sweepLower L d y α j.succ r x) =
        fun r ↦ sweepLower L d y α (Fin.castSucc j) r x := by
    funext r
    exact sweepLower_succ_eq_castSucc_of_ne L d y α j x r hx
  rw [sweepDiagonal_succ_eq_castSucc_of_ne L d y α j x hx, hcolumn]

/-- Helper for Chapter01 Algorithm 1.2.18: the changing pivot column together with the residual
rank-one term satisfies the one-step rank-one identity. -/
private theorem pivotColumnResidualStep
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (h : wellDefined L d y α)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y)
    (j : Fin n) :
    sweepDiagonal L d y α j.succ j •
        vecMulVec (fun r ↦ sweepLower L d y α j.succ r j)
          (fun r ↦ sweepLower L d y α j.succ r j) +
      alpha L d y α j.succ •
        vecMulVec (tailVector L d y α j.succ) (tailVector L d y α j.succ) =
    sweepDiagonal L d y α (Fin.castSucc j) j •
        vecMulVec (fun r ↦ sweepLower L d y α (Fin.castSucc j) r j)
          (fun r ↦ sweepLower L d y α (Fin.castSucc j) r j) +
      alpha L d y α (Fin.castSucc j) •
        vecMulVec (tailVector L d y α (Fin.castSucc j))
          (tailVector L d y α (Fin.castSucc j)) := by
  let u : Fin n → 𝕜 := fun r ↦ L r j
  let v : Fin n → 𝕜 := tailVector L d y α j.succ
  have hL : L.IsUnitLowerTriangular := wellDefined_unitLowerTriangular L d y α h
  have hbarD_ne : barD L d y α j ≠ 0 := wellDefined_barD_ne_zero L d y α h j
  have htail :
      tailVector L d y α (Fin.castSucc j) =
        fun r ↦ p j * u r + v r := by
    -- The current residual splits into the pivot contribution plus the next tail.
    simpa [u, v] using tailVectorDecompose L d y α hL p hp j
  have hcolumn :
      (fun r ↦ sweepLower L d y α j.succ r j) =
        fun r ↦ u r + beta L d y α j * v r := by
    -- The processed pivot column is `L` plus the `β_j` correction against the next tail.
    simpa [u, v] using sweepLowerSuccColumn L d y α j
  have hcolumnCast :
      (fun r ↦ sweepLower L d y α (Fin.castSucc j) r j) = u := by
    -- Before the pivot is processed, the mixed factor still uses the original column `L(_, j)`.
    funext r
    simp [sweepLower, u]
  have hdiagSucc : sweepDiagonal L d y α j.succ j = barD L d y α j := by
    -- Stage `j + 1` has already committed the pivot diagonal entry.
    simp [sweepDiagonal]
  have hdiagCast : sweepDiagonal L d y α (Fin.castSucc j) j = d j := by
    -- Stage `j` still sees the original diagonal entry at the pivot slot.
    simp [sweepDiagonal]
  have hbarD :
      barD L d y α j = d j + alpha L d y α (Fin.castSucc j) * (p j) ^ 2 :=
    barD_apply L d y α hL p hp j
  have hβ :
      beta L d y α j = p j * alpha L d y α (Fin.castSucc j) / barD L d y α j :=
    beta_apply L d y α hL p hp j
  have hαNext :
      alpha L d y α j.succ = d j * alpha L d y α (Fin.castSucc j) / barD L d y α j :=
    alpha_step L d y α j
  -- Route correction: normalize the two stage-specific expressions to the generic pivot identity.
  rw [hdiagSucc, hdiagCast, hcolumn, hcolumnCast, htail]
  simpa [u, v] using
    (pivotRankOneIdentity u v (d j) (alpha L d y α (Fin.castSucc j)) (p j)
      (beta L d y α j) (barD L d y α j) (alpha L d y α j.succ)
      hbarD hβ hαNext hbarD_ne).symm

/-- Helper for Chapter01 Algorithm 1.2.18: stage `0` already matches the original rank-one update
matrix. -/
private theorem sweepMatrix_zero
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    sweepMatrix L d y α 0 =
      L * diagonal d * transpose L + α • vecMulVec y y := by
  -- At stage `0` all factor owners are still the original ones.
  rw [sweepMatrix, sweepLower_zero, sweepDiagonal_zero, alpha_zero, tailVector_zero]

/-- Helper for Chapter01 Algorithm 1.2.18: after the last pivot the residual rank-one term
vanishes, leaving the final factorization matrix. -/
private theorem sweepMatrix_last
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜) :
    sweepMatrix L d y α (Fin.last n) =
      ((barL L d y α : Hessian) * diagonal (barD L d y α) * transpose (barL L d y α) : Hessian) := by
  -- The terminal tail vector is zero, so only the factor part remains.
  rw [sweepMatrix, sweepLower_last, sweepDiagonal_last, tailVector_last]
  ext r c
  simp [Matrix.vecMulVec]

/-- Helper for Chapter01 Algorithm 1.2.18: one pivot step preserves the mixed sweep invariant. -/
private theorem sweepMatrixSucc
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (h : wellDefined L d y α)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y)
    (j : Fin n) :
    sweepMatrix L d y α j.succ = sweepMatrix L d y α (Fin.castSucc j) := by
  let columnTerm : Fin (n + 1) → Fin n → Hessian := fun k x ↦
    sweepDiagonal L d y α k x •
      vecMulVec (fun r ↦ sweepLower L d y α k r x)
        (fun r ↦ sweepLower L d y α k r x)
  let s : Finset (Fin n) := Finset.erase Finset.univ j
  have hsum :
      Finset.sum s (fun x ↦ columnTerm j.succ x) =
        Finset.sum s (fun x ↦ columnTerm (Fin.castSucc j) x) := by
    -- Every non-pivot column term is literally unchanged across the stage transition.
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact sweepColumnTerm_succ_eq_castSucc_of_ne L d y α j x (Finset.mem_erase.mp hx).1
  have hpivot :
      columnTerm j.succ j +
          alpha L d y α j.succ •
            vecMulVec (tailVector L d y α j.succ) (tailVector L d y α j.succ) =
        columnTerm (Fin.castSucc j) j +
          alpha L d y α (Fin.castSucc j) •
            vecMulVec (tailVector L d y α (Fin.castSucc j))
              (tailVector L d y α (Fin.castSucc j)) := by
    -- The pivot column and the residual term are exactly the dedicated rank-one update step.
    simpa [columnTerm] using pivotColumnResidualStep L d y α h p hp j
  -- Rewrite both factor parts into total column sums, split once at the pivot, and finish with the
  -- dedicated non-pivot and pivot identities.
  rw [sweepMatrix, sweepMatrix, sweepFactorColumnSum, sweepFactorColumnSum]
  change
      (∑ x : Fin n, columnTerm j.succ x) +
          alpha L d y α j.succ •
            vecMulVec (tailVector L d y α j.succ) (tailVector L d y α j.succ) =
        (∑ x : Fin n, columnTerm (Fin.castSucc j) x) +
          alpha L d y α (Fin.castSucc j) •
            vecMulVec (tailVector L d y α (Fin.castSucc j))
              (tailVector L d y α (Fin.castSucc j))
  have hsplitSucc :
      (∑ x : Fin n, columnTerm j.succ x) =
        columnTerm j.succ j + Finset.sum s (fun x ↦ columnTerm j.succ x) := by
    -- Isolate the pivot column from the total column sum.
    symm
    simpa [s] using
      (Finset.univ.add_sum_erase (fun x : Fin n ↦ columnTerm j.succ x) (Finset.mem_univ j))
  have hsplitCast :
      (∑ x : Fin n, columnTerm (Fin.castSucc j) x) =
        columnTerm (Fin.castSucc j) j + Finset.sum s (fun x ↦ columnTerm (Fin.castSucc j) x) := by
    -- The same split holds at the previous stage.
    symm
    simpa [s] using
      (Finset.univ.add_sum_erase (fun x : Fin n ↦ columnTerm (Fin.castSucc j) x) (Finset.mem_univ j))
  rw [hsplitSucc, hsplitCast, hsum]
  simpa [add_assoc, add_left_comm, add_comm] using
    congrArg
      (fun M ↦ M + Finset.sum s (fun x ↦ columnTerm (Fin.castSucc j) x))
      hpivot

/-- Helper for Chapter01 Algorithm 1.2.18: iterating the one-step sweep invariant collapses every
processed stage to stage `0`. -/
private theorem sweepMatrix_stageEqZero
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (h : wellDefined L d y α)
    (p : Fin n → 𝕜) (hp : L.mulVec p = y) :
    ∀ k : Nat, (hk : k ≤ n) →
      sweepMatrix L d y α ⟨k, Nat.lt_succ_of_le hk⟩ = sweepMatrix L d y α 0 := by
  intro k hk
  induction k with
  | zero =>
      -- Stage `0` is the base point of the telescoping argument.
      rfl
  | succ k ih =>
      have hklt : k < n := by
        omega
      let j : Fin n := ⟨k, hklt⟩
      have hstep :
          sweepMatrix L d y α ⟨k + 1, Nat.lt_succ_of_le hk⟩ =
            sweepMatrix L d y α (Fin.castSucc j) := by
        -- The adjacent-stage invariant identifies stage `k + 1` with stage `k`.
        simpa [j] using sweepMatrixSucc L d y α h p hp j
      have hprev :
          sweepMatrix L d y α (Fin.castSucc j) = sweepMatrix L d y α 0 := by
        -- The induction hypothesis already collapsed all earlier stages to stage `0`.
        simpa [j] using ih (Nat.le_of_lt hklt)
      exact hstep.trans hprev

/-- Chapter01 Algorithm 1.2.18: Algorithm 1.2.18 produces factors of the rank-one update
`L * diagonal d * Lᵀ + α • vecMulVec y y`. Equivalently, if `B = L D Lᵀ`, then the output
`barL`, `barD` satisfies `barL * diagonal barD * barLᵀ = B + α y yᵀ`. -/
theorem barL_mul_diagonal_transpose_eq_rankOneUpdate
    (L : Hessian) (d y : Fin n → 𝕜) (α : 𝕜)
    (h : wellDefined L d y α) :
    ((barL L d y α : Hessian) * diagonal (barD L d y α) * transpose (barL L d y α) : Hessian) =
      L * diagonal d * transpose L + α • vecMulVec y y := by
  let q : Fin n → 𝕜 := fun j => w L d y α (Fin.castSucc j) j
  have hL : L.IsUnitLowerTriangular := wellDefined_unitLowerTriangular L d y α h
  have hq : L.mulVec q = y := by
    -- The diagonal auxiliary entries already solve the forward-substitution system.
    simpa [q] using diagonalAuxSolveEq L d y α hL
  have hlast :
      sweepMatrix L d y α (Fin.last n) = sweepMatrix L d y α 0 := by
    -- Telescoping all `n` pivot steps identifies the terminal stage with the initial stage.
    simpa [Fin.last] using sweepMatrix_stageEqZero L d y α h q hq n le_rfl
  calc
    ((barL L d y α : Hessian) * diagonal (barD L d y α) * transpose (barL L d y α) : Hessian)
        = sweepMatrix L d y α (Fin.last n) := by
            symm
            exact sweepMatrix_last L d y α
    _ = sweepMatrix L d y α 0 := hlast
    _ = L * diagonal d * transpose L + α • vecMulVec y y := sweepMatrix_zero L d y α

end

section

variable (L : Matrix (Fin n) (Fin n) 𝕜) (d y : Fin n → 𝕜) (α : 𝕜)

/-- The inverse-based solve is a derived bridge from the source-facing solve equation. -/
theorem w_diag_inv
    (hL : L.IsUnitLowerTriangular)
    (j : Fin n) :
    w L d y α (Fin.castSucc j) j = (L⁻¹ *ᵥ y) j := by
  letI := invertibleOfUnitLowerTriangular hL
  have hp : L.mulVec (L⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  simpa using RankOneCholeskyUpdate.w_diag L d y α hL (L⁻¹ *ᵥ y) hp j

/-- The inverse-based diagonal formula is a derived bridge from the source-facing solve
equation. -/
theorem barD_apply_inv
    (hL : L.IsUnitLowerTriangular)
    (j : Fin n) :
    barD L d y α j =
      d j + alpha L d y α (Fin.castSucc j) * ((L⁻¹ *ᵥ y) j) ^ 2 := by
  letI := invertibleOfUnitLowerTriangular hL
  have hp : L.mulVec (L⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  -- Specialize the source-facing diagonal formula to the canonical inverse solve.
  simpa using RankOneCholeskyUpdate.barD_apply L d y α hL (L⁻¹ *ᵥ y) hp j

/-- The inverse-based coefficient formula is a derived bridge from the source-facing solve
equation. -/
theorem beta_apply_inv
    (hL : L.IsUnitLowerTriangular)
    (j : Fin n) :
    beta L d y α j =
      (L⁻¹ *ᵥ y) j * alpha L d y α (Fin.castSucc j) / barD L d y α j := by
  letI := invertibleOfUnitLowerTriangular hL
  have hp : L.mulVec (L⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  -- Specialize the source-facing coefficient formula to the canonical inverse solve.
  simpa using RankOneCholeskyUpdate.beta_apply L d y α hL (L⁻¹ *ᵥ y) hp j

/-- The inverse-based auxiliary-vector step is a derived bridge from the source-facing solve
equation. -/
theorem w_step_inv
    (hL : L.IsUnitLowerTriangular)
    (r j : Fin n) (hjr : j < r) :
    w L d y α j.succ r = w L d y α (Fin.castSucc j) r - (L⁻¹ *ᵥ y) j * L r j := by
  letI := invertibleOfUnitLowerTriangular hL
  have hp : L.mulVec (L⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hjr' : j < r := hjr
  simpa using RankOneCholeskyUpdate.w_step L d y α hL (L⁻¹ *ᵥ y) hp r j hjr'

end

end

end RankOneCholeskyUpdate
