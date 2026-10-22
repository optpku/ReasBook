/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OptimizationTheoryAndMethods_SunYuan_2006.Matrix.UnitLowerTriangular

noncomputable section

open Matrix
open scoped BigOperators

-- Domain sampling:
-- * `Mathlib.Analysis.Matrix.LDL` provides the ambient canonical `LDL` owner.
-- * `Matrix.IsUnitLowerTriangular` is the project owner for the unit-lower hypothesis on `L`,
--   and `Matrix.mulVec` is the canonical owner for the forward-substitution equation
--   `L.mulVec p = y`.
-- * `Matrix.inv_mulVec_eq_vec` and `Matrix.mulVec_mulVec` are the canonical bridge lemmas for
--   recovering the inverse-based solve from a source-facing solution equation when `L` is
--   invertible.
-- * `Algorithm_1_2_18` keeps its source-facing stagewise outputs over the textbook inputs while
--   leaving the iterative working state private.
-- Source/core/bridge triage:
-- * source-facing: the algorithm outputs `t`, `barD`, `beta`, `w`, and `barL` over
--   `(L, d, p, εM)`, where `p` is the solve vector from the first step `L.mulVec p = y`.
-- * core/canonical: `Matrix.mulVec`.
-- * bridge/view: under extra invertibility, one may recover the same solve vector as
--   `L⁻¹.mulVec y`, but that inverse formula is not the main public owner.

namespace NegativeRankOneCholeskyUpdate

section

variable {n : Nat}

local notation "Hessian" => Matrix (Fin n) (Fin n) ℝ

private structure ScalarState (n : Nat) where
  t : Fin (n + 1) → ℝ
  barD : Fin n → ℝ
  beta : Fin n → ℝ

private def initScalars (d p : Fin n → ℝ) (εM : ℝ) : ScalarState n where
  t :=
    Function.update
      (fun _ ↦ 0)
      (Fin.last n)
      (max εM (1 - Finset.sum Finset.univ (fun i : Fin n ↦ (p i) ^ 2 / d i)))
  barD := fun _ ↦ 0
  beta := fun _ ↦ 0

private def scalarStep (d p : Fin n → ℝ) (j : Fin n) (state : ScalarState n) : ScalarState n :=
  let tj := state.t j.succ + (p j) ^ 2 / d j
  let barDj := d j * state.t j.succ / tj
  let betaj := -(p j) / (d j * state.t j.succ)
  { t := Function.update state.t (Fin.castSucc j) tj
    barD := Function.update state.barD j barDj
    beta := Function.update state.beta j betaj }

/-- Running the scalar recurrences of Algorithm 1.2.19 for the first `k` backward steps. -/
private def scalarStateAt (d p : Fin n → ℝ) (εM : ℝ) : Nat → ScalarState n
  | 0 => initScalars d p εM
  | k + 1 =>
      if hk : k < n then
        scalarStep d p (Fin.rev ⟨k, hk⟩) (scalarStateAt d p εM k)
      else
        scalarStateAt d p εM k

/-- The scalar sequence `t_j` produced by Algorithm 1.2.19 from the solved vector `p`. -/
private def tFromP (d p : Fin n → ℝ) (εM : ℝ) : Fin (n + 1) → ℝ :=
  (scalarStateAt d p εM n).t

/-- The updated diagonal sequence `barD_j` produced by Algorithm 1.2.19 from the solved
vector `p`. -/
private def barDFromP (d p : Fin n → ℝ) (εM : ℝ) : Fin n → ℝ :=
  (scalarStateAt d p εM n).barD

/-- The coefficient sequence `β_j` produced by Algorithm 1.2.19 from the solved vector `p`. -/
private def betaFromP (d p : Fin n → ℝ) (εM : ℝ) : Fin n → ℝ :=
  (scalarStateAt d p εM n).beta

private structure WState (n : Nat) where
  w : Fin n → Fin n → ℝ

private def initW : WState n where
  w := fun _ _ ↦ 0

private def wStep
    (L : Hessian) (p : Fin n → ℝ) (j : Fin n)
    (state : WState n) : WState n :=
  let nextWj : Fin n → ℝ := fun r ↦
    if _ : r = j then
      p j
    else if hjr : j < r then
      let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
      state.w jNext r + p j * L r j
    else
      0
  { w := Function.update state.w j nextWj }

/-- Running the auxiliary-vector recurrences of Algorithm 1.2.19 for the first `k`
backward steps. -/
private def wStateAt
    (L : Hessian) (p : Fin n → ℝ) : Nat → WState n
  | 0 => initW
  | k + 1 =>
      if hk : k < n then
        wStep L p (Fin.rev ⟨k, hk⟩) (wStateAt L p k)
      else
        wStateAt L p k

/-- The auxiliary vectors `w_r^(j)` produced by Algorithm 1.2.19 from the solved vector `p`. -/
private def wFromP (L : Hessian) (p : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  (wStateAt L p n).w

/-- The updated lower factor `barL` produced by Algorithm 1.2.19 from the solved vector `p`. -/
private def barLFromP (L : Hessian) (d p : Fin n → ℝ) (εM : ℝ) :
    Hessian := fun r j ↦
  if hjr : j.1 < r.1 then
    let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
    L r j + betaFromP d p εM j * wFromP L p jNext r
  else
    L r j

/-- The scalar sequence `t_j` produced by Algorithm 1.2.19 from the solve vector `p`. -/
def t (d p : Fin n → ℝ) (εM : ℝ) : Fin (n + 1) → ℝ :=
  tFromP d p εM

/-- The updated diagonal sequence `barD_j` produced by Algorithm 1.2.19 from the solve vector
`p`. -/
def barD (d p : Fin n → ℝ) (εM : ℝ) : Fin n → ℝ :=
  barDFromP d p εM

/-- The coefficient sequence `β_j` produced by Algorithm 1.2.19 from the solve vector `p`. -/
def beta (d p : Fin n → ℝ) (εM : ℝ) : Fin n → ℝ :=
  betaFromP d p εM

/-- The auxiliary vectors `w_r^(j)` produced by Algorithm 1.2.19 from the solve vector `p`. -/
def w (L : Hessian) (p : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  wFromP L p

/-- The updated lower factor `barL` produced by Algorithm 1.2.19 from the solve vector `p`. -/
def barL (L : Hessian) (d p : Fin n → ℝ) (εM : ℝ) : Hessian :=
  barLFromP L d p εM

/-- The source-faithful well-definedness conditions for Algorithm 1.2.19: `L` is unit lower
triangular, the machine threshold `εM` is positive, the original diagonal entries are positive,
and the derived scalars `t_j` are positive, so every displayed division by `d_i` and `t_j` is
justified in the source LDL downdate setting. The solve equation `L.mulVec p = y` is bridge data
relating `p` to the textbook right-hand side; it is not primitive data of the recurrences. -/
def wellDefined
    (L : Hessian) (d p : Fin n → ℝ) (εM : ℝ) : Prop :=
  L.IsUnitLowerTriangular ∧
    0 < εM ∧
    (∀ i : Fin n, 0 < d i) ∧
    ∀ j : Fin (n + 1), 0 < t d p εM j

variable (L : Hessian) (d p : Fin n → ℝ) (εM : ℝ)

/-- Helper for Chapter01 Algorithm 1.2.19: the terminal scalar slot `t_(n+1)` is never
rewritten during the backward sweep. -/
private theorem scalarStateAt_last
    (d p : Fin n → ℝ) (εM : ℝ) :
    ∀ k : Nat,
      (scalarStateAt d p εM k).t (Fin.last n) =
        max εM (1 - Finset.sum Finset.univ (fun i : Fin n ↦ (p i) ^ 2 / d i))
  | 0 => by
      -- The initial state stores the floored source value exactly in the last slot.
      simp [scalarStateAt, initScalars]
  | k + 1 => by
      -- Each backward step rewrites only a predecessor slot, so the last slot persists.
      by_cases hk : k < n
      · have hstep :
            scalarStateAt d p εM (k + 1) =
              scalarStep d p (Fin.rev ⟨k, hk⟩) (scalarStateAt d p εM k) := by
          simp [scalarStateAt, hk]
        rw [hstep]
        dsimp [scalarStep]
        rw [Function.update_of_ne (Fin.castSucc_ne_last (Fin.rev ⟨k, hk⟩)).symm]
        exact scalarStateAt_last d p εM k
      · simp [scalarStateAt, hk, scalarStateAt_last d p εM k]

/-- Helper for Chapter01 Algorithm 1.2.19: stage `k + 1` writes the current backward pivot's
scalar data exactly as in the textbook recurrence. -/
private theorem scalarStateAt_write_rev
    (d p : Fin n → ℝ) (εM : ℝ) {k : Nat} (hk : k < n) {j : Fin n}
    (hj : Fin.rev ⟨k, hk⟩ = j) :
    (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) =
        (scalarStateAt d p εM k).t j.succ + (p j) ^ 2 / d j ∧
      (scalarStateAt d p εM (k + 1)).barD j =
        d j * (scalarStateAt d p εM k).t j.succ /
          (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) ∧
      (scalarStateAt d p εM (k + 1)).beta j =
        -(p j) / (d j * (scalarStateAt d p εM k).t j.succ) := by
  -- Unfolding one recursive step exposes the textbook formulas directly.
  subst hj
  simp [scalarStateAt, hk, scalarStep]

/-- Helper for Chapter01 Algorithm 1.2.19: once stage `k` processes pivot `j`, every later
stage from `k` onward processes a pivot at or below `j` in the reverse order. -/
private theorem rev_stage_le_processed
    {k l : Nat} (hk : k < n) {j : Fin n}
    (hj : Fin.rev ⟨k, hk⟩ = j) (hstage : k + l < n) :
    Fin.rev ⟨k + l, hstage⟩ ≤ j := by
  -- Reverse order turns the monotone stage counter into an antitone pivot order.
  subst hj
  have hkl : (⟨k, hk⟩ : Fin n) ≤ ⟨k + l, hstage⟩ := by
    change k ≤ k + l
    exact Nat.le_add_right k l
  exact Fin.rev_anti hkl

/-- Helper for Chapter01 Algorithm 1.2.19: once pivot `j` is written, every strictly later stage
processes a strictly smaller pivot in the reverse sweep. -/
private theorem rev_later_stage_lt_processed
    {k l : Nat} (hk : k < n) {j : Fin n}
    (hj : Fin.rev ⟨k, hk⟩ = j) (hstage : k + 1 + l < n) :
    Fin.rev ⟨k + 1 + l, hstage⟩ < j := by
  -- A later stage has a larger counter, so reverse order gives a smaller pivot.
  subst hj
  have hkl : (⟨k, hk⟩ : Fin n) < ⟨k + 1 + l, hstage⟩ := by
    change k < k + 1 + l
    omega
  simpa [Nat.add_assoc] using Fin.rev_strictAnti hkl

/-- Helper for Chapter01 Algorithm 1.2.19: once the sweep reaches index `j`, the successor slot
`t_(j+1)` is already final and never changes again. -/
private theorem scalarStateAt_succ_stable
    (d p : Fin n → ℝ) (εM : ℝ) {k : Nat} (hk : k < n) {j : Fin n}
    (hj : Fin.rev ⟨k, hk⟩ = j) :
    ∀ l : Nat,
      (scalarStateAt d p εM (k + l)).t j.succ =
        (scalarStateAt d p εM k).t j.succ
  | 0 => by
      rfl
  | l + 1 => by
      -- Later stages can only rewrite predecessor slots of `j.succ`, never `j.succ` itself.
      by_cases hstage : k + l < n
      · have hle : Fin.rev ⟨k + l, hstage⟩ ≤ j :=
          rev_stage_le_processed hk hj hstage
        have hlt : Fin.castSucc (Fin.rev ⟨k + l, hstage⟩) < j.succ := by
          exact Fin.castSucc_lt_succ_iff.mpr hle
        have hne : Fin.castSucc (Fin.rev ⟨k + l, hstage⟩) ≠ j.succ := ne_of_lt hlt
        have hstep :
            scalarStateAt d p εM (k + (l + 1)) =
              scalarStep d p (Fin.rev ⟨k + l, hstage⟩) (scalarStateAt d p εM (k + l)) := by
          have hadd : k + (l + 1) = (k + l) + 1 := by
            omega
          rw [hadd]
          simp [scalarStateAt, hstage]
        rw [hstep]
        dsimp [scalarStep]
        rw [Function.update_of_ne hne.symm]
        exact scalarStateAt_succ_stable d p εM hk hj l
      · -- Once the stage counter leaves `Fin n`, the recursion stops changing the state.
        have hconst :
            scalarStateAt d p εM (k + (l + 1)) =
              scalarStateAt d p εM (k + l) := by
          have hadd : k + (l + 1) = (k + l) + 1 := by
            omega
          rw [hadd]
          simp [scalarStateAt, hstage]
        rw [hconst]
        exact scalarStateAt_succ_stable d p εM hk hj l

/-- Helper for Chapter01 Algorithm 1.2.19: after row `j` is written, later backward stages leave
its scalar outputs unchanged. -/
private theorem scalarStateAt_processed_stable
    (d p : Fin n → ℝ) (εM : ℝ) {k : Nat} (hk : k < n) {j : Fin n}
    (hj : Fin.rev ⟨k, hk⟩ = j) :
    ∀ l : Nat,
      (scalarStateAt d p εM (k + 1 + l)).t (Fin.castSucc j) =
          (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) ∧
        (scalarStateAt d p εM (k + 1 + l)).barD j =
        (scalarStateAt d p εM (k + 1)).barD j ∧
      (scalarStateAt d p εM (k + 1 + l)).beta j =
          (scalarStateAt d p εM (k + 1)).beta j
  | 0 => by
      simp
  | l + 1 => by
      -- After stage `k + 1`, all later pivots are strictly smaller than `j`.
      by_cases hstage : k + 1 + l < n
      · have hlt : Fin.rev ⟨k + 1 + l, hstage⟩ < j :=
          rev_later_stage_lt_processed hk hj hstage
        have hltT : Fin.castSucc (Fin.rev ⟨k + 1 + l, hstage⟩) < Fin.castSucc j := by
          exact hlt
        have hneT : Fin.castSucc (Fin.rev ⟨k + 1 + l, hstage⟩) ≠ Fin.castSucc j :=
          ne_of_lt hltT
        have hne : Fin.rev ⟨k + 1 + l, hstage⟩ ≠ j := ne_of_lt hlt
        have hstep :
            scalarStateAt d p εM (k + 1 + (l + 1)) =
              scalarStep d p (Fin.rev ⟨k + 1 + l, hstage⟩) (scalarStateAt d p εM (k + 1 + l)) := by
          have hadd : k + 1 + (l + 1) = (k + 1 + l) + 1 := by
            omega
          rw [hadd]
          simp [scalarStateAt, hstage]
        rw [hstep]
        dsimp [scalarStep]
        constructor
        · rw [Function.update_of_ne hneT.symm]
          exact (scalarStateAt_processed_stable d p εM hk hj l).1
        · constructor
          · rw [Function.update_of_ne hne.symm]
            exact (scalarStateAt_processed_stable d p εM hk hj l).2.1
          · rw [Function.update_of_ne hne.symm]
            exact (scalarStateAt_processed_stable d p εM hk hj l).2.2
      · -- After the last genuine pivot, recursive calls are definitionally constant.
        have hconst :
            scalarStateAt d p εM (k + 1 + (l + 1)) =
              scalarStateAt d p εM (k + 1 + l) := by
          have hadd : k + 1 + (l + 1) = (k + 1 + l) + 1 := by
            omega
          rw [hadd]
          simp [scalarStateAt, hstage]
        rw [hconst]
        exact scalarStateAt_processed_stable d p εM hk hj l

/-- Helper for Chapter01 Algorithm 1.2.19: stage `k + 1` writes the current row of the auxiliary
state exactly as in the backward recurrence. -/
private theorem wStateAt_write_rev
    (L : Hessian) (p : Fin n → ℝ) {k : Nat} (hk : k < n) {j : Fin n}
    (hj : Fin.rev ⟨k, hk⟩ = j) :
    (wStateAt L p (k + 1)).w j j = p j ∧
      ∀ {r : Fin n} (hjr : j.1 < r.1),
        let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
        (wStateAt L p (k + 1)).w j r = (wStateAt L p k).w jNext r + p j * L r j := by
  -- Unfolding the unique row update exposes both the diagonal and off-diagonal formulas.
  subst j
  constructor
  · simp [wStateAt, hk, wStep]
  · intro r hjr
    have hrj : r ≠ Fin.rev ⟨k, hk⟩ := ne_of_gt hjr
    have hstep :
        wStateAt L p (k + 1) =
          wStep L p (Fin.rev ⟨k, hk⟩) (wStateAt L p k) := by
      simp [wStateAt, hk]
    rw [hstep]
    dsimp [wStep]
    rw [Function.update_self]
    split_ifs with hEq hlt
    · exact False.elim (hrj hEq)
    · rfl
    · exact False.elim (hlt hjr)

/-- Helper for Chapter01 Algorithm 1.2.19: after row `j` is written, later stages do not modify
that row of the auxiliary state. -/
private theorem wStateAt_processed_row_stable
    (L : Hessian) (p : Fin n → ℝ) {k : Nat} (hk : k < n) {j : Fin n}
    (hj : Fin.rev ⟨k, hk⟩ = j) (r : Fin n) :
    ∀ l : Nat,
      (wStateAt L p (k + 1 + l)).w j r =
        (wStateAt L p (k + 1)).w j r
  | 0 => by
      rfl
  | l + 1 => by
      -- Once row `j` is written, later stages update only strictly smaller rows.
      by_cases hstage : k + 1 + l < n
      · have hlt : Fin.rev ⟨k + 1 + l, hstage⟩ < j :=
          rev_later_stage_lt_processed hk hj hstage
        have hne : Fin.rev ⟨k + 1 + l, hstage⟩ ≠ j := ne_of_lt hlt
        have hstep :
            wStateAt L p (k + 1 + (l + 1)) =
              wStep L p (Fin.rev ⟨k + 1 + l, hstage⟩) (wStateAt L p (k + 1 + l)) := by
          have hadd : k + 1 + (l + 1) = (k + 1 + l) + 1 := by
            omega
          rw [hadd]
          simp [wStateAt, hstage]
        rw [hstep]
        dsimp [wStep]
        rw [Function.update_of_ne hne.symm]
        exact wStateAt_processed_row_stable L p hk hj r l
      · -- No further genuine stages means the row stays definitionally unchanged.
        have hconst :
            wStateAt L p (k + 1 + (l + 1)) =
              wStateAt L p (k + 1 + l) := by
          have hadd : k + 1 + (l + 1) = (k + 1 + l) + 1 := by
            omega
          rw [hadd]
          simp [wStateAt, hstage]
        rw [hconst]
        exact wStateAt_processed_row_stable L p hk hj r l

/-- Helper for Chapter01 Algorithm 1.2.19: any row strictly larger than the current pivot `j` is
already final at stage `(Fin.rev j).1`. -/
private theorem wStateAt_larger_row_stable
    (L : Hessian) (p : Fin n → ℝ) {k : Nat} (hk : k < n) {j i r : Fin n}
    (hj : Fin.rev ⟨k, hk⟩ = j) (hji : j < i) :
    ∀ l : Nat,
      (wStateAt L p (k + l)).w i r =
        (wStateAt L p k).w i r
  | 0 => by
      rfl
  | l + 1 => by
      -- Every stage from `k` onward rewrites a row at most `j`, so it misses any larger row.
      by_cases hstage : k + l < n
      · have hle : Fin.rev ⟨k + l, hstage⟩ ≤ j :=
          rev_stage_le_processed hk hj hstage
        have hlt : Fin.rev ⟨k + l, hstage⟩ < i := lt_of_le_of_lt hle hji
        have hne : Fin.rev ⟨k + l, hstage⟩ ≠ i := ne_of_lt hlt
        have hstep :
            wStateAt L p (k + (l + 1)) =
              wStep L p (Fin.rev ⟨k + l, hstage⟩) (wStateAt L p (k + l)) := by
          have hadd : k + (l + 1) = (k + l) + 1 := by
            omega
          rw [hadd]
          simp [wStateAt, hstage]
        rw [hstep]
        dsimp [wStep]
        rw [Function.update_of_ne hne.symm]
        exact wStateAt_larger_row_stable L p hk hj hji l
      · -- Beyond the last true stage the recursion is constant, so the larger row remains fixed.
        have hconst :
            wStateAt L p (k + (l + 1)) =
              wStateAt L p (k + l) := by
          have hadd : k + (l + 1) = (k + l) + 1 := by
            omega
          rw [hadd]
          simp [wStateAt, hstage]
        rw [hconst]
        exact wStateAt_larger_row_stable L p hk hj hji l

/-- The terminal scalar `t_(n+1)` is the floored value `max εM (1 - pᵀ D⁻¹ p)`. -/
theorem tLast_eq :
    t d p εM (Fin.last n) =
      max εM (1 - Finset.sum Finset.univ (fun i : Fin n ↦ (p i) ^ 2 / d i)) := by
  -- The public owner `t` is the terminal scalar state.
  simpa [t, tFromP] using scalarStateAt_last d p εM n

/-- The `t`-sequence satisfies the backward scalar update from the algorithm. -/
theorem tStep_eq
    (j : Fin n) :
    t d p εM (Fin.castSucc j) = t d p εM j.succ + (p j) ^ 2 / d j := by
  let k : Nat := (Fin.rev j).1
  have hk : k < n := (Fin.rev j).is_lt
  have hkLe : k ≤ n := Nat.le_of_lt hk
  have hkSuccLe : k + 1 ≤ n := Nat.succ_le_of_lt hk
  have hj : Fin.rev ⟨k, hk⟩ = j := by
    change Fin.rev (Fin.rev j) = j
    exact Fin.rev_rev j
  have hwrite :
      (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) =
        (scalarStateAt d p εM k).t j.succ + (p j) ^ 2 / d j := by
    -- The stage that processes `j` writes exactly the textbook recurrence.
    exact (scalarStateAt_write_rev d p εM hk hj).1
  have hsucc :
      (scalarStateAt d p εM n).t j.succ =
        (scalarStateAt d p εM k).t j.succ := by
    -- The successor slot was already finalized before row `j` is processed.
    simpa [Nat.add_sub_of_le hkLe] using
      scalarStateAt_succ_stable d p εM hk hj (n - k)
  have hprocessed :
      (scalarStateAt d p εM n).t (Fin.castSucc j) =
        (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) := by
    -- Once row `j` is written, later stages never revisit its scalar slot.
    simpa [Nat.add_assoc, Nat.add_sub_of_le hkSuccLe] using
      (scalarStateAt_processed_stable d p εM hk hj (n - (k + 1))).1
  calc
    t d p εM (Fin.castSucc j)
        = (scalarStateAt d p εM n).t (Fin.castSucc j) := rfl
    _ = (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) := hprocessed
    _ = (scalarStateAt d p εM k).t j.succ + (p j) ^ 2 / d j := hwrite
    _ = t d p εM j.succ + (p j) ^ 2 / d j := by
          rw [← hsucc]
          rfl

/-- The updated diagonal entry satisfies `barD j = d j * t_(j+1) / t_j`. -/
theorem barD_apply
    (j : Fin n) :
    barD d p εM j = d j * t d p εM j.succ / t d p εM (Fin.castSucc j) := by
  let k : Nat := (Fin.rev j).1
  have hk : k < n := (Fin.rev j).is_lt
  have hkLe : k ≤ n := Nat.le_of_lt hk
  have hkSuccLe : k + 1 ≤ n := Nat.succ_le_of_lt hk
  have hj : Fin.rev ⟨k, hk⟩ = j := by
    change Fin.rev (Fin.rev j) = j
    exact Fin.rev_rev j
  have hwrite :
      (scalarStateAt d p εM (k + 1)).barD j =
        d j * (scalarStateAt d p εM k).t j.succ /
          (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) := by
    -- The local scalar write already has the desired `barD` shape.
    exact (scalarStateAt_write_rev d p εM hk hj).2.1
  have hsucc :
      (scalarStateAt d p εM n).t j.succ =
        (scalarStateAt d p εM k).t j.succ := by
    -- The successor slot is final before row `j` is processed.
    simpa [Nat.add_sub_of_le hkLe] using
      scalarStateAt_succ_stable d p εM hk hj (n - k)
  have hprocessed :
      (scalarStateAt d p εM n).t (Fin.castSucc j) =
          (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) ∧
        (scalarStateAt d p εM n).barD j =
          (scalarStateAt d p εM (k + 1)).barD j ∧
        (scalarStateAt d p εM n).beta j =
          (scalarStateAt d p εM (k + 1)).beta j := by
    -- After stage `k + 1`, the public scalar entries for row `j` are frozen.
    simpa [Nat.add_assoc, Nat.add_sub_of_le hkSuccLe] using
      scalarStateAt_processed_stable d p εM hk hj (n - (k + 1))
  calc
    barD d p εM j
        = (scalarStateAt d p εM n).barD j := rfl
    _ = (scalarStateAt d p εM (k + 1)).barD j := hprocessed.2.1
    _ = d j * (scalarStateAt d p εM k).t j.succ /
          (scalarStateAt d p εM (k + 1)).t (Fin.castSucc j) := hwrite
    _ = d j * t d p εM j.succ / t d p εM (Fin.castSucc j) := by
          rw [← hsucc, ← hprocessed.1]
          rfl

/-- The update coefficient satisfies `beta j = -p j / (d j * t_(j+1))`. -/
theorem beta_apply
    (j : Fin n) :
    beta d p εM j = -(p j) / (d j * t d p εM j.succ) := by
  let k : Nat := (Fin.rev j).1
  have hk : k < n := (Fin.rev j).is_lt
  have hkLe : k ≤ n := Nat.le_of_lt hk
  have hkSuccLe : k + 1 ≤ n := Nat.succ_le_of_lt hk
  have hj : Fin.rev ⟨k, hk⟩ = j := by
    change Fin.rev (Fin.rev j) = j
    exact Fin.rev_rev j
  have hwrite :
      (scalarStateAt d p εM (k + 1)).beta j =
        -(p j) / (d j * (scalarStateAt d p εM k).t j.succ) := by
    -- The pivot-stage write stores the displayed coefficient formula.
    exact (scalarStateAt_write_rev d p εM hk hj).2.2
  have hsucc :
      (scalarStateAt d p εM n).t j.succ =
        (scalarStateAt d p εM k).t j.succ := by
    -- The denominator `t_(j+1)` is already final before processing `j`.
    simpa [Nat.add_sub_of_le hkLe] using
      scalarStateAt_succ_stable d p εM hk hj (n - k)
  have hprocessed :
      (scalarStateAt d p εM n).beta j =
        (scalarStateAt d p εM (k + 1)).beta j := by
    -- Later scalar stages do not revisit `beta j`.
    simpa [Nat.add_assoc, Nat.add_sub_of_le hkSuccLe] using
      (scalarStateAt_processed_stable d p εM hk hj (n - (k + 1))).2.2
  calc
    beta d p εM j = (scalarStateAt d p εM n).beta j := rfl
    _ = (scalarStateAt d p εM (k + 1)).beta j := hprocessed
    _ = -(p j) / (d j * (scalarStateAt d p εM k).t j.succ) := hwrite
    _ = -(p j) / (d j * t d p εM j.succ) := by
          rw [← hsucc]
          rfl

/-- The diagonal auxiliary entry satisfies `w_j^(j) = p j`. -/
theorem w_diag
    (j : Fin n) :
    w L p j j = p j :=
  let k : Nat := (Fin.rev j).1
  have hk : k < n := by
    simpa [k] using (Fin.rev j).is_lt
  have hkSuccLe : k + 1 ≤ n := Nat.succ_le_of_lt hk
  have hj : Fin.rev ⟨k, hk⟩ = j := by
    subst k
    change Fin.rev (Fin.rev j) = j
    exact Fin.rev_rev j
  have hwrite :
      (wStateAt L p (k + 1)).w j j = p j := by
    -- The pivot stage writes the diagonal auxiliary entry directly as `p j`.
    simpa using (wStateAt_write_rev L p hk hj).1
  have hprocessed :
      (wStateAt L p n).w j j = (wStateAt L p (k + 1)).w j j := by
    -- After row `j` is written, later stages touch only smaller rows.
    simpa [Nat.add_assoc, Nat.add_sub_of_le hkSuccLe] using
      wStateAt_processed_row_stable L p hk hj j (n - (k + 1))
  by
    simpa [w, wFromP] using hprocessed.trans hwrite

/-- For `j < r`, the auxiliary vector satisfies `w_r^(j) = w_r^(j+1) + p j * l_rj`. -/
theorem w_step
    (r j : Fin n) (hjr : j.1 < r.1) :
    let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
    w L p j r = w L p jNext r + p j * L r j :=
  let k : Nat := (Fin.rev j).1
  have hk : k < n := by
    simpa [k] using (Fin.rev j).is_lt
  have hkLe : k ≤ n := Nat.le_of_lt hk
  have hkSuccLe : k + 1 ≤ n := Nat.succ_le_of_lt hk
  have hj : Fin.rev ⟨k, hk⟩ = j := by
    subst k
    change Fin.rev (Fin.rev j) = j
    exact Fin.rev_rev j
  let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
  have hjNext : j < jNext := by
    change j.1 < j.1 + 1
    exact Nat.lt_succ_self _
  have hwrite :
      (wStateAt L p (k + 1)).w j r =
        (wStateAt L p k).w jNext r + p j * L r j := by
    -- The row written at stage `k + 1` is exactly the textbook off-diagonal recurrence.
    simpa [jNext] using (wStateAt_write_rev L p hk hj).2 (r := r) hjr
  have hprocessed :
      (wStateAt L p n).w j r = (wStateAt L p (k + 1)).w j r := by
    -- Later stages do not modify the row that has just been written.
    simpa [Nat.add_assoc, Nat.add_sub_of_le hkSuccLe] using
      wStateAt_processed_row_stable L p hk hj r (n - (k + 1))
  have hnext :
      (wStateAt L p n).w jNext r = (wStateAt L p k).w jNext r := by
    -- The next row was already final before processing the current pivot.
    simpa [Nat.add_sub_of_le hkLe] using
      wStateAt_larger_row_stable (L := L) (p := p) (hk := hk) (hj := hj)
        (i := jNext) (r := r) hjNext (n - k)
  have hfinal :
      (wStateAt L p n).w j r = (wStateAt L p n).w jNext r + p j * L r j := by
    calc
      (wStateAt L p n).w j r = (wStateAt L p (k + 1)).w j r := hprocessed
      _ = (wStateAt L p k).w jNext r + p j * L r j := hwrite
      _ = (wStateAt L p n).w jNext r + p j * L r j := by
            rw [hnext]
  by
    simpa [w, wFromP, jNext] using hfinal

/-- A strict lower entry of `barL` is updated by the stated `beta`-`w` correction term. -/
theorem barL_apply
    (r j : Fin n) (hjr : j.1 < r.1) :
    let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
    barL L d p εM r j = L r j + beta d p εM j * w L p jNext r := by
  -- In the strict-lower branch, `barL` is definitionally the textbook correction term.
  rw [barL, barLFromP, if_pos hjr]
  simp [beta, betaFromP, w, wFromP]

/-- Chapter01 Algorithm 1.2.19 (Cholesky Factorization of Negative Rank-One Update): the
source-facing outputs `t`, `barD`, `beta`, `w`, and `barL` satisfy the textbook backward
recurrences once the solve vector `p` is fixed. -/
theorem negative_rank_one_update_recurrences :
    t d p εM (Fin.last n) =
        max εM (1 - Finset.sum Finset.univ (fun i : Fin n ↦ (p i) ^ 2 / d i)) ∧
      (∀ j : Fin n, t d p εM (Fin.castSucc j) = t d p εM j.succ + (p j) ^ 2 / d j) ∧
      (∀ j : Fin n, barD d p εM j = d j * t d p εM j.succ / t d p εM (Fin.castSucc j)) ∧
      (∀ j : Fin n, beta d p εM j = -(p j) / (d j * t d p εM j.succ)) ∧
      (∀ j : Fin n, w L p j j = p j) ∧
      (∀ (r j : Fin n) (hjr : j.1 < r.1),
        let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
        w L p j r = w L p jNext r + p j * L r j) ∧
      ∀ (r j : Fin n) (hjr : j.1 < r.1),
        let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
        barL L d p εM r j = L r j + beta d p εM j * w L p jNext r := by
  refine ⟨tLast_eq d p εM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact tStep_eq d p εM j
  · intro j
    exact barD_apply d p εM j
  · intro j
    exact beta_apply d p εM j
  · intro j
    exact w_diag L p j
  · intro r j hjr
    exact w_step L p r j hjr
  · intro r j hjr
    exact barL_apply L d p εM r j hjr

end

section

variable {n : Nat}

local notation "Hessian" => Matrix (Fin n) (Fin n) ℝ

section

variable (L : Hessian) [Invertible L] (d y : Fin n → ℝ) (εM : ℝ)

/-- The inverse-based scalar formula is a derived bridge from the source-facing owner
`t d p εM`, obtained by specializing to the canonical solve `p = L⁻¹.mulVec y`. -/
theorem tLast_eq_inv :
    t d (L⁻¹ *ᵥ y) εM (Fin.last n) =
      max εM (1 - Finset.sum Finset.univ (fun i : Fin n ↦ ((L⁻¹ *ᵥ y) i) ^ 2 / d i)) :=
  tLast_eq d (L⁻¹ *ᵥ y) εM

/-- The inverse-based scalar update is a derived bridge from the source-facing owner
`t d p εM`, obtained by specializing to the canonical solve `p = L⁻¹.mulVec y`. -/
theorem tStep_eq_inv
    (j : Fin n) :
    t d (L⁻¹ *ᵥ y) εM (Fin.castSucc j) =
      t d (L⁻¹ *ᵥ y) εM j.succ + ((L⁻¹ *ᵥ y) j) ^ 2 / d j :=
  tStep_eq d (L⁻¹ *ᵥ y) εM j

/-- The inverse-based diagonal formula is a derived bridge from the source-facing owner
`barD d p εM`, obtained by specializing to the canonical solve `p = L⁻¹.mulVec y`. -/
theorem barD_apply_inv
    (j : Fin n) :
    barD d (L⁻¹ *ᵥ y) εM j =
      d j * t d (L⁻¹ *ᵥ y) εM j.succ / t d (L⁻¹ *ᵥ y) εM (Fin.castSucc j) :=
  barD_apply d (L⁻¹ *ᵥ y) εM j

/-- The inverse-based coefficient formula is a derived bridge from the source-facing owner
`beta d p εM`, obtained by specializing to the canonical solve `p = L⁻¹.mulVec y`. -/
theorem beta_apply_inv
    (j : Fin n) :
    beta d (L⁻¹ *ᵥ y) εM j = -((L⁻¹ *ᵥ y) j) / (d j * t d (L⁻¹ *ᵥ y) εM j.succ) :=
  beta_apply d (L⁻¹ *ᵥ y) εM j

end

section

variable (L : Hessian) [Invertible L] (y : Fin n → ℝ)

/-- Helper for Chapter01 Algorithm 1.2.19: the canonical inverse solve vector, named explicitly
to keep inverse-facing specializations stable. -/
abbrev inverse_solve_vector (L : Hessian) [Invertible L] (y : Fin n → ℝ) : Fin n → ℝ :=
  L⁻¹ *ᵥ y

/-- Helper for Chapter01 Algorithm 1.2.19: package the source-facing `w` identities for an
explicit solve vector, so inverse-facing wrappers only need direct specialization. -/
theorem inverse_w_specialize
    (L : Hessian) (q : Fin n → ℝ) :
    (∀ j : Fin n, w L q j j = q j) ∧
      ∀ (r j : Fin n) (hjr : j.1 < r.1),
        let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
        w L q j r = w L q jNext r + q j * L r j :=
  ⟨fun j ↦ by
      -- Route correction: the remaining blocker is elaboration around the inverse term, so first
      -- package the already-proved source-facing diagonal identity for an explicit solve vector.
      simpa using w_diag L q j,
    fun r j hjr ↦ by
      -- The off-diagonal recurrence is the same source-facing theorem, again with explicit `q`.
      simpa using w_step L q r j hjr⟩

/-- The inverse-based diagonal auxiliary formula is a derived bridge from the source-facing owner
`w L p`, obtained by specializing to the canonical solve `p = L⁻¹.mulVec y`. -/
theorem w_diag_inv
    (rhs : Fin n → ℝ) (j : Fin n) :
    w L (L⁻¹ *ᵥ rhs) j j = (L⁻¹ *ᵥ rhs) j :=
  -- Route correction: infer the solve vector from the target, so the proof never names the
  -- inaccessible inverse binder explicitly.
  (inverse_w_specialize (L := L) (q := L⁻¹ *ᵥ rhs)).1 j

/-- The inverse-based auxiliary-vector step is a derived bridge from the source-facing owner
`w L p`, obtained by specializing to the canonical solve `p = L⁻¹.mulVec y`. -/
theorem w_step_inv
    (rhs : Fin n → ℝ) (r j : Fin n) (hjr : j.1 < r.1) :
    let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
    w L (L⁻¹ *ᵥ rhs) j r = w L (L⁻¹ *ᵥ rhs) jNext r + (L⁻¹ *ᵥ rhs) j * L r j :=
  -- The same target-driven specialization recovers the inverse-facing off-diagonal recurrence.
  (inverse_w_specialize (L := L) (q := L⁻¹ *ᵥ rhs)).2 r j hjr

end

section

variable (L : Hessian) [Invertible L] (d y : Fin n → ℝ) (εM : ℝ)

/-- The inverse-based lower-factor formula is a derived bridge from the source-facing owner
`barL L d p εM`, obtained by specializing to the canonical solve `p = L⁻¹.mulVec y`. -/
theorem barL_apply_inv
    (r j : Fin n) (hjr : j.1 < r.1) :
    let jNext : Fin n := ⟨j.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjr) r.is_lt⟩
    barL L d (L⁻¹ *ᵥ y) εM r j =
      L r j + beta d (L⁻¹ *ᵥ y) εM j * w L (L⁻¹ *ᵥ y) jNext r :=
  barL_apply L d (L⁻¹ *ᵥ y) εM r j hjr

end

end

end NegativeRankOneCholeskyUpdate
