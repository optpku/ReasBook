/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.MinMax
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Symmetric

open scoped BigOperators

noncomputable section

/-- The modified Cholesky system matrix `L D Lᵀ` built from a lower factor `L`
and diagonal entries `D`. -/
def modifiedCholeskySystemMatrix {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  L * Matrix.diagonal D * Matrix.transpose L

-- Domain sampling:
-- * `Matrix.IsSymm` is the mathlib owner for the symmetric-matrix hypothesis appearing in the
--   Gill-Murray setup.
-- * `RankOneCholeskyUpdate` in Chapter 1 keeps the iterative state private and exposes the
--   source-named outputs through one owner namespace.
-- * `ModifiedNewtonMethod` and `modifiedCholeskySystemMatrix` in Chapter 3 consume this
--   algorithm through the source-facing correction matrix `E`, corrected matrix `G + E`, and the
--   terminal factor data. The pivot-order matrix is only a bridge/view for the factorization.

/-- A Gill-Murray modified Cholesky factorization for Chapter03 Algorithm 3.3.2 starts from a
real symmetric matrix `G`, uses a positive safeguard parameter `δ`, and computes the Step-1
quantity `β = max {γ, ξ / ν, 0}^{1/2}` from `G`. The algorithm then runs the pivoted
modified-Cholesky recursion on this fixed input to produce the working matrices `C^(k)`, lower
factors `L^(k)`, diagonal entries `d^(k)`, correction entries `e^(k)`, auxiliary maxima
`theta^(k)`, and pivot sequence, together with the cumulative pivot permutation. -/
structure ModifiedCholeskyFactorization (n : Nat) where
  G : Matrix (Fin n) (Fin n) ℝ
  symm : G.IsSymm
  δ : ℝ
  delta_pos : 0 < δ

namespace ModifiedCholeskyFactorization

variable {n : Nat}

local notation "Hessian" => Matrix (Fin n) (Fin n) ℝ

/-- The candidate pivot indices at stage `j` are the indices `i` with `j ≤ i < n`. -/
def tailIndices (j : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun i ↦ j ≤ i

/-- The strict tail at stage `j` consists of the indices `i` with `j < i < n`. -/
def strictTailIndices (j : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun i ↦ j < i

/-- The pivot index is the smallest tail index whose diagonal entry has maximal absolute value. -/
noncomputable def pivotIndex (C : Hessian) (j : Fin n) : Fin n :=
  ((tailIndices j).argmax fun i ↦ |C i i|).getD j

private structure State (n : Nat) where
  C : Matrix (Fin n) (Fin n) ℝ
  L : Matrix (Fin n) (Fin n) ℝ
  d : Fin n → ℝ
  e : Fin n → ℝ
  theta : Fin n → ℝ
  perm : Equiv.Perm (Fin n)
  pivot : Fin n → Fin n

/-- The initial working state starts from the input matrix, the identity lower factor,
and zero placeholders for the stagewise data produced by the recursion. -/
private def init (G : Hessian) : State n where
  C := G
  L := 1
  d := fun _ ↦ 0
  e := fun _ ↦ 0
  theta := fun _ ↦ 0
  perm := Equiv.refl _
  pivot := fun j ↦ j

/-- Before computing the `j`-th factor column, a symmetric pivot `j ↔ q` swaps the rows already
filled in the previous columns of `L`. -/
private def priorFactor (j q : Fin n) (L : Hessian) : Hessian :=
  let σ := Equiv.swap j q
  fun r s ↦
    if s < j then
      L (σ r) s
    else
      L r s

/-- One step of the Gill-Murray modified Cholesky factorization algorithm. -/
private def step (β δ : ℝ) (j : Fin n) (state : State n) : State n :=
  let q := pivotIndex state.C j
  let σ := Equiv.swap j q
  let Cswap := state.C.submatrix σ σ
  let Lprior := priorFactor j q state.L
  let Lrow : Fin n → ℝ := fun s ↦
    if s = j then
      1
    else if s < j then
      Cswap j s / state.d s
    else
      0
  let Lnext : Hessian := Function.update Lprior j Lrow
  let Cj : Fin n → ℝ := fun i ↦
    if j < i then
      Cswap i j -
        Finset.sum (Finset.univ.filter fun s : Fin n ↦ s < j) (fun s ↦ Lrow s * Cswap i s)
    else
      Cswap i j
  let thetaj := (strictTailIndices j).foldl (fun acc i ↦ max acc |Cj i|) 0
  let djj := max δ (max |Cj j| (thetaj ^ 2 / β ^ 2))
  let ejj := djj - Cj j
  let Cnext : Hessian := fun i k ↦
    if k = j then
      Cj i
    else if i = j then
      Cj k
    else if j < i ∧ j < k then
      if i = k then
        Cswap i k - Cj i * Cj k / djj
      else
        Cswap i k
    else
      Cswap i k
  { C := Cnext
    L := Lnext
    d := Function.update state.d j djj
    e := Function.update state.e j ejj
    theta := Function.update state.theta j thetaj
    perm := state.perm.trans σ
    pivot := Function.update state.pivot j q }

/-- The quantity `γ` from the Gill-Murray Step-1 setup is the maximum absolute diagonal
entry of the input matrix. -/
def gamma (G : Hessian) : ℝ :=
  (List.finRange n).foldl (fun acc i ↦ max acc |G i i|) 0

/-- The quantity `ξ` from the Gill-Murray Step-1 setup is the maximum absolute off-diagonal
entry of the input matrix. -/
def xi (G : Hessian) : ℝ :=
  (List.finRange n).foldl
    (fun acc i ↦
      (List.finRange n).foldl
        (fun acc' j ↦ if i = j then acc' else max acc' |G i j|)
        acc)
    0

/-- The Step-1 quantity `β` for Algorithm 3.3.2, computed from the matrix data of `G`
as in formula `(3.3.14)`. -/
noncomputable def beta (G : Hessian) : ℝ :=
  let γ := gamma G
  let ξ := xi G
  let ν := max (1 : ℝ) (Real.sqrt ((n : ℝ) ^ 2 - 1))
  Real.sqrt (max γ (max (ξ / ν) 0))

/-- The Step-1 quantity `γ` attached to a fixed modified Cholesky factorization. -/
def γ (A : ModifiedCholeskyFactorization n) : ℝ :=
  gamma A.G

/-- The Step-1 quantity `ξ` attached to a fixed modified Cholesky factorization. -/
def ξ (A : ModifiedCholeskyFactorization n) : ℝ :=
  xi A.G

/-- The Step-1 quantity `β` attached to a fixed modified Cholesky factorization. -/
noncomputable def β (A : ModifiedCholeskyFactorization n) : ℝ :=
  beta A.G

/-- The private state after `k` iterations of the modified Cholesky recursion attached to `A`. -/
private def stateAt (A : ModifiedCholeskyFactorization n) : Nat → State n
  | 0 => init A.G
  | k + 1 =>
      if hk : k < n then
        step A.β A.δ ⟨k, hk⟩ (stateAt A k)
      else
        stateAt A k

/-- The working matrix `C^(k)` produced after `k` iterations. -/
def CAt (A : ModifiedCholeskyFactorization n) : Nat → Hessian :=
  fun k ↦ (stateAt A k).C

/-- The lower-triangular factor `L^(k)` produced after `k` iterations. -/
def LAt (A : ModifiedCholeskyFactorization n) : Nat → Hessian :=
  fun k ↦ (stateAt A k).L

/-- The diagonal sequence `d^(k)` produced after `k` iterations. -/
def dAt (A : ModifiedCholeskyFactorization n) : Nat → Fin n → ℝ :=
  fun k ↦ (stateAt A k).d

/-- The correction sequence `e^(k)` produced after `k` iterations. -/
def eAt (A : ModifiedCholeskyFactorization n) : Nat → Fin n → ℝ :=
  fun k ↦ (stateAt A k).e

/-- The auxiliary maxima `theta^(k)` produced after `k` iterations. -/
def thetaAt (A : ModifiedCholeskyFactorization n) : Nat → Fin n → ℝ :=
  fun k ↦ (stateAt A k).theta

/-- The cumulative pivot permutation after `k` iterations, sending original indices to the
current working order. -/
def permAt (A : ModifiedCholeskyFactorization n) : Nat → Equiv.Perm (Fin n) :=
  fun k ↦ (stateAt A k).perm

/-- The pivot sequence accumulated after `k` iterations. -/
def pivotAt (A : ModifiedCholeskyFactorization n) : Nat → Fin n → Fin n :=
  fun k ↦ (stateAt A k).pivot

/-- The terminal working matrix `C` after all `n` iterations. -/
def C (A : ModifiedCholeskyFactorization n) : Hessian :=
  A.CAt n

/-- The terminal lower-triangular factor `L` after all `n` iterations. -/
def L (A : ModifiedCholeskyFactorization n) : Hessian :=
  A.LAt n

/-- The terminal diagonal entries `d` after all `n` iterations. -/
def d (A : ModifiedCholeskyFactorization n) : Fin n → ℝ :=
  A.dAt n

/-- The terminal correction entries `e` after all `n` iterations. -/
def e (A : ModifiedCholeskyFactorization n) : Fin n → ℝ :=
  A.eAt n

/-- The terminal auxiliary maxima `theta` after all `n` iterations. -/
def theta (A : ModifiedCholeskyFactorization n) : Fin n → ℝ :=
  A.thetaAt n

/-- The terminal cumulative pivot permutation, sending original indices to the final working
order. -/
def perm (A : ModifiedCholeskyFactorization n) : Equiv.Perm (Fin n) :=
  A.permAt n

/-- The terminal pivot sequence after all `n` iterations. -/
def pivot (A : ModifiedCholeskyFactorization n) : Fin n → Fin n :=
  A.pivotAt n

/-- The terminal diagonal correction matrix `E` in the original coordinates of `G`. -/
def correctionMatrix (A : ModifiedCholeskyFactorization n) : Hessian :=
  Matrix.reindex A.perm.symm A.perm.symm (Matrix.diagonal A.e)

/-- The terminal corrected matrix `G + E` in the original coordinates of the input matrix. -/
def correctedMatrix (A : ModifiedCholeskyFactorization n) : Hessian :=
  A.G + A.correctionMatrix

/-- The corrected matrix in the cumulative pivot order, `P G Pᵀ + E`, where `P` is encoded by
`perm`. This is the bridge/view consumed by the factorization identity. -/
def permutedCorrectedMatrix (A : ModifiedCholeskyFactorization n) : Hessian :=
  Matrix.reindex A.perm A.perm A.G + Matrix.diagonal A.e

/-- The rowwise Gershgorin upper bound `b₁` attached to the input Hessian `G`. -/
def shiftUpperBound1 (A : ModifiedCholeskyFactorization n) : ℝ :=
  let rowShiftDeficit : Fin n → ℝ := fun i ↦
    max 0 (Finset.sum (Finset.univ.erase i) (fun j ↦ |A.G i j|) - A.G i i)
  if h : (Finset.univ : Finset (Fin n)).Nonempty then
    Finset.univ.sup' h rowShiftDeficit
  else
    0

/-- The diagonal-correction upper bound `b₂` attached to the correction entries `e`. -/
def shiftUpperBound2 (A : ModifiedCholeskyFactorization n) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then
    Finset.univ.sup' h A.e
  else
    0

/-- The pivot chosen at stage `j` is the tail index maximizing `|C i i|`, with smallest-index
tie breaking inherited from `List.argmax` on `List.finRange n`. -/
theorem pivotAt_step_eq (A : ModifiedCholeskyFactorization n) (j : Fin n) :
    A.pivotAt (j.1 + 1) j = pivotIndex (A.CAt j.1) j := by
  -- The `(j + 1)`-st state is obtained by running exactly the `j`-th step.
  have hj : j.1 < n := j.is_lt
  simp [pivotAt, CAt, stateAt, hj, step]

/-- Helper for Chapter03 Algorithm 3.3.2: the pivot index always lies in the active tail
starting at `j`. -/
private theorem le_pivotIndex (C : Hessian) (j : Fin n) :
    j ≤ pivotIndex C j := by
  -- The chosen pivot is an element of `tailIndices j`, so its index is at least `j`.
  unfold pivotIndex
  rcases harg : (tailIndices j).argmax fun i ↦ |C i i| with _ | q
  · simp [harg]
  · have hmemArg : q ∈ (tailIndices j).argmax fun i ↦ |C i i| := by
      simpa [harg]
    have hmemTail : q ∈ tailIndices j := List.argmax_mem hmemArg
    simpa [tailIndices] using hmemTail

/-- The cumulative permutation after stage `j` appends the symmetric swap
`j ↔ pivot_j` to the previous working order. -/
theorem permAt_step_eq (A : ModifiedCholeskyFactorization n) (j : Fin n) :
    A.permAt (j.1 + 1) = (A.permAt j.1).trans (Equiv.swap j (A.pivotAt (j.1 + 1) j)) := by
  -- The step records the new cumulative permutation by composing with the pivot swap.
  have hj : j.1 < n := j.is_lt
  rw [pivotAt_step_eq]
  simp [permAt, CAt, stateAt, hj, step]

/-- Helper for Chapter03 Algorithm 3.3.2: on a processed index, the inverse cumulative
permutation is unchanged by the next pivot swap. -/
private theorem permAtSymm_step_apply_processed (A : ModifiedCholeskyFactorization n)
    (i j : Fin n) (hij : i < j) :
    (A.permAt (j.1 + 1)).symm i = (A.permAt j.1).symm i := by
  have hi_ne_j : i ≠ j := ne_of_lt hij
  have hi_ne_q : i ≠ pivotIndex (A.CAt j.1) j := by
    intro h
    have hq_ge : j ≤ pivotIndex (A.CAt j.1) j := le_pivotIndex (A.CAt j.1) j
    exact (not_le_of_gt hij) (h ▸ hq_ge)
  -- The inverse permutation sees the stage-`j` swap first, and that swap fixes processed indices.
  have hperm := congrArg (fun e : Equiv.Perm (Fin n) ↦ e.symm i) (permAt_step_eq A j)
  rw [pivotAt_step_eq] at hperm
  simpa [Equiv.swap_apply_def, hi_ne_j, hi_ne_q] using hperm

/-- Helper for Chapter03 Algorithm 3.3.2: reindexing the input matrix across one step only
swaps the row index of a processed column. -/
private theorem reindexInputAtStep_processedColumn (A : ModifiedCholeskyFactorization n)
    (j i s : Fin n) (hsj : s < j) :
    Matrix.reindex (A.permAt (j.1 + 1)) (A.permAt (j.1 + 1)) A.G i s =
      Matrix.reindex (A.permAt j.1) (A.permAt j.1) A.G
        ((Equiv.swap j (A.pivotAt (j.1 + 1) j)) i) s := by
  have hs_ne_j : s ≠ j := ne_of_lt hsj
  have hs_ne_q : s ≠ pivotIndex (A.CAt j.1) j := by
    intro h
    have hq_ge : j ≤ pivotIndex (A.CAt j.1) j := le_pivotIndex (A.CAt j.1) j
    exact (not_le_of_gt hsj) (h ▸ hq_ge)
  have hs_fixed : (Equiv.swap j (pivotIndex (A.CAt j.1) j)) s = s := by
    simp [Equiv.swap_apply_def, hs_ne_j, hs_ne_q]
  -- `Matrix.reindex` uses the inverse permutation, so the processed column index is fixed.
  rw [Matrix.reindex_apply, Matrix.reindex_apply, permAt_step_eq, pivotAt_step_eq]
  simp [hs_fixed]

/-- Helper for Chapter03 Algorithm 3.3.2: once both coordinates lie strictly before the active
pivot, reindexing the input matrix across one more step leaves that entry unchanged. -/
private theorem reindexInputAtStep_processedEntry (A : ModifiedCholeskyFactorization n)
    (j i s : Fin n) (hij : i < j) (hsj : s < j) :
    Matrix.reindex (A.permAt (j.1 + 1)) (A.permAt (j.1 + 1)) A.G i s =
      Matrix.reindex (A.permAt j.1) (A.permAt j.1) A.G i s := by
  -- Later pivot swaps fix already processed row and column indices inside `Matrix.reindex`.
  change A.G ((A.permAt (j.1 + 1)).symm i) ((A.permAt (j.1 + 1)).symm s) =
      A.G ((A.permAt j.1).symm i) ((A.permAt j.1).symm s)
  rw [permAtSymm_step_apply_processed A i j hij, permAtSymm_step_apply_processed A s j hsj]

/-- Helper for Chapter03 Algorithm 3.3.2: once row `i` has been processed, every later pivot
keeps the diagonal input entry in that pivot order unchanged. -/
private theorem reindexInputAtStep_processedDiag (A : ModifiedCholeskyFactorization n)
    (i j : Fin n) (hij : i < j) :
    Matrix.reindex (A.permAt (j.1 + 1)) (A.permAt (j.1 + 1)) A.G i i =
      Matrix.reindex (A.permAt j.1) (A.permAt j.1) A.G i i := by
  -- This is the diagonal specialization of processed-entry stability.
  simpa using reindexInputAtStep_processedEntry A j i i hij hij

/-- Helper for Chapter03 Algorithm 3.3.2: once a strict-lower input entry lies in a fully
processed row and column, every later pivot leaves its pivot-ordered value unchanged. -/
private theorem reindexInputStableAfterProcessed (A : ModifiedCholeskyFactorization n)
    (i s : Fin n) (hsi : s < i) :
    ∀ k : Nat, i.1 + 1 ≤ k → k ≤ n →
      Matrix.reindex (A.permAt k) (A.permAt k) A.G i s =
        Matrix.reindex (A.permAt (i.1 + 1)) (A.permAt (i.1 + 1)) A.G i s := by
  intro k hk _
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  clear hk
  induction t with
  | zero =>
      rfl
  | succ t iht =>
      by_cases hk : i.1 + 1 + t < n
      · have hk' : i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        have hprocessed : i < (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
          show i.1 < i.1 + 1 + t
          omega
        have hprocessed' : s < (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
          show s.1 < i.1 + 1 + t
          omega
        have hstep :
            Matrix.reindex (A.permAt (i.1 + 1 + t + 1)) (A.permAt (i.1 + 1 + t + 1)) A.G i s =
              Matrix.reindex (A.permAt (i.1 + 1 + t)) (A.permAt (i.1 + 1 + t)) A.G i s := by
          simpa [Nat.add_assoc] using
            reindexInputAtStep_processedEntry A ⟨i.1 + 1 + t, hk⟩ i s hprocessed hprocessed'
        have hbound : i.1 + 1 + t ≤ n := by
          omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)
      · have hk' : ¬ i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        -- After stage `n`, the recursive state and its pivot order remain constant.
        have hstep :
            Matrix.reindex (A.permAt (i.1 + 1 + t + 1)) (A.permAt (i.1 + 1 + t + 1)) A.G i s =
              Matrix.reindex (A.permAt (i.1 + 1 + t)) (A.permAt (i.1 + 1 + t)) A.G i s := by
          simp [permAt, stateAt, hk', Nat.add_assoc]
        have hbound : i.1 + 1 + t ≤ n := by
          omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)

/-- Helper for Chapter03 Algorithm 3.3.2: once row `i` has been processed, the pivot-ordered
diagonal input entry at `i` is stable under all later pivots. -/
private theorem reindexInputDiagStableAfterProcessed (A : ModifiedCholeskyFactorization n)
    (i : Fin n) :
    ∀ k : Nat, i.1 + 1 ≤ k → k ≤ n →
      Matrix.reindex (A.permAt k) (A.permAt k) A.G i i =
        Matrix.reindex (A.permAt (i.1 + 1)) (A.permAt (i.1 + 1)) A.G i i := by
  intro k hk _
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  clear hk
  induction t with
  | zero =>
      rfl
  | succ t iht =>
      by_cases hk : i.1 + 1 + t < n
      · have hprocessed : i < (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
          show i.1 < i.1 + 1 + t
          omega
        have hstep :
            Matrix.reindex (A.permAt (i.1 + 1 + t + 1)) (A.permAt (i.1 + 1 + t + 1)) A.G i i =
              Matrix.reindex (A.permAt (i.1 + 1 + t)) (A.permAt (i.1 + 1 + t)) A.G i i := by
          simpa [Nat.add_assoc] using reindexInputAtStep_processedDiag A i ⟨i.1 + 1 + t, hk⟩ hprocessed
        have hbound : i.1 + 1 + t ≤ n := by
          omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)
      · have hk' : ¬ i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        have hstep :
            Matrix.reindex (A.permAt (i.1 + 1 + t + 1)) (A.permAt (i.1 + 1 + t + 1)) A.G i i =
              Matrix.reindex (A.permAt (i.1 + 1 + t)) (A.permAt (i.1 + 1 + t)) A.G i i := by
          simp [permAt, stateAt, hk', Nat.add_assoc]
        have hbound : i.1 + 1 + t ≤ n := by
          omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)

/-- The auxiliary quantity `theta j` is the maximum absolute value of the updated strict-lower
entries in column `j`, with value `0` when the strict tail is empty. -/
theorem thetaAt_step_eq (A : ModifiedCholeskyFactorization n) (j : Fin n) :
    A.thetaAt (j.1 + 1) j =
      (strictTailIndices j).foldl (fun acc i ↦ max acc |A.CAt (j.1 + 1) i j|) 0 := by
  -- At column `j`, the updated working matrix stores exactly the freshly computed `Cj` data.
  have hj : j.1 < n := j.is_lt
  simp [thetaAt, CAt, stateAt, hj, step]

/-- The diagonal entry `d j` is the stagewise maximum of `δ`, `|c_jj|`,
and `theta j ^ 2 / β ^ 2`. -/
theorem dAt_step_eq (A : ModifiedCholeskyFactorization n) (j : Fin n) :
    A.dAt (j.1 + 1) j =
      max A.δ (max |A.CAt (j.1 + 1) j j| ((A.thetaAt (j.1 + 1) j) ^ 2 / A.β ^ 2)) := by
  -- The stage formula is definitional once both sides are expressed through the same state.
  have hj : j.1 < n := j.is_lt
  unfold dAt thetaAt CAt
  simp [stateAt, hj, step]

/-- The correction entry satisfies `e j = d j - c_jj` at stage `j`. -/
theorem eAt_step_eq (A : ModifiedCholeskyFactorization n) (j : Fin n) :
    A.eAt (j.1 + 1) j = A.dAt (j.1 + 1) j - A.CAt (j.1 + 1) j j := by
  -- The step stores `e_j` directly as the diagonal gap in the updated state.
  have hj : j.1 < n := j.is_lt
  unfold eAt dAt CAt
  simp [stateAt, hj, step]

/-- Helper for Chapter03 Algorithm 3.3.2: a step at index `j` leaves the diagonal data `d i`
unchanged at every other index `i ≠ j`. -/
private theorem stepDApplyNe {β δ : ℝ} (j i : Fin n) (state : State n) (hij : i ≠ j) :
    (step β δ j state).d i = state.d i := by
  simp [step, hij]

/-- Helper for Chapter03 Algorithm 3.3.2: a step at index `j` leaves the correction entry `e i`
unchanged at every other index `i ≠ j`. -/
private theorem stepEApplyNe {β δ : ℝ} (j i : Fin n) (state : State n) (hij : i ≠ j) :
    (step β δ j state).e i = state.e i := by
  simp [step, hij]

/-- Helper for Chapter03 Algorithm 3.3.2: once a row lies strictly before the active pivot,
later steps do not change that row of `L`. -/
private theorem stepLApplyProcessed {β δ : ℝ} (j i s : Fin n) (state : State n)
    (hij : i < j) :
    (step β δ j state).L i s = state.L i s := by
  -- Later swaps act only on the current tail, so every already processed row is fixed.
  have hi_ne_j : i ≠ j := ne_of_lt hij
  have hi_ne_q : i ≠ pivotIndex state.C j := by
    intro hiq
    have hq_ge : j ≤ pivotIndex state.C j := le_pivotIndex state.C j
    exact (not_le_of_gt hij) (hiq ▸ hq_ge)
  have hswap : (Equiv.swap j (pivotIndex state.C j)) i = i := by
    simp [Equiv.swap_apply_def, hi_ne_j, hi_ne_q]
  by_cases hs : s < j
  · simp [step, priorFactor, hi_ne_j, hs, hswap]
  · simp [step, priorFactor, hi_ne_j, hs, hswap]

/-- Helper for Chapter03 Algorithm 3.3.2: once both indices lie strictly before the active
pivot, later steps leave that working-matrix entry unchanged. -/
private theorem stepCApplyProcessed {β δ : ℝ} (j i s : Fin n) (state : State n)
    (hij : i < j) (hsj : s < j) :
    (step β δ j state).C i s = state.C i s := by
  -- The active swap fixes the processed block, and Step 5 only modifies the strict tail.
  have hi_ne_j : i ≠ j := ne_of_lt hij
  have hs_ne_j : s ≠ j := ne_of_lt hsj
  have hi_ne_q : i ≠ pivotIndex state.C j := by
    intro hiq
    have hq_ge : j ≤ pivotIndex state.C j := le_pivotIndex state.C j
    exact (not_le_of_gt hij) (hiq ▸ hq_ge)
  have hs_ne_q : s ≠ pivotIndex state.C j := by
    intro hsq
    have hq_ge : j ≤ pivotIndex state.C j := le_pivotIndex state.C j
    exact (not_le_of_gt hsj) (hsq ▸ hq_ge)
  have hswap_i : (Equiv.swap j (pivotIndex state.C j)) i = i := by
    simp [Equiv.swap_apply_def, hi_ne_j, hi_ne_q]
  have hswap_s : (Equiv.swap j (pivotIndex state.C j)) s = s := by
    simp [Equiv.swap_apply_def, hs_ne_j, hs_ne_q]
  have hnotTail : ¬ (j < i ∧ j < s) := by
    intro htail
    exact (not_le_of_gt hij) (le_of_lt htail.1)
  simp [step, hi_ne_j, hs_ne_j, hswap_i, hswap_s, hnotTail]

/-- Helper for Chapter03 Algorithm 3.3.2: in a processed column, one step transports the working
entry by the active symmetric swap on the row index. -/
private theorem stepCApplyProcessedColumn {β δ : ℝ} (j i s : Fin n) (state : State n)
    (hsymm : state.C.IsSymm) (hsj : s < j) :
    (step β δ j state).C i s =
      state.C ((Equiv.swap j (pivotIndex state.C j)) i) s := by
  let q := pivotIndex state.C j
  let σ := Equiv.swap j q
  have hs_ne_j : s ≠ j := ne_of_lt hsj
  have hs_ne_q : s ≠ q := by
    intro hsq
    have hq_ge : j ≤ q := by
      simpa [q] using le_pivotIndex state.C j
    exact (not_le_of_gt hsj) (hsq ▸ hq_ge)
  have hswap_s : σ s = s := by
    simp [σ, Equiv.swap_apply_def, hs_ne_j, hs_ne_q]
  by_cases hij : i = j
  · subst i
    -- The new pivot row is read from the swapped column, so symmetry converts it back to a row entry.
    calc
      (step β δ j state).C j s = state.C s q := by
        simp [step, q, σ, hs_ne_j, hsj.not_gt, hswap_s]
      _ = state.C q s := (hsymm.apply s q).symm
      _ = state.C (σ j) s := by
        simp [σ, q]
  · have hnotTail : ¬ (j < i ∧ j < s) := by
      intro htail
      exact (not_lt_of_ge (le_of_lt hsj)) htail.2
    -- Away from the pivot row, the step only reindexes the processed column by the active swap.
    simp [step, q, σ, hij, hs_ne_j, hnotTail, hswap_s]

/-- Helper for Chapter03 Algorithm 3.3.2: once stage `i` writes the `i`-th diagonal data,
all later stages leave that `d`-entry and `e`-entry unchanged. -/
private theorem processedDiagonalDataStable (A : ModifiedCholeskyFactorization n) (i : Fin n) :
    A.d i = A.dAt (i.1 + 1) i ∧ A.e i = A.eAt (i.1 + 1) i := by
  have hdStable : ∀ t : Nat, A.dAt (i.1 + 1 + t) i = A.dAt (i.1 + 1) i := by
    intro t
    induction t with
    | zero =>
        rfl
    | succ t iht =>
        by_cases hk : i.1 + 1 + t < n
        · have hne : i ≠ (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
            intro h
            have hval : i.1 = i.1 + 1 + t := by
              simpa using congrArg Fin.val h
            omega
          have hk' : i.1 + (1 + t) < n := by
            simpa [Nat.add_assoc] using hk
          -- Later steps update index `i.1 + 1 + t`, so the already processed index `i` is fixed.
          have hstep : A.dAt (i.1 + 1 + t + 1) i = A.dAt (i.1 + 1 + t) i := by
            calc
              A.dAt (i.1 + 1 + t + 1) i
                  = (step A.β A.δ ⟨i.1 + 1 + t, hk⟩ (A.stateAt (i.1 + 1 + t))).d i := by
                      simp [dAt, stateAt, hk', Nat.add_assoc]
              _ = (A.stateAt (i.1 + 1 + t)).d i := stepDApplyNe _ _ _ hne
              _ = A.dAt (i.1 + 1 + t) i := by
                    rfl
          simpa [Nat.add_assoc] using hstep.trans iht
        · -- Once the recursion has reached `n`, `stateAt` is constant.
          have hk' : ¬ i.1 + (1 + t) < n := by
            simpa [Nat.add_assoc] using hk
          have hstep : A.dAt (i.1 + 1 + t + 1) i = A.dAt (i.1 + 1 + t) i := by
            simp [dAt, stateAt, hk', Nat.add_assoc]
          simpa [Nat.add_assoc] using hstep.trans iht
  have heStable : ∀ t : Nat, A.eAt (i.1 + 1 + t) i = A.eAt (i.1 + 1) i := by
    intro t
    induction t with
    | zero =>
        rfl
    | succ t iht =>
        by_cases hk : i.1 + 1 + t < n
        · have hne : i ≠ (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
            intro h
            have hval : i.1 = i.1 + 1 + t := by
              simpa using congrArg Fin.val h
            omega
          have hk' : i.1 + (1 + t) < n := by
            simpa [Nat.add_assoc] using hk
          -- The same stability argument applies to the correction entries.
          have hstep : A.eAt (i.1 + 1 + t + 1) i = A.eAt (i.1 + 1 + t) i := by
            calc
              A.eAt (i.1 + 1 + t + 1) i
                  = (step A.β A.δ ⟨i.1 + 1 + t, hk⟩ (A.stateAt (i.1 + 1 + t))).e i := by
                      simp [eAt, stateAt, hk', Nat.add_assoc]
              _ = (A.stateAt (i.1 + 1 + t)).e i := stepEApplyNe _ _ _ hne
              _ = A.eAt (i.1 + 1 + t) i := by
                    rfl
          simpa [Nat.add_assoc] using hstep.trans iht
        · -- Beyond the last stage the recursion stops changing the state.
          have hk' : ¬ i.1 + (1 + t) < n := by
            simpa [Nat.add_assoc] using hk
          have hstep : A.eAt (i.1 + 1 + t + 1) i = A.eAt (i.1 + 1 + t) i := by
            simp [eAt, stateAt, hk', Nat.add_assoc]
          simpa [Nat.add_assoc] using hstep.trans iht
  have hi_le : i.1 + 1 ≤ n := Nat.succ_le_of_lt i.is_lt
  constructor
  · -- Specializing the stability statement at the terminal stage recovers the public `d`.
    simpa [d, Nat.add_sub_of_le hi_le] using hdStable (n - (i.1 + 1))
  · -- The same specialization recovers the public correction entry `e`.
    simpa [e, Nat.add_sub_of_le hi_le] using heStable (n - (i.1 + 1))

/-- Helper for Chapter03 Algorithm 3.3.2: once stage `i` writes `d_i`, every later stage agrees
with that processed diagonal entry. -/
private theorem dAtStableAfterProcessed (A : ModifiedCholeskyFactorization n) (i : Fin n) :
    ∀ k : Nat, i.1 + 1 ≤ k → k ≤ n → A.dAt k i = A.dAt (i.1 + 1) i := by
  intro k hk _
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  clear hk
  induction t with
  | zero =>
      rfl
  | succ t iht =>
      by_cases hk : i.1 + 1 + t < n
      · have hne : i ≠ (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
          intro h
          have hval : i.1 = i.1 + 1 + t := by
            simpa using congrArg Fin.val h
          omega
        have hk' : i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        -- The current step writes a later pivot index, so the processed entry `d_i` is fixed.
        have hstep : A.dAt (i.1 + 1 + t + 1) i = A.dAt (i.1 + 1 + t) i := by
          calc
            A.dAt (i.1 + 1 + t + 1) i
                = (step A.β A.δ ⟨i.1 + 1 + t, hk⟩ (A.stateAt (i.1 + 1 + t))).d i := by
                    simp [dAt, stateAt, hk', Nat.add_assoc]
            _ = (A.stateAt (i.1 + 1 + t)).d i := stepDApplyNe _ _ _ hne
            _ = A.dAt (i.1 + 1 + t) i := by
                  rfl
        have hbound : i.1 + 1 + t ≤ n := by omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)
      · have hk' : ¬ i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        -- Beyond the last stage, the recursive state is constant.
        have hstep : A.dAt (i.1 + 1 + t + 1) i = A.dAt (i.1 + 1 + t) i := by
          simp [dAt, stateAt, hk', Nat.add_assoc]
        have hbound : i.1 + 1 + t ≤ n := by omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)

/-- Helper for Chapter03 Algorithm 3.3.2: once row `i` has been written, every later stage keeps
that row of `L` unchanged. -/
private theorem lAtStableAfterProcessed (A : ModifiedCholeskyFactorization n) (i s : Fin n) :
    ∀ k : Nat, i.1 + 1 ≤ k → k ≤ n → A.LAt k i s = A.LAt (i.1 + 1) i s := by
  intro k hk _
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  clear hk
  induction t with
  | zero =>
      rfl
  | succ t iht =>
      by_cases hk : i.1 + 1 + t < n
      · have hk' : i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        have hprocessed : i < (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
          show i.1 < i.1 + 1 + t
          omega
        -- The current pivot lies strictly after row `i`, so that row of `L` is preserved.
        have hstep : A.LAt (i.1 + 1 + t + 1) i s = A.LAt (i.1 + 1 + t) i s := by
          calc
            A.LAt (i.1 + 1 + t + 1) i s
                = (step A.β A.δ ⟨i.1 + 1 + t, hk⟩ (A.stateAt (i.1 + 1 + t))).L i s := by
                    simp [LAt, stateAt, hk', Nat.add_assoc]
            _ = (A.stateAt (i.1 + 1 + t)).L i s := stepLApplyProcessed _ _ _ _ hprocessed
            _ = A.LAt (i.1 + 1 + t) i s := by
                  rfl
        have hbound : i.1 + 1 + t ≤ n := by omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)
      · have hk' : ¬ i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        -- After stage `n`, the recursion stops changing `L`.
        have hstep : A.LAt (i.1 + 1 + t + 1) i s = A.LAt (i.1 + 1 + t) i s := by
          simp [LAt, stateAt, hk', Nat.add_assoc]
        have hbound : i.1 + 1 + t ≤ n := by omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)

/-- Helper for Chapter03 Algorithm 3.3.2: later stages leave every fully processed
strict-lower working-matrix entry unchanged. -/
private theorem cAtStableAfterProcessed (A : ModifiedCholeskyFactorization n)
    (i s : Fin n) (hsi : s < i) :
    ∀ k : Nat, i.1 + 1 ≤ k → k ≤ n → A.CAt k i s = A.CAt (i.1 + 1) i s := by
  intro k hk _
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  clear hk
  induction t with
  | zero =>
      rfl
  | succ t iht =>
      by_cases hk : i.1 + 1 + t < n
      · have hk' : i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        have hprocessed : i < (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
          show i.1 < i.1 + 1 + t
          omega
        have hprocessed' : s < (⟨i.1 + 1 + t, hk⟩ : Fin n) := by
          show s.1 < i.1 + 1 + t
          omega
        -- Both indices are already processed before this later pivot, so the entry is fixed.
        have hstep : A.CAt (i.1 + 1 + t + 1) i s = A.CAt (i.1 + 1 + t) i s := by
          calc
            A.CAt (i.1 + 1 + t + 1) i s
                = (step A.β A.δ ⟨i.1 + 1 + t, hk⟩ (A.stateAt (i.1 + 1 + t))).C i s := by
                    simp [CAt, stateAt, hk', Nat.add_assoc]
            _ = (A.stateAt (i.1 + 1 + t)).C i s := stepCApplyProcessed _ _ _ _ hprocessed hprocessed'
            _ = A.CAt (i.1 + 1 + t) i s := by
                  rfl
        have hbound : i.1 + 1 + t ≤ n := by omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)
      · have hk' : ¬ i.1 + (1 + t) < n := by
          simpa [Nat.add_assoc] using hk
        -- After the final stage the state is constant.
        have hstep : A.CAt (i.1 + 1 + t + 1) i s = A.CAt (i.1 + 1 + t) i s := by
          simp [CAt, stateAt, hk', Nat.add_assoc]
        have hbound : i.1 + 1 + t ≤ n := by omega
        simpa [Nat.add_assoc] using hstep.trans (iht hbound)

/-- Helper for Chapter03 Algorithm 3.3.2: the repaired Step 5 leaves every untouched
off-diagonal tail entry equal to the swapped working matrix entry. -/
private theorem stepCApplyTailOffDiag {β δ : ℝ} (j i k : Fin n) (state : State n)
    (hji : j < i) (hjk : j < k) (hik : i ≠ k) :
    (step β δ j state).C i k =
      (state.C.submatrix (Equiv.swap j (pivotIndex state.C j))
        (Equiv.swap j (pivotIndex state.C j))) i k := by
  -- The repaired branch keeps off-diagonal tail entries unchanged after the symmetric pivot.
  have hi_ne : i ≠ j := ne_of_gt hji
  have hk_ne : k ≠ j := ne_of_gt hjk
  simp [step, hi_ne, hk_ne, hji, hjk, hik]

/-- Helper for Chapter03 Algorithm 3.3.2: the repaired Step 5 updates each strict-tail diagonal
entry by subtracting the square of the new pivot-column entry divided by `d_j`. -/
private theorem stepCApplyTailDiag {β δ : ℝ} (j i : Fin n) (state : State n)
    (hji : j < i) :
    (step β δ j state).C i i =
      (state.C.submatrix (Equiv.swap j (pivotIndex state.C j))
        (Equiv.swap j (pivotIndex state.C j))) i i -
        ((step β δ j state).C i j * (step β δ j state).C i j) / (step β δ j state).d j := by
  -- On the tail diagonal, the only new Step-5 correction is the scalar square update.
  have hi_ne : i ≠ j := ne_of_gt hji
  simp [step, hi_ne, hji]

/-- Helper for Chapter03 Algorithm 3.3.2: one Gill-Murray step preserves symmetry of the working
matrix. -/
private theorem stepPreservesSymm {β δ : ℝ} (j : Fin n) (state : State n)
    (hsymm : state.C.IsSymm) :
    (step β δ j state).C.IsSymm := by
  let q := pivotIndex state.C j
  let σ := Equiv.swap j q
  let Cswap := state.C.submatrix σ σ
  have hCswapSymm : Cswap.IsSymm := by
    -- The symmetric pivot is a simultaneous row/column reindex of the symmetric working matrix.
    simpa [Cswap, σ] using hsymm.submatrix σ
  -- Compare the updated matrix entrywise and split by the position of the active pivot `j`.
  refine Matrix.IsSymm.ext ?_
  intro i k
  by_cases hi : i = j
  · subst i
    by_cases hk : k = j
    · subst k
      simp [step]
    · simp [step, hk]
  by_cases hk : k = j
  · subst k
    simp [step, hi]
  by_cases hji : j < i
  · by_cases hjk : j < k
    · by_cases hik : i = k
      · subst hik
        rfl
      · have htail :
          (step β δ j state).C i k = Cswap i k := by
            simpa [Cswap, σ, q] using
              stepCApplyTailOffDiag (j := j) (i := i) (k := k) (state := state) hji hjk hik
        have htail' :
            (step β δ j state).C k i = Cswap k i := by
          have hki : k ≠ i := by
            simpa [eq_comm] using hik
          simpa [Cswap, σ, q] using
            stepCApplyTailOffDiag (j := j) (i := k) (k := i) (state := state) hjk hji hki
        calc
          (step β δ j state).C k i = Cswap k i := htail'
          _ = Cswap i k := hCswapSymm.apply i k
          _ = (step β δ j state).C i k := htail.symm
    · have hstepik : (step β δ j state).C i k = Cswap i k := by
        -- If `k` is not in the strict tail, Step 5 leaves this off-pivot entry untouched.
        simp [step, hi, hk, hji, hjk, Cswap, σ, q]
      have hstepki : (step β δ j state).C k i = Cswap k i := by
        have hnot : ¬ (j < k ∧ j < i) := by
          intro htail
          exact hjk htail.1
        simp [step, hk, hi, hji, hjk, hnot, Cswap, σ, q]
      calc
        (step β δ j state).C k i = Cswap k i := hstepki
        _ = Cswap i k := hCswapSymm.apply i k
        _ = (step β δ j state).C i k := hstepik.symm
  · by_cases hjk : j < k
    · have hstepik : (step β δ j state).C i k = Cswap i k := by
        have hnot : ¬ (j < i ∧ j < k) := by
          intro htail
          exact hji htail.1
        simp [step, hi, hk, hji, hjk, hnot, Cswap, σ, q]
      have hstepki : (step β δ j state).C k i = Cswap k i := by
        simp [step, hk, hi, hjk, hji, Cswap, σ, q]
      calc
        (step β δ j state).C k i = Cswap k i := hstepki
        _ = Cswap i k := hCswapSymm.apply i k
        _ = (step β δ j state).C i k := hstepik.symm
    · have hstepik : (step β δ j state).C i k = Cswap i k := by
        have hnot : ¬ (j < i ∧ j < k) := by
          intro htail
          exact hji htail.1
        simp [step, hi, hk, hji, hjk, hnot, Cswap, σ, q]
      have hstepki : (step β δ j state).C k i = Cswap k i := by
        have hnot : ¬ (j < k ∧ j < i) := by
          intro htail
          exact hjk htail.1
        simp [step, hk, hi, hjk, hji, hnot, Cswap, σ, q]
      calc
        (step β δ j state).C k i = Cswap k i := hstepki
        _ = Cswap i k := hCswapSymm.apply i k
        _ = (step β δ j state).C i k := hstepik.symm

/-- Helper for Chapter03 Algorithm 3.3.2: every stagewise working matrix remains symmetric. -/
private theorem cAtIsSymm (A : ModifiedCholeskyFactorization n) :
    ∀ k : Nat, k ≤ n → (A.CAt k).IsSymm := by
  intro k hk
  induction k with
  | zero =>
      -- The initial working matrix is exactly the symmetric input Hessian.
      simpa [CAt, stateAt, init] using A.symm
  | succ k ih =>
      have hklt : k < n := by omega
      have hkprev : k ≤ n := by omega
      -- The successor stage runs one Gill-Murray step from the previous symmetric state.
      simpa [CAt, stateAt, hklt] using
        stepPreservesSymm (β := A.β) (δ := A.δ) ⟨k, hklt⟩ (A.stateAt k) (ih hkprev)

/-- The terminal diagonal entries stay strictly positive because every stage takes
`d j = max δ (max |c_jj| (theta j ^ 2 / β ^ 2))` with `0 < δ`. -/
theorem d_pos (A : ModifiedCholeskyFactorization n) (i : Fin n) :
    0 < A.d i := by
  rcases processedDiagonalDataStable A i with ⟨hd, _⟩
  -- Rewriting to the stage where `d i` is created exposes the `max δ ...` formula.
  rw [hd, dAt_step_eq]
  exact lt_of_lt_of_le A.delta_pos (le_max_left _ _)

/-- The terminal diagonal correction is entrywise nonnegative. -/
theorem correction_nonneg (A : ModifiedCholeskyFactorization n) (i : Fin n) :
    0 ≤ A.e i := by
  rcases processedDiagonalDataStable A i with ⟨_, he⟩
  -- The correction is the safeguarded diagonal minus the current working diagonal entry.
  rw [he, eAt_step_eq]
  apply sub_nonneg.mpr
  rw [dAt_step_eq]
  calc
    A.CAt (i.1 + 1) i i ≤ |A.CAt (i.1 + 1) i i| := le_abs_self _
    _ ≤ max |A.CAt (i.1 + 1) i i| ((A.thetaAt (i.1 + 1) i) ^ 2 / A.β ^ 2) := le_max_left _ _
    _ ≤ max A.δ (max |A.CAt (i.1 + 1) i i| ((A.thetaAt (i.1 + 1) i) ^ 2 / A.β ^ 2)) :=
      le_max_right _ _

/-- Helper for Chapter03 Algorithm 3.3.2: when row `i` is created, every strict-lower entry is
stored as the matching working entry divided by the previously processed diagonal. -/
private theorem lAtStageLowerEqDiv (A : ModifiedCholeskyFactorization n) (i s : Fin n)
    (hsi : s < i) :
    A.LAt (i.1 + 1) i s = A.CAt (i.1 + 1) s i / A.dAt (i.1 + 1) s := by
  let q := pivotIndex (A.stateAt i.1).C i
  let σ := Equiv.swap i q
  let Cswap := (A.stateAt i.1).C.submatrix σ σ
  have hi : i.1 < n := i.is_lt
  have hs_ne : s ≠ i := ne_of_lt hsi
  have hstageSymm : (A.stateAt i.1).C.IsSymm := by
    simpa [CAt] using cAtIsSymm A i.1 (Nat.le_of_lt hi)
  have hCswapSymm : Cswap.IsSymm := by
    -- The pre-update working matrix is symmetric, so its swapped view is also symmetric.
    simpa [Cswap, σ] using hstageSymm.submatrix σ
  have hrow :
      A.LAt (i.1 + 1) i s = Cswap i s / A.dAt (i.1 + 1) s := by
    -- Unfold the single stage that creates row `i`.
    simp [LAt, dAt, stateAt, step, hi, hsi, hs_ne, Cswap, σ, q]
  have hcol :
      A.CAt (i.1 + 1) s i = Cswap s i := by
    -- The symmetric row write records the same stage-`i` entry in column `i`.
    simp [CAt, stateAt, step, hi, hsi.not_gt, Cswap, σ, q]
  -- Route correction: the numerator is produced from the swapped row formula, so symmetry of the
  -- swapped working matrix is the bridge back to the column-oriented `CAt` API.
  calc
    A.LAt (i.1 + 1) i s = Cswap i s / A.dAt (i.1 + 1) s := hrow
    _ = Cswap s i / A.dAt (i.1 + 1) s := by
      rw [← hCswapSymm.apply i s]
    _ = A.CAt (i.1 + 1) s i / A.dAt (i.1 + 1) s := by
      rw [hcol]

/-- Helper for Chapter03 Algorithm 3.3.2: when row `i` is created, its processed-column
coefficients are the pre-step pivot-row entries divided by the already stabilized diagonals. -/
private theorem lAtStageLowerEqDiv_prePivotRow (A : ModifiedCholeskyFactorization n)
    (i s : Fin n) (hsi : s < i) :
    A.LAt (i.1 + 1) i s =
      A.CAt i.1 (A.pivotAt (i.1 + 1) i) s / A.d s := by
  let q := A.pivotAt (i.1 + 1) i
  have hstageSymm :
      A.CAt (i.1 + 1) s i = A.CAt (i.1 + 1) i s := by
    -- The updated working matrix stays symmetric at the row-creation stage.
    exact (cAtIsSymm A (i.1 + 1) (Nat.succ_le_of_lt i.is_lt)).apply i s
  have hcreatedColumn :
      A.CAt (i.1 + 1) i s = A.CAt i.1 q s := by
    -- On a processed column, the new row reads the pre-step pivot row through the active swap.
    have hsymmPrev : (A.stateAt i.1).C.IsSymm := by
      simpa [CAt] using cAtIsSymm A i.1 (Nat.le_of_lt i.is_lt)
    have hraw :
        A.CAt (i.1 + 1) i s = A.CAt i.1 (pivotIndex (A.CAt i.1) i) s := by
      simpa [CAt, stateAt] using
        (stepCApplyProcessedColumn
          (β := A.β) (δ := A.δ) i i s (A.stateAt i.1) hsymmPrev hsi)
    simpa [q, pivotAt_step_eq A i] using hraw
  have hdstable : A.dAt (i.1 + 1) s = A.d s := by
    -- Every earlier processed diagonal entry is fixed once column `s` is completed.
    have hstage : A.dAt (i.1 + 1) s = A.dAt (s.1 + 1) s := by
      exact dAtStableAfterProcessed A s (i.1 + 1) (by omega) (by omega)
    rcases processedDiagonalDataStable A s with ⟨hd, _⟩
    exact hstage.trans hd.symm
  calc
    A.LAt (i.1 + 1) i s = A.CAt (i.1 + 1) s i / A.dAt (i.1 + 1) s :=
      lAtStageLowerEqDiv A i s hsi
    _ = A.CAt (i.1 + 1) i s / A.dAt (i.1 + 1) s := by
      rw [hstageSymm]
    _ = A.CAt i.1 q s / A.dAt (i.1 + 1) s := by
      rw [hcreatedColumn]
    _ = A.CAt i.1 q s / A.d s := by
      rw [hdstable]
    _ = A.CAt i.1 (A.pivotAt (i.1 + 1) i) s / A.d s := by
      rfl

/-- Helper for Chapter03 Algorithm 3.3.2: when stage `i` creates column `i`, the new strict-lower
entry at row `i` is the pre-step pivot-row entry in the processed column `j`. -/
private theorem cAtStageCreatedColumn_prePivotRow (A : ModifiedCholeskyFactorization n)
    (i j : Fin n) (hji : j < i) :
    A.CAt (i.1 + 1) i j = A.CAt i.1 (A.pivotAt (i.1 + 1) i) j := by
  let q := A.pivotAt (i.1 + 1) i
  have hsymmPrev : (A.stateAt i.1).C.IsSymm := by
    simpa [CAt] using cAtIsSymm A i.1 (Nat.le_of_lt i.is_lt)
  -- The freshly created column is the old pivot column viewed through the active swap.
  have hraw :
      A.CAt (i.1 + 1) i j = A.CAt i.1 (pivotIndex (A.CAt i.1) i) j := by
    simpa [CAt, stateAt] using
      (stepCApplyProcessedColumn
        (β := A.β) (δ := A.δ) i i j (A.stateAt i.1) hsymmPrev hji)
  simpa [q, pivotAt_step_eq A i] using hraw

/-- Helper for Chapter03 Algorithm 3.3.2: the terminal pivot-ordered input entry in a processed
column rewrites at the creation stage to the corresponding pre-step pivot-row input entry. -/
private theorem reindexInputStageCreatedColumn_prePivotRow (A : ModifiedCholeskyFactorization n)
    (i j : Fin n) (hji : j < i) :
    Matrix.reindex (A.permAt (i.1 + 1)) (A.permAt (i.1 + 1)) A.G i j =
      Matrix.reindex (A.permAt i.1) (A.permAt i.1) A.G (A.pivotAt (i.1 + 1) i) j := by
  -- The processed column index `j` is fixed by the active swap, so only the pivot row moves.
  simpa using reindexInputAtStep_processedColumn A i i j hji

/-- Helper for Chapter03 Algorithm 3.3.2: the diagonal input entry created at stage `i`
is exactly the pre-step pivot-row diagonal entry. -/
private theorem reindexInputStageCreatedDiag_prePivotRow (A : ModifiedCholeskyFactorization n)
    (i : Fin n) :
    Matrix.reindex (A.permAt (i.1 + 1)) (A.permAt (i.1 + 1)) A.G i i =
      Matrix.reindex (A.permAt i.1) (A.permAt i.1) A.G
        (A.pivotAt (i.1 + 1) i) (A.pivotAt (i.1 + 1) i) := by
  -- The active swap sends the new row index `i` back to the pre-step pivot row.
  rw [Matrix.reindex_apply, Matrix.reindex_apply, permAt_step_eq, pivotAt_step_eq]
  simp

/-- Helper for Chapter03 Algorithm 3.3.2: the diagonal working entry created at stage `i`
is the pre-step pivot-row diagonal entry. -/
private theorem cAtStageCreatedDiag_prePivotRow (A : ModifiedCholeskyFactorization n)
    (i : Fin n) :
    A.CAt (i.1 + 1) i i =
      A.CAt i.1 (A.pivotAt (i.1 + 1) i) (A.pivotAt (i.1 + 1) i) := by
  have hi : i.1 < n := i.is_lt
  -- Unfolding the single row-creation step shows that the diagonal is read from the pivot row.
  rw [pivotAt_step_eq A i]
  simp [CAt, stateAt, step, hi]

/-- Helper for Chapter03 Algorithm 3.3.2: the algorithm writes `1` on the diagonal of each new
row of `L`. -/
private theorem lAtStageDiag (A : ModifiedCholeskyFactorization n) (i : Fin n) :
    A.LAt (i.1 + 1) i i = 1 := by
  -- The stage-local row formula sets the pivot entry to `1`.
  have hi : i.1 < n := i.is_lt
  unfold LAt
  simp [stateAt, hi, step]

/-- Helper for Chapter03 Algorithm 3.3.2: when row `i` is created, every entry strictly to its
right is `0`. -/
private theorem lAtStageUpperZero (A : ModifiedCholeskyFactorization n) (i s : Fin n)
    (his : i < s) :
    A.LAt (i.1 + 1) i s = 0 := by
  -- The stage-local row formula only fills columns strictly before the pivot row.
  have hi : i.1 < n := i.is_lt
  have hs_ne : s ≠ i := ne_of_gt his
  unfold LAt
  simp [stateAt, hi, step, hs_ne, his.not_gt]

/-- Helper for Chapter03 Algorithm 3.3.2: the terminal factor keeps `1` on its diagonal. -/
private theorem l_diag (A : ModifiedCholeskyFactorization n) (i : Fin n) :
    A.L i i = 1 := by
  -- Later pivots do not rewrite an already processed row.
  have hstable := lAtStableAfterProcessed A i i n (Nat.succ_le_of_lt i.is_lt) le_rfl
  simpa [L] using hstable.trans (lAtStageDiag A i)

/-- Helper for Chapter03 Algorithm 3.3.2: the terminal factor is zero strictly above the
diagonal. -/
private theorem l_upperZero (A : ModifiedCholeskyFactorization n) (i s : Fin n)
    (his : i < s) :
    A.L i s = 0 := by
  -- The stage that creates row `i` writes `0` to every later column, and that row then stays fixed.
  have hstable := lAtStableAfterProcessed A i s n (Nat.succ_le_of_lt i.is_lt) le_rfl
  simpa [L] using hstable.trans (lAtStageUpperZero A i s his)

/-- Helper for Chapter03 Algorithm 3.3.2: every strict-lower terminal working entry equals the
corresponding factor entry times the processed diagonal. -/
private theorem c_eq_mulDiag (A : ModifiedCholeskyFactorization n) (i s : Fin n)
    (hsi : s < i) :
    A.C i s = A.L i s * A.d s := by
  -- First move every term back to the stage where row `i` is written.
  have hCstable := cAtStableAfterProcessed A i s hsi n (Nat.succ_le_of_lt i.is_lt) le_rfl
  have hLstable := lAtStableAfterProcessed A i s n (Nat.succ_le_of_lt i.is_lt) le_rfl
  have hdstable :
      A.dAt (i.1 + 1) s = A.d s := by
    have hstage : A.dAt (i.1 + 1) s = A.dAt (s.1 + 1) s := by
      exact dAtStableAfterProcessed A s (i.1 + 1) (by omega) (by omega)
    rcases processedDiagonalDataStable A s with ⟨hd, _⟩
    exact hstage.trans hd.symm
  have hstage := lAtStageLowerEqDiv A i s hsi
  have hdne : A.dAt (i.1 + 1) s ≠ 0 := by
    rw [hdstable]
    exact (A.d_pos s).ne'
  have hstageSymm : A.CAt (i.1 + 1) s i = A.CAt (i.1 + 1) i s := by
    -- At the stage that writes row `i`, the symmetric row/column pair is filled from the same `Cj s`.
    have hi : i.1 < n := i.is_lt
    have hs_ne : s ≠ i := ne_of_lt hsi
    have hs_not : ¬ i < s := by
      exact not_lt_of_gt hsi
    unfold CAt
    simp [stateAt, hi, step, hs_ne, hs_not]
  -- Clearing the nonzero denominator turns the stage-local quotient into the desired product.
  have hmul : A.CAt (i.1 + 1) i s = A.LAt (i.1 + 1) i s * A.dAt (i.1 + 1) s := by
    rw [← hstageSymm, hstage]
    field_simp [hdne]
  calc
    A.C i s = A.CAt (i.1 + 1) i s := by simpa [C] using hCstable
    _ = A.LAt (i.1 + 1) i s * A.dAt (i.1 + 1) s := hmul
    _ = A.L i s * A.d s := by
          rw [hdstable]
          simpa [L] using congrArg (fun x ↦ x * A.d s) hLstable.symm

/-- Helper for Chapter03 Algorithm 3.3.2: each entry of `L D Lᵀ` is the columnwise sum
`∑ s, L i s * d s * L j s`. -/
private theorem modifiedCholeskySystemMatrix_apply (L : Hessian) (D : Fin n → ℝ)
    (i j : Fin n) :
    modifiedCholeskySystemMatrix L D i j = ∑ s : Fin n, L i s * D s * L j s := by
  -- Expanding the two matrix products and collapsing the diagonal factor isolates one column
  -- contribution at a time.
  rw [modifiedCholeskySystemMatrix, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.mul_apply]
  simp [Matrix.diagonal_apply, mul_assoc]

/-- Helper for Chapter03 Algorithm 3.3.2: every `L D Lᵀ` matrix is symmetric. -/
private theorem modifiedCholeskySystemMatrix_isSymm (A : ModifiedCholeskyFactorization n) :
    (modifiedCholeskySystemMatrix A.L A.d).IsSymm := by
  -- The entry formula is symmetric in `i` and `j` because the diagonal contribution is scalar.
  refine Matrix.IsSymm.ext ?_
  intro i j
  rw [modifiedCholeskySystemMatrix_apply, modifiedCholeskySystemMatrix_apply]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Helper for Chapter03 Algorithm 3.3.2: on a strict-lower entry, `L D Lᵀ` expands as the
terminal working entry plus the previously processed column contributions. -/
private theorem modifiedCholeskySystemMatrix_lowerEntry (A : ModifiedCholeskyFactorization n)
    (i j : Fin n) (hji : j < i) :
    modifiedCholeskySystemMatrix A.L A.d i j =
      A.C i j +
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j)) (fun s ↦ A.L i s * A.C j s) := by
  classical
  -- Expand the matrix product, then isolate the unique nonzero term with `s = j`.
  rw [modifiedCholeskySystemMatrix_apply]
  have hsplit :
      (∑ s : Fin n, A.L i s * A.d s * A.L j s) =
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
            (fun s ↦ A.L i s * A.d s * A.L j s) +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ ¬ s < j))
            (fun s ↦ A.L i s * A.d s * A.L j s) := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun s : Fin n ↦ s < j) (f := fun s ↦ A.L i s * A.d s * A.L j s)).symm
  rw [hsplit]
  have htail :
      Finset.sum (Finset.univ.filter (fun s : Fin n ↦ ¬ s < j))
          (fun s ↦ A.L i s * A.d s * A.L j s) =
        A.L i j * A.d j * A.L j j := by
    -- Every `s > j` term vanishes because row `j` of `L` is zero strictly above the diagonal.
    refine Finset.sum_eq_single_of_mem j ?_ ?_
    · simp
    · intro s hs hsne
      have hs_not_lt : ¬ s < j := (Finset.mem_filter.mp hs).2
      have hjs : j < s := lt_of_le_of_ne (le_of_not_gt hs_not_lt) hsne.symm
      simp [l_upperZero A j s hjs]
  rw [htail]
  have hsum :
      Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
          (fun s ↦ A.L i s * A.d s * A.L j s) =
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
          (fun s ↦ A.L i s * A.C j s) := by
    -- On processed columns, `C j s = L j s * d s`.
    apply Finset.sum_congr rfl
    intro s hs
    have hsj : s < j := (Finset.mem_filter.mp hs).2
    calc
      A.L i s * A.d s * A.L j s = A.L i s * (A.L j s * A.d s) := by ring
      _ = A.L i s * A.C j s := by rw [c_eq_mulDiag A j s hsj]
  rw [hsum]
  -- The isolated `s = j` contribution is exactly the terminal strict-lower working entry.
  calc
    Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
        (fun s ↦ A.L i s * A.C j s) +
        A.L i j * A.d j * A.L j j
        =
      Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
          (fun s ↦ A.L i s * A.C j s) + A.C i j := by
          rw [l_diag A j, mul_one, c_eq_mulDiag A i j hji]
    _ = A.C i j +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
            (fun s ↦ A.L i s * A.C j s) := by
          ring

/-- Helper for Chapter03 Algorithm 3.3.2: on a diagonal entry, `L D Lᵀ` expands as the
processed diagonal term plus the earlier column contributions. -/
private theorem modifiedCholeskySystemMatrix_diagEntry (A : ModifiedCholeskyFactorization n)
    (i : Fin n) :
    modifiedCholeskySystemMatrix A.L A.d i i =
      A.d i +
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i)) (fun s ↦ A.L i s * A.C i s) := by
  classical
  -- Expand the matrix product, then isolate the unique surviving `s = i` diagonal term.
  rw [modifiedCholeskySystemMatrix_apply]
  have hsplit :
      (∑ s : Fin n, A.L i s * A.d s * A.L i s) =
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
            (fun s ↦ A.L i s * A.d s * A.L i s) +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ ¬ s < i))
            (fun s ↦ A.L i s * A.d s * A.L i s) := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun s : Fin n ↦ s < i) (f := fun s ↦ A.L i s * A.d s * A.L i s)).symm
  rw [hsplit]
  have htail :
      Finset.sum (Finset.univ.filter (fun s : Fin n ↦ ¬ s < i))
          (fun s ↦ A.L i s * A.d s * A.L i s) =
        A.L i i * A.d i * A.L i i := by
    -- Every `s > i` term vanishes because row `i` is zero strictly above its diagonal.
    refine Finset.sum_eq_single_of_mem i ?_ ?_
    · simp
    · intro s hs hsne
      have hs_not_lt : ¬ s < i := (Finset.mem_filter.mp hs).2
      have his : i < s := lt_of_le_of_ne (le_of_not_gt hs_not_lt) hsne.symm
      simp [l_upperZero A i s his]
  rw [htail]
  have hsum :
      Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
          (fun s ↦ A.L i s * A.d s * A.L i s) =
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
          (fun s ↦ A.L i s * A.C i s) := by
    -- On earlier processed columns, `C i s = L i s * d s`.
    apply Finset.sum_congr rfl
    intro s hs
    have hsi : s < i := (Finset.mem_filter.mp hs).2
    calc
      A.L i s * A.d s * A.L i s = A.L i s * (A.L i s * A.d s) := by ring
      _ = A.L i s * A.C i s := by rw [c_eq_mulDiag A i s hsi]
  rw [hsum]
  -- The isolated diagonal term reduces to `d i` because `L i i = 1`.
  calc
    Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
        (fun s ↦ A.L i s * A.C i s) +
        A.L i i * A.d i * A.L i i
        =
      Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
          (fun s ↦ A.L i s * A.C i s) + A.d i := by
          rw [l_diag A i]
          ring
    _ = A.d i +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
            (fun s ↦ A.L i s * A.C i s) := by
          ring

/-- Helper for Chapter03 Algorithm 3.3.2: the final corrected matrix in pivot order stays
symmetric. -/
private theorem permutedCorrectedMatrix_isSymm (A : ModifiedCholeskyFactorization n) :
    A.permutedCorrectedMatrix.IsSymm := by
  -- Reindexing preserves the input symmetry, and the correction term is diagonal.
  simpa [permutedCorrectedMatrix] using
    (A.symm.reindex A.perm).add (Matrix.isSymm_diagonal A.e)

/-- Helper for Chapter03 Algorithm 3.3.2: reindexing the input matrix across one step applies
the active pivot swap to both row and column indices in the previous pivot order. -/
private theorem reindexInputAtStep_tailEntry (A : ModifiedCholeskyFactorization n)
    (j r u : Fin n) :
    Matrix.reindex (A.permAt (j.1 + 1)) (A.permAt (j.1 + 1)) A.G r u =
      Matrix.reindex (A.permAt j.1) (A.permAt j.1) A.G
        ((Equiv.swap j (A.pivotAt (j.1 + 1) j)) r)
        ((Equiv.swap j (A.pivotAt (j.1 + 1) j)) u) := by
  -- `Matrix.reindex` sees the inverse cumulative permutation, so one more step pulls both
  -- coordinates back through the active pivot swap.
  rw [Matrix.reindex_apply, Matrix.reindex_apply, permAt_step_eq A j]
  simp

/-- Helper for Chapter03 Algorithm 3.3.2: the active pivot swap keeps every tail index inside
the current tail. -/
private theorem swapPivotPreservesTail (A : ModifiedCholeskyFactorization n)
    (j r : Fin n) (hjr : j ≤ r) :
    j ≤ (Equiv.swap j (A.pivotAt (j.1 + 1) j)) r := by
  let q := A.pivotAt (j.1 + 1) j
  by_cases hrq : r = q
  · subst hrq
    simp [q]
  · by_cases hrj : r = j
    · rw [hrj]
      have hq : j ≤ q := by
        simpa [q, pivotAt_step_eq A j] using le_pivotIndex (A.CAt j.1) j
      simpa [q]
    · simp [Equiv.swap_apply_def, q, hrj, hrq, hjr]

/-- Helper for Chapter03 Algorithm 3.3.2: a strict-tail row cannot be sent to the pivot row by
the active swap. -/
private theorem swapPivotTailNePivot (A : ModifiedCholeskyFactorization n)
    (j r : Fin n) (hjr : j < r) :
    (Equiv.swap j (A.pivotAt (j.1 + 1) j)) r ≠ A.pivotAt (j.1 + 1) j := by
  -- If the swapped row landed on the pivot image `σ j`, injectivity would force `r = j`.
  intro h
  have hσj :
      (Equiv.swap j (A.pivotAt (j.1 + 1) j)) j = A.pivotAt (j.1 + 1) j := by
    simp
  have : r = j := by
    exact (Equiv.swap j (A.pivotAt (j.1 + 1) j)).injective (h.trans hσj.symm)
  exact (ne_of_gt hjr) this

/-- Helper for Chapter03 Algorithm 3.3.2: before a tail row is processed, every off-diagonal
tail entry in the pivot-ordered input still matches the current working matrix entry. -/
private theorem reindexedInputTailOffDiagAt (A : ModifiedCholeskyFactorization n) :
    ∀ k, k ≤ n → ∀ r u : Fin n, k ≤ r → k ≤ u → r ≠ u →
      Matrix.reindex (A.permAt k) (A.permAt k) A.G r u = A.CAt k r u := by
  intro k
  induction k with
  | zero =>
      intro _ r u _ _ _
      -- At stage `0`, the pivot order is trivial and the working matrix is the input matrix.
      simp [permAt, CAt, stateAt, init]
  | succ k ih =>
      intro hk r u hkr hku hru
      have hklt : k < n := by omega
      let j : Fin n := ⟨k, hklt⟩
      let σ := Equiv.swap j (A.pivotAt (k + 1) j)
      have hjr : j < r := by
        show k < r.1
        omega
      have hju : j < u := by
        show k < u.1
        omega
      have hσrFin : j ≤ σ r := swapPivotPreservesTail A j r (by exact Nat.le_of_succ_le hkr)
      have hσuFin : j ≤ σ u := swapPivotPreservesTail A j u (by exact Nat.le_of_succ_le hku)
      have hσr : k ≤ (σ r).1 := by
        exact hσrFin
      have hσu : k ≤ (σ u).1 := by
        exact hσuFin
      have hσru : σ r ≠ σ u := fun h ↦ hru (σ.injective h)
      have hinput :
          Matrix.reindex (A.permAt (k + 1)) (A.permAt (k + 1)) A.G r u =
            Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) (σ u) := by
        -- One step just pulls the two active-tail indices back through the symmetric swap.
        simpa [j, σ] using reindexInputAtStep_tailEntry A j r u
      have hstep :
          A.CAt (k + 1) r u = A.CAt k (σ r) (σ u) := by
        -- Off-diagonal tail entries are unaffected by the rank-one update itself.
        simpa [CAt, stateAt, hklt, j, σ, pivotAt_step_eq A j] using
          stepCApplyTailOffDiag
            (β := A.β) (δ := A.δ) (j := j) (i := r) (k := u) (state := A.stateAt k)
            hjr hju hru
      calc
        Matrix.reindex (A.permAt (k + 1)) (A.permAt (k + 1)) A.G r u =
            Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) (σ u) := hinput
        _ = A.CAt k (σ r) (σ u) := ih (Nat.le_of_lt hklt) (σ r) (σ u) hσr hσu hσru
        _ = A.CAt (k + 1) r u := hstep.symm

/-- Helper for Chapter03 Algorithm 3.3.2: the canonical `Fin`-stage version of the active-tail
off-diagonal input invariant. -/
private theorem reindexedInputTailOffDiag (A : ModifiedCholeskyFactorization n)
    (j r u : Fin n) (hjr : j ≤ r) (hju : j ≤ u) (hru : r ≠ u) :
    Matrix.reindex (A.permAt j.1) (A.permAt j.1) A.G r u = A.CAt j.1 r u := by
  -- This is the stage-`j` specialization of the natural-number induction above.
  exact reindexedInputTailOffDiagAt A j.1 (Nat.le_of_lt j.is_lt) r u hjr hju hru

/-- Helper for Chapter03 Algorithm 3.3.2: before a tail row is processed, every processed-column
input entry satisfies the stagewise Schur-complement quotient formula. -/
private theorem reindexedInputTailLowerQuotientAt (A : ModifiedCholeskyFactorization n) :
    ∀ k, k ≤ n → ∀ r s : Fin n, s.1 < k → k ≤ r →
      Matrix.reindex (A.permAt k) (A.permAt k) A.G r s =
        A.CAt k r s +
          Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < s))
            (fun t ↦ (A.CAt k r t / A.d t) * A.CAt k s t) := by
  intro k
  induction k with
  | zero =>
      intro _ r s hsk _
      have : False := by omega
      exact this.elim
  | succ k ih =>
      intro hk r s hsk hkr
      have hklt : k < n := by omega
      let j : Fin n := ⟨k, hklt⟩
      let q := A.pivotAt (k + 1) j
      let σ := Equiv.swap j q
      have hjr : j < r := by
        show k < r.1
        omega
      have hsymmPrev : (A.stateAt k).C.IsSymm := by
        simpa [CAt] using cAtIsSymm A k (Nat.le_of_lt hklt)
      by_cases hsj : s = j
      · subst hsj
        have hσr : j ≤ σ r := swapPivotPreservesTail A j r (le_of_lt hjr)
        have hq : j ≤ q := by
          simpa [j, q, pivotAt_step_eq A j] using le_pivotIndex (A.CAt k) j
        have hσrq : σ r ≠ q := by
          simpa [j, q, σ] using swapPivotTailNePivot A j r hjr
        have hinput :
            Matrix.reindex (A.permAt (k + 1)) (A.permAt (k + 1)) A.G r j =
              Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) q := by
          -- The newly created column `j` comes from the pre-step pivot column.
          simpa [j, q, σ] using reindexInputAtStep_tailEntry A j r j
        have hrawInput :
            Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) q =
              A.CAt k (σ r) q := by
          -- That pivot column is still a raw tail entry before the current row is processed.
          exact reindexedInputTailOffDiag A j (σ r) q hσr hq hσrq
        have hcurrentRaw :
            A.CAt (k + 1) r j =
              A.CAt k (σ r) q -
                Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                  (fun t ↦ (A.CAt k q t / A.dAt k t) * A.CAt k (σ r) t) := by
          -- The new pivot column subtracts the previously processed Schur-complement terms.
          have hstate :
              (step A.β A.δ j (A.stateAt k)).C r j =
                (A.stateAt k).C (σ r) q -
                  Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                    (fun t ↦ ((A.stateAt k).C q t / A.dAt k t) * (A.stateAt k).C (σ r) t) := by
            simp [step, j, q, σ, pivotAt_step_eq A j, hjr]
            refine congrArg
              (fun z ↦
                (A.stateAt k).C ((Equiv.swap j (pivotIndex (A.CAt k) j)) r)
                    (pivotIndex (A.CAt k) j) - z) ?_
            apply Finset.sum_congr rfl
            intro x hx
            have hxj : x < j := (Finset.mem_filter.mp hx).2
            have hxq : x ≠ q := by
              intro hxq
              exact (not_le_of_gt hxj) (hxq ▸ hq)
            rw [if_neg (ne_of_lt hxj), if_pos hxj]
            have hxPivotCAt : x ≠ pivotIndex (A.CAt k) j := by
              intro hxPivot
              apply hxq
              calc
                x = pivotIndex (A.CAt k) j := hxPivot
                _ = A.pivotAt (k + 1) j := by
                      symm
                      exact pivotAt_step_eq A j
            have hxPivot : x ≠ pivotIndex (A.stateAt k).C j := by
              simpa [CAt] using hxPivotCAt
            have hswapState :
                (Equiv.swap j (pivotIndex (A.stateAt k).C j)) x = x := by
              rw [Equiv.swap_apply_def, if_neg (ne_of_lt hxj), if_neg hxPivot]
            rw [hswapState]
            simpa [CAt, dAt]
          calc
            A.CAt (k + 1) r j = (step A.β A.δ j (A.stateAt k)).C r j := by
              simpa [j, CAt, stateAt, hklt]
            _ =
                (A.stateAt k).C (σ r) q -
                  Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                    (fun t ↦ ((A.stateAt k).C q t / A.dAt k t) * (A.stateAt k).C (σ r) t) := hstate
            _ =
                A.CAt k (σ r) q -
                  Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                    (fun t ↦ (A.CAt k q t / A.dAt k t) * A.CAt k (σ r) t) := by
                      rfl
        have hcurrent :
            A.CAt (k + 1) r j =
              A.CAt k (σ r) q -
                Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                  (fun t ↦ (A.CAt k q t / A.d t) * A.CAt k (σ r) t) := by
          -- Every denominator in the processed block has already stabilized to the terminal `d`.
          calc
            A.CAt (k + 1) r j =
                A.CAt k (σ r) q -
                  Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                    (fun t ↦ (A.CAt k q t / A.dAt k t) * A.CAt k (σ r) t) := hcurrentRaw
            _ =
                A.CAt k (σ r) q -
                  Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                    (fun t ↦ (A.CAt k q t / A.d t) * A.CAt k (σ r) t) := by
                  refine congrArg (fun z ↦ A.CAt k (σ r) q - z) ?_
                  apply Finset.sum_congr rfl
                  intro t ht
                  have htj : t < j := (Finset.mem_filter.mp ht).2
                  have hdt :
                      A.dAt k t = A.d t := by
                    have hstage : A.dAt k t = A.dAt (t.1 + 1) t := by
                      exact dAtStableAfterProcessed A t k (by omega) (Nat.le_of_lt hklt)
                    rcases processedDiagonalDataStable A t with ⟨hd, _⟩
                    exact hstage.trans hd.symm
                  rw [hdt]
        have hsum :
            Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                (fun t ↦ (A.CAt k q t / A.d t) * A.CAt k (σ r) t) =
              Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                (fun t ↦ (A.CAt (k + 1) r t / A.d t) * A.CAt (k + 1) j t) := by
          -- Each processed-column term is recorded in the new row `j` and transported on row `r`.
          apply Finset.sum_congr rfl
          intro t ht
          have htj : t < j := (Finset.mem_filter.mp ht).2
          have hrt :
              A.CAt (k + 1) r t = A.CAt k (σ r) t := by
            simpa [CAt, stateAt, hklt, j, q, σ, pivotAt_step_eq A j] using
              stepCApplyProcessedColumn
                (β := A.β) (δ := A.δ) (j := j) (i := r) (s := t) (state := A.stateAt k)
                hsymmPrev htj
          have hjt :
              A.CAt (k + 1) j t = A.CAt k q t := by
            simpa [j, q] using cAtStageCreatedColumn_prePivotRow A j t htj
          calc
            (A.CAt k q t / A.d t) * A.CAt k (σ r) t =
                (A.CAt (k + 1) j t / A.d t) * A.CAt (k + 1) r t := by
                  rw [hjt, hrt]
            _ = (A.CAt (k + 1) r t / A.d t) * A.CAt (k + 1) j t := by
                  ring
        calc
          Matrix.reindex (A.permAt (k + 1)) (A.permAt (k + 1)) A.G r j =
              Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) q := hinput
          _ = A.CAt k (σ r) q := hrawInput
          _ =
              A.CAt (k + 1) r j +
                Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                  (fun t ↦ (A.CAt k q t / A.d t) * A.CAt k (σ r) t) := by
                    rw [hcurrent]
                    ring
          _ =
              A.CAt (k + 1) r j +
                Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
                  (fun t ↦ (A.CAt (k + 1) r t / A.d t) * A.CAt (k + 1) j t) := by
                    rw [hsum]
      · have hsj : s < j := by
          have hs_le : s ≤ j := by
            show s.1 ≤ k
            exact Nat.lt_succ_iff.mp hsk
          exact lt_of_le_of_ne hs_le hsj
        have hσrFin : j ≤ σ r := swapPivotPreservesTail A j r (by exact Nat.le_of_succ_le hkr)
        have hσr : k ≤ (σ r).1 := by
          exact hσrFin
        have hinput :
            Matrix.reindex (A.permAt (k + 1)) (A.permAt (k + 1)) A.G r s =
              Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) s := by
          -- An already processed column is fixed by the active swap on the column side.
          simpa [j, q, σ] using reindexInputAtStep_processedColumn A j r s hsj
        have hrow :
            A.CAt (k + 1) r s = A.CAt k (σ r) s := by
          -- The same processed-column transport controls the working matrix.
          simpa [CAt, stateAt, hklt, j, q, σ, pivotAt_step_eq A j] using
            stepCApplyProcessedColumn
              (β := A.β) (δ := A.δ) (j := j) (i := r) (s := s) (state := A.stateAt k)
              hsymmPrev hsj
        have hsum :
            Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < s))
                (fun t ↦ (A.CAt k (σ r) t / A.d t) * A.CAt k s t) =
              Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < s))
                (fun t ↦ (A.CAt (k + 1) r t / A.d t) * A.CAt (k + 1) s t) := by
          -- Old processed columns stay in the same owner normal form after the step.
          apply Finset.sum_congr rfl
          intro t ht
          have hts : t < s := (Finset.mem_filter.mp ht).2
          have htj : t < j := lt_trans hts hsj
          have hrt :
              A.CAt (k + 1) r t = A.CAt k (σ r) t := by
            simpa [CAt, stateAt, hklt, j, q, σ, pivotAt_step_eq A j] using
              stepCApplyProcessedColumn
                (β := A.β) (δ := A.δ) (j := j) (i := r) (s := t) (state := A.stateAt k)
                hsymmPrev htj
          have hst :
              A.CAt (k + 1) s t = A.CAt k s t := by
            simpa [CAt, stateAt, hklt, j, q, σ, pivotAt_step_eq A j] using
              stepCApplyProcessed
                (β := A.β) (δ := A.δ) (j := j) (i := s) (s := t) (state := A.stateAt k)
                hsj htj
          rw [hrt, hst]
        calc
          Matrix.reindex (A.permAt (k + 1)) (A.permAt (k + 1)) A.G r s =
              Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) s := hinput
          _ =
              A.CAt k (σ r) s +
                Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < s))
                  (fun t ↦ (A.CAt k (σ r) t / A.d t) * A.CAt k s t) := by
                    exact ih (Nat.le_of_lt hklt) (σ r) s (by
                      show s.1 < k
                      exact hsj) hσr
          _ =
              A.CAt (k + 1) r s +
                Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < s))
                  (fun t ↦ (A.CAt k (σ r) t / A.d t) * A.CAt k s t) := by
                    rw [hrow]
          _ =
              A.CAt (k + 1) r s +
                Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < s))
                  (fun t ↦ (A.CAt (k + 1) r t / A.d t) * A.CAt (k + 1) s t) := by
                    rw [hsum]

/-- Helper for Chapter03 Algorithm 3.3.2: the canonical `Fin`-stage version of the active-tail
processed-column quotient invariant. -/
private theorem reindexedInputTailLowerQuotient (A : ModifiedCholeskyFactorization n)
    (j r s : Fin n) (hsj : s < j) (hjr : j ≤ r) :
    Matrix.reindex (A.permAt j.1) (A.permAt j.1) A.G r s =
      A.CAt j.1 r s +
        Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < s))
          (fun t ↦ (A.CAt j.1 r t / A.d t) * A.CAt j.1 s t) := by
  -- This is the stage-`j` specialization of the natural-number induction above.
  simpa using
    reindexedInputTailLowerQuotientAt A j.1 (Nat.le_of_lt j.is_lt) r s (by simpa using hsj) hjr

/-- Helper for Chapter03 Algorithm 3.3.2: before a tail row is processed, its diagonal input
entry satisfies the stagewise Schur-complement quotient formula. -/
private theorem reindexedInputTailDiagQuotientAt (A : ModifiedCholeskyFactorization n) :
    ∀ k, k ≤ n → ∀ r : Fin n, k ≤ r →
      Matrix.reindex (A.permAt k) (A.permAt k) A.G r r =
        A.CAt k r r +
          Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t.1 < k))
            (fun t ↦ (A.CAt k r t / A.d t) * A.CAt k r t) := by
  intro k
  induction k with
  | zero =>
      intro _ r _
      -- At stage `0`, there are no processed columns, so the diagonal formula is tautological.
      simp [permAt, CAt, stateAt, init]
  | succ k ih =>
      intro hk r hkr
      have hklt : k < n := by omega
      let j : Fin n := ⟨k, hklt⟩
      let q := A.pivotAt (k + 1) j
      let σ := Equiv.swap j q
      let f : Fin n → ℝ := fun t ↦ (A.CAt (k + 1) r t / A.d t) * A.CAt (k + 1) r t
      have hjr : j < r := by
        show k < r.1
        omega
      have hσrFin : j ≤ σ r := swapPivotPreservesTail A j r (by exact Nat.le_of_succ_le hkr)
      have hσr : k ≤ (σ r).1 := by
        exact hσrFin
      have hinput :
          Matrix.reindex (A.permAt (k + 1)) (A.permAt (k + 1)) A.G r r =
            Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) (σ r) := by
        -- The diagonal input entry is transported by the active swap exactly as in the
        -- off-diagonal tail case.
        simpa [j, q, σ] using reindexInputAtStep_tailEntry A j r r
      have hdiagRaw :
          A.CAt (k + 1) r r =
            A.CAt k (σ r) (σ r) -
              ((A.CAt (k + 1) r j * A.CAt (k + 1) r j) / A.dAt (k + 1) j) := by
        -- The new diagonal equals the swapped old diagonal minus the square update.
        simpa [CAt, dAt, stateAt, hklt, j, q, σ, pivotAt_step_eq A j] using
          stepCApplyTailDiag
            (β := A.β) (δ := A.δ) (j := j) (i := r) (state := A.stateAt k) hjr
      have hdj : A.dAt (k + 1) j = A.d j := by
        rcases processedDiagonalDataStable A j with ⟨hd, _⟩
        exact hd.symm
      have hdiag :
          A.CAt (k + 1) r r =
            A.CAt k (σ r) (σ r) -
              ((A.CAt (k + 1) r j * A.CAt (k + 1) r j) / A.d j) := by
        rw [hdj] at hdiagRaw
        exact hdiagRaw
      have hsumOld :
          Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t.1 < k))
              (fun t ↦ (A.CAt k (σ r) t / A.d t) * A.CAt k (σ r) t) =
            Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t.1 < k)) f := by
        -- Every previously processed column is transported on row `r` by the processed-column API.
        apply Finset.sum_congr rfl
        intro t ht
        have htk : t.1 < k := (Finset.mem_filter.mp ht).2
        have hrt :
            A.CAt (k + 1) r t = A.CAt k (σ r) t := by
          have htj : t < j := by
            show t.1 < k
            exact htk
          simpa [CAt, stateAt, hklt, j, q, σ, pivotAt_step_eq A j] using
            stepCApplyProcessedColumn
              (β := A.β) (δ := A.δ) (j := j) (i := r) (s := t) (state := A.stateAt k)
              (by simpa [CAt] using cAtIsSymm A k (Nat.le_of_lt hklt)) htj
        simp [f, hrt]
      have hfilter :
          Finset.univ.filter (fun t : Fin n ↦ t.1 < k + 1) =
            insert j (Finset.univ.filter (fun t : Fin n ↦ t.1 < k)) := by
        -- The indices strictly before stage `k + 1` are exactly the old processed block plus `j`.
        ext t
        constructor
        · intro ht
          have htk1 : t.1 < k + 1 := (Finset.mem_filter.mp ht).2
          have htle : t.1 ≤ k := Nat.lt_succ_iff.mp htk1
          rcases lt_or_eq_of_le htle with htk | htk
          · simp [htk]
          · have htj : t = j := Fin.ext htk
            simp [htj]
        · intro ht
          rcases Finset.mem_insert.mp ht with rfl | ht
          · simp [j]
          · have htk : t.1 < k := (Finset.mem_filter.mp ht).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_of_lt htk⟩
      have hjNotMem :
          j ∉ Finset.univ.filter (fun t : Fin n ↦ t.1 < k) := by
        simp [j]
      calc
        Matrix.reindex (A.permAt (k + 1)) (A.permAt (k + 1)) A.G r r =
            Matrix.reindex (A.permAt k) (A.permAt k) A.G (σ r) (σ r) := hinput
        _ =
            A.CAt k (σ r) (σ r) +
              Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t.1 < k))
                (fun t ↦ (A.CAt k (σ r) t / A.d t) * A.CAt k (σ r) t) := by
                  exact ih (Nat.le_of_lt hklt) (σ r) hσr
        _ =
            A.CAt (k + 1) r r +
              ((A.CAt (k + 1) r j / A.d j) * A.CAt (k + 1) r j) +
              Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t.1 < k)) f := by
                  rw [hdiag, hsumOld]
                  ring
        _ =
            A.CAt (k + 1) r r +
              (f j + Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t.1 < k)) f) := by
                  ring
        _ =
            A.CAt (k + 1) r r +
              Finset.sum (insert j (Finset.univ.filter (fun t : Fin n ↦ t.1 < k))) f := by
                  rw [Finset.sum_insert hjNotMem]
        _ =
            A.CAt (k + 1) r r +
              Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t.1 < k + 1)) f := by
                  simpa using
                    congrArg
                      (fun s : Finset (Fin n) ↦ A.CAt (k + 1) r r + s.sum f)
                      hfilter.symm

/-- Helper for Chapter03 Algorithm 3.3.2: the canonical `Fin`-stage version of the active-tail
diagonal quotient invariant. -/
private theorem reindexedInputTailDiagQuotient (A : ModifiedCholeskyFactorization n)
    (j r : Fin n) (hjr : j ≤ r) :
    Matrix.reindex (A.permAt j.1) (A.permAt j.1) A.G r r =
      A.CAt j.1 r r +
        Finset.sum (Finset.univ.filter (fun t : Fin n ↦ t < j))
          (fun t ↦ (A.CAt j.1 r t / A.d t) * A.CAt j.1 r t) := by
  -- This is the stage-`j` specialization of the natural-number induction above.
  simpa using reindexedInputTailDiagQuotientAt A j.1 (Nat.le_of_lt j.is_lt) r hjr

/-- Helper for Chapter03 Algorithm 3.3.2: in the terminal pivot order, each strict-lower input
entry equals the final working entry plus the earlier-column contributions recorded by the final
factor row. -/
private theorem reindexedInputPrePivotLowerQuotient (A : ModifiedCholeskyFactorization n)
    (i j : Fin n) (hji : j < i) :
    Matrix.reindex (A.permAt i.1) (A.permAt i.1) A.G (A.pivotAt (i.1 + 1) i) j =
      A.CAt i.1 (A.pivotAt (i.1 + 1) i) j +
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
          (fun s ↦ (A.CAt i.1 (A.pivotAt (i.1 + 1) i) s / A.d s) * A.CAt i.1 j s) := by
  -- Route correction: the fixed-stage frontier formula is now owned by the generic tail-row
  -- processed-column invariant, so this wrapper is only a specialization to the pre-step pivot
  -- row chosen at stage `i`.
  have hiq : i ≤ A.pivotAt (i.1 + 1) i := by
    simpa [pivotAt_step_eq A i] using le_pivotIndex (A.CAt i.1) i
  exact reindexedInputTailLowerQuotient A i (A.pivotAt (i.1 + 1) i) j hji hiq

/-- Helper for Chapter03 Algorithm 3.3.2: in the terminal pivot order, the stage-`i` pre-step
pivot-row diagonal entry splits into the processed diagonal term and the earlier-column
contributions. -/
private theorem reindexedInputPrePivotDiagQuotient (A : ModifiedCholeskyFactorization n)
    (i : Fin n) :
    Matrix.reindex (A.permAt i.1) (A.permAt i.1) A.G
        (A.pivotAt (i.1 + 1) i) (A.pivotAt (i.1 + 1) i) =
      A.CAt i.1 (A.pivotAt (i.1 + 1) i) (A.pivotAt (i.1 + 1) i) +
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
          (fun s ↦
            (A.CAt i.1 (A.pivotAt (i.1 + 1) i) s / A.d s) *
              A.CAt i.1 (A.pivotAt (i.1 + 1) i) s) := by
  -- Route correction: the diagonal wrapper is now just the pre-step pivot-row specialization of
  -- the generic tail-row diagonal Schur-complement invariant.
  have hiq : i ≤ A.pivotAt (i.1 + 1) i := by
    simpa [pivotAt_step_eq A i] using le_pivotIndex (A.CAt i.1) i
  exact reindexedInputTailDiagQuotient A i (A.pivotAt (i.1 + 1) i) hiq

/-- Helper for Chapter03 Algorithm 3.3.2: in the terminal pivot order, each strict-lower input
entry equals the final working entry plus the earlier-column contributions recorded by the final
factor row. -/
private theorem reindexedInput_lowerEntry (A : ModifiedCholeskyFactorization n)
    (i j : Fin n) (hji : j < i) :
    Matrix.reindex A.perm A.perm A.G i j =
      A.C i j +
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
          (fun s ↦ A.L i s * A.C j s) := by
  have hinput :
      Matrix.reindex A.perm A.perm A.G i j =
        Matrix.reindex (A.permAt (i.1 + 1)) (A.permAt (i.1 + 1)) A.G i j := by
    -- Later pivots leave this fully processed input entry unchanged.
    simpa [perm] using
      (reindexInputStableAfterProcessed A i j hji n (Nat.succ_le_of_lt i.is_lt) le_rfl)
  have hCterm :
      A.CAt (i.1 + 1) i j = A.C i j := by
    -- Once row `i` is created, later stages keep this strict-lower working entry fixed.
    simpa [C] using
      (cAtStableAfterProcessed A i j hji n (Nat.succ_le_of_lt i.is_lt) le_rfl).symm
  have hLterm : ∀ s : Fin n, A.LAt (i.1 + 1) i s = A.L i s := by
    intro s
    -- Later pivots keep the completed row `i` of `L` unchanged.
    simpa [L] using
      (lAtStableAfterProcessed A i s n (Nat.succ_le_of_lt i.is_lt) le_rfl).symm
  have hCjterm : ∀ s : Fin n, s < j → A.CAt i.1 j s = A.C j s := by
    intro s hsj
    have hstage :
        A.CAt i.1 j s = A.CAt (j.1 + 1) j s := by
      exact cAtStableAfterProcessed A j s hsj i.1 (by omega) (Nat.le_of_lt i.is_lt)
    -- Row `j` is already processed before stage `i`, so its strict-lower entries are stable.
    calc
      A.CAt i.1 j s = A.CAt (j.1 + 1) j s := hstage
      _ = A.CAt n j s := by
            symm
            exact cAtStableAfterProcessed A j s hsj n (Nat.succ_le_of_lt j.is_lt) le_rfl
      _ = A.C j s := by
            rfl
  -- Reduce the terminal entry to the row-creation stage and then rewrite it through the
  -- pre-step pivot row.
  calc
    Matrix.reindex A.perm A.perm A.G i j =
        Matrix.reindex (A.permAt (i.1 + 1)) (A.permAt (i.1 + 1)) A.G i j := hinput
    _ =
        Matrix.reindex (A.permAt i.1) (A.permAt i.1) A.G (A.pivotAt (i.1 + 1) i) j := by
          rw [reindexInputStageCreatedColumn_prePivotRow A i j hji]
    _ =
        A.CAt i.1 (A.pivotAt (i.1 + 1) i) j +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
            (fun s ↦ (A.CAt i.1 (A.pivotAt (i.1 + 1) i) s / A.d s) * A.CAt i.1 j s) := by
          rw [reindexedInputPrePivotLowerQuotient A i j hji]
    _ =
        A.CAt (i.1 + 1) i j +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
            (fun s ↦ A.L i s * A.C j s) := by
          rw [(cAtStageCreatedColumn_prePivotRow A i j hji).symm]
          refine congrArg (fun t ↦ A.CAt (i.1 + 1) i j + t) ?_
          apply Finset.sum_congr rfl
          intro s hs
          have hsj : s < j := (Finset.mem_filter.mp hs).2
          have hsi : s < i := lt_trans hsj hji
          calc
            (A.CAt i.1 (A.pivotAt (i.1 + 1) i) s / A.d s) * A.CAt i.1 j s
                = A.LAt (i.1 + 1) i s * A.CAt i.1 j s := by
                    rw [lAtStageLowerEqDiv_prePivotRow A i s hsi]
            _ = A.L i s * A.CAt i.1 j s := by
                  rw [hLterm s]
            _ = A.L i s * A.C j s := by
                  rw [hCjterm s hsj]
    _ = A.C i j +
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
          (fun s ↦ A.L i s * A.C j s) := by
          rw [hCterm]

/-- Helper for Chapter03 Algorithm 3.3.2: in the terminal pivot order, each diagonal input entry
splits into the stage-`i` diagonal working entry and the earlier-column contributions carried by
the final factor row. -/
private theorem reindexedInput_diagEntry (A : ModifiedCholeskyFactorization n)
    (i : Fin n) :
    Matrix.reindex A.perm A.perm A.G i i =
      A.CAt (i.1 + 1) i i +
        Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
          (fun s ↦ A.L i s * A.C i s) := by
  have hinput :
      Matrix.reindex A.perm A.perm A.G i i =
        Matrix.reindex (A.permAt (i.1 + 1)) (A.permAt (i.1 + 1)) A.G i i := by
    -- Later pivots leave the processed diagonal input entry unchanged.
    simpa [perm] using
      (reindexInputDiagStableAfterProcessed A i n (Nat.succ_le_of_lt i.is_lt) le_rfl)
  have hLterm : ∀ s : Fin n, A.LAt (i.1 + 1) i s = A.L i s := by
    intro s
    -- The completed row `i` of `L` stays fixed after stage `i`.
    simpa [L] using
      (lAtStableAfterProcessed A i s n (Nat.succ_le_of_lt i.is_lt) le_rfl).symm
  have hCiterm :
      ∀ s : Fin n, s < i → A.CAt i.1 (A.pivotAt (i.1 + 1) i) s = A.C i s := by
    intro s hsi
    have hcreated :
        A.CAt i.1 (A.pivotAt (i.1 + 1) i) s = A.CAt (i.1 + 1) i s := by
      exact (cAtStageCreatedColumn_prePivotRow A i s hsi).symm
    have hstable :
        A.CAt (i.1 + 1) i s = A.C i s := by
      simpa [C] using
        (cAtStableAfterProcessed A i s hsi n (Nat.succ_le_of_lt i.is_lt) le_rfl).symm
    -- The newly created row `i` records the same processed-column data as the pre-step pivot row.
    exact hcreated.trans hstable
  -- Reduce the terminal diagonal entry to the row-creation stage and then rewrite it through the
  -- pre-step pivot row.
  calc
    Matrix.reindex A.perm A.perm A.G i i =
        Matrix.reindex (A.permAt (i.1 + 1)) (A.permAt (i.1 + 1)) A.G i i := hinput
    _ =
        Matrix.reindex (A.permAt i.1) (A.permAt i.1) A.G
          (A.pivotAt (i.1 + 1) i) (A.pivotAt (i.1 + 1) i) := by
            rw [reindexInputStageCreatedDiag_prePivotRow A i]
    _ =
        A.CAt i.1 (A.pivotAt (i.1 + 1) i) (A.pivotAt (i.1 + 1) i) +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
            (fun s ↦
              (A.CAt i.1 (A.pivotAt (i.1 + 1) i) s / A.d s) *
                A.CAt i.1 (A.pivotAt (i.1 + 1) i) s) := by
          rw [reindexedInputPrePivotDiagQuotient A i]
    _ =
        A.CAt (i.1 + 1) i i +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
            (fun s ↦ A.L i s * A.C i s) := by
          rw [(cAtStageCreatedDiag_prePivotRow A i).symm]
          refine congrArg (fun t ↦ A.CAt (i.1 + 1) i i + t) ?_
          apply Finset.sum_congr rfl
          intro s hs
          have hsi : s < i := (Finset.mem_filter.mp hs).2
          calc
            (A.CAt i.1 (A.pivotAt (i.1 + 1) i) s / A.d s) *
                A.CAt i.1 (A.pivotAt (i.1 + 1) i) s
                = A.LAt (i.1 + 1) i s * A.CAt i.1 (A.pivotAt (i.1 + 1) i) s := by
                    rw [lAtStageLowerEqDiv_prePivotRow A i s hsi]
            _ = A.L i s * A.CAt i.1 (A.pivotAt (i.1 + 1) i) s := by
                  rw [hLterm s]
            _ = A.L i s * A.C i s := by
                  rw [hCiterm s hsi]

/-- Helper for Chapter03 Algorithm 3.3.2: every strict-lower entry of the terminal corrected
matrix already matches the corresponding `L D Lᵀ` entry. -/
private theorem permutedCorrectedMatrix_lowerEntry_eq (A : ModifiedCholeskyFactorization n)
    (i j : Fin n) (hji : j < i) :
    A.permutedCorrectedMatrix i j = modifiedCholeskySystemMatrix A.L A.d i j := by
  -- On off-diagonal entries the diagonal correction vanishes, so the public reindexed-input
  -- invariant rewrites the left-hand side into the owner-normal form of the LDL-side lemma.
  calc
    A.permutedCorrectedMatrix i j = Matrix.reindex A.perm A.perm A.G i j := by
      simp [permutedCorrectedMatrix, ne_of_gt hji]
    _ = A.C i j +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < j))
            (fun s ↦ A.L i s * A.C j s) := by
          exact reindexedInput_lowerEntry A i j hji
    _ = modifiedCholeskySystemMatrix A.L A.d i j := by
          rw [modifiedCholeskySystemMatrix_lowerEntry A i j hji]

/-- Helper for Chapter03 Algorithm 3.3.2: every diagonal entry of the terminal corrected matrix
already matches the corresponding `L D Lᵀ` entry. -/
private theorem permutedCorrectedMatrix_diagEntry_eq (A : ModifiedCholeskyFactorization n)
    (i : Fin n) :
    A.permutedCorrectedMatrix i i = modifiedCholeskySystemMatrix A.L A.d i i := by
  have hreindex :
      Matrix.reindex A.perm A.perm A.G i i =
        A.CAt (i.1 + 1) i i +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
            (fun s ↦ A.L i s * A.C i s) := by
    -- The corrected diagonal helper now packages the only normalization consumed below.
    exact reindexedInput_diagEntry A i
  -- The diagonal correction is exactly the gap between the processed diagonal entry and `d_i`.
  calc
    A.permutedCorrectedMatrix i i = Matrix.reindex A.perm A.perm A.G i i + A.e i := by
      simp [permutedCorrectedMatrix]
    _ = A.CAt (i.1 + 1) i i +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
            (fun s ↦ A.L i s * A.C i s) + A.e i := by
          rw [hreindex]
    _ = A.d i +
          Finset.sum (Finset.univ.filter (fun s : Fin n ↦ s < i))
            (fun s ↦ A.L i s * A.C i s) := by
          rcases processedDiagonalDataStable A i with ⟨hd, he⟩
          rw [hd, he, eAt_step_eq]
          ring
    _ = modifiedCholeskySystemMatrix A.L A.d i i := by
          rw [modifiedCholeskySystemMatrix_diagEntry A i]

/-- Chapter03 Algorithm 3.3.2: the terminal outputs satisfy the modified Cholesky factorization
identity for the cumulatively permuted corrected matrix `P G Pᵀ + E = L D Lᵀ`, with `P`
encoded by `perm`, `E = diagonal e`, and `D = diagonal d`. -/
theorem factorization (A : ModifiedCholeskyFactorization n) :
    -- Route correction: the earlier arbitrary-stage public-entry lemmas were too strong for this
    -- row-wise `L` implementation, so the remaining blocker is now concentrated in the final
    -- owner-normal forms `reindexedInput_lowerEntry` and `reindexedInput_diagEntry`; the
    -- `L D Lᵀ` side already matches the target entries via
    -- `modifiedCholeskySystemMatrix_lowerEntry` / `modifiedCholeskySystemMatrix_diagEntry`.
    A.permutedCorrectedMatrix = modifiedCholeskySystemMatrix A.L A.d := by
  classical
  -- Compare the corrected matrix and `L D Lᵀ` entrywise, splitting into diagonal and
  -- strict-lower cases and then using symmetry for the upper triangle.
  ext i j
  by_cases hij : i = j
  · subst hij
    -- The diagonal wrapper isolates the reindexed-input normalization from the final `Matrix.ext`
    -- proof, leaving only the previously established LDL-side diagonal entry lemma to consume it.
    simpa using permutedCorrectedMatrix_diagEntry_eq A i
  · by_cases hji : j < i
    · -- The strict-lower wrapper packages the off-diagonal diagonal-matrix simplification and the
      -- processed-column entry normalization into one reusable closing step.
      exact permutedCorrectedMatrix_lowerEntry_eq A i j hji
    · have hij' : i < j := lt_of_le_of_ne (le_of_not_gt hji) hij
      -- Symmetry reduces the upper-triangular branch to the already-handled strict-lower case.
      have hsymmLeft := permutedCorrectedMatrix_isSymm A
      have hsymmRight := modifiedCholeskySystemMatrix_isSymm A
      have hlower :
          A.permutedCorrectedMatrix j i = modifiedCholeskySystemMatrix A.L A.d j i := by
        -- Swapping the indices lands in the strict-lower branch that was just packaged above.
        exact permutedCorrectedMatrix_lowerEntry_eq A j i hij'
      simpa [hsymmLeft.apply i j, hsymmRight.apply i j] using hlower

end ModifiedCholeskyFactorization

/-
Chapter03 Algorithm 3.3.2 (2)

The source also records the complexity remark that the modified Cholesky factorization
needs about `(1 / 6) n^3` arithmetic operations, which is almost the same as the normal
Cholesky factorization. This file has no dedicated operation-count owner for the Gill-Murray
algorithm, so that final sentence is preserved here as an explicit labeled recall companion.
-/
