/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (toLp)

noncomputable section

section

variable {m n : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "X" => Fin n → ℝ

/- Algorithm 8.15 is `source-facing`: the textbook specifies the score vector
`v = c + Aᵀ λ^k`, an index-selection rule choosing a minimizing coordinate of `v`, the associated
simplex vertex `x^k = e_{i_k}`, and the normalized projected update of the dual multiplier.
Domain sampling against the surrounding Chapter 8 files shows that the natural owner is the
recursive multiplier sequence itself, while the minimizing-index condition should remain a separate
admissibility predicate on the selection rule instead of being hidden behind a noncanonical
`argmin` choice. -/

/-- The LP score vector `v = c + Aᵀ λ` attached to a dual multiplier `λ`. -/
def dual_projected_subgradient_lp_score_vector
    (A : Matrix (Fin m) (Fin n) ℝ) (c : X) (lam : Fin m → NNReal) : X :=
  c + Aᵀ *ᵥ fun i ↦ (lam i : ℝ)

-- Proof sketch: unfold `dual_projected_subgradient_lp_score_vector`; its `i`-th coordinate is
-- the `i`-th coordinate of `c + Aᵀ λ`.
/-- Evaluating `dual_projected_subgradient_lp_score_vector A c lam` at `i` returns the `i`-th
coordinate of `c + Aᵀ λ`. -/
@[simp] theorem dual_projected_subgradient_lp_score_vector_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (c : X) (lam : Fin m → NNReal) (i : Fin n) :
    dual_projected_subgradient_lp_score_vector A c lam i =
      c i + (Aᵀ *ᵥ fun j ↦ (lam j : ℝ)) i := by
  -- Unfold the score vector once; its coordinates are exactly those of `c + Aᵀ λ`.
  rfl

/-- The minimizing index selected at the multiplier `λ`. -/
def dual_projected_subgradient_lp_selected_index
    (iSel : (Fin m → NNReal) → Fin n) (lam : Fin m → NNReal) : Fin n :=
  iSel lam

/-- The simplex vertex `e_i` selected by the minimizing-index rule at the multiplier `λ`. -/
def dual_projected_subgradient_lp_primal_vertex
    (iSel : (Fin m → NNReal) → Fin n) (lam : Fin m → NNReal) : X :=
  Pi.single (dual_projected_subgradient_lp_selected_index iSel lam) 1

-- Proof sketch: unfold `dual_projected_subgradient_lp_primal_vertex`; the chosen primal point is
-- definitionally the standard basis vector at the selected index.
/-- The primal vertex chosen at `λ` is exactly the standard basis vector at the selected index. -/
@[simp] theorem dual_projected_subgradient_lp_primal_vertex_eq
    (iSel : (Fin m → NNReal) → Fin n) (lam : Fin m → NNReal) :
    dual_projected_subgradient_lp_primal_vertex iSel lam =
      Pi.single (dual_projected_subgradient_lp_selected_index iSel lam) 1 := by
  -- Unfold the selected primal vertex; it is definitionally the chosen basis vector.
  rfl

/-- The residual vector `A x - b`, viewed in Euclidean multiplier space `ℝ^m`. -/
def dual_projected_subgradient_lp_residual_vector
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : X) : Λ :=
  toLp 2 (A *ᵥ x - b)

-- Proof sketch: unfold `dual_projected_subgradient_lp_residual_vector`; the `i`-th coordinate is
-- definitionally `(A x - b)_i`.
/-- Evaluating `dual_projected_subgradient_lp_residual_vector A b x` at `i` returns
`(A x - b)_i`. -/
@[simp] theorem dual_projected_subgradient_lp_residual_vector_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : X) (i : Fin m) :
    dual_projected_subgradient_lp_residual_vector A b x i = (A *ᵥ x) i - b i := by
  -- Unfold the residual vector once; `WithLp.toLp` preserves the displayed coordinates.
  rfl

/-- The coordinatewise projected multiplier update of Algorithm 8.15. -/
def dual_projected_subgradient_lp_multiplier_update
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (iSel : (Fin m → NNReal) → Fin n) (k : ℕ) (lam : Fin m → NNReal) :
    Fin m → NNReal :=
  let x := dual_projected_subgradient_lp_primal_vertex iSel lam
  fun i ↦
    Real.toNNReal
      ((lam i : ℝ) +
        (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) *
          (dual_projected_subgradient_lp_residual_vector A b x i /
            ‖dual_projected_subgradient_lp_residual_vector A b x‖))

/-- Algorithm 8.15: given an initial multiplier `λ⁰ ∈ ℝ_+^m` and a rule selecting for each
multiplier `λ` an index minimizing the score vector `v = c + Aᵀ λ`, the dual projected
subgradient method for `(LP)` generates the multiplier sequence `λ^k` by setting
`x^k = e_{i_k}` and updating
`λ^{k+1} = [λ^k + (1 / √(k + 1)) (A x^k - b) / ‖A x^k - b‖₂]_+`. -/
def dual_projected_subgradient_lp_method
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (iSel : (Fin m → NNReal) → Fin n) (lam0 : Fin m → NNReal) : ℕ → Fin m → NNReal
  | 0 => lam0
  | k + 1 =>
      let lamk := dual_projected_subgradient_lp_method A b iSel lam0 k
      dual_projected_subgradient_lp_multiplier_update A b iSel k lamk

/-- The index selected by the minimizing-coordinate rule at iteration `k`. -/
def dual_projected_subgradient_lp_selected_index_iterate
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (iSel : (Fin m → NNReal) → Fin n) (lam0 : Fin m → NNReal) (k : ℕ) : Fin n :=
  dual_projected_subgradient_lp_selected_index iSel
    (dual_projected_subgradient_lp_method A b iSel lam0 k)

/-- The primal iterate `x^k = e_{i_k}` associated to the current dual multiplier iterate. -/
def dual_projected_subgradient_lp_primal_iterate
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (iSel : (Fin m → NNReal) → Fin n) (lam0 : Fin m → NNReal) (k : ℕ) : X :=
  dual_projected_subgradient_lp_primal_vertex iSel
    (dual_projected_subgradient_lp_method A b iSel lam0 k)

/-- A minimizing-index rule is admissible when it always chooses a coordinate attaining the
minimum of the LP score vector `v = c + Aᵀ λ`. -/
def dual_projected_subgradient_lp_index_rule_is_admissible
    (A : Matrix (Fin m) (Fin n) ℝ) (c : X)
    (iSel : (Fin m → NNReal) → Fin n) : Prop :=
  ∀ lam : Fin m → NNReal, ∀ j : Fin n,
    dual_projected_subgradient_lp_score_vector A c lam
        (dual_projected_subgradient_lp_selected_index iSel lam) ≤
      dual_projected_subgradient_lp_score_vector A c lam j

section

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : X)
variable (iSel : (Fin m → NNReal) → Fin n) (lam0 : Fin m → NNReal)

local notation "lam[" k "]" =>
  dual_projected_subgradient_lp_method A b iSel lam0 k

local notation "i[" k "]" =>
  dual_projected_subgradient_lp_selected_index_iterate A b iSel lam0 k

local notation "x[" k "]" =>
  dual_projected_subgradient_lp_primal_iterate A b iSel lam0 k

-- Proof sketch: unfold the recursive definition of `dual_projected_subgradient_lp_method` at
-- `0`.
/-- The dual projected-subgradient multiplier sequence starts at the prescribed initial
multiplier. -/
@[simp] theorem dual_projected_subgradient_lp_method_zero :
    lam[0] = lam0 := by
  -- The recursive definition starts the multiplier sequence at the prescribed initial point.
  rfl

-- Proof sketch: unfold `dual_projected_subgradient_lp_selected_index_iterate`; by definition,
-- `i_k` is obtained by applying the selection rule to the current multiplier iterate `λ^k`.
/-- The selected index at step `k` is obtained by applying the minimizing-index rule to
`λ^k`. -/
@[simp] theorem dual_projected_subgradient_lp_selected_index_iterate_eq (k : ℕ) :
    i[k] = dual_projected_subgradient_lp_selected_index iSel lam[k] := by
  -- By definition, the selected index at step `k` is computed from the current iterate `λ^k`.
  rfl

-- Proof sketch: unfold `dual_projected_subgradient_lp_primal_iterate`; the primal iterate is
-- definitionally the selected simplex vertex at the current multiplier iterate.
/-- The primal iterate `x^k` is the selected simplex vertex associated to `λ^k`. -/
@[simp] theorem dual_projected_subgradient_lp_primal_iterate_eq (k : ℕ) :
    x[k] = dual_projected_subgradient_lp_primal_vertex iSel lam[k] := by
  -- By definition, the primal iterate is the selected simplex vertex at the current multiplier.
  rfl

-- Proof sketch: unfold the recursive clause of `dual_projected_subgradient_lp_method` at
-- `k + 1`.
/-- One step of Algorithm 8.15 updates the current multiplier by the projected normalized
residual step computed from the current selected simplex vertex. -/
theorem dual_projected_subgradient_lp_method_succ (k : ℕ) :
    lam[k + 1] =
      dual_projected_subgradient_lp_multiplier_update A b iSel k lam[k] := by
  -- Unfold one recursive step; the owner object is the multiplier sequence `lam[k]`.
  simp [dual_projected_subgradient_lp_method]

-- Proof sketch: unfold `dual_projected_subgradient_lp_index_rule_is_admissible` and specialize
-- it at the current multiplier iterate `λ^k`.
/-- Under the admissibility condition, the selected index at iteration `k` minimizes the score
vector `v = c + Aᵀ λ^k`. -/
theorem dual_projected_subgradient_lp_selected_index_iterate_minimizes
    (c : X) (h : dual_projected_subgradient_lp_index_rule_is_admissible A c iSel) (k : ℕ)
    (j : Fin n) :
    dual_projected_subgradient_lp_score_vector A c lam[k] i[k] ≤
      dual_projected_subgradient_lp_score_vector A c lam[k] j := by
  -- Specialize admissibility at the current multiplier iterate `λ^k`.
  simpa using h lam[k] j

end

end
