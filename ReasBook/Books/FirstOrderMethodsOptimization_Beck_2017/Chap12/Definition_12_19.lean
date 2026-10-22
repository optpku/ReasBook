/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_44
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Em" => EuclideanSpace ℝ (Fin (n - 1))

/- This item is `source-facing`: the textbook object is the explicit one-dimensional total
variation denoising objective on `ℝ^n`.

Domain sampling against the nearby Chapter 12 API gives:
- `source-facing`: the adjacent-difference total-variation penalty on `ℝ^n`;
- `core/canonical`: `denoising_problem_objective` and `denoising_problem_optimal_value` from
  Definition 12.10;
- `bridge/view`: the first-difference operator `D[n]` together with the Euclidean `ℓ¹` norm
  `‖·‖₁`, and the explicit finite-sum formula over neighboring coordinates.

Primitive source data are only the standard adjacent constructors `Fin.castSucc` and `Fin.succ`
on `Fin n`. The difference matrix/operator and its canonical adjoint are derived from that
adjacent-edge data, and the denoising objective/optimal value should then reuse the existing
Chapter 12.10 owners rather than rebuilding a parallel specialization on `ℝ^n`. -/

/-- The one-dimensional first-difference matrix `D` whose `i`-th row encodes the forward
adjacent difference `x_i - x_(i+1)`. It maps `ℝ^n` to `ℝ^(n-1)`. -/
def one_dimensional_total_variation_difference_matrix :
    (n : ℕ) → Matrix (Fin (n - 1)) (Fin n) ℝ
  | 0 => fun i ↦ i.elim0
  | _ + 1 => fun i j ↦
      if j = i.castSucc then (1 : ℝ)
      else if j = i.succ then (-1 : ℝ)
      else 0

/-- Evaluating the finite-difference matrix gives the row formula for the forward adjacent
difference `x_i - x_(i+1)`. -/
@[simp] theorem one_dimensional_total_variation_difference_matrix_apply
    (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    one_dimensional_total_variation_difference_matrix (n + 1) i j =
      if j = i.castSucc then (1 : ℝ)
      else if j = i.succ then (-1 : ℝ)
      else 0 :=
  rfl

/-- The first-difference operator `D : ℝ^n → ℝ^(n-1)` for one-dimensional total variation
denoising, sending `x` to its forward adjacent differences. -/
def one_dimensional_total_variation_difference_operator (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
  (one_dimensional_total_variation_difference_matrix n).toEuclideanLin

notation:max "D[" n "]" => one_dimensional_total_variation_difference_operator n

/- Textbook notation for the canonical Hilbert adjoint of the one-dimensional TV difference
operator. -/
set_option quotPrecheck false in
notation:max "Dᵀ[" n "]" =>
  (show EuclideanSpace ℝ (Fin (n - 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) from
    (D[n]).adjoint)

/-- The finite-difference operator `D` is the Euclidean linear map attached to the matrix
`one_dimensional_total_variation_difference_matrix`. -/
@[simp] theorem one_dimensional_total_variation_difference_operator_eq
    (n : ℕ) :
    D[n] =
      (one_dimensional_total_variation_difference_matrix n).toEuclideanLin :=
  rfl

/-- The canonical adjoint operator `Dᵀ` is represented in Euclidean coordinates by the transpose
of the one-dimensional TV difference matrix. -/
@[simp] theorem one_dimensional_total_variation_difference_operator_adjoint_eq_transpose
    (n : ℕ) :
    Dᵀ[n] = (one_dimensional_total_variation_difference_matrix n).transpose.toEuclideanLin := by
  -- Rewrite the source-facing adjoint notation using the canonical transpose representation.
  simpa [one_dimensional_total_variation_difference_operator_eq] using
    (matrix_transpose_toEuclideanLin_eq_adjoint
      (A := one_dimensional_total_variation_difference_matrix n)).symm

/-- Helper for Definition 12.19: summing the two nonzero entries in a difference-matrix row
 gives the adjacent coordinate difference. -/
private theorem one_dimensional_total_variation_difference_row_sum
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    (∑ j : Fin (n + 1),
      (if j = i.castSucc then (1 : ℝ) else if j = i.succ then (-1 : ℝ) else 0) * x.ofLp j) =
        x.ofLp i.castSucc - x.ofLp i.succ := by
  -- Split the row sum into the left-endpoint and right-endpoint singleton contributions.
  have hcast_ne : i.castSucc ≠ i.succ := by
    exact ne_of_lt i.castSucc_lt_succ
  have hsucc_ne : i.succ ≠ i.castSucc := by
    exact ne_of_gt i.castSucc_lt_succ
  have hsplit :
      (∑ j : Fin (n + 1),
        (if j = i.castSucc then (1 : ℝ) else if j = i.succ then (-1 : ℝ) else 0) * x.ofLp j) =
        ((∑ j : Fin (n + 1), if j = i.castSucc then x.ofLp j else (0 : ℝ)) +
          ∑ j : Fin (n + 1), if j = i.succ then -x.ofLp j else (0 : ℝ)) := by
    have hpointwise :
        (fun j : Fin (n + 1) ↦
          (if j = i.castSucc then (1 : ℝ) else if j = i.succ then (-1 : ℝ) else 0) * x.ofLp j) =
        (fun j : Fin (n + 1) ↦
          (if j = i.castSucc then x.ofLp j else (0 : ℝ)) +
            (if j = i.succ then -x.ofLp j else (0 : ℝ))) := by
      ext j
      by_cases hleft : j = i.castSucc
      · -- At the left endpoint, the right-endpoint branch is impossible.
        simp [hleft, hcast_ne]
      · by_cases hright : j = i.succ
        · -- At the right endpoint, only the negative singleton contribution remains.
          simp [hright, hsucc_ne]
        · -- Every other column contributes zero to this row.
          simp [hleft, hright]
    rw [hpointwise, Finset.sum_add_distrib]
  rw [hsplit]
  -- Each singleton indicator sum evaluates at its distinguished adjacent endpoint.
  simp [sub_eq_add_neg]

/-- Evaluating `D[n]` at `x` gives the adjacent difference `x_i - x_(i+1)` in coordinate `i`. -/
@[simp] theorem one_dimensional_total_variation_difference_operator_apply
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    D[n + 1] x i = x i.castSucc - x i.succ := by
  -- Rewrite `D[n + 1]` as the Euclidean linear map of the difference matrix.
  rw [one_dimensional_total_variation_difference_operator_eq, Matrix.toEuclideanLin_apply]
  -- Only the two adjacent entries in row `i` contribute to the matrix-vector product.
  simp only [Matrix.mulVec, dotProduct, one_dimensional_total_variation_difference_matrix_apply]
  exact one_dimensional_total_variation_difference_row_sum x i

private theorem one_dimensional_total_variation_edge_bound_eq (e : Fin (n - 1)) :
    (n - 1) + 1 = n := by
  apply Nat.sub_add_cancel
  exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le e.pos (Nat.sub_le n 1))

/-- The left endpoint of the adjacent edge indexed by `e` for the one-dimensional TV difference
operator. -/
def one_dimensional_total_variation_edge_left (e : Fin (n - 1)) : Fin n :=
  e.castSucc.cast (one_dimensional_total_variation_edge_bound_eq e)

/-- The right endpoint of the adjacent edge indexed by `e` for the one-dimensional TV difference
operator. -/
def one_dimensional_total_variation_edge_right (e : Fin (n - 1)) : Fin n :=
  e.succ.cast (one_dimensional_total_variation_edge_bound_eq e)

/-- The left endpoint of edge `e` has index `e`. -/
@[simp] theorem one_dimensional_total_variation_edge_left_val (e : Fin (n - 1)) :
    (one_dimensional_total_variation_edge_left e).1 = e.1 :=
  rfl

/-- The right endpoint of edge `e` has index `e + 1`. -/
@[simp] theorem one_dimensional_total_variation_edge_right_val (e : Fin (n - 1)) :
    (one_dimensional_total_variation_edge_right e).1 = e.1 + 1 :=
  rfl

/-- Evaluating `D[n]` on edge `e` is the difference between the values at the canonical adjacent
endpoints of `e`. -/
@[simp] theorem one_dimensional_total_variation_difference_operator_apply_edge
    (x : En) (e : Fin (n - 1)) :
    D[n] x e = x (one_dimensional_total_variation_edge_left e) -
      x (one_dimensional_total_variation_edge_right e) := by
  cases n with
  | zero =>
      exact e.elim0
  | succ n =>
      simpa [one_dimensional_total_variation_edge_left,
        one_dimensional_total_variation_edge_right] using
        (one_dimensional_total_variation_difference_operator_apply (n := n) x e)

/-- The one-dimensional total-variation regularizer on `ℝ^n`, realized as the Euclidean `ℓ¹`
norm of the first-difference vector `D[n] x`. -/
def one_dimensional_total_variation (x : En) : ℝ :=
  ‖D[n] x‖₁

-- Proof sketch: unfold `one_dimensional_total_variation`; the displayed finite sum is exactly its
-- defining formula.
/-- Expanding the one-dimensional total-variation regularizer gives the sum of adjacent absolute
differences. -/
theorem one_dimensional_total_variation_def (x : EuclideanSpace ℝ (Fin (n + 1))) :
    one_dimensional_total_variation x =
      ∑ i : Fin n, |x i.castSucc - x i.succ| := by
  -- Expand the `ℓ¹` norm into the finite sum of coordinate absolute values.
  rw [one_dimensional_total_variation, EuclideanSpace.l1Norm_eq_sum_abs]
  -- Each coordinate of `D[n + 1] x` is the adjacent difference from the previous theorem.
  congr with i
  rw [one_dimensional_total_variation_difference_operator_apply]

/-- Definition 12.19: for datum `d ∈ ℝ^n` and positive parameter `λ`, encoded by
`lam : PosReal`, the one-dimensional total-variation denoising objective is
`F(x) = (1 / 2) ‖x - d‖_2^2 + λ * ∑_{i=1}^{n-1} |x_(i-1) - x_i|`. -/
abbrev one_dimensional_total_variation_denoising_objective
    (d : En) (lam : PosReal) : En → EReal :=
  denoising_problem_objective d
    (fun y : Em ↦ ↑((lam : ℝ) * ‖y‖₁))
    D[n]

-- Proof sketch: unfold
-- `one_dimensional_total_variation_denoising_objective` through `denoising_problem_objective`,
-- then expand the quadratic fidelity term from Definition 12.10.
/-- Evaluating the one-dimensional total-variation denoising objective gives the quadratic
data-fidelity term plus the scaled total-variation penalty. -/
@[simp] theorem one_dimensional_total_variation_denoising_objective_apply
    (d x : En) (lam : PosReal) :
    one_dimensional_total_variation_denoising_objective d lam x =
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) +
        ↑((lam : ℝ) * one_dimensional_total_variation x) := by
  -- Unfold the Chapter 12.10 denoising objective specialized to the TV regularizer.
  simp [one_dimensional_total_variation_denoising_objective, one_dimensional_total_variation]

end
