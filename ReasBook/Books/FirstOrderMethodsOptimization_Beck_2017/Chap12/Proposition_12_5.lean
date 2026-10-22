/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_33
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_12.Spaces
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius
open Matrix TwoDimensionalTV WithLp

section

variable (m n : ℕ)

/- Proposition 12.5 is `bridge/view` in the two-dimensional total-variation denoising API.

Domain sampling identifies the owner split:
- `core/canonical`: `two_dimensional_total_variation_difference :
  MatrixSpace m n →ₗ[ℝ] DualSpace m n` from
  Proposition 12.4;
- `core/canonical`: mathlib's `WithLp.linearEquiv`, `WithLp.fst`, and `WithLp.snd`, which equip
  `WithLp 2 (HorizontalSpace m n × VerticalSpace m n)` with the canonical `L²` product structure
  used for the TV dual pair;
- `core/canonical`: `LinearMap.adjoint`, once the source and target carry the Frobenius and `L²`
  Hilbert structures used in the chapter;
- `bridge/view`: the explicit boundary-value formula for `Aᵀ z`.

Primitive data here are only the Frobenius/`L²` Hilbert structures. The divergence formula is
derived API from the adjoint owner, not a second public operator parallel to `A.adjoint`. The
owner-level notation `A[m, n]` and `Aᵀ[m, n]` is imported from Proposition 12.4. -/

-- Proof sketch: identify `Aᵀ` with the unique map satisfying the Hilbert adjoint identity for the
-- Proposition 12.4 forward-difference operator, then compute the resulting coordinate formula by
-- summing the four boundary-adjusted contributions incident to the pixel `(i, j)`.
/-- Helper for Proposition 12.5: subtracting one from a positive `Fin n` index lands in
`Fin (n - 1)`. -/
lemma sub_one_val_lt_sub_one (j : Fin n) (h : 0 < j.1) : j.1 - 1 < n - 1 := by
  omega

/-- Helper for Proposition 12.5: the previous index in `Fin (n - 1)` attached to a positive
`Fin n` index. -/
abbrev pred_sub_index (j : Fin n) (h : 0 < j.1) : Fin (n - 1) :=
  ⟨j.1 - 1, sub_one_val_lt_sub_one n j h⟩

/-- Helper for Proposition 12.5: the real inner product on scalar entries is ordinary
multiplication. -/
lemma real_inner_eq_mul (a b : ℝ) : inner ℝ a b = a * b := by
  change b * a = a * b
  ring

/-- Helper for Proposition 12.5: casting a forward-difference index from `Fin n` into
`Fin (n + 1)` agrees with `Fin.castSucc`. -/
lemma castLE_sub_eq_castSucc (j : Fin n) :
    Fin.castLE (Nat.sub_le (n + 1) 1) j = j.castSucc := by
  -- Both constructions keep the same underlying natural-number value.
  apply Fin.ext
  rfl

/-- Helper for Proposition 12.5: adding one to the value of a `Fin n` index agrees with
`Fin.succ`. -/
lemma mk_add_one_eq_succ (j : Fin n) :
    (⟨(j : ℕ) + 1, by omega⟩ : Fin (n + 1)) = j.succ := by
  -- Both constructions represent the successor coordinate inside `Fin (n + 1)`.
  apply Fin.ext
  rfl

/-- Helper for Proposition 12.5: one-dimensional summation by parts rewrites the forward-difference
pairing as a zero-padded divergence pairing. -/
lemma forward_difference_sum_eq_zero_padded
    (x : Fin n → ℝ) (p : Fin (n - 1) → ℝ) :
    (∑ j : Fin (n - 1), (x (Fin.castLE (Nat.sub_le n 1) j) - x ⟨(j : ℕ) + 1, by omega⟩) * p j) =
      ∑ j : Fin n, x j *
        ((if h : j.1 < n - 1 then p (j.castLT h) else 0) -
          (if h : 0 < j.1 then p (pred_sub_index n j h) else 0)) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      -- Split the forward-difference sum into the outgoing and incoming boundary contributions.
      calc
        (∑ j : Fin n, (x (Fin.castLE (Nat.sub_le (n + 1) 1) j) - x ⟨(j : ℕ) + 1, by omega⟩) * p j) =
            (∑ j : Fin n, x (Fin.castSucc j) * p j) - ∑ j : Fin n, x j.succ * p j := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib]
          have h_cast :
              ∑ j : Fin n, x (Fin.castLE (Nat.sub_le (n + 1) 1) j) * p j =
                ∑ j : Fin n, x (Fin.castSucc j) * p j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            -- Replace the source index by the canonical `castSucc` representative.
            rw [castLE_sub_eq_castSucc]
          have h_succ :
              ∑ j : Fin n, x ⟨(j : ℕ) + 1, by omega⟩ * p j =
                ∑ j : Fin n, x j.succ * p j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            -- Rewrite the shifted target index into the canonical `succ` form.
            rw [mk_add_one_eq_succ]
          rw [h_cast, h_succ]
        _ =
            (∑ j : Fin (n + 1), x j * (if h : j.1 < n then p (j.castLT h) else 0)) -
              ∑ j : Fin (n + 1),
                x j * (if h : 0 < j.1 then p (pred_sub_index (n + 1) j h) else 0) := by
          rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
          simp [pred_sub_index]
        _ = ∑ j : Fin (n + 1), x j *
              ((if h : j.1 < n then p (j.castLT h) else 0) -
                (if h : 0 < j.1 then p (pred_sub_index (n + 1) j h) else 0)) := by
          simp_rw [mul_sub]
          rw [← Finset.sum_sub_distrib]

/-- Helper for Proposition 12.5: the horizontal inner-product term is the zero-padded horizontal
divergence contribution. -/
lemma horizontal_difference_inner_eq_zero_padded
    (x : MatrixSpace m n) (z : DualSpace m n) :
    inner ℝ (two_dimensional_total_variation_horizontal_difference x) z.fst =
      ∑ i : Fin m, ∑ j : Fin n,
        x i j *
          ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) -
            (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0)) := by
  -- Expand the Frobenius inner product rowwise, then apply the one-dimensional summation formula.
  change
    inner ℝ
        (WithLp.toLp 2 fun i : Fin m ↦
          WithLp.toLp 2 fun j : Fin (n - 1) ↦
            two_dimensional_total_variation_horizontal_difference x i j)
        (WithLp.toLp 2 fun i : Fin m ↦ WithLp.toLp 2 fun j : Fin (n - 1) ↦ z.fst i j) =
      ∑ i : Fin m, ∑ j : Fin n,
        x i j *
          ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) -
            (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0))
  calc
    inner ℝ
        (WithLp.toLp 2 fun i : Fin m ↦
          WithLp.toLp 2 fun j : Fin (n - 1) ↦
            two_dimensional_total_variation_horizontal_difference x i j)
        (WithLp.toLp 2 fun i : Fin m ↦ WithLp.toLp 2 fun j : Fin (n - 1) ↦ z.fst i j) =
      ∑ i : Fin m, ∑ j : Fin (n - 1),
        (two_dimensional_total_variation_horizontal_difference x i j) * z.fst i j := by
      simp_rw [PiLp.inner_apply, real_inner_eq_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) -
              (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [two_dimensional_total_variation_horizontal_difference_apply] using
        forward_difference_sum_eq_zero_padded n (x i) (z.fst i)

/-- Helper for Proposition 12.5: the vertical inner-product term is the zero-padded vertical
divergence contribution. -/
lemma vertical_difference_inner_eq_zero_padded
    (x : MatrixSpace m n) (z : DualSpace m n) :
    inner ℝ (two_dimensional_total_variation_vertical_difference x) z.snd =
      ∑ i : Fin m, ∑ j : Fin n,
        x i j *
          ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
            (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
  -- Commute the finite sums so each column can reuse the same one-dimensional summation formula.
  change
    inner ℝ
        (WithLp.toLp 2 fun i : Fin (m - 1) ↦
          WithLp.toLp 2 fun j : Fin n ↦
            two_dimensional_total_variation_vertical_difference x i j)
        (WithLp.toLp 2 fun i : Fin (m - 1) ↦ WithLp.toLp 2 fun j : Fin n ↦ z.snd i j) =
      ∑ i : Fin m, ∑ j : Fin n,
        x i j *
          ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
            (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0))
  calc
    inner ℝ
        (WithLp.toLp 2 fun i : Fin (m - 1) ↦
          WithLp.toLp 2 fun j : Fin n ↦
            two_dimensional_total_variation_vertical_difference x i j)
        (WithLp.toLp 2 fun i : Fin (m - 1) ↦ WithLp.toLp 2 fun j : Fin n ↦ z.snd i j) =
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        (two_dimensional_total_variation_vertical_difference x i j) * z.snd i j := by
      simp_rw [PiLp.inner_apply, real_inner_eq_mul]
    _ = ∑ j : Fin n, ∑ i : Fin (m - 1),
          (two_dimensional_total_variation_vertical_difference x i j) * z.snd i j := by
      rw [Finset.sum_comm]
    _ =
      ∑ j : Fin n, ∑ i : Fin m,
        x i j *
          ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
            (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa [two_dimensional_total_variation_vertical_difference_apply] using
        forward_difference_sum_eq_zero_padded m (fun i ↦ x i j) (fun i ↦ z.snd i j)
    _ = ∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
              (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
      rw [Finset.sum_comm]

/-- Helper for Proposition 12.5: the adjoint of the discrete TV difference operator is the
zero-padded discrete divergence. -/
abbrev zero_padded_divergence (z : DualSpace m n) : MatrixSpace m n :=
  fun i j ↦
    (if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) +
      (if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
      (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0) -
      (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)

/-- Helper for Proposition 12.5: the Hilbert adjoint agrees with the zero-padded divergence matrix
on every entry. -/
lemma two_dimensional_total_variation_difference_adjoint_eq_zero_padded_divergence
    (z : DualSpace m n) :
    Aᵀ[m, n] z = zero_padded_divergence m n z := by
  apply ext_inner_left ℝ
  intro x
  -- Route correction: identify the adjoint globally by the Hilbert pairing before reading off a
  -- coordinate formula; this keeps the proof aligned with the textbook summation-by-parts route.
  calc
    inner ℝ x (Aᵀ[m, n] z) = inner ℝ (A[m, n] x) z := by
      simpa using (LinearMap.adjoint_inner_right (A[m, n]) x z)
    _ = inner ℝ ((A[m, n] x).fst) z.fst + inner ℝ ((A[m, n] x).snd) z.snd := by
      simp [WithLp.prod_inner_apply]
    _ = inner ℝ (two_dimensional_total_variation_horizontal_difference x) z.fst +
          inner ℝ (two_dimensional_total_variation_vertical_difference x) z.snd := by
      rw [two_dimensional_total_variation_difference_fst,
        two_dimensional_total_variation_difference_snd]
    _ =
        (∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) -
              (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0))) +
          ∑ i : Fin m, ∑ j : Fin n,
            x i j *
              ((if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
                (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
      rw [horizontal_difference_inner_eq_zero_padded, vertical_difference_inner_eq_zero_padded]
    _ = ∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) +
              (if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
              (if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0) -
              (if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0)) := by
      -- Combine the horizontal and vertical contributions into the single divergence summand.
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j hj
      ring
    _ = inner ℝ x (zero_padded_divergence m n z) := by
      -- Re-expand the Frobenius pairing of matrices back into the entrywise double sum.
      change
        ∑ i : Fin m, ∑ j : Fin n,
          x i j *
            ((((if h : j.1 < n - 1 then z.fst i (j.castLT h) else 0) +
                  if h : i.1 < m - 1 then z.snd (i.castLT h) j else 0) -
                if h : 0 < j.1 then z.fst i (pred_sub_index n j h) else 0) -
              if h : 0 < i.1 then z.snd (pred_sub_index m i h) j else 0) =
          inner ℝ
            (WithLp.toLp 2 fun i : Fin m ↦ WithLp.toLp 2 fun j : Fin n ↦ x i j)
            (WithLp.toLp 2 fun i : Fin m ↦
              WithLp.toLp 2 fun j : Fin n ↦ zero_padded_divergence m n z i j)
      simp_rw [PiLp.inner_apply, real_inner_eq_mul]

/-- Proposition 12.5: the Hilbert adjoint `Aᵀ[m, n]` of the two-dimensional TV operator
`A[m, n]` has the divergence-style coordinate formula with zero-extended boundary terms. -/
@[simp]
theorem two_dimensional_total_variation_difference_adjoint_apply
    (z : DualSpace m n) (i : Fin m) (j : Fin n) :
    Aᵀ[m, n] z i j =
      (if h : j.1 < n - 1 then z.fst i ⟨j.1, h⟩ else 0) +
        (if h : i.1 < m - 1 then z.snd ⟨i.1, h⟩ j else 0) -
        (if h : 0 < j.1 then z.fst i ⟨j.1 - 1, by omega⟩ else 0) -
        (if h : 0 < i.1 then z.snd ⟨i.1 - 1, by omega⟩ j else 0) := by
  -- Read off the coordinate formula from the global adjoint identification.
  simpa [zero_padded_divergence, pred_sub_index] using
    congr_fun (congr_fun
      (two_dimensional_total_variation_difference_adjoint_eq_zero_padded_divergence m n z) i) j

-- Proof sketch: specialize `two_dimensional_total_variation_difference_adjoint_apply` to the
-- canonical `L²` owner point `WithLp.toLp 2 (p, q)`, then simplify the `fst`/`snd` projections.
/-- Evaluating `Aᵀ[m, n]` on the canonical dual pair `(p, q)` recovers the textbook divergence
formula `p_{i,j} + q_{i,j} - p_{i,j-1} - q_{i-1,j}` with zero boundary extension. -/
@[simp] theorem two_dimensional_total_variation_difference_adjoint_toLp_apply
    (p : HorizontalSpace m n) (q : VerticalSpace m n) (i : Fin m) (j : Fin n) :
    Aᵀ[m, n] (toLp 2 (p, q)) i j =
      (if h : j.1 < n - 1 then p i ⟨j.1, h⟩ else 0) +
        (if h : i.1 < m - 1 then q ⟨i.1, h⟩ j else 0) -
        (if h : 0 < j.1 then p i ⟨j.1 - 1, by omega⟩ else 0) -
        (if h : 0 < i.1 then q ⟨i.1 - 1, by omega⟩ j else 0) := by
  simpa only using
    two_dimensional_total_variation_difference_adjoint_apply m n (toLp 2 (p, q)) i j

end
