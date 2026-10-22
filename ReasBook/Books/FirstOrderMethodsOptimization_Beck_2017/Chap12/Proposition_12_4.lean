/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_19
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_10
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_12.Spaces

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Matrix.Norms.Frobenius
open TwoDimensionalTV WithLp

noncomputable section

section

variable {m n : ℕ}

/- Semantic search note: `lean_leansearch` was unavailable in this environment, so this file uses
the Chapter 12 `TwoDimensionalTV` space owners together with mathlib's canonical `WithLp 2`
product owner for the horizontal/vertical dual pair. -/

/-- The raw horizontal forward-difference array `p^x`. -/
private def horizontal_difference_data (x : MatrixSpace m n) : HorizontalSpace m n :=
  fun i j ↦ x i (Fin.castLE (Nat.sub_le n 1) j) - x i ⟨(j : ℕ) + 1, by omega⟩

/-- The raw horizontal forward-difference array is additive in `x`. -/
private theorem horizontal_difference_data_map_add (x y : MatrixSpace m n) :
    horizontal_difference_data (x + y) =
      horizontal_difference_data x + horizontal_difference_data y := by
  -- Compare the two matrices entrywise and expand the forward differences.
  ext i j
  simp [horizontal_difference_data, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The raw horizontal forward-difference array is homogeneous in `x`. -/
private theorem horizontal_difference_data_map_smul (a : ℝ) (x : MatrixSpace m n) :
    horizontal_difference_data (a • x) = a • horizontal_difference_data x := by
  -- Scalar multiplication distributes through each displayed difference entry.
  ext i j
  simp [horizontal_difference_data, sub_eq_add_neg, mul_add]

/-- The horizontal forward-difference operator `x ↦ p^x`, with
`p^x_(i,j) = x_(i,j) - x_(i,j+1)`. -/
def two_dimensional_total_variation_horizontal_difference :
    MatrixSpace m n →ₗ[ℝ] HorizontalSpace m n where
  toFun := horizontal_difference_data
  map_add' := horizontal_difference_data_map_add
  map_smul' := horizontal_difference_data_map_smul

/-- Evaluating the horizontal forward-difference array gives
`p^x_(i,j) = x_(i,j) - x_(i,j+1)`. -/
@[simp] theorem two_dimensional_total_variation_horizontal_difference_apply
    (x : MatrixSpace m n) (i : Fin m) (j : Fin (n - 1)) :
    two_dimensional_total_variation_horizontal_difference x i j =
      x i (Fin.castLE (Nat.sub_le n 1) j) - x i ⟨(j : ℕ) + 1, by omega⟩ := by
  -- The linear map was defined from the raw horizontal-difference data.
  rfl

/-- The raw vertical forward-difference array `q^x`. -/
private def vertical_difference_data (x : MatrixSpace m n) : VerticalSpace m n :=
  fun i j ↦ x (Fin.castLE (Nat.sub_le m 1) i) j - x ⟨(i : ℕ) + 1, by omega⟩ j

/-- The raw vertical forward-difference array is additive in `x`. -/
private theorem vertical_difference_data_map_add (x y : MatrixSpace m n) :
    vertical_difference_data (x + y) =
      vertical_difference_data x + vertical_difference_data y := by
  -- Compare the two matrices entrywise and expand the forward differences.
  ext i j
  simp [vertical_difference_data, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The raw vertical forward-difference array is homogeneous in `x`. -/
private theorem vertical_difference_data_map_smul (a : ℝ) (x : MatrixSpace m n) :
    vertical_difference_data (a • x) = a • vertical_difference_data x := by
  -- Scalar multiplication distributes through each displayed difference entry.
  ext i j
  simp [vertical_difference_data, sub_eq_add_neg, mul_add]

/-- The vertical forward-difference operator `x ↦ q^x`, with
`q^x_(i,j) = x_(i,j) - x_(i+1,j)`. -/
def two_dimensional_total_variation_vertical_difference :
    MatrixSpace m n →ₗ[ℝ] VerticalSpace m n where
  toFun := vertical_difference_data
  map_add' := vertical_difference_data_map_add
  map_smul' := vertical_difference_data_map_smul

/-- Evaluating the vertical forward-difference array gives
`q^x_(i,j) = x_(i,j) - x_(i+1,j)`. -/
@[simp] theorem two_dimensional_total_variation_vertical_difference_apply
    (x : MatrixSpace m n) (i : Fin (m - 1)) (j : Fin n) :
    two_dimensional_total_variation_vertical_difference x i j =
      x (Fin.castLE (Nat.sub_le m 1) i) j - x ⟨(i : ℕ) + 1, by omega⟩ j := by
  -- The linear map was defined from the raw vertical-difference data.
  rfl

/-- The discrete two-dimensional total-variation difference operator
`A(x) = (p^x, q^x)`. -/
def two_dimensional_total_variation_difference : MatrixSpace m n →ₗ[ℝ] DualSpace m n :=
  ((WithLp.linearEquiv 2 ℝ (HorizontalSpace m n × VerticalSpace m n)).symm.toLinearMap).comp
    (two_dimensional_total_variation_horizontal_difference.prod
      two_dimensional_total_variation_vertical_difference)

/- Textbook notation for the two-dimensional TV difference operator. -/
set_option quotPrecheck false in
notation:max "A[" m "," n "]" =>
  (show MatrixSpace m n →ₗ[ℝ] DualSpace m n from
    two_dimensional_total_variation_difference)

/- Textbook notation for the Hilbert adjoint of the two-dimensional TV difference operator. -/
set_option quotPrecheck false in
notation:max "Aᵀ[" m "," n "]" =>
  (A[m, n]).adjoint

/-- The first component of `A(x)` is the horizontal-difference array `p^x`. -/
@[simp] theorem two_dimensional_total_variation_difference_fst (x : MatrixSpace m n) :
    (A[m, n] x).fst = two_dimensional_total_variation_horizontal_difference x := by
  -- The `WithLp` product equivalence reads back the first component definitionally.
  rfl

/-- The second component of `A(x)` is the vertical-difference array `q^x`. -/
@[simp] theorem two_dimensional_total_variation_difference_snd (x : MatrixSpace m n) :
    (A[m, n] x).snd = two_dimensional_total_variation_vertical_difference x := by
  -- The `WithLp` product equivalence reads back the second component definitionally.
  rfl

/-- Proposition 12.4 (1): evaluating the Chapter 12 denoising objective with the
two-dimensional TV operator `A[m, n]` gives the main-model form
`x ↦ (1 / 2) ‖x - d‖_F^2 + λ g (A x)`. Choosing `g` to be the isotropic or anisotropic
regularizer below gives the two textbook TV denoising models. -/
theorem two_dimensional_total_variation_denoising_problem_objective_apply
    (g : DualSpace m n → ℝ) (d : MatrixSpace m n) (lam : ℝ) (x : MatrixSpace m n) :
    denoising_problem_objective d (fun z : DualSpace m n ↦ ↑(lam * g z)) A[m, n] x =
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + ↑(lam * g (A[m, n] x)) := by
  -- This is exactly Definition 12.10 specialized to the TV operator and regularizer.
  simpa using
    (denoising_problem_objective_apply d (fun z : DualSpace m n ↦ ↑(lam * g z)) A[m, n] x)

attribute [simp] two_dimensional_total_variation_denoising_problem_objective_apply

/-- The isotropic two-dimensional total-variation regularizer `g₁` on the canonical `L²`
product of the horizontal and vertical difference spaces. -/
def two_dimensional_total_variation_isotropic_regularizer (z : DualSpace m n) : ℝ :=
  let p := z.fst
  let q := z.snd
  (∑ i : Fin m, ∑ j : Fin (n - 1),
      if hi : (i : ℕ) + 1 < m then
        Real.sqrt
          (p i j ^ (2 : ℕ) +
            q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j) ^
              (2 : ℕ))
      else
        |p i j|) +
    ∑ i : Fin (m - 1), ∑ j : Fin n, if (j : ℕ) + 1 < n then (0 : ℝ) else |q i j|

/-- Expanding `g₁` gives the textbook isotropic TV formula with interior Euclidean norms and
boundary absolute values. -/
@[simp] theorem two_dimensional_total_variation_isotropic_regularizer_apply
    (p : HorizontalSpace m n) (q : VerticalSpace m n) :
    two_dimensional_total_variation_isotropic_regularizer (toLp 2 (p, q)) =
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        if hi : (i : ℕ) + 1 < m then
          Real.sqrt
            (p i j ^ (2 : ℕ) +
              q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j) ^
                (2 : ℕ))
        else
          |p i j|) +
        ∑ i : Fin (m - 1), ∑ j : Fin n, if (j : ℕ) + 1 < n then (0 : ℝ) else |q i j| := by
  -- Evaluating the regularizer at `toLp 2 (p, q)` just exposes the two coordinates.
  rfl

/-- The anisotropic two-dimensional total-variation regularizer `g_{ℓ¹}` on the canonical `L²`
product of the horizontal and vertical difference spaces. -/
def two_dimensional_total_variation_anisotropic_regularizer (z : DualSpace m n) : ℝ :=
  let p := z.fst
  let q := z.snd
  (∑ i : Fin m, ∑ j : Fin (n - 1), |p i j|) +
    ∑ i : Fin (m - 1), ∑ j : Fin n, |q i j|

/-- Expanding `g_{ℓ¹}` gives the textbook anisotropic TV formula as the sum of the absolute
values of all horizontal and vertical differences. -/
@[simp] theorem two_dimensional_total_variation_anisotropic_regularizer_apply
    (p : HorizontalSpace m n) (q : VerticalSpace m n) :
    two_dimensional_total_variation_anisotropic_regularizer (toLp 2 (p, q)) =
      (∑ i : Fin m, ∑ j : Fin (n - 1), |p i j|) +
        ∑ i : Fin (m - 1), ∑ j : Fin n, |q i j| := by
  -- Evaluating the regularizer at `toLp 2 (p, q)` just exposes the two coordinates.
  rfl

/-- The isotropic shrinkage factor
`1 - λ / max {sqrt (p^2 + q^2), λ}` appearing in the proximal formula for `g₁`. -/
def two_dimensional_total_variation_isotropic_shrink_factor (lam p q : ℝ) : ℝ :=
  1 - lam / max (Real.sqrt (p ^ (2 : ℕ) + q ^ (2 : ℕ))) lam

/-- Helper for Proposition 12.4: the proximal map of the two-dimensional Euclidean norm penalty is
the singleton given by the textbook isotropic shrinkage factor. -/
private theorem two_dimensional_total_variation_pair_prox_eq_singleton
    (lam : ℝ) (hlam : 0 ≤ lam) (a b : ℝ) :
    prox[fun y : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖y‖)]
      (toLp 2 ![a, b]) =
        {toLp 2
          ![two_dimensional_total_variation_isotropic_shrink_factor lam a b * a,
            two_dimensional_total_variation_isotropic_shrink_factor lam a b * b]} := by
  let x : EuclideanSpace ℝ (Fin 2) := toLp 2 ![a, b]
  have hnorm_sq : ‖x‖ ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    -- Compute the squared Euclidean norm of the two-entry block explicitly.
    simpa [x, Fin.sum_univ_two, pow_two] using EuclideanSpace.real_norm_sq_eq x
  have hnorm :
      ‖x‖ = Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    -- Both sides are nonnegative and have the same square, so they coincide.
    have hsqrt :
        Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
      exact Real.sq_sqrt (by positivity)
    nlinarith [hnorm_sq, hsqrt, norm_nonneg x, Real.sqrt_nonneg (a ^ (2 : ℕ) + b ^ (2 : ℕ))]
  have hpoint :
      ((1 - lam / max ‖x‖ lam) • x : EuclideanSpace ℝ (Fin 2)) =
        toLp 2
          ![two_dimensional_total_variation_isotropic_shrink_factor lam a b * a,
            two_dimensional_total_variation_isotropic_shrink_factor lam a b * b] := by
    -- After rewriting the norm, the singleton point is just scalar multiplication of a 2-vector.
    ext i
    fin_cases i <;> simp [x, two_dimensional_total_variation_isotropic_shrink_factor, hnorm]
  have hpen :
      (norm_penalty lam : EuclideanSpace ℝ (Fin 2) → EReal) =
        fun y : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖y‖) := by
    -- The Chapter 6 norm penalty is exactly the displayed scalar multiple of the Euclidean norm.
    funext y
    simp [norm_penalty_apply]
  by_cases hzero : lam = 0
  · -- At `λ = 0`, the norm penalty is the zero function, so the prox map is the identity.
    subst lam
    have hpen0 : (norm_penalty (0 : ℝ) : EuclideanSpace ℝ (Fin 2) → EReal) = 0 := by
      funext y
      simp [norm_penalty_apply]
    rw [← hpen, hpen0]
    simpa [x, two_dimensional_total_variation_isotropic_shrink_factor] using
      (prox_zero_eq_singleton x)
  · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hzero)
    -- Specialize the Chapter 6 norm-prox formula and rewrite its singleton point.
    rw [← hpen]
    simpa [x, hpoint] using
      prox_norm_penalty_eq_singleton_shrinkage lam hlam_pos x

/-- Helper for Proposition 12.4: the Chapter 6 two-dimensional norm proximal objective expands
to the explicit scalar formula used by the isotropic interior TV block. -/
private theorem pair_norm_proximal_objective_apply
    (lam pa qb a b : ℝ) :
    proximal_objective
        (fun y : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖y‖))
        (toLp 2 ![pa, qb]) (toLp 2 ![a, b]) =
      (((lam * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) +
          (1 / 2 : ℝ) * (a - pa) ^ (2 : ℕ) +
          (1 / 2 : ℝ) * (b - qb) ^ (2 : ℕ) : ℝ)) : EReal) := by
  let y : EuclideanSpace ℝ (Fin 2) := toLp 2 ![a, b]
  let x : EuclideanSpace ℝ (Fin 2) := toLp 2 ![pa, qb]
  have hy_norm_sq : ‖y‖ ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    -- Expand the squared Euclidean norm of the current interior pair.
    simpa [y, Fin.sum_univ_two, pow_two] using EuclideanSpace.real_norm_sq_eq y
  have hy_norm : ‖y‖ = Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    -- Both sides are nonnegative and have the same square, so they agree.
    have hsqrt :
        Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
      exact Real.sq_sqrt (by positivity)
    nlinarith [hy_norm_sq, hsqrt, norm_nonneg y,
      Real.sqrt_nonneg (a ^ (2 : ℕ) + b ^ (2 : ℕ))]
  have hdist_sq : ‖y - x‖ ^ (2 : ℕ) = (a - pa) ^ (2 : ℕ) + (b - qb) ^ (2 : ℕ) := by
    -- Expand the squared distance between the current pair and the data pair entrywise.
    simpa [x, y, Fin.sum_univ_two, pow_two, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using EuclideanSpace.real_norm_sq_eq (y - x)
  -- Rewrite the proximal objective into the explicit real-valued pair expression.
  calc
    proximal_objective
        (fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖))
        x y =
      (((lam * ‖y‖ + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
        rw [proximal_objective_apply, ← EReal.coe_add]
    _ =
      (((lam * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) +
          (1 / 2 : ℝ) * (a - pa) ^ (2 : ℕ) +
          (1 / 2 : ℝ) * (b - qb) ^ (2 : ℕ) : ℝ)) : EReal) := by
        congr 1
        rw [hy_norm, hdist_sq]
        ring

/-- Helper for Proposition 12.4: the Chapter 6 pair proximal objective is always a coercion of a
finite real number, so it is ready for `EReal` cancellation arguments. -/
private theorem pair_norm_proximal_objective_eq_coe
    (lam pa qb a b : ℝ) :
    ∃ r : ℝ,
      proximal_objective
          (fun y : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖y‖))
          (toLp 2 ![pa, qb]) (toLp 2 ![a, b]) = (r : EReal) := by
  -- Package the explicit pair-objective formula as a finite real witness.
  refine ⟨lam * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) +
      (1 / 2 : ℝ) * (a - pa) ^ (2 : ℕ) +
      (1 / 2 : ℝ) * (b - qb) ^ (2 : ℕ), ?_⟩
  simpa using pair_norm_proximal_objective_apply lam pa qb a b

/-- Helper for Proposition 12.4: coercing a finite real sum into `EReal` matches summing the
coerced real terms. -/
private theorem ereal_coe_sum {α : Type*} (s : Finset α) (φ : α → ℝ) :
    (((∑ a ∈ s, φ a : ℝ) : EReal)) = ∑ a ∈ s, ((φ a : ℝ) : EReal) := by
  classical
  -- Induct over the finite set and push the coercion through one inserted summand at a time.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, hs]

/-- Helper for Proposition 12.4: coercing a finite double real sum into `EReal` matches summing
the coerced real terms entrywise. -/
private theorem ereal_coe_double_sum
    {α β : Type*} [Fintype α] [Fintype β] (φ : α → β → ℝ) :
    (((∑ a, ∑ b, φ a b : ℝ) : EReal)) = ∑ a, ∑ b, ((φ a b : ℝ) : EReal) := by
  -- Push the `EReal` coercion through the outer sum and then through each inner sum.
  calc
    (((∑ a, ∑ b, φ a b : ℝ) : EReal))
        = ∑ a, (((∑ b, φ a b : ℝ) : EReal)) := by
            simpa using (ereal_coe_sum Finset.univ fun a : α ↦ ∑ b, φ a b)
    _ = ∑ a, ∑ b, ((φ a b : ℝ) : EReal) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa using (ereal_coe_sum Finset.univ fun b : β ↦ φ a b)

/-- Helper for Proposition 12.4: squaring the Frobenius norm of a horizontal-difference matrix
recovers the sum of the squares of its entries. -/
private theorem horizontal_matrix_frobenius_norm_sq_eq_sum_sq
    (x : HorizontalSpace m n) :
    ‖x‖ ^ (2 : ℕ) = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
  have hnorm :
      ‖x‖ = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) := by
    -- This is the Frobenius norm formula specialized to the horizontal matrix space.
    simpa [Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def x)
  -- Square the Frobenius formula and simplify the entrywise absolute-value squares.
  calc
    ‖x‖ ^ (2 : ℕ) = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [hnorm]
    _ = ∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ) := by
      exact Real.sq_sqrt (by positivity)
    _ = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
      simp_rw [Real.norm_eq_abs, sq_abs]

/-- Helper for Proposition 12.4: squaring the Frobenius norm of a vertical-difference matrix
recovers the sum of the squares of its entries. -/
private theorem vertical_matrix_frobenius_norm_sq_eq_sum_sq
    (x : VerticalSpace m n) :
    ‖x‖ ^ (2 : ℕ) = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
  have hnorm :
      ‖x‖ = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) := by
    -- This is the Frobenius norm formula specialized to the vertical matrix space.
    simpa [Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def x)
  -- Square the Frobenius formula and simplify the entrywise absolute-value squares.
  calc
    ‖x‖ ^ (2 : ℕ) = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [hnorm]
    _ = ∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ) := by
      exact Real.sq_sqrt (by positivity)
    _ = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
      simp_rw [Real.norm_eq_abs, sq_abs]

/-- Helper for Proposition 12.4: the quadratic term in the TV-space proximal objective splits into
the horizontal and vertical Frobenius-coordinate sums. -/
private theorem tv_pair_quadratic_term_eq_sum
    (p u : HorizontalSpace m n) (q v : VerticalSpace m n) :
    ((((1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) : ℝ)) : EReal) =
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        ((((1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal)) +
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        ((((1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
  have hnorm_sq :
      ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) =
        ‖u - p‖ ^ (2 : ℕ) + ‖v - q‖ ^ (2 : ℕ) := by
    -- The `WithLp 2` product norm is the sum of the squared Frobenius norms of the two blocks.
    simpa using
      (WithLp.prod_norm_sq_eq_of_L2
        ((toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)))
  have hreal :
      ((1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) : ℝ) =
        (∑ i : Fin m, ∑ j : Fin (n - 1), (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)) +
        ∑ i : Fin (m - 1), ∑ j : Fin n, (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) := by
    -- Rewrite both Frobenius squares by their entrywise formulas and distribute the factor `1/2`.
    rw [hnorm_sq, horizontal_matrix_frobenius_norm_sq_eq_sum_sq (u - p),
      vertical_matrix_frobenius_norm_sq_eq_sum_sq (v - q), mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
      simpa using rfl
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
      simpa using rfl
  -- Coerce the real identity into `EReal` and push the coercion through both finite sums.
  calc
    ((((1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) : ℝ)) : EReal) =
        ((((∑ i : Fin m, ∑ j : Fin (n - 1), (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)) +
            ∑ i : Fin (m - 1), ∑ j : Fin n,
              (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    _ =
        (((∑ i : Fin m, ∑ j : Fin (n - 1),
            (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          (((∑ i : Fin (m - 1), ∑ j : Fin n,
            (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
      rw [EReal.coe_add]
    _ =
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          ((((1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal)) +
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          ((((1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
      rw [ereal_coe_double_sum (fun i j ↦ (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)),
        ereal_coe_double_sum (fun i j ↦ (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ))]

/-- Helper for Proposition 12.4: the anisotropic TV proximal objective is the sum of the scalar
absolute-value proximal objectives over the horizontal and vertical entries. -/
private theorem anisotropic_proximal_objective_sum_formula
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) :
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (u, v)) =
      ((((∑ i : Fin m, ∑ j : Fin (n - 1),
          (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) +
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ) : ℝ)) : EReal) := by
  have hregularizer :
      lam *
          (two_dimensional_total_variation_anisotropic_regularizer (toLp 2 (u, v))) =
        (∑ i : Fin m, ∑ j : Fin (n - 1), (lam * |u i j| : ℝ)) +
          ∑ i : Fin (m - 1), ∑ j : Fin n, (lam * |v i j| : ℝ) := by
    -- First rewrite the anisotropic regularizer as the two absolute-value double sums, then
    -- distribute the scalar `λ` through each finite sum.
    rw [two_dimensional_total_variation_anisotropic_regularizer_apply, mul_add, Finset.mul_sum,
      Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
  have hhorizontal_block :
      ((((∑ i : Fin m, ∑ j : Fin (n - 1), (lam * |u i j| : ℝ)) : ℝ)) : EReal) +
          ∑ i : Fin m, ∑ j : Fin (n - 1),
            ((((1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal) =
        ((((∑ i : Fin m, ∑ j : Fin (n - 1),
            (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : ℝ)) : EReal) := by
    -- Regroup the horizontal penalty and quadratic pieces inside a single real double sum.
    rw [← ereal_coe_double_sum (fun i j ↦ (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)),
      ← EReal.coe_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
  have hvertical_block :
      ((((∑ i : Fin (m - 1), ∑ j : Fin n, (lam * |v i j| : ℝ)) : ℝ)) : EReal) +
          ∑ i : Fin (m - 1), ∑ j : Fin n,
            ((((1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) =
        ((((∑ i : Fin (m - 1), ∑ j : Fin n,
            (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : ℝ)) : EReal) := by
    -- Regroup the vertical penalty and quadratic pieces inside a single real double sum.
    rw [← ereal_coe_double_sum (fun i j ↦ (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ)),
      ← EReal.coe_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
  have hregularizer_ereal :
      ((((lam * two_dimensional_total_variation_anisotropic_regularizer (toLp 2 (u, v)) : ℝ)) :
        EReal)) =
        ((((∑ i : Fin m, ∑ j : Fin (n - 1), (lam * |u i j| : ℝ)) +
            ∑ i : Fin (m - 1), ∑ j : Fin n, (lam * |v i j| : ℝ) : ℝ)) : EReal) := by
    -- Coerce the real-coordinate regularizer decomposition into `EReal`.
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hregularizer
  -- Route correction: keep the source-proof split into horizontal and vertical scalar blocks,
  -- and only combine the blocks after the real-coordinate regrouping is finished.
  calc
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (u, v)) =
      ((((∑ i : Fin m, ∑ j : Fin (n - 1), (lam * |u i j| : ℝ)) +
          ∑ i : Fin (m - 1), ∑ j : Fin n, (lam * |v i j| : ℝ) : ℝ)) : EReal) +
        ((∑ i : Fin m, ∑ j : Fin (n - 1),
            ((((1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal)) +
          ∑ i : Fin (m - 1), ∑ j : Fin n,
            ((((1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal)) := by
          rw [proximal_objective_apply, tv_pair_quadratic_term_eq_sum, hregularizer_ereal]
    _ =
      (((((∑ i : Fin m, ∑ j : Fin (n - 1), (lam * |u i j| : ℝ)) : ℝ)) : EReal) +
          ∑ i : Fin m, ∑ j : Fin (n - 1),
            ((((1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal)) +
        (((((∑ i : Fin (m - 1), ∑ j : Fin n, (lam * |v i j| : ℝ)) : ℝ)) : EReal) +
          ∑ i : Fin (m - 1), ∑ j : Fin n,
            ((((1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal)) := by
      rw [EReal.coe_add]
      simp [add_assoc, add_left_comm, add_comm]
    _ =
      ((((∑ i : Fin m, ∑ j : Fin (n - 1),
          (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : ℝ)) : EReal) +
        ((((∑ i : Fin (m - 1), ∑ j : Fin n,
          (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : ℝ)) : EReal) := by
      rw [hhorizontal_block, hvertical_block]
    _ =
      ((((∑ i : Fin m, ∑ j : Fin (n - 1),
          (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) +
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ) : ℝ)) : EReal) := by
      rw [← EReal.coe_add]

/-- Helper for Proposition 12.4: when the ambient index is a successor, the canonical
`castLE` embedding from `Fin k` into `Fin (k + 1)` is exactly `Fin.castSucc`. -/
private theorem castLE_sub_one_eq_castSucc {k : ℕ} (i : Fin k) :
    Fin.castLE (Nat.sub_le (k + 1) 1) i = i.castSucc := by
  -- Both successor embeddings preserve the underlying natural number.
  ext
  rfl

/-- Helper for Proposition 12.4: summing an interior branch over `Fin k` is equivalent to
reindexing the sum over the canonical interior copy `Fin (k - 1)`. -/
private theorem interior_sum_eq_castLE_sum {k : ℕ} (φ : Fin k → ℝ) :
    (∑ i : Fin k, if hi : (i : ℕ) + 1 < k then φ i else 0) =
      ∑ i : Fin (k - 1), φ (Fin.castLE (Nat.sub_le k 1) i) := by
  cases k with
  | zero =>
      simp
  | succ k =>
      -- Split the successor-index sum into the interior `castSucc` part and the final boundary term.
      calc
        (∑ i : Fin (k + 1), if hi : (i : ℕ) + 1 < k + 1 then φ i else 0) =
            ∑ i : Fin k, φ i.castSucc := by
              rw [Fin.sum_univ_castSucc]
              simp
        _ = ∑ i : Fin k, φ (Fin.castLE (Nat.sub_le (k + 1) 1) i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [castLE_sub_one_eq_castSucc]

/-- Helper for Proposition 12.4: summing a proof-dependent interior branch over `Fin k` is
equivalent to reindexing it over the canonical interior copy `Fin (k - 1)`. -/
private theorem dependent_interior_sum_eq_castLE_sum {k : ℕ}
    (ψ : ∀ i : Fin k, ((i : ℕ) + 1 < k) → ℝ) :
    (∑ i : Fin k, if hi : (i : ℕ) + 1 < k then ψ i hi else 0) =
      ∑ i : Fin (k - 1), ψ (Fin.castLE (Nat.sub_le k 1) i)
        (Nat.lt_sub_iff_add_lt.mp i.isLt) := by
  cases k with
  | zero =>
      simp
  | succ k =>
      -- Split the successor-index sum into the interior `castSucc` part and the final boundary
      -- term, then identify the surviving proof-dependent interior branches by proof irrelevance.
      calc
        (∑ i : Fin (k + 1), if hi : (i : ℕ) + 1 < k + 1 then ψ i hi else 0) =
            ∑ i : Fin k, ψ i.castSucc (by simpa using i.isLt) := by
              rw [Fin.sum_univ_castSucc]
              have hsum :
                  (∑ i : Fin k,
                      if hi : ((i.castSucc : Fin (k + 1)) : ℕ) + 1 < k + 1 then
                        ψ i.castSucc hi
                      else
                        0) =
                    ∑ i : Fin k, ψ i.castSucc (by simpa using i.isLt) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hlt : ((i.castSucc : Fin (k + 1)) : ℕ) + 1 < k + 1 := by
                  simpa using i.isLt
                rw [dif_pos hlt]
              have hlast :
                  (if hi : (((Fin.last k : Fin (k + 1)) : ℕ) + 1 < k + 1) then
                    ψ (Fin.last k) hi
                  else
                    0) = 0 := by
                have hnot : ¬ (((Fin.last k : Fin (k + 1)) : ℕ) + 1 < k + 1) := by
                  simp [Fin.last]
                simp [hnot]
              simpa [hsum, hlast]
        _ = ∑ i : Fin k, ψ (Fin.castLE (Nat.sub_le (k + 1) 1) i)
              (Nat.lt_sub_iff_add_lt.mp i.isLt) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hcast : Fin.castLE (Nat.sub_le (k + 1) 1) i = i.castSucc := by
                simpa using castLE_sub_one_eq_castSucc i
              cases hcast
              have hproof :
                  Nat.lt_sub_iff_add_lt.mp i.isLt =
                    (by simpa using i.isLt :
                      ((i.castSucc : Fin (k + 1)) : ℕ) + 1 < k + 1) := by
                apply Subsingleton.elim
              cases hproof
              rfl

/-- Helper for Proposition 12.4: an interior row-conditional double sum can be reindexed over
the canonical interior row set `Fin (m - 1)`. -/
private theorem interior_row_double_sum_eq_castLE_sum
    (φ : Fin m → Fin (n - 1) → ℝ) :
    (∑ i : Fin m, ∑ j : Fin (n - 1), if hi : (i : ℕ) + 1 < m then φ i j else 0) =
      ∑ i : Fin (m - 1), ∑ j : Fin (n - 1), φ (Fin.castLE (Nat.sub_le m 1) i) j := by
  -- Reindex the outer sum and leave the inner sum unchanged.
  simpa using
    (interior_sum_eq_castLE_sum (k := m) (φ := fun i : Fin m ↦ ∑ j : Fin (n - 1), φ i j))

/-- Helper for Proposition 12.4: an interior row-conditional double sum with proof-dependent row
branches can be reindexed over the canonical interior row set `Fin (m - 1)`. -/
private theorem dependent_interior_row_double_sum_eq_castLE_sum
    (ψ : ∀ i : Fin m, ((i : ℕ) + 1 < m) → Fin (n - 1) → ℝ) :
    (∑ i : Fin m, ∑ j : Fin (n - 1), if hi : (i : ℕ) + 1 < m then ψ i hi j else 0) =
      ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        ψ (Fin.castLE (Nat.sub_le m 1) i) (Nat.lt_sub_iff_add_lt.mp i.isLt) j := by
  -- Reindex the outer row sum while keeping the inner column sum unchanged.
  simpa using
    (dependent_interior_sum_eq_castLE_sum (k := m)
      (ψ := fun i hi ↦ ∑ j : Fin (n - 1), ψ i hi j))

/-- Helper for Proposition 12.4: an interior column-conditional double sum can be reindexed over
the canonical interior column set `Fin (n - 1)`. -/
private theorem interior_column_double_sum_eq_castLE_sum
    (φ : Fin (m - 1) → Fin n → ℝ) :
    (∑ i : Fin (m - 1), ∑ j : Fin n, if hj : (j : ℕ) + 1 < n then φ i j else 0) =
      ∑ i : Fin (m - 1), ∑ j : Fin (n - 1), φ i (Fin.castLE (Nat.sub_le n 1) j) := by
  -- Reindex each rowwise interior-column sum separately.
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa using
    (interior_sum_eq_castLE_sum (k := n) (φ := fun j : Fin n ↦ φ i j))

/-- Helper for Proposition 12.4: multiplying the first isotropic TV sum by `λ` splits it into the
interior coupled Euclidean-norm blocks and the last-row scalar boundary blocks. -/
private theorem isotropic_horizontal_regularizer_split
    (lam : ℝ) (u : HorizontalSpace m n) (v : VerticalSpace m n) :
    lam *
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          if hi : (i : ℕ) + 1 < m then
            Real.sqrt
              (u i j ^ (2 : ℕ) +
                v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi))
                  (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ))
          else
            |u i j|) =
      (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        (lam *
            Real.sqrt
              (u (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
                v i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)) +
      ∑ i : Fin m, ∑ j : Fin (n - 1),
        if hi : (i : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |u i j| : ℝ) := by
  -- Split the first isotropic TV sum into interior coupled blocks and last-row scalar blocks.
  calc
    lam *
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          if hi : (i : ℕ) + 1 < m then
            Real.sqrt
              (u i j ^ (2 : ℕ) +
                v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi))
                  (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ))
          else
            |u i j|) =
      ∑ i : Fin m, ∑ j : Fin (n - 1),
        if hi : (i : ℕ) + 1 < m then
          (lam *
            Real.sqrt
              (u i j ^ (2 : ℕ) +
                v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi))
                  (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)
        else
          (lam * |u i j| : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        by_cases hrow : (i : ℕ) + 1 < m <;> simp [hrow]
    _ =
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        if hi : (i : ℕ) + 1 < m then
          (lam *
            Real.sqrt
              (u i j ^ (2 : ℕ) +
                v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi))
                  (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)
        else
          (0 : ℝ)) +
        ∑ i : Fin m, ∑ j : Fin (n - 1),
          if hi : (i : ℕ) + 1 < m then
            (0 : ℝ)
          else
            (lam * |u i j| : ℝ) := by
        calc
          (∑ i : Fin m, ∑ j : Fin (n - 1),
              if hi : (i : ℕ) + 1 < m then
                (lam *
                  Real.sqrt
                    (u i j ^ (2 : ℕ) +
                      v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi))
                        (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)
              else
                (lam * |u i j| : ℝ)) =
            ∑ i : Fin m, ∑ j : Fin (n - 1),
              ((if hi : (i : ℕ) + 1 < m then
                  (lam *
                    Real.sqrt
                      (u i j ^ (2 : ℕ) +
                        v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi))
                          (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)
                else
                  (0 : ℝ)) +
                (if hi : (i : ℕ) + 1 < m then
                  (0 : ℝ)
                else
                  (lam * |u i j| : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hrow : (i : ℕ) + 1 < m <;> simp [hrow]
          _ =
            (∑ i : Fin m, ∑ j : Fin (n - 1),
              if hi : (i : ℕ) + 1 < m then
                (lam *
                  Real.sqrt
                    (u i j ^ (2 : ℕ) +
                      v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi))
                        (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)
              else
                (0 : ℝ)) +
              ∑ i : Fin m, ∑ j : Fin (n - 1),
                if hi : (i : ℕ) + 1 < m then
                  (0 : ℝ)
                else
                  (lam * |u i j| : ℝ) := by
              simp_rw [Finset.sum_add_distrib]
    _ =
      (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        (lam *
            Real.sqrt
              (u (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
                v i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)) +
        ∑ i : Fin m, ∑ j : Fin (n - 1),
          if hi : (i : ℕ) + 1 < m then
            (0 : ℝ)
          else
            (lam * |u i j| : ℝ) := by
        congr 1
        simpa using
          (dependent_interior_row_double_sum_eq_castLE_sum
            (ψ := fun i hi j ↦
              (lam *
                  Real.sqrt
                    (u i j ^ (2 : ℕ) +
                      v (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi))
                        (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)))

/-- Helper for Proposition 12.4: multiplying the second isotropic TV sum by `λ` keeps only the
last-column scalar boundary blocks. -/
private theorem isotropic_vertical_regularizer_split
    (lam : ℝ) (v : VerticalSpace m n) :
    lam *
        (∑ i : Fin (m - 1), ∑ j : Fin n,
          if (j : ℕ) + 1 < n then
            (0 : ℝ)
          else
            |v i j|) =
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        if (j : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |v i j| : ℝ) := by
  -- Distribute `λ` through the last-column scalar boundary sum.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases hcol : (j : ℕ) + 1 < n <;> simp [hcol]

/-- Helper for Proposition 12.4: the quadratic TV-space term splits into interior coupled blocks
and the last-row/last-column scalar boundary blocks. -/
private theorem isotropic_quadratic_block_split
    (p u : HorizontalSpace m n) (q v : VerticalSpace m n) :
    (∑ i : Fin m, ∑ j : Fin (n - 1),
        ((1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) +
      ∑ i : Fin (m - 1), ∑ j : Fin n,
        ((1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ) =
      ((∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          ((1 / 2 : ℝ) * (u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
              (1 / 2 : ℝ) * (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ)) +
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          if hi : (i : ℕ) + 1 < m then
            (0 : ℝ)
          else
            ((1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ))) +
        (∑ i : Fin (m - 1), ∑ j : Fin n,
          if hj : (j : ℕ) + 1 < n then
            (0 : ℝ)
          else
            ((1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) := by
  let uQuad : Fin m → Fin (n - 1) → ℝ :=
    fun i j ↦ (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)
  let vQuad : Fin (m - 1) → Fin n → ℝ :=
    fun i j ↦ (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ)
  have hu_split :
      (∑ i : Fin m, ∑ j : Fin (n - 1), uQuad i j) =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1), uQuad (Fin.castLE (Nat.sub_le m 1) i) j) +
          ∑ i : Fin m, ∑ j : Fin (n - 1),
            if hi : (i : ℕ) + 1 < m then
              (0 : ℝ)
            else
              uQuad i j := by
    -- Split the horizontal quadratic sum into interior rows and the last-row boundary.
    calc
      (∑ i : Fin m, ∑ j : Fin (n - 1), uQuad i j) =
          ∑ i : Fin m, ∑ j : Fin (n - 1),
            ((if hi : (i : ℕ) + 1 < m then uQuad i j else 0) +
              (if hi : (i : ℕ) + 1 < m then 0 else uQuad i j)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hrow : (i : ℕ) + 1 < m <;> simp [hrow]
      _ =
          (∑ i : Fin m, ∑ j : Fin (n - 1),
              if hi : (i : ℕ) + 1 < m then uQuad i j else 0) +
            ∑ i : Fin m, ∑ j : Fin (n - 1),
              if hi : (i : ℕ) + 1 < m then 0 else uQuad i j := by
            simp_rw [Finset.sum_add_distrib]
      _ =
          (∑ i : Fin (m - 1), ∑ j : Fin (n - 1), uQuad (Fin.castLE (Nat.sub_le m 1) i) j) +
            ∑ i : Fin m, ∑ j : Fin (n - 1),
              if hi : (i : ℕ) + 1 < m then 0 else uQuad i j := by
            rw [interior_row_double_sum_eq_castLE_sum (φ := uQuad)]
  have hv_split :
      (∑ i : Fin (m - 1), ∑ j : Fin n, vQuad i j) =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1), vQuad i (Fin.castLE (Nat.sub_le n 1) j)) +
          ∑ i : Fin (m - 1), ∑ j : Fin n,
            if hj : (j : ℕ) + 1 < n then
              (0 : ℝ)
            else
              vQuad i j := by
    -- Split the vertical quadratic sum into interior columns and the last-column boundary.
    calc
      (∑ i : Fin (m - 1), ∑ j : Fin n, vQuad i j) =
          ∑ i : Fin (m - 1), ∑ j : Fin n,
            ((if hj : (j : ℕ) + 1 < n then vQuad i j else 0) +
              (if hj : (j : ℕ) + 1 < n then 0 else vQuad i j)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hcol : (j : ℕ) + 1 < n <;> simp [hcol]
      _ =
          (∑ i : Fin (m - 1), ∑ j : Fin n,
              if hj : (j : ℕ) + 1 < n then vQuad i j else 0) +
            ∑ i : Fin (m - 1), ∑ j : Fin n,
              if hj : (j : ℕ) + 1 < n then 0 else vQuad i j := by
            simp_rw [Finset.sum_add_distrib]
      _ =
          (∑ i : Fin (m - 1), ∑ j : Fin (n - 1), vQuad i (Fin.castLE (Nat.sub_le n 1) j)) +
            ∑ i : Fin (m - 1), ∑ j : Fin n,
              if hj : (j : ℕ) + 1 < n then 0 else vQuad i j := by
            rw [interior_column_double_sum_eq_castLE_sum (φ := vQuad)]
  have hinterior_block :
      (∑ i : Fin (m - 1), ∑ j : Fin (n - 1), uQuad (Fin.castLE (Nat.sub_le m 1) i) j) +
          ∑ i : Fin (m - 1), ∑ j : Fin (n - 1), vQuad i (Fin.castLE (Nat.sub_le n 1) j) =
        ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          (uQuad (Fin.castLE (Nat.sub_le m 1) i) j +
            vQuad i (Fin.castLE (Nat.sub_le n 1) j) : ℝ) := by
    -- Regroup the two interior quadratic sums entrywise on the same interior grid.
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
  let interiorH : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin (n - 1), uQuad (Fin.castLE (Nat.sub_le m 1) i) j
  let interiorV : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin (n - 1), vQuad i (Fin.castLE (Nat.sub_le n 1) j)
  let boundaryH : ℝ :=
    ∑ i : Fin m, ∑ j : Fin (n - 1),
      if hi : (i : ℕ) + 1 < m then 0 else uQuad i j
  let boundaryV : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin n,
      if hj : (j : ℕ) + 1 < n then 0 else vQuad i j
  have hmiddle :
      ((interiorH + boundaryH) + (interiorV + boundaryV)) =
        ((interiorH + interiorV) + boundaryH + boundaryV) := by
    -- Reassociate the four real blocks before replacing the paired interior sum.
    ring
  have hcombined :
      ((interiorH + interiorV) + boundaryH + boundaryV) =
        (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
            (uQuad (Fin.castLE (Nat.sub_le m 1) i) j +
              vQuad i (Fin.castLE (Nat.sub_le n 1) j) : ℝ)) +
          boundaryH + boundaryV := by
    -- Replace the two separate interior sums by the coupled interior quadratic block sum.
    simpa [interiorH, interiorV, boundaryH, boundaryV, add_assoc] using
      congrArg (fun t : ℝ ↦ t + boundaryH + boundaryV) hinterior_block
  -- Reassemble the quadratic term in the same interior/boundary geometry as the isotropic TV
  -- regularizer.
  calc
    (∑ i : Fin m, ∑ j : Fin (n - 1), uQuad i j) +
        ∑ i : Fin (m - 1), ∑ j : Fin n, vQuad i j =
      ((interiorH + boundaryH) + (interiorV + boundaryV)) := by
          rw [hu_split, hv_split]
    _ =
      ((interiorH + interiorV) + boundaryH + boundaryV) := hmiddle
    _ =
      (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          (uQuad (Fin.castLE (Nat.sub_le m 1) i) j +
            vQuad i (Fin.castLE (Nat.sub_le n 1) j) : ℝ)) +
        boundaryH + boundaryV := hcombined
    _ = _ := by
      simp [boundaryH, boundaryV, uQuad, vQuad]

/-- Helper for Proposition 12.4: the canonical real-valued isotropic proximal-objective block sum
used by the source-proof decomposition. -/
private def isotropic_proximal_objective_sum_rhs
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) : ℝ :=
  (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
      (lam *
          Real.sqrt
            (u (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
              v i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) +
        (1 / 2 : ℝ) *
          (u (Fin.castLE (Nat.sub_le m 1) i) j -
              p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
        (1 / 2 : ℝ) *
          (v i (Fin.castLE (Nat.sub_le n 1) j) -
              q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ)) +
    (∑ i : Fin m, ∑ j : Fin (n - 1),
      if hi : (i : ℕ) + 1 < m then
        (0 : ℝ)
      else
        (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) +
    (∑ i : Fin (m - 1), ∑ j : Fin n,
      if hj : (j : ℕ) + 1 < n then
        (0 : ℝ)
      else
        (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ))

/-- Helper for Proposition 12.4: in `ℝ`, the isotropic TV proximal objective already has the
canonical interior-pair plus boundary-scalar decomposition used by the source proof. -/
private theorem isotropic_proximal_objective_sum_formula_real
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) :
    lam * two_dimensional_total_variation_isotropic_regularizer (toLp 2 (u, v)) +
        (1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) =
      isotropic_proximal_objective_sum_rhs lam p u q v := by
  let interiorReg : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
      (lam *
          Real.sqrt
            (u (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
              v i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) : ℝ)
  let boundaryHReg : ℝ :=
    ∑ i : Fin m, ∑ j : Fin (n - 1),
      if hi : (i : ℕ) + 1 < m then
        (0 : ℝ)
      else
        (lam * |u i j| : ℝ)
  let boundaryVReg : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin n,
      if hj : (j : ℕ) + 1 < n then
        (0 : ℝ)
      else
        (lam * |v i j| : ℝ)
  let interiorQuad : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
      ((1 / 2 : ℝ) * (u (Fin.castLE (Nat.sub_le m 1) i) j -
            p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
        (1 / 2 : ℝ) * (v i (Fin.castLE (Nat.sub_le n 1) j) -
            q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ)
  let boundaryHQuad : ℝ :=
    ∑ i : Fin m, ∑ j : Fin (n - 1),
      if hi : (i : ℕ) + 1 < m then
        (0 : ℝ)
      else
        ((1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)
  let boundaryVQuad : ℝ :=
    ∑ i : Fin (m - 1), ∑ j : Fin n,
      if hj : (j : ℕ) + 1 < n then
        (0 : ℝ)
      else
        ((1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)
  have hregularizer :
      lam * two_dimensional_total_variation_isotropic_regularizer (toLp 2 (u, v)) =
        interiorReg + boundaryHReg + boundaryVReg := by
    -- Split the real isotropic regularizer into the interior coupled blocks and the two boundary
    -- scalar blocks before touching any `EReal` coercions.
    rw [two_dimensional_total_variation_isotropic_regularizer_apply, mul_add,
      isotropic_horizontal_regularizer_split, isotropic_vertical_regularizer_split]
    simp [interiorReg, boundaryHReg, boundaryVReg, add_assoc]
  have hquadratic_raw :
      (1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) =
        (∑ i : Fin m, ∑ j : Fin (n - 1), (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)) +
          ∑ i : Fin (m - 1), ∑ j : Fin n, (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) := by
    have hnorm_sq :
        ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) =
          ‖u - p‖ ^ (2 : ℕ) + ‖v - q‖ ^ (2 : ℕ) := by
      -- The `WithLp 2` product norm splits into the two Frobenius-square contributions.
      simpa using
        (WithLp.prod_norm_sq_eq_of_L2
          ((toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)))
    -- Rewrite both Frobenius squares entrywise and distribute the scalar `1 / 2`.
    rw [hnorm_sq, horizontal_matrix_frobenius_norm_sq_eq_sum_sq (u - p),
      vertical_matrix_frobenius_norm_sq_eq_sum_sq (v - q), mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
      simpa using rfl
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
      simpa using rfl
  have hquadratic :
      (1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) =
        interiorQuad + boundaryHQuad + boundaryVQuad := by
    -- Reindex the quadratic term into the same interior/boundary geometry as the regularizer.
    calc
      (1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) =
          (∑ i : Fin m, ∑ j : Fin (n - 1), (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ)) +
            ∑ i : Fin (m - 1), ∑ j : Fin n, (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) :=
        hquadratic_raw
      _ = interiorQuad + boundaryHQuad + boundaryVQuad := by
        simpa [interiorQuad, boundaryHQuad, boundaryVQuad, add_assoc] using
          isotropic_quadratic_block_split p u q v
  have hinterior_block :
      interiorReg + interiorQuad =
        ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          (lam *
              Real.sqrt
                (u (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
                  v i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (u (Fin.castLE (Nat.sub_le m 1) i) j -
                  p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i (Fin.castLE (Nat.sub_le n 1) j) -
                  q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ) := by
    -- Merge the interior regularizer and interior quadratic pieces entrywise.
    dsimp [interiorReg, interiorQuad]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  have hboundaryH_block :
      boundaryHReg + boundaryHQuad =
        ∑ i : Fin m, ∑ j : Fin (n - 1),
          if hi : (i : ℕ) + 1 < m then
            (0 : ℝ)
          else
            (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ) := by
    -- Merge the last-row regularizer and quadratic terms pointwise.
    dsimp [boundaryHReg, boundaryHQuad]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hrow : (i : ℕ) + 1 < m <;> simp [hrow]
  have hboundaryV_block :
      boundaryVReg + boundaryVQuad =
        ∑ i : Fin (m - 1), ∑ j : Fin n,
          if hj : (j : ℕ) + 1 < n then
            (0 : ℝ)
          else
            (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ) := by
    -- Merge the last-column regularizer and quadratic terms pointwise.
    dsimp [boundaryVReg, boundaryVQuad]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hcol : (j : ℕ) + 1 < n <;> simp [hcol]
  -- Route correction: stabilize the exact parenthesized real identity first, then coerce it once
  -- to `EReal` in the wrapper theorem below.
  calc
    lam * two_dimensional_total_variation_isotropic_regularizer (toLp 2 (u, v)) +
        (1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) =
      (interiorReg + boundaryHReg + boundaryVReg) + (interiorQuad + boundaryHQuad + boundaryVQuad) := by
        rw [hregularizer, hquadratic]
    _ =
      (interiorReg + interiorQuad) + (boundaryHReg + boundaryHQuad) + (boundaryVReg + boundaryVQuad) := by
        ring
    _ = _ := by
      rw [hinterior_block]
      rw [hboundaryH_block]
      rw [hboundaryV_block]
      rfl

/-- Helper for Proposition 12.4: the isotropic TV proximal objective splits into interior
two-dimensional pair objectives together with boundary scalar absolute-value objectives. -/
private theorem isotropic_proximal_objective_sum_formula
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) :
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (u, v)) =
      ((isotropic_proximal_objective_sum_rhs lam p u q v : ℝ) : EReal) := by
  -- Route correction: the coercion-heavy regrouping is now delegated to the real-valued theorem
  -- above, so this `EReal` statement is only the canonical wrapper.
  calc
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (u, v)) =
      ((((lam * two_dimensional_total_variation_isotropic_regularizer (toLp 2 (u, v)) +
            (1 / 2 : ℝ) * ‖(toLp 2 (u, v) : DualSpace m n) - toLp 2 (p, q)‖ ^ (2 : ℕ) : ℝ)) :
          EReal)) := by
            rw [proximal_objective_apply, EReal.coe_add]
    _ = _ := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (isotropic_proximal_objective_sum_formula_real lam p u q v)

/-- Helper for Proposition 12.4: updating one horizontal entry changes a double sum only at that
entry. -/
private def horizontal_update (x : HorizontalSpace m n) (i : Fin m) (j : Fin (n - 1)) (a : ℝ) : HorizontalSpace m n :=
  Function.update x i (Function.update (x i) j a)

/-- Helper for Proposition 12.4: updating one vertical entry changes a double sum only at that
entry. -/
private def vertical_update (x : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin n) (a : ℝ) : VerticalSpace m n :=
  Function.update x i (Function.update (x i) j a)

/-- Helper for Proposition 12.4: a horizontal single-entry update rewrites the horizontal double
sum as the changed summand plus the unchanged remainder. -/
private theorem horizontal_double_sum_update
    (φ : Fin m → Fin (n - 1) → ℝ → ℝ)
    (x : HorizontalSpace m n) (i : Fin m) (j : Fin (n - 1)) (a : ℝ) :
    (∑ i' : Fin m, ∑ j' : Fin (n - 1),
      φ i' j' (horizontal_update x i j a i' j')) =
      φ i j a +
        Finset.sum (Finset.univ.erase j) (fun j' ↦ φ i j' (x i j')) +
        Finset.sum (Finset.univ.erase i) (fun i' ↦ ∑ j' : Fin (n - 1), φ i' j' (x i' j')) := by
  classical
  have hrow_split :
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        φ i' j' (horizontal_update x i j a i' j')) =
        (∑ j' : Fin (n - 1), φ i j' (horizontal_update x i j a i j')) +
          Finset.sum (Finset.univ.erase i) (fun i' ↦ ∑ j' : Fin (n - 1),
            φ i' j' (horizontal_update x i j a i' j')) := by
    -- Isolate the updated row from the outer double sum.
    symm
    exact Finset.add_sum_erase Finset.univ
      (fun i' : Fin m ↦ ∑ j' : Fin (n - 1), φ i' j' (horizontal_update x i j a i' j'))
      (Finset.mem_univ i)
  have hupdated_row :
      (∑ j' : Fin (n - 1), φ i j' (horizontal_update x i j a i j')) =
        φ i j a + Finset.sum (Finset.univ.erase j) (fun j' ↦ φ i j' (x i j')) := by
    -- Inside the updated row, isolate the updated column and simplify the remaining columns.
    calc
      (∑ j' : Fin (n - 1), φ i j' (horizontal_update x i j a i j')) =
          φ i j (horizontal_update x i j a i j) +
            Finset.sum (Finset.univ.erase j) (fun j' ↦ φ i j' (horizontal_update x i j a i j')) := by
              symm
              exact Finset.add_sum_erase Finset.univ
                (fun j' : Fin (n - 1) ↦ φ i j' (horizontal_update x i j a i j'))
                (Finset.mem_univ j)
      _ = φ i j a + Finset.sum (Finset.univ.erase j) (fun j' ↦ φ i j' (x i j')) := by
        congr 1
        · simp [horizontal_update]
        · refine Finset.sum_congr rfl ?_
          intro j' hj'
          have hj'ne : j' ≠ j := (Finset.mem_erase.mp hj').1
          simp [horizontal_update, Function.update_of_ne, hj'ne]
  have hunchanged_rows :
      Finset.sum (Finset.univ.erase i) (fun i' ↦ ∑ j' : Fin (n - 1),
        φ i' j' (horizontal_update x i j a i' j')) =
        Finset.sum (Finset.univ.erase i) (fun i' ↦ ∑ j' : Fin (n - 1), φ i' j' (x i' j')) := by
    -- Every untouched row is unchanged by the outer `Function.update`.
    refine Finset.sum_congr rfl ?_
    intro i' hi'
    have hi'ne : i' ≠ i := (Finset.mem_erase.mp hi').1
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    simp [horizontal_update, Function.update_of_ne, hi'ne]
  -- Reassemble the split row and remainder in the target order.
  rw [hrow_split, hupdated_row, hunchanged_rows]

/-- Helper for Proposition 12.4: a vertical single-entry update rewrites the vertical double sum
as the changed summand plus the unchanged remainder. -/
private theorem vertical_double_sum_update
    (φ : Fin (m - 1) → Fin n → ℝ → ℝ)
    (x : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin n) (a : ℝ) :
    (∑ i' : Fin (m - 1), ∑ j' : Fin n,
      φ i' j' (vertical_update x i j a i' j')) =
      φ i j a +
        Finset.sum (Finset.univ.erase j) (fun j' ↦ φ i j' (x i j')) +
        Finset.sum (Finset.univ.erase i) (fun i' ↦ ∑ j' : Fin n, φ i' j' (x i' j')) := by
  classical
  have hrow_split :
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        φ i' j' (vertical_update x i j a i' j')) =
        (∑ j' : Fin n, φ i j' (vertical_update x i j a i j')) +
          Finset.sum (Finset.univ.erase i) (fun i' ↦ ∑ j' : Fin n,
            φ i' j' (vertical_update x i j a i' j')) := by
    -- Isolate the updated row from the outer double sum.
    symm
    exact Finset.add_sum_erase Finset.univ
      (fun i' : Fin (m - 1) ↦ ∑ j' : Fin n, φ i' j' (vertical_update x i j a i' j'))
      (Finset.mem_univ i)
  have hupdated_row :
      (∑ j' : Fin n, φ i j' (vertical_update x i j a i j')) =
        φ i j a + Finset.sum (Finset.univ.erase j) (fun j' ↦ φ i j' (x i j')) := by
    -- Inside the updated row, isolate the updated column and simplify the remaining columns.
    calc
      (∑ j' : Fin n, φ i j' (vertical_update x i j a i j')) =
          φ i j (vertical_update x i j a i j) +
            Finset.sum (Finset.univ.erase j) (fun j' ↦ φ i j' (vertical_update x i j a i j')) := by
              symm
              exact Finset.add_sum_erase Finset.univ
                (fun j' : Fin n ↦ φ i j' (vertical_update x i j a i j'))
                (Finset.mem_univ j)
      _ = φ i j a + Finset.sum (Finset.univ.erase j) (fun j' ↦ φ i j' (x i j')) := by
        congr 1
        · simp [vertical_update]
        · refine Finset.sum_congr rfl ?_
          intro j' hj'
          have hj'ne : j' ≠ j := (Finset.mem_erase.mp hj').1
          simp [vertical_update, Function.update_of_ne, hj'ne]
  have hunchanged_rows :
      Finset.sum (Finset.univ.erase i) (fun i' ↦ ∑ j' : Fin n,
        φ i' j' (vertical_update x i j a i' j')) =
        Finset.sum (Finset.univ.erase i) (fun i' ↦ ∑ j' : Fin n, φ i' j' (x i' j')) := by
    -- Every untouched row is unchanged by the outer `Function.update`.
    refine Finset.sum_congr rfl ?_
    intro i' hi'
    have hi'ne : i' ≠ i := (Finset.mem_erase.mp hi').1
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    simp [vertical_update, Function.update_of_ne, hi'ne]
  -- Reassemble the split row and remainder in the target order.
  rw [hrow_split, hupdated_row, hunchanged_rows]

/-- Helper for Proposition 12.4: casting an interior row from `Fin (k - 1)` up to `Fin k` and
then back down recovers the original row index. -/
private theorem castLE_castLT_sub_one_eq_self {k : ℕ} (i : Fin (k - 1)) :
    (Fin.castLE (Nat.sub_le k 1) i).castLT i.isLt = i := by
  -- Both `Fin` indices have the same underlying natural number, so extensionality closes the goal.
  ext
  rfl

/-- Helper for Proposition 12.4: the same cast-up/cast-down identity is independent of the
particular proof used for the interior bound. -/
private theorem castLE_castLT_sub_one_eq_self_of_lt {k : ℕ} (i : Fin (k - 1))
    (h : (Fin.castLE (Nat.sub_le k 1) i : Fin k).1 < k - 1) :
    (Fin.castLE (Nat.sub_le k 1) i).castLT h = i := by
  -- Proof irrelevance leaves only the underlying value, which matches `i`.
  ext
  rfl

/-- Helper for Proposition 12.4: lifting two distinct `Fin (k - 1)` indices into `Fin k` keeps
them distinct. -/
private theorem castLE_ne_castLE_sub_one_of_ne {k : ℕ} {i j : Fin (k - 1)} (h : i ≠ j) :
    Fin.castLE (Nat.sub_le k 1) i ≠ Fin.castLE (Nat.sub_le k 1) j := by
  intro hij
  apply h
  simpa using hij

/-- Helper for Proposition 12.4: if an interior `Fin k` row is not the lifted copy of `i`, then
its cast-back `Fin (k - 1)` row is not `i` either. -/
private theorem castLT_ne_of_ne_castLE_sub_one {k : ℕ} {i : Fin (k - 1)} {i' : Fin k}
    (hi' : (i' : ℕ) + 1 < k) (h : i' ≠ Fin.castLE (Nat.sub_le k 1) i) :
    i'.castLT (Nat.lt_sub_iff_add_lt.mpr hi') ≠ i := by
  intro hcast
  apply h
  exact Fin.ext (by simpa using congrArg Fin.val hcast)

/-- Helper for Proposition 12.4: a boundary index of `Fin k` cannot be the lifted image of an
interior index of `Fin (k - 1)`. -/
private theorem castLE_ne_of_not_lt_last {k : ℕ} {i : Fin k}
    (hboundary : ¬ ((i : ℕ) + 1 < k)) (i' : Fin (k - 1)) :
    Fin.castLE (Nat.sub_le k 1) i' ≠ i := by
  -- Any lifted `Fin (k - 1)` index is still strictly before the last index, contradicting the
  -- boundary hypothesis.
  intro hEq
  have hlt : ((Fin.castLE (Nat.sub_le k 1) i' : Fin k) : ℕ) + 1 < k := by
    simpa using (Nat.lt_sub_iff_add_lt.mp i'.isLt)
  apply hboundary
  simpa [hEq] using hlt

/-- Helper for Proposition 12.4: after replacing one horizontal entry, the anisotropic proximal
objective becomes the scalar absolute-value proximal objective at that entry plus a constant
remainder independent of the new scalar. -/
private theorem anisotropic_horizontal_update_objective_eq_scalar_objective_add_const
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) (i : Fin m) (j : Fin (n - 1)) (a : ℝ) :
    let remainder : ℝ :=
      Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
        (lam * |u i j'| + (1 / 2 : ℝ) * (u i j' - p i j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
        ∑ j' : Fin (n - 1),
          (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      ∑ i' : Fin (m - 1), ∑ j' : Fin n,
        (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ)
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (horizontal_update u i j a, v)) =
      (((lam * |a| + (1 / 2 : ℝ) * (a - p i j) ^ (2 : ℕ) : ℝ)) : EReal) + (remainder : EReal) := by
  dsimp only
  let φ : Fin m → Fin (n - 1) → ℝ → ℝ :=
    fun i' j' t ↦ lam * |t| + (1 / 2 : ℝ) * (t - p i' j') ^ (2 : ℕ)
  have hhorizontal :
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        (lam * |horizontal_update u i j a i' j'| +
            (1 / 2 : ℝ) * (horizontal_update u i j a i' j' - p i' j') ^ (2 : ℕ) : ℝ)) =
        φ i j a +
          Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ φ i j' (u i j')) +
          Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
            ∑ j' : Fin (n - 1), φ i' j' (u i' j')) := by
    -- Isolate the updated horizontal coordinate from the global horizontal double sum.
    simpa [φ] using horizontal_double_sum_update φ u i j a
  -- Route correction: package the global anisotropic objective as one scalar prox term plus a
  -- constant remainder before invoking scalar prox uniqueness in the main theorem.
  rw [anisotropic_proximal_objective_sum_formula, hhorizontal]
  let remainder : ℝ :=
    Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ φ i j' (u i j')) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
        ∑ j' : Fin (n - 1), φ i' j' (u i' j')) +
      ∑ i' : Fin (m - 1), ∑ j' : Fin n,
        (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ)
  calc
    (((φ i j a +
          Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ φ i j' (u i j')) +
          Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
            ∑ j' : Fin (n - 1), φ i' j' (u i' j')) +
          ∑ i' : Fin (m - 1), ∑ j' : Fin n,
            (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ) : ℝ)) : EReal)
        =
      (((φ i j a + remainder : ℝ)) : EReal) := by
            congr 1
            simp [remainder]
            ring
    _ =
      (((φ i j a : ℝ)) : EReal) + ((remainder : ℝ) : EReal) := by
            rw [EReal.coe_add]
    _ = (((lam * |a| + (1 / 2 : ℝ) * (a - p i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          ((((Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
                (lam * |u i j'| + (1 / 2 : ℝ) * (u i j' - p i j') ^ (2 : ℕ) : ℝ))) +
              Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
                ∑ j' : Fin (n - 1),
                  (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
              ∑ i' : Fin (m - 1), ∑ j' : Fin n,
                (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ) : ℝ)) :
            EReal) := by
              simp [remainder, φ]

/-- Helper for Proposition 12.4: after replacing one vertical entry, the anisotropic proximal
objective becomes the scalar absolute-value proximal objective at that entry plus a constant
remainder independent of the new scalar. -/
private theorem anisotropic_vertical_update_objective_eq_scalar_objective_add_const
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin n) (a : ℝ) :
    let remainder : ℝ :=
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
          (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦
        (lam * |v i j'| + (1 / 2 : ℝ) * (v i j' - q i j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
        ∑ j' : Fin n,
          (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ))
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (u, vertical_update v i j a)) =
      (((lam * |a| + (1 / 2 : ℝ) * (a - q i j) ^ (2 : ℕ) : ℝ)) : EReal) + (remainder : EReal) := by
  dsimp only
  let φ : Fin (m - 1) → Fin n → ℝ → ℝ :=
    fun i' j' t ↦ lam * |t| + (1 / 2 : ℝ) * (t - q i' j') ^ (2 : ℕ)
  have hvertical :
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        (lam * |vertical_update v i j a i' j'| +
            (1 / 2 : ℝ) * (vertical_update v i j a i' j' - q i' j') ^ (2 : ℕ) : ℝ)) =
        φ i j a +
          Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦ φ i j' (v i j')) +
          Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
            ∑ j' : Fin n, φ i' j' (v i' j')) := by
    -- Isolate the updated vertical coordinate from the global vertical double sum.
    simpa [φ] using vertical_double_sum_update φ v i j a
  -- Route correction: mirror the horizontal proof exactly, but isolate the vertical scalar term
  -- before combining it with the untouched horizontal block.
  rw [anisotropic_proximal_objective_sum_formula, hvertical]
  let remainder : ℝ :=
    (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦ φ i j' (v i j')) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
        ∑ j' : Fin n, φ i' j' (v i' j'))
  calc
    ((((∑ i' : Fin m, ∑ j' : Fin (n - 1),
            (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
          (φ i j a +
            Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦ φ i j' (v i j')) +
            Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
              ∑ j' : Fin n, φ i' j' (v i' j')) : ℝ)) : ℝ) : EReal) =
      (((φ i j a + remainder : ℝ)) : EReal) := by
        congr 1
        simp [remainder]
        ring
    _ =
      (((φ i j a : ℝ)) : EReal) + ((remainder : ℝ) : EReal) := by
        rw [EReal.coe_add]
    _ = (((lam * |a| + (1 / 2 : ℝ) * (a - q i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          (remainder : EReal) := by
        simp [φ]

/-- Helper for Proposition 12.4: updating one interior horizontal/vertical pair isolates the
single coupled isotropic `sqrt (a^2 + b^2)` regularizer term plus an unchanged remainder. -/
private theorem isotropic_interior_regularizer_update_eq_sqrt_add_remainder
    (lam : ℝ) (u : HorizontalSpace m n) (v : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin (n - 1)) (a b : ℝ) :
    let iu : Fin m := Fin.castLE (Nat.sub_le m 1) i
    let jv : Fin n := Fin.castLE (Nat.sub_le n 1) j
    let remainder : ℝ :=
      lam *
        (Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
            Real.sqrt
              (u iu j' ^ (2 : ℕ) + v i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))) +
          Finset.sum (Finset.univ.erase iu) (fun i' : Fin m ↦
            ∑ j' : Fin (n - 1),
              if hi' : (i' : ℕ) + 1 < m then
                Real.sqrt
                  (u i' j' ^ (2 : ℕ) +
                    v (i'.castLT (Nat.lt_sub_iff_add_lt.mpr hi'))
                      (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))
              else
                |u i' j'|) +
          ∑ i' : Fin (m - 1), ∑ j' : Fin n, if (j' : ℕ) + 1 < n then (0 : ℝ) else |v i' j'|)
    lam *
        two_dimensional_total_variation_isotropic_regularizer
          (toLp 2 (horizontal_update u iu j a, vertical_update v i jv b)) =
      lam * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) + remainder := by
  dsimp only
  let iu : Fin m := Fin.castLE (Nat.sub_le m 1) i
  let jv : Fin n := Fin.castLE (Nat.sub_le n 1) j
  have hiu : (iu : ℕ) + 1 < m := by
    -- The lifted interior row still lies strictly before the last row.
    simpa [iu] using (Nat.lt_sub_iff_add_lt.mp i.isLt)
  have hjv : (jv : ℕ) + 1 < n := by
    -- The lifted interior column still lies strictly before the last column.
    simpa [jv] using (Nat.lt_sub_iff_add_lt.mp j.isLt)
  let φ : Fin m → Fin (n - 1) → ℝ → ℝ :=
    fun i' j' t ↦
      if hi' : (i' : ℕ) + 1 < m then
        Real.sqrt
          (t ^ (2 : ℕ) +
            vertical_update v i jv b
              (i'.castLT (Nat.lt_sub_iff_add_lt.mpr hi'))
              (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))
      else
        |t|
  have hfirst_raw :
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          Real.sqrt
            (horizontal_update u iu j a i' j' ^ (2 : ℕ) +
              vertical_update v i jv b
                (i'.castLT (Nat.lt_sub_iff_add_lt.mpr hi'))
                (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))
        else
          |horizontal_update u iu j a i' j'|) =
        φ iu j a +
          Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ φ iu j' (u iu j')) +
          Finset.sum (Finset.univ.erase iu) (fun i' : Fin m ↦
            ∑ j' : Fin (n - 1), φ i' j' (u i' j')) := by
    -- First isolate the updated horizontal entry while keeping the vertical update frozen.
    simpa [φ] using horizontal_double_sum_update φ u iu j a
  have hfirst :
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          Real.sqrt
            (horizontal_update u iu j a i' j' ^ (2 : ℕ) +
              vertical_update v i jv b
                (i'.castLT (Nat.lt_sub_iff_add_lt.mpr hi'))
                (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))
        else
          |horizontal_update u iu j a i' j'|) =
        Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) +
          Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
            Real.sqrt
              (u iu j' ^ (2 : ℕ) + v i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))) +
          Finset.sum (Finset.univ.erase iu) (fun i' : Fin m ↦
            ∑ j' : Fin (n - 1),
              if hi' : (i' : ℕ) + 1 < m then
                Real.sqrt
                  (u i' j' ^ (2 : ℕ) +
                    v (i'.castLT (Nat.lt_sub_iff_add_lt.mpr hi'))
                      (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))
              else
                |u i' j'|) := by
    -- Simplify the singled-out interior term and show that every remaining term uses the original
    -- `u` and `v` coordinates because the update misses those indices.
    rw [hfirst_raw]
    have hhead :
        φ iu j a = Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
      dsimp [φ]
      have hi_cast :
          iu.castLT (Nat.lt_sub_iff_add_lt.mpr hiu) = i := by
        exact castLE_castLT_sub_one_eq_self_of_lt i (Nat.lt_sub_iff_add_lt.mpr hiu)
      calc
        (if hi' : (iu : ℕ) + 1 < m then
            Real.sqrt
              (a ^ (2 : ℕ) +
                vertical_update v i jv b
                  (iu.castLT (Nat.lt_sub_iff_add_lt.mpr hi'))
                  (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ))
          else
            |a|) =
          Real.sqrt
            (a ^ (2 : ℕ) +
              vertical_update v i jv b
                (iu.castLT (Nat.lt_sub_iff_add_lt.mpr hiu))
                (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) := by
            simpa [hiu]
        _ = Real.sqrt (a ^ (2 : ℕ) + vertical_update v i jv b i jv ^ (2 : ℕ)) := by
          rw [hi_cast]
        _ = Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
          simp [vertical_update]
    have hrow :
        Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ φ iu j' (u iu j')) =
          Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
            Real.sqrt
              (u iu j' ^ (2 : ℕ) + v i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))) := by
      refine Finset.sum_congr rfl ?_
      intro j' hj'
      have hj'ne : j' ≠ j := (Finset.mem_erase.mp hj').1
      have hcast_ne : Fin.castLE (Nat.sub_le n 1) j' ≠ jv := by
        exact castLE_ne_castLE_sub_one_of_ne (k := n) hj'ne
      dsimp [φ]
      have hi_cast :
          iu.castLT (Nat.lt_sub_iff_add_lt.mpr hiu) = i := by
        exact castLE_castLT_sub_one_eq_self_of_lt i (Nat.lt_sub_iff_add_lt.mpr hiu)
      calc
        (if hi' : (iu : ℕ) + 1 < m then
            Real.sqrt
              (u iu j' ^ (2 : ℕ) +
                vertical_update v i jv b
                  (iu.castLT (Nat.lt_sub_iff_add_lt.mpr hi'))
                  (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))
          else
            |u iu j'|) =
          Real.sqrt
            (u iu j' ^ (2 : ℕ) +
              vertical_update v i jv b
                (iu.castLT (Nat.lt_sub_iff_add_lt.mpr hiu))
                (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) := by
            simpa [hiu]
        _ = Real.sqrt
            (u iu j' ^ (2 : ℕ) +
              vertical_update v i jv b i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) := by
            rw [hi_cast]
        _ = Real.sqrt
            (u iu j' ^ (2 : ℕ) + v i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) := by
            simp [vertical_update, hcast_ne]
    have hrows :
        Finset.sum (Finset.univ.erase iu) (fun i' : Fin m ↦
          ∑ j' : Fin (n - 1), φ i' j' (u i' j')) =
          Finset.sum (Finset.univ.erase iu) (fun i' : Fin m ↦
            ∑ j' : Fin (n - 1),
              if hi' : (i' : ℕ) + 1 < m then
                Real.sqrt
                  (u i' j' ^ (2 : ℕ) +
                    v (i'.castLT (Nat.lt_sub_iff_add_lt.mpr hi'))
                      (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ))
              else
                |u i' j'|) := by
      refine Finset.sum_congr rfl ?_
      intro i' hi'
      have hi'ne : i' ≠ iu := (Finset.mem_erase.mp hi').1
      refine Finset.sum_congr rfl ?_
      intro j' hj'
      by_cases hi'lt : (i' : ℕ) + 1 < m
      · have hrow_ne :
            i'.castLT (Nat.lt_sub_iff_add_lt.mpr hi'lt) ≠ i :=
          castLT_ne_of_ne_castLE_sub_one (i := i) hi'lt hi'ne
        simp [φ, hi'lt, vertical_update, hrow_ne]
      · simp [φ, hi'lt]
    rw [hhead, hrow, hrows]
  have hsecond :
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        if (j' : ℕ) + 1 < n then (0 : ℝ) else |vertical_update v i jv b i' j'|) =
        ∑ i' : Fin (m - 1), ∑ j' : Fin n, if (j' : ℕ) + 1 < n then (0 : ℝ) else |v i' j'| := by
    -- The vertical update hits an interior column, so the boundary `|q_{i,n}|` sum is unchanged.
    refine Finset.sum_congr rfl ?_
    intro i' hi'
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    by_cases hi'eq : i' = i
    · subst i'
      by_cases hj'eq : j' = jv
      · subst j'
        simp [vertical_update, hjv]
      · simp [vertical_update, hj'eq, hjv]
    · simp [vertical_update, hi'eq]
  -- Route correction: first finish the source-level real decomposition of the coupled interior TV
  -- block, and only then wrap it into the Chapter 6 pair proximal objective.
  rw [two_dimensional_total_variation_isotropic_regularizer_apply, hfirst, hsecond]
  ring

/-- The explicit proximal point of `λ g₁` at `(p, q)`, obtained by isotropic shrinkage on
interior pairs and soft-thresholding on the boundary entries. -/
def two_dimensional_total_variation_isotropic_prox_point
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) : DualSpace m n :=
  toLp 2
    ((fun i j ↦
        if hi : (i : ℕ) + 1 < m then
          two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
            (q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) *
            p i j
        else
          𝒯[lam] (p i j)),
      fun i j ↦
        if hj : (j : ℕ) + 1 < n then
          two_dimensional_total_variation_isotropic_shrink_factor lam
            (p (Fin.castLE (Nat.sub_le m 1) i) (j.castLT (Nat.lt_sub_iff_add_lt.mpr hj)))
            (q i j) * q i j
        else
          𝒯[lam] (q i j))

/-- The horizontal component of the isotropic proximal point has the textbook entrywise
formula. -/
@[simp] theorem two_dimensional_total_variation_isotropic_prox_point_fst_apply
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) (i : Fin m) (j : Fin (n - 1)) :
    (two_dimensional_total_variation_isotropic_prox_point lam p q).fst i j =
      if hi : (i : ℕ) + 1 < m then
        two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
          (q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) * p i j
      else
        𝒯[lam] (p i j) := by
  -- Read back the first component of the explicit `toLp 2` pair.
  rfl

/-- The vertical component of the isotropic proximal point has the textbook entrywise formula. -/
@[simp] theorem two_dimensional_total_variation_isotropic_prox_point_snd_apply
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin n) :
    (two_dimensional_total_variation_isotropic_prox_point lam p q).snd i j =
      if hj : (j : ℕ) + 1 < n then
        two_dimensional_total_variation_isotropic_shrink_factor lam
          (p (Fin.castLE (Nat.sub_le m 1) i) (j.castLT (Nat.lt_sub_iff_add_lt.mpr hj)))
          (q i j) * q i j
      else
        𝒯[lam] (q i j) := by
  -- Read back the second component of the explicit `toLp 2` pair.
  rfl

/-- The explicit proximal point of `λ g_{ℓ¹}` at `(p, q)`, obtained by entrywise
soft-thresholding. -/
def two_dimensional_total_variation_anisotropic_prox_point
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) : DualSpace m n :=
  toLp 2 (fun i j ↦ 𝒯[lam] (p i j), fun i j ↦ 𝒯[lam] (q i j))

/-- The horizontal component of the anisotropic proximal point is entrywise
soft-thresholding. -/
@[simp] theorem two_dimensional_total_variation_anisotropic_prox_point_fst_apply
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) (i : Fin m) (j : Fin (n - 1)) :
    (two_dimensional_total_variation_anisotropic_prox_point lam p q).fst i j =
      𝒯[lam] (p i j) := by
  -- Read back the first component of the explicit `toLp 2` pair.
  rfl

/-- The vertical component of the anisotropic proximal point is entrywise
soft-thresholding. -/
@[simp] theorem two_dimensional_total_variation_anisotropic_prox_point_snd_apply
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin n) :
    (two_dimensional_total_variation_anisotropic_prox_point lam p q).snd i j =
      𝒯[lam] (q i j) := by
  -- Read back the second component of the explicit `toLp 2` pair.
  rfl

/-- Helper for Proposition 12.4: replacing one interior coupled block in the stabilized real RHS
isolates exactly the corresponding two-dimensional proximal block plus an unchanged remainder. -/
private theorem isotropic_interior_rhs_update_eq_pair_block_add_remainder
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin (n - 1)) (a b : ℝ) :
    let iu : Fin m := Fin.castLE (Nat.sub_le m 1) i
    let jv : Fin n := Fin.castLE (Nat.sub_le n 1) j
    let remainder : ℝ :=
      Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
        (lam *
            Real.sqrt
              (u iu j' ^ (2 : ℕ) + v i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) * (u iu j' - p iu j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (v i (Fin.castLE (Nat.sub_le n 1) j') -
                q i (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
        ∑ j' : Fin (n - 1),
          (lam *
              Real.sqrt
                (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                  v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                  p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                  q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ))
    isotropic_proximal_objective_sum_rhs lam p (horizontal_update u iu j a) q
        (vertical_update v i jv b) =
      (lam * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) +
        (1 / 2 : ℝ) * (a - p iu j) ^ (2 : ℕ) +
        (1 / 2 : ℝ) * (b - q i jv) ^ (2 : ℕ)) +
        remainder := by
  dsimp only
  let iu : Fin m := Fin.castLE (Nat.sub_le m 1) i
  let jv : Fin n := Fin.castLE (Nat.sub_le n 1) j
  let G : Fin (m - 1) → Fin (n - 1) → ℝ :=
    fun i' j' ↦
      (lam *
          Real.sqrt
            (horizontal_update u iu j a (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
              vertical_update v i jv b i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
        (1 / 2 : ℝ) *
          (horizontal_update u iu j a (Fin.castLE (Nat.sub_le m 1) i') j' -
              p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
        (1 / 2 : ℝ) *
          (vertical_update v i jv b i' (Fin.castLE (Nat.sub_le n 1) j') -
              q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)
  have hiu : (iu : ℕ) + 1 < m := by
    -- The lifted row `iu` is still an interior row.
    simpa [iu] using (Nat.lt_sub_iff_add_lt.mp i.isLt)
  have hjv : (jv : ℕ) + 1 < n := by
    -- The lifted column `jv` is still an interior column.
    simpa [jv] using (Nat.lt_sub_iff_add_lt.mp j.isLt)
  have hinterior_raw :
      (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1), G i' j') =
        G i j +
          Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ G i j') +
          Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
            ∑ j' : Fin (n - 1), G i' j') := by
    have hrow_split :
        (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1), G i' j') =
          (∑ j' : Fin (n - 1), G i j') +
            Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
              ∑ j' : Fin (n - 1), G i' j') := by
      -- Isolate the updated interior row from the outer finite sum.
      symm
      exact Finset.add_sum_erase Finset.univ
        (fun i' : Fin (m - 1) ↦ ∑ j' : Fin (n - 1), G i' j') (Finset.mem_univ i)
    have hrow_updated :
        (∑ j' : Fin (n - 1), G i j') =
          G i j + Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ G i j') := by
      -- Inside the updated row, isolate the updated column.
      symm
      exact Finset.add_sum_erase Finset.univ (fun j' : Fin (n - 1) ↦ G i j')
        (Finset.mem_univ j)
    rw [hrow_split, hrow_updated]
  have hhead :
      G i j =
        (lam * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) +
          (1 / 2 : ℝ) * (a - p iu j) ^ (2 : ℕ) +
          (1 / 2 : ℝ) * (b - q i jv) ^ (2 : ℕ) : ℝ) := by
    -- The singled-out interior block sees both updates exactly once.
    simp [G, iu, jv, horizontal_update, vertical_update]
  have hrow :
      Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ G i j') =
        Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
          (lam *
              Real.sqrt
                (u iu j' ^ (2 : ℕ) + v i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
            (1 / 2 : ℝ) * (u iu j' - p iu j') ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i (Fin.castLE (Nat.sub_le n 1) j') -
                  q i (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) := by
    -- Every other column in the updated row uses the original `u` and `v` entries.
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    have hj'ne : j' ≠ j := (Finset.mem_erase.mp hj').1
    have hcast_ne : Fin.castLE (Nat.sub_le n 1) j' ≠ jv := by
      exact castLE_ne_castLE_sub_one_of_ne (k := n) hj'ne
    simp [G, iu, jv, horizontal_update, vertical_update, hj'ne, hcast_ne]
  have hrows :
      Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦ ∑ j' : Fin (n - 1), G i' j') =
        Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
          ∑ j' : Fin (n - 1),
            (lam *
                Real.sqrt
                  (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                    v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
              (1 / 2 : ℝ) *
                (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                    p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
              (1 / 2 : ℝ) *
                (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                    q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) := by
    -- Every untouched interior row misses both updates.
    refine Finset.sum_congr rfl ?_
    intro i' hi'
    have hi'ne : i' ≠ i := (Finset.mem_erase.mp hi').1
    have hrow_ne : Fin.castLE (Nat.sub_le m 1) i' ≠ iu := by
      exact castLE_ne_castLE_sub_one_of_ne (k := m) hi'ne
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    simp [G, iu, jv, horizontal_update, vertical_update, hrow_ne, hi'ne]
  have hboundaryH :
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |horizontal_update u iu j a i' j'| +
            (1 / 2 : ℝ) * (horizontal_update u iu j a i' j' - p i' j') ^ (2 : ℕ) : ℝ)) =
        ∑ i' : Fin m, ∑ j' : Fin (n - 1),
          if hi' : (i' : ℕ) + 1 < m then
            (0 : ℝ)
          else
            (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ) := by
    -- Updating an interior row leaves the last-row scalar block sum unchanged.
    refine Finset.sum_congr rfl ?_
    intro i' hi'
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    by_cases hi'eq : i' = iu
    · subst i'
      simp [hiu]
    · simp [horizontal_update, hi'eq]
  have hboundaryV :
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |vertical_update v i jv b i' j'| +
            (1 / 2 : ℝ) * (vertical_update v i jv b i' j' - q i' j') ^ (2 : ℕ) : ℝ)) =
        ∑ i' : Fin (m - 1), ∑ j' : Fin n,
          if hj' : (j' : ℕ) + 1 < n then
            (0 : ℝ)
          else
            (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ) := by
    -- Updating an interior column leaves the last-column scalar block sum unchanged.
    refine Finset.sum_congr rfl ?_
    intro i' hi'
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    by_cases hi'eq : i' = i
    · subst i'
      by_cases hj'eq : j' = jv
      · subst j'
        simp [hjv]
      · simp [vertical_update, hj'eq]
    · simp [vertical_update, hi'eq]
  -- Route correction: decompose the stabilized real RHS first, so the later `EReal` proof only
  -- wraps this local coupled-block identity once.
  rw [isotropic_proximal_objective_sum_rhs]
  rw [show
      (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (horizontal_update u iu j a (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                vertical_update v i jv b i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (horizontal_update u iu j a (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (vertical_update v i jv b i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) =
      ∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1), G i' j' by
      simp [G]]
  rw [hinterior_raw, hhead, hrow, hrows, hboundaryH, hboundaryV]
  ring

/-- Helper for Proposition 12.4: after replacing one interior coupled block, the isotropic TV
proximal objective becomes the Chapter 6 pair proximal objective plus a constant remainder. -/
private theorem isotropic_interior_update_objective_eq_pair_objective_add_const
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin (n - 1)) (a b : ℝ) :
    let iu : Fin m := Fin.castLE (Nat.sub_le m 1) i
    let jv : Fin n := Fin.castLE (Nat.sub_le n 1) j
    let remainder : ℝ :=
      Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
        (lam *
            Real.sqrt
              (u iu j' ^ (2 : ℕ) + v i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) * (u iu j' - p iu j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (v i (Fin.castLE (Nat.sub_le n 1) j') -
                q i (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
        ∑ j' : Fin (n - 1),
          (lam *
              Real.sqrt
                (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                  v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                  p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                  q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ))
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
        (toLp 2 (p, q))
        (toLp 2 (horizontal_update u iu j a, vertical_update v i jv b)) =
      proximal_objective
          (fun y : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖y‖))
          (toLp 2 ![p iu j, q i jv]) (toLp 2 ![a, b]) + (remainder : EReal) := by
  dsimp only
  -- Rewrite the global isotropic objective to the stabilized real RHS, then identify the singled
  -- out block with the Chapter 6 pair objective.
  rw [isotropic_proximal_objective_sum_formula]
  rw [isotropic_interior_rhs_update_eq_pair_block_add_remainder]
  rw [pair_norm_proximal_objective_apply]
  rw [EReal.coe_add]

/-- Helper for Proposition 12.4: replacing one last-row horizontal entry turns the isotropic TV
proximal objective into the scalar absolute-value proximal objective plus a constant remainder. -/
private theorem isotropic_boundary_horizontal_update_objective_eq_scalar_objective_add_const
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) (i : Fin m) (j : Fin (n - 1))
    (hboundary : ¬ ((i : ℕ) + 1 < m)) (a : ℝ) :
    let remainder : ℝ :=
      (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
          (lam *
              Real.sqrt
                (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                  v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                  p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                  q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
        (lam * |u i j'| + (1 / 2 : ℝ) * (u i j' - p i j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
        ∑ j' : Fin (n - 1),
          if hi' : (i' : ℕ) + 1 < m then
            (0 : ℝ)
          else
            (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ))
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (horizontal_update u i j a, v)) =
      (((lam * |a| + (1 / 2 : ℝ) * (a - p i j) ^ (2 : ℕ) : ℝ)) : EReal) +
        (remainder : EReal) := by
  dsimp only
  let φ : Fin m → Fin (n - 1) → ℝ → ℝ :=
    fun i' j' t ↦
      if hi' : (i' : ℕ) + 1 < m then
        (0 : ℝ)
      else
        (lam * |t| + (1 / 2 : ℝ) * (t - p i' j') ^ (2 : ℕ) : ℝ)
  have hinterior :
      (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (horizontal_update u i j a (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (horizontal_update u i j a (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) =
        ∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
          (lam *
              Real.sqrt
                (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                  v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                  p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                  q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ) := by
    -- A last-row horizontal update never touches the interior coupled blocks.
    refine Finset.sum_congr rfl ?_
    intro i' hi'
    have hrow_ne : Fin.castLE (Nat.sub_le m 1) i' ≠ i :=
      castLE_ne_of_not_lt_last hboundary i'
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    simp [horizontal_update, hrow_ne]
  have hboundaryH :
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |horizontal_update u i j a i' j'| +
            (1 / 2 : ℝ) * (horizontal_update u i j a i' j' - p i' j') ^ (2 : ℕ) : ℝ)) =
        φ i j a +
          Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ φ i j' (u i j')) +
          Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
            ∑ j' : Fin (n - 1), φ i' j' (u i' j')) := by
    -- Split the last-row boundary block into the updated scalar term and the untouched remainder.
    simpa [φ, hboundary] using horizontal_double_sum_update φ u i j a
  -- Route correction: because the updated row is already boundary, the source proof only needs a
  -- scalar last-row split; the interior coupled sum is unchanged.
  rw [isotropic_proximal_objective_sum_formula, isotropic_proximal_objective_sum_rhs]
  rw [hinterior, hboundaryH]
  let remainder : ℝ :=
    (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ φ i j' (u i j')) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
        ∑ j' : Fin (n - 1), φ i' j' (u i' j')) +
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ))
  calc
    ((((∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
            (lam *
                Real.sqrt
                  (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                    v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
              (1 / 2 : ℝ) *
                (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                    p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
              (1 / 2 : ℝ) *
                (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                    q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
          (φ i j a +
            Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦ φ i j' (u i j')) +
            Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
              ∑ j' : Fin (n - 1), φ i' j' (u i' j'))) +
          (∑ i' : Fin (m - 1), ∑ j' : Fin n,
            if hj' : (j' : ℕ) + 1 < n then
              (0 : ℝ)
            else
              (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ)) : ℝ)) :
        EReal) =
      (((φ i j a + remainder : ℝ)) : EReal) := by
        congr 1
        simp [remainder]
        ring
    _ = (((φ i j a : ℝ)) : EReal) + ((remainder : ℝ) : EReal) := by
      rw [EReal.coe_add]
    _ = (((lam * |a| + (1 / 2 : ℝ) * (a - p i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          ((remainder : ℝ) : EReal) := by
        simp [φ, hboundary]
  simpa [remainder, φ, hboundary]

/-- Helper for Proposition 12.4: replacing one last-column vertical entry turns the isotropic TV
proximal objective into the scalar absolute-value proximal objective plus a constant remainder. -/
private theorem isotropic_boundary_vertical_update_objective_eq_scalar_objective_add_const
    (lam : ℝ) (p u : HorizontalSpace m n) (q v : VerticalSpace m n) (i : Fin (m - 1)) (j : Fin n)
    (hboundary : ¬ ((j : ℕ) + 1 < n)) (a : ℝ) :
    let remainder : ℝ :=
      (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
          (lam *
              Real.sqrt
                (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                  v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                  p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                  q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |v i j'| + (1 / 2 : ℝ) * (v i j' - q i j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
        ∑ j' : Fin n,
          if hj' : (j' : ℕ) + 1 < n then
            (0 : ℝ)
          else
            (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ))
    proximal_objective
        (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
        (toLp 2 (p, q)) (toLp 2 (u, vertical_update v i j a)) =
      (((lam * |a| + (1 / 2 : ℝ) * (a - q i j) ^ (2 : ℕ) : ℝ)) : EReal) +
        (remainder : EReal) := by
  dsimp only
  let φ : Fin (m - 1) → Fin n → ℝ → ℝ :=
    fun i' j' t ↦
      if hj' : (j' : ℕ) + 1 < n then
        (0 : ℝ)
      else
        (lam * |t| + (1 / 2 : ℝ) * (t - q i' j') ^ (2 : ℕ) : ℝ)
  have hinterior :
      (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                vertical_update v i j a i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (vertical_update v i j a i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) =
        ∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
          (lam *
              Real.sqrt
                (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                  v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                  p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                  q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ) := by
    -- A last-column vertical update never touches the interior coupled blocks.
    refine Finset.sum_congr rfl ?_
    intro i' hi'
    refine Finset.sum_congr rfl ?_
    intro j' hj'
    have hcol_ne : Fin.castLE (Nat.sub_le n 1) j' ≠ j :=
      castLE_ne_of_not_lt_last hboundary j'
    by_cases hi'eq : i' = i
    · subst i'
      simp [vertical_update, hcol_ne]
    · simp [vertical_update, hi'eq]
  have hboundaryV :
      (∑ i' : Fin (m - 1), ∑ j' : Fin n,
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |vertical_update v i j a i' j'| +
            (1 / 2 : ℝ) * (vertical_update v i j a i' j' - q i' j') ^ (2 : ℕ) : ℝ)) =
        φ i j a +
          Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦ φ i j' (v i j')) +
          Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
            ∑ j' : Fin n, φ i' j' (v i' j')) := by
    -- Split the last-column boundary block into the updated scalar term and the untouched
    -- vertical remainder.
    simpa [φ, hboundary] using vertical_double_sum_update φ v i j a
  -- Route correction: keep the source proof at the last-column scalar block level, so only the
  -- boundary vertical sum is split while the interior coupled and horizontal boundary sums stay
  -- fixed.
  rw [isotropic_proximal_objective_sum_formula, isotropic_proximal_objective_sum_rhs]
  rw [hinterior, hboundaryV]
  let remainder : ℝ :=
    (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |v i j'| + (1 / 2 : ℝ) * (v i j' - q i j') ^ (2 : ℕ) : ℝ)) +
      Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
        ∑ j' : Fin n,
          if hj' : (j' : ℕ) + 1 < n then
            (0 : ℝ)
          else
            (lam * |v i' j'| + (1 / 2 : ℝ) * (v i' j' - q i' j') ^ (2 : ℕ) : ℝ))
  let lhs : ℝ :=
    (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (u (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                v i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (u (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (v i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
      (∑ i' : Fin m, ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |u i' j'| + (1 / 2 : ℝ) * (u i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
      (φ i j a +
        Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦ φ i j' (v i j')) +
        Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
          ∑ j' : Fin n, φ i' j' (v i' j')) : ℝ)
  have hlhs : lhs = φ i j a + remainder := by
    dsimp [lhs, remainder]
    simp [φ]
    ring
  have hcollapse : ((lhs : ℝ) : EReal) = ((φ i j a + remainder : ℝ) : EReal) := by
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hlhs
  calc
    ((lhs : ℝ) : EReal) = ((φ i j a + remainder : ℝ) : EReal) := hcollapse
    _ =
      (((φ i j a : ℝ)) : EReal) + ((remainder : ℝ) : EReal) := by
        rw [EReal.coe_add]
    _ = (((lam * |a| + (1 / 2 : ℝ) * (a - q i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          ((remainder : ℝ) : EReal) := by
        simp [φ, hboundary]

/-- Helper for Proposition 12.4: the displayed isotropic shrinkage/soft-threshold point is a
global minimizer of the isotropic proximal objective. -/
private theorem isotropic_prox_point_mem_proximal_mapping
    (lam : ℝ) (hlam : 0 ≤ lam) (p : HorizontalSpace m n) (q : VerticalSpace m n) :
    two_dimensional_total_variation_isotropic_prox_point lam p q ∈
      prox[fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z)]
        (toLp 2 (p, q)) := by
  let u : HorizontalSpace m n :=
    fun i j ↦
      if hi : (i : ℕ) + 1 < m then
        two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
          (q (i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) * p i j
      else
        𝒯[lam] (p i j)
  let v : VerticalSpace m n :=
    fun i j ↦
      if hj : (j : ℕ) + 1 < n then
        two_dimensional_total_variation_isotropic_shrink_factor lam
          (p (Fin.castLE (Nat.sub_le m 1) i) (j.castLT (Nat.lt_sub_iff_add_lt.mpr hj)))
          (q i j) * q i j
      else
        𝒯[lam] (q i j)
  have hpoint : two_dimensional_total_variation_isotropic_prox_point lam p q = toLp 2 (u, v) := by
    -- The explicit isotropic prox point is definitionally the `WithLp` pair built from `u` and
    -- `v`.
    rfl
  rw [hpoint, mem_proximal_mapping_iff, isMinOn_univ_iff]
  intro y
  have hinterior_term
      (i : Fin (m - 1)) (j : Fin (n - 1)) :
      (lam *
          Real.sqrt
            (u (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
              v i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) +
        (1 / 2 : ℝ) *
          (u (Fin.castLE (Nat.sub_le m 1) i) j -
              p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
        (1 / 2 : ℝ) *
          (v i (Fin.castLE (Nat.sub_le n 1) j) -
              q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ) ≤
        (lam *
            Real.sqrt
              (y.fst (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
                y.snd i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (y.fst (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (y.snd i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ) := by
    let iu : Fin m := Fin.castLE (Nat.sub_le m 1) i
    let jv : Fin n := Fin.castLE (Nat.sub_le n 1) j
    have hiu : (iu : ℕ) + 1 < m := by
      -- The lifted row index still lies in the interior row set.
      simpa [iu] using (Nat.lt_sub_iff_add_lt.mp i.isLt)
    have hjv : (jv : ℕ) + 1 < n := by
      -- The lifted column index still lies in the interior column set.
      simpa [jv] using (Nat.lt_sub_iff_add_lt.mp j.isLt)
    have hi_cast :
        iu.castLT (Nat.lt_sub_iff_add_lt.mpr hiu) = i := by
      -- Casting the lifted interior row back down recovers the original interior row.
      exact castLE_castLT_sub_one_eq_self_of_lt i (Nat.lt_sub_iff_add_lt.mpr hiu)
    have hj_cast :
        jv.castLT (Nat.lt_sub_iff_add_lt.mpr hjv) = j := by
      -- Casting the lifted interior column back down recovers the original interior column.
      exact castLE_castLT_sub_one_eq_self_of_lt j (Nat.lt_sub_iff_add_lt.mpr hjv)
    have hu_eq :
        u iu j =
          two_dimensional_total_variation_isotropic_shrink_factor lam (p iu j) (q i jv) *
            p iu j := by
      -- The horizontal coordinate of the explicit point uses the interior shrinkage formula.
      rw [show u iu j =
          (if hi : (iu : ℕ) + 1 < m then
            two_dimensional_total_variation_isotropic_shrink_factor lam (p iu j)
              (q (iu.castLT (Nat.lt_sub_iff_add_lt.mpr hi)) (Fin.castLE (Nat.sub_le n 1) j)) *
                p iu j
          else
            𝒯[lam] (p iu j)) by
            rfl]
      rw [dif_pos hiu]
      simpa [jv, hi_cast]
    have hv_eq :
        v i jv =
          two_dimensional_total_variation_isotropic_shrink_factor lam (p iu j) (q i jv) *
            q i jv := by
      -- The vertical coordinate of the explicit point uses the same interior shrinkage factor.
      rw [show v i jv =
          (if hj : (jv : ℕ) + 1 < n then
            two_dimensional_total_variation_isotropic_shrink_factor lam
              (p (Fin.castLE (Nat.sub_le m 1) i) (jv.castLT (Nat.lt_sub_iff_add_lt.mpr hj)))
              (q i jv) * q i jv
          else
            𝒯[lam] (q i jv)) by
            rfl]
      rw [dif_pos hjv]
      simpa [iu, hj_cast]
    have hpair_mem :
        toLp 2
          ![two_dimensional_total_variation_isotropic_shrink_factor lam (p iu j) (q i jv) *
              p iu j,
            two_dimensional_total_variation_isotropic_shrink_factor lam (p iu j) (q i jv) *
              q i jv] ∈
          prox[fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖)]
            (toLp 2 ![p iu j, q i jv]) := by
      -- The explicit interior block is the singleton Chapter 6 proximal point for the paired data.
      rw [two_dimensional_total_variation_pair_prox_eq_singleton lam hlam (p iu j) (q i jv)]
      simp
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hpair_mem
    have hpair_le := hpair_mem (toLp 2 ![y.fst iu j, y.snd i jv])
    let shrinkP : ℝ :=
      two_dimensional_total_variation_isotropic_shrink_factor lam (p iu j) (q i jv) * p iu j
    let shrinkQ : ℝ :=
      two_dimensional_total_variation_isotropic_shrink_factor lam (p iu j) (q i jv) * q i jv
    have hleft_obj :
        proximal_objective
            (fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖))
            (toLp 2 ![p iu j, q i jv]) (toLp 2 ![shrinkP, shrinkQ]) =
          (((lam * Real.sqrt (shrinkP ^ (2 : ℕ) + shrinkQ ^ (2 : ℕ)) +
                (1 / 2 : ℝ) * (shrinkP - p iu j) ^ (2 : ℕ) +
                (1 / 2 : ℝ) * (shrinkQ - q i jv) ^ (2 : ℕ) : ℝ)) : EReal) := by
      -- Expand the paired objective at the shrinkage point into the explicit scalar formula.
      simpa [shrinkP, shrinkQ] using
        (pair_norm_proximal_objective_apply lam (p iu j) (q i jv) shrinkP shrinkQ)
    have hright_obj :
        proximal_objective
            (fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖))
            (toLp 2 ![p iu j, q i jv]) (toLp 2 ![y.fst iu j, y.snd i jv]) =
          (((lam * Real.sqrt (y.fst iu j ^ (2 : ℕ) + y.snd i jv ^ (2 : ℕ)) +
                (1 / 2 : ℝ) * (y.fst iu j - p iu j) ^ (2 : ℕ) +
                (1 / 2 : ℝ) * (y.snd i jv - q i jv) ^ (2 : ℕ) : ℝ)) : EReal) := by
      -- Expand the paired objective at the arbitrary competitor into the explicit scalar formula.
      simpa using
        (pair_norm_proximal_objective_apply lam (p iu j) (q i jv) (y.fst iu j) (y.snd i jv))
    have hpair_le' :
        (((lam * Real.sqrt (shrinkP ^ (2 : ℕ) + shrinkQ ^ (2 : ℕ)) +
              (1 / 2 : ℝ) * (shrinkP - p iu j) ^ (2 : ℕ) +
              (1 / 2 : ℝ) * (shrinkQ - q i jv) ^ (2 : ℕ) : ℝ)) : EReal) ≤
          (((lam * Real.sqrt (y.fst iu j ^ (2 : ℕ) + y.snd i jv ^ (2 : ℕ)) +
              (1 / 2 : ℝ) * (y.fst iu j - p iu j) ^ (2 : ℕ) +
              (1 / 2 : ℝ) * (y.snd i jv - q i jv) ^ (2 : ℕ) : ℝ)) : EReal) := by
      -- Replace both paired objectives by their explicit scalar formulas.
      rw [hleft_obj, hright_obj] at hpair_le
      exact hpair_le
    have hpair_le_real :
        (lam * Real.sqrt (shrinkP ^ (2 : ℕ) + shrinkQ ^ (2 : ℕ)) +
            (1 / 2 : ℝ) * (shrinkP - p iu j) ^ (2 : ℕ) +
            (1 / 2 : ℝ) * (shrinkQ - q i jv) ^ (2 : ℕ) : ℝ) ≤
          (lam * Real.sqrt (y.fst iu j ^ (2 : ℕ) + y.snd i jv ^ (2 : ℕ)) +
            (1 / 2 : ℝ) * (y.fst iu j - p iu j) ^ (2 : ℕ) +
            (1 / 2 : ℝ) * (y.snd i jv - q i jv) ^ (2 : ℕ) : ℝ) := by
      exact_mod_cast hpair_le'
    have hpair_le_real' :
        (lam * Real.sqrt (u iu j ^ (2 : ℕ) + v i jv ^ (2 : ℕ)) +
            (1 / 2 : ℝ) * (u iu j - p iu j) ^ (2 : ℕ) +
            (1 / 2 : ℝ) * (v i jv - q i jv) ^ (2 : ℕ) : ℝ) ≤
          (lam * Real.sqrt (y.fst iu j ^ (2 : ℕ) + y.snd i jv ^ (2 : ℕ)) +
            (1 / 2 : ℝ) * (y.fst iu j - p iu j) ^ (2 : ℕ) +
            (1 / 2 : ℝ) * (y.snd i jv - q i jv) ^ (2 : ℕ) : ℝ) := by
      simpa [shrinkP, shrinkQ, hu_eq, hv_eq] using hpair_le_real
    simpa [iu, jv] using hpair_le_real'
  have hboundary_horizontal_term
      (i : Fin m) (j : Fin (n - 1)) :
      (if hi : (i : ℕ) + 1 < m then
        (0 : ℝ)
      else
        (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) ≤
        (if hi : (i : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) := by
    by_cases hi : (i : ℕ) + 1 < m
    · -- Interior rows contribute `0` to the last-row scalar sum on both sides.
      simp [hi]
    · have hsoft_mem : u i j ∈ prox[absolute_value_penalty lam] (p i j) := by
        -- On the boundary row, the explicit prox point is the scalar soft-thresholding prox point.
        rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (p i j)]
        simp [u, hi]
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hsoft_mem
      have hsoft_le := hsoft_mem (y.fst i j)
      have hsoft_le' :
          (((lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal) ≤
            (((lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) :
              EReal) := by
        -- Rewrite the scalar Chapter 6 prox objective into the displayed absolute-value formula.
        simpa [proximal_objective_apply, absolute_value_penalty_apply] using hsoft_le
      have hsoft_le_real :
          (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ) ≤
            (lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ) := by
        exact_mod_cast hsoft_le'
      simpa [hi] using hsoft_le_real
  have hboundary_vertical_term
      (i : Fin (m - 1)) (j : Fin n) :
      (if hj : (j : ℕ) + 1 < n then
        (0 : ℝ)
      else
        (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) ≤
        (if hj : (j : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ)) := by
    by_cases hj : (j : ℕ) + 1 < n
    · -- Interior columns contribute `0` to the last-column scalar sum on both sides.
      simp [hj]
    · have hsoft_mem : v i j ∈ prox[absolute_value_penalty lam] (q i j) := by
        -- On the boundary column, the explicit prox point is the scalar soft-thresholding prox
        -- point.
        rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (q i j)]
        simp [v, hj]
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hsoft_mem
      have hsoft_le := hsoft_mem (y.snd i j)
      have hsoft_le' :
          (((lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) ≤
            (((lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ)) :
              EReal) := by
        -- Rewrite the scalar Chapter 6 prox objective into the displayed absolute-value formula.
        simpa [proximal_objective_apply, absolute_value_penalty_apply] using hsoft_le
      have hsoft_le_real :
          (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ) ≤
            (lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ) := by
        exact_mod_cast hsoft_le'
      simpa [hj] using hsoft_le_real
  have hinterior_sum :
      ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          (lam *
              Real.sqrt
                (u (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
                  v i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (u (Fin.castLE (Nat.sub_le m 1) i) j -
                  p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (v i (Fin.castLE (Nat.sub_le n 1) j) -
                  q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ) ≤
        ∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
          (lam *
              Real.sqrt
                (y.fst (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
                  y.snd i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) +
            (1 / 2 : ℝ) *
              (y.fst (Fin.castLE (Nat.sub_le m 1) i) j -
                  p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              (y.snd i (Fin.castLE (Nat.sub_le n 1) j) -
                  q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ) := by
    -- Sum the interior pairwise optimality inequalities over all interior grid blocks.
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hinterior_term i j
  have hboundary_horizontal_sum :
      (∑ i : Fin m, ∑ j : Fin (n - 1),
          if hi : (i : ℕ) + 1 < m then
            (0 : ℝ)
          else
            (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) ≤
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          if hi : (i : ℕ) + 1 < m then
            (0 : ℝ)
          else
            (lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) := by
    -- Sum the last-row scalar inequalities over all horizontal coordinates.
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hboundary_horizontal_term i j
  have hboundary_vertical_sum :
      (∑ i : Fin (m - 1), ∑ j : Fin n,
          if hj : (j : ℕ) + 1 < n then
            (0 : ℝ)
          else
            (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ)) ≤
        (∑ i : Fin (m - 1), ∑ j : Fin n,
          if hj : (j : ℕ) + 1 < n then
            (0 : ℝ)
          else
            (lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ)) := by
    -- Sum the last-column scalar inequalities over all vertical coordinates.
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hboundary_vertical_term i j
  have htarget_obj :
      proximal_objective
          (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
          (toLp 2 (p, q)) (toLp 2 (u, v)) =
        ((isotropic_proximal_objective_sum_rhs lam p u q v : ℝ) : EReal) := by
    -- Rewrite the isotropic objective at the explicit point into the stabilized interior/boundary
    -- block sum.
    simpa using
      isotropic_proximal_objective_sum_formula lam p u q v
  have hy_obj :
      proximal_objective
          (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
          (toLp 2 (p, q)) y =
        ((isotropic_proximal_objective_sum_rhs lam p y.fst q y.snd : ℝ) : EReal) := by
    -- Read `y` as its canonical `WithLp` pair and rewrite the isotropic objective into the same
    -- stabilized block sum.
    rw [show y = toLp 2 (y.fst, y.snd) by cases y; rfl]
    simpa using
      isotropic_proximal_objective_sum_formula lam p y.fst q y.snd
  let lhs : ℝ :=
    (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        (lam *
            Real.sqrt
              (u (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
                v i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (u (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (v i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ)) +
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        if hi : (i : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |u i j| + (1 / 2 : ℝ) * (u i j - p i j) ^ (2 : ℕ) : ℝ)) +
      (∑ i : Fin (m - 1), ∑ j : Fin n,
        if hj : (j : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |v i j| + (1 / 2 : ℝ) * (v i j - q i j) ^ (2 : ℕ) : ℝ))
  let rhs : ℝ :=
    (∑ i : Fin (m - 1), ∑ j : Fin (n - 1),
        (lam *
            Real.sqrt
              (y.fst (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
                y.snd i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (y.fst (Fin.castLE (Nat.sub_le m 1) i) j -
                p (Fin.castLE (Nat.sub_le m 1) i) j) ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (y.snd i (Fin.castLE (Nat.sub_le n 1) j) -
                q i (Fin.castLE (Nat.sub_le n 1) j)) ^ (2 : ℕ) : ℝ)) +
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        if hi : (i : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) +
      (∑ i : Fin (m - 1), ∑ j : Fin n,
        if hj : (j : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ))
  have hsum : lhs ≤ rhs := by
    -- Combine the interior-pair and boundary-scalar inequalities into the global real-valued
    -- isotropic objective inequality.
    dsimp [lhs, rhs]
    exact add_le_add (add_le_add hinterior_sum hboundary_horizontal_sum) hboundary_vertical_sum
  rw [htarget_obj, hy_obj]
  have hsum_ereal : ((lhs : ℝ) : EReal) ≤ ((rhs : ℝ) : EReal) := by
    exact_mod_cast hsum
  simpa [lhs, rhs, isotropic_proximal_objective_sum_rhs] using hsum_ereal

/-- Helper for Proposition 12.4: a global minimizer of the isotropic proximal objective induces
the corresponding Chapter 6 two-dimensional prox membership on every interior coupled block. -/
private theorem isotropic_global_minimizer_gives_interior_pair_prox_membership
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) (y : DualSpace m n)
    (hy : y ∈ prox[fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z)]
      (toLp 2 (p, q)))
    (i : Fin (m - 1)) (j : Fin (n - 1)) :
    toLp 2 ![y.fst (Fin.castLE (Nat.sub_le m 1) i) j, y.snd i (Fin.castLE (Nat.sub_le n 1) j)] ∈
      prox[fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖)]
        (toLp 2 ![p (Fin.castLE (Nat.sub_le m 1) i) j, q i (Fin.castLE (Nat.sub_le n 1) j)]) := by
  let iu : Fin m := Fin.castLE (Nat.sub_le m 1) i
  let jv : Fin n := Fin.castLE (Nat.sub_le n 1) j
  have hy_min :
      ∀ z : DualSpace m n,
        proximal_objective
            (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
            (toLp 2 (p, q)) y ≤
          proximal_objective
            (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
            (toLp 2 (p, q)) z := by
    -- Membership in the proximal map is exactly global minimality of the isotropic proximal
    -- objective.
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    exact hy
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
  intro z
  let remainder : ℝ :=
    Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
      (lam *
          Real.sqrt
            (y.fst iu j' ^ (2 : ℕ) + y.snd i (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
        (1 / 2 : ℝ) * (y.fst iu j' - p iu j') ^ (2 : ℕ) +
        (1 / 2 : ℝ) *
          (y.snd i (Fin.castLE (Nat.sub_le n 1) j') -
              q i (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
    Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
      ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (y.fst (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                y.snd i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (y.fst (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (y.snd i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
    (∑ i' : Fin m, ∑ j' : Fin (n - 1),
      if hi' : (i' : ℕ) + 1 < m then
        (0 : ℝ)
      else
        (lam * |y.fst i' j'| + (1 / 2 : ℝ) * (y.fst i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
    (∑ i' : Fin (m - 1), ∑ j' : Fin n,
      if hj' : (j' : ℕ) + 1 < n then
        (0 : ℝ)
      else
        (lam * |y.snd i' j'| + (1 / 2 : ℝ) * (y.snd i' j' - q i' j') ^ (2 : ℕ) : ℝ))
  have hy_self :
      proximal_objective
          (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
          (toLp 2 (p, q)) y =
        proximal_objective
            (fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖))
            (toLp 2 ![p iu j, q i jv]) (toLp 2 ![y.fst iu j, y.snd i jv]) +
          (remainder : EReal) := by
    -- Rewrite the untouched minimizer as a self-update so the same remainder appears on both
    -- sides of the comparison.
    rw [show y = toLp 2 (y.fst, y.snd) by cases y; rfl]
    simpa [iu, jv, remainder, horizontal_update, vertical_update] using
      (isotropic_interior_update_objective_eq_pair_objective_add_const
        lam p y.fst q y.snd i j (y.fst iu j) (y.snd i jv))
  have hz_update :
      proximal_objective
          (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
          (toLp 2 (p, q))
          (toLp 2 (horizontal_update y.fst iu j (z 0), vertical_update y.snd i jv (z 1))) =
        proximal_objective
            (fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖))
            (toLp 2 ![p iu j, q i jv]) (toLp 2 ![z 0, z 1]) +
          (remainder : EReal) := by
    -- Replacing only the current interior block changes the global objective by exactly the
    -- corresponding Chapter 6 pair objective, up to the common remainder.
    simpa [iu, jv, remainder] using
      (isotropic_interior_update_objective_eq_pair_objective_add_const
        lam p y.fst q y.snd i j (z 0) (z 1))
  have hcompare := hy_min (toLp 2 (horizontal_update y.fst iu j (z 0), vertical_update y.snd i jv (z 1)))
  rw [hy_self, hz_update] at hcompare
  have hpair_compare :
      proximal_objective
          (fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖))
          (toLp 2 ![p iu j, q i jv]) (toLp 2 ![y.fst iu j, y.snd i jv]) ≤
        proximal_objective
          (fun z : EuclideanSpace ℝ (Fin 2) ↦ ↑(lam * ‖z‖))
          (toLp 2 ![p iu j, q i jv]) (toLp 2 ![z 0, z 1]) := by
    -- Cancel the common finite remainder inside `EReal`.
    exact ((EReal.addLECancellable_coe remainder).add_le_add_iff_right).mp hcompare
  have hz_eq : (toLp 2 ![z 0, z 1] : EuclideanSpace ℝ (Fin 2)) = z := by
    -- Every two-dimensional Euclidean vector is determined by its two coordinates.
    ext k
    fin_cases k <;> simp
  simpa [iu, jv, hz_eq] using hpair_compare

/-- Helper for Proposition 12.4: a global minimizer of the isotropic proximal objective induces
the scalar absolute-value prox membership on every last-row horizontal entry. -/
private theorem isotropic_global_minimizer_gives_boundary_horizontal_prox_membership
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) (y : DualSpace m n)
    (hy : y ∈ prox[fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z)]
      (toLp 2 (p, q)))
    (i : Fin m) (j : Fin (n - 1)) (hboundary : ¬ ((i : ℕ) + 1 < m)) :
    y.fst i j ∈ prox[absolute_value_penalty lam] (p i j) := by
  have hy_min :
      ∀ z : DualSpace m n,
        proximal_objective
            (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
            (toLp 2 (p, q)) y ≤
          proximal_objective
            (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
            (toLp 2 (p, q)) z := by
    -- Membership in the proximal map is exactly global minimality of the isotropic proximal
    -- objective.
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    exact hy
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
  intro a
  let remainder : ℝ :=
    (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (y.fst (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                y.snd i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (y.fst (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (y.snd i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
    Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
      (lam * |y.fst i j'| + (1 / 2 : ℝ) * (y.fst i j' - p i j') ^ (2 : ℕ) : ℝ)) +
    Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
      ∑ j' : Fin (n - 1),
        if hi' : (i' : ℕ) + 1 < m then
          (0 : ℝ)
        else
          (lam * |y.fst i' j'| + (1 / 2 : ℝ) * (y.fst i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
    (∑ i' : Fin (m - 1), ∑ j' : Fin n,
      if hj' : (j' : ℕ) + 1 < n then
        (0 : ℝ)
      else
        (lam * |y.snd i' j'| + (1 / 2 : ℝ) * (y.snd i' j' - q i' j') ^ (2 : ℕ) : ℝ))
  have hy_self :
      proximal_objective
          (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
          (toLp 2 (p, q)) y =
        (((lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          (remainder : EReal) := by
    -- Rewrite the untouched minimizer as a self-update so the same scalar remainder appears on
    -- both sides.
    rw [show y = toLp 2 (y.fst, y.snd) by cases y; rfl]
    simpa [remainder, horizontal_update] using
      (isotropic_boundary_horizontal_update_objective_eq_scalar_objective_add_const
        lam p y.fst q y.snd i j hboundary (y.fst i j))
  have ha_update :
      proximal_objective
          (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
          (toLp 2 (p, q)) (toLp 2 (horizontal_update y.fst i j a, y.snd)) =
        (((lam * |a| + (1 / 2 : ℝ) * (a - p i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          (remainder : EReal) := by
    -- Replacing only the boundary horizontal entry isolates the scalar absolute-value prox block.
    simpa [remainder] using
      (isotropic_boundary_horizontal_update_objective_eq_scalar_objective_add_const
        lam p y.fst q y.snd i j hboundary a)
  have hcompare := hy_min (toLp 2 (horizontal_update y.fst i j a, y.snd))
  rw [hy_self, ha_update] at hcompare
  have hscalar :
      (((lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal) ≤
        (((lam * |a| + (1 / 2 : ℝ) * (a - p i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
    -- Cancel the common finite remainder inside `EReal`.
    exact ((EReal.addLECancellable_coe remainder).add_le_add_iff_right).mp hcompare
  simpa [proximal_objective_apply, absolute_value_penalty_apply] using hscalar

/-- Helper for Proposition 12.4: a global minimizer of the isotropic proximal objective induces
the scalar absolute-value prox membership on every last-column vertical entry. -/
private theorem isotropic_global_minimizer_gives_boundary_vertical_prox_membership
    (lam : ℝ) (p : HorizontalSpace m n) (q : VerticalSpace m n) (y : DualSpace m n)
    (hy : y ∈ prox[fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z)]
      (toLp 2 (p, q)))
    (i : Fin (m - 1)) (j : Fin n) (hboundary : ¬ ((j : ℕ) + 1 < n)) :
    y.snd i j ∈ prox[absolute_value_penalty lam] (q i j) := by
  have hy_min :
      ∀ z : DualSpace m n,
        proximal_objective
            (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
            (toLp 2 (p, q)) y ≤
          proximal_objective
            (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
            (toLp 2 (p, q)) z := by
    -- Membership in the proximal map is exactly global minimality of the isotropic proximal
    -- objective.
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    exact hy
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
  intro a
  let remainder : ℝ :=
    (∑ i' : Fin (m - 1), ∑ j' : Fin (n - 1),
        (lam *
            Real.sqrt
              (y.fst (Fin.castLE (Nat.sub_le m 1) i') j' ^ (2 : ℕ) +
                y.snd i' (Fin.castLE (Nat.sub_le n 1) j') ^ (2 : ℕ)) +
          (1 / 2 : ℝ) *
            (y.fst (Fin.castLE (Nat.sub_le m 1) i') j' -
                p (Fin.castLE (Nat.sub_le m 1) i') j') ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            (y.snd i' (Fin.castLE (Nat.sub_le n 1) j') -
                q i' (Fin.castLE (Nat.sub_le n 1) j')) ^ (2 : ℕ) : ℝ)) +
    (∑ i' : Fin m, ∑ j' : Fin (n - 1),
      if hi' : (i' : ℕ) + 1 < m then
        (0 : ℝ)
      else
        (lam * |y.fst i' j'| + (1 / 2 : ℝ) * (y.fst i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
    Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦
      if hj' : (j' : ℕ) + 1 < n then
        (0 : ℝ)
      else
        (lam * |y.snd i j'| + (1 / 2 : ℝ) * (y.snd i j' - q i j') ^ (2 : ℕ) : ℝ)) +
    Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
      ∑ j' : Fin n,
        if hj' : (j' : ℕ) + 1 < n then
          (0 : ℝ)
        else
          (lam * |y.snd i' j'| + (1 / 2 : ℝ) * (y.snd i' j' - q i' j') ^ (2 : ℕ) : ℝ))
  have hy_self :
      proximal_objective
          (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
          (toLp 2 (p, q)) y =
        (((lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          (remainder : EReal) := by
    -- Rewrite the untouched minimizer as a self-update so the same scalar remainder appears on
    -- both sides.
    rw [show y = toLp 2 (y.fst, y.snd) by cases y; rfl]
    simpa [remainder, vertical_update] using
      (isotropic_boundary_vertical_update_objective_eq_scalar_objective_add_const
        lam p y.fst q y.snd i j hboundary (y.snd i j))
  have ha_update :
      proximal_objective
          (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z))
          (toLp 2 (p, q)) (toLp 2 (y.fst, vertical_update y.snd i j a)) =
        (((lam * |a| + (1 / 2 : ℝ) * (a - q i j) ^ (2 : ℕ) : ℝ)) : EReal) +
          (remainder : EReal) := by
    -- Replacing only the boundary vertical entry isolates the scalar absolute-value prox block.
    simpa [remainder] using
      (isotropic_boundary_vertical_update_objective_eq_scalar_objective_add_const
        lam p y.fst q y.snd i j hboundary a)
  have hcompare := hy_min (toLp 2 (y.fst, vertical_update y.snd i j a))
  rw [hy_self, ha_update] at hcompare
  have hscalar :
      (((lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) ≤
        (((lam * |a| + (1 / 2 : ℝ) * (a - q i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
    -- Cancel the common finite remainder inside `EReal`.
    exact ((EReal.addLECancellable_coe remainder).add_le_add_iff_right).mp hcompare
  simpa [proximal_objective_apply, absolute_value_penalty_apply] using hscalar

/-- Proposition 12.4 (2): for `0 ≤ λ`, the proximal mapping of the scaled isotropic regularizer
`λ g₁`, evaluated at the canonical `L²` product point corresponding to `(p, q)`, is the singleton
given by isotropic shrinkage on the interior pairs and soft-thresholding on the boundary terms. -/
theorem prox_two_dimensional_total_variation_isotropic_regularizer_eq_singleton
    (lam : ℝ) (hlam : 0 ≤ lam) (p : HorizontalSpace m n) (q : VerticalSpace m n) :
    prox[fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_isotropic_regularizer z)]
      (toLp 2 (p, q)) = {two_dimensional_total_variation_isotropic_prox_point lam p q} := by
  -- Route correction: the anisotropic scalar-entry replacement proof does not directly transfer to
  -- `g₁`; the missing source-faithful step is to rewrite one coupled interior `(p_{i,j}, q_{i,j})`
  -- block as the literal Chapter 6 two-dimensional norm proximal objective plus a common
  -- remainder, and only then handle the boundary absolute-value terms as scalar updates.
  refine Set.eq_singleton_iff_unique_mem.2 ?_
  constructor
  · -- The explicit isotropic prox point is a global minimizer by summing the interior pair and
    -- boundary scalar optimality inequalities.
    exact isotropic_prox_point_mem_proximal_mapping lam hlam p q
  · intro y hy
    have hhorizontal_eq
        (i : Fin m) (j : Fin (n - 1)) :
        y.fst i j = (two_dimensional_total_variation_isotropic_prox_point lam p q).fst i j := by
      by_cases hi : (i : ℕ) + 1 < m
      · let ii : Fin (m - 1) := i.castLT (Nat.lt_sub_iff_add_lt.mpr hi)
        have hcast_i : Fin.castLE (Nat.sub_le m 1) ii = i := by
          -- Casting the interior row back up recovers the original row.
          ext
          rfl
        have hpair_mem :=
          isotropic_global_minimizer_gives_interior_pair_prox_membership lam p q y hy ii j
        rw [two_dimensional_total_variation_pair_prox_eq_singleton lam hlam
          (p (Fin.castLE (Nat.sub_le m 1) ii) j)
          (q ii (Fin.castLE (Nat.sub_le n 1) j))] at hpair_mem
        have hpair_eq :
            toLp 2 ![y.fst i j, y.snd ii (Fin.castLE (Nat.sub_le n 1) j)] =
              toLp 2
                ![two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
                    (q ii (Fin.castLE (Nat.sub_le n 1) j)) * p i j,
                  two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
                    (q ii (Fin.castLE (Nat.sub_le n 1) j)) *
                      q ii (Fin.castLE (Nat.sub_le n 1) j)] := by
          -- The interior prox membership identifies the current pair with the unique paired
          -- shrinkage point.
          simpa [ii, hcast_i] using hpair_mem
        have hcoord :
            y.fst i j =
              two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
                (q ii (Fin.castLE (Nat.sub_le n 1) j)) * p i j := by
          -- Project the paired equality to the horizontal coordinate.
          simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0) hpair_eq
        have htarget :
            (two_dimensional_total_variation_isotropic_prox_point lam p q).fst i j =
              two_dimensional_total_variation_isotropic_shrink_factor lam (p i j)
                (q ii (Fin.castLE (Nat.sub_le n 1) j)) * p i j := by
          -- On an interior row, the explicit point uses the isotropic shrinkage formula.
          simpa [ii, hi] using
            (two_dimensional_total_variation_isotropic_prox_point_fst_apply lam p q i j)
        exact hcoord.trans htarget.symm
      · have hmem :=
          isotropic_global_minimizer_gives_boundary_horizontal_prox_membership
            lam p q y hy i j hi
        rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (p i j)] at hmem
        have hyij : y.fst i j = 𝒯[lam] (p i j) := by
          -- The last-row scalar prox is unique, so the horizontal boundary coordinate is fixed.
          simpa using hmem
        have htarget :
            (two_dimensional_total_variation_isotropic_prox_point lam p q).fst i j =
              𝒯[lam] (p i j) := by
          -- On the boundary row, the explicit point uses soft-thresholding.
          simpa [hi] using
            (two_dimensional_total_variation_isotropic_prox_point_fst_apply lam p q i j)
        exact hyij.trans htarget.symm
    have hvertical_eq
        (i : Fin (m - 1)) (j : Fin n) :
        y.snd i j = (two_dimensional_total_variation_isotropic_prox_point lam p q).snd i j := by
      by_cases hj : (j : ℕ) + 1 < n
      · let jj : Fin (n - 1) := j.castLT (Nat.lt_sub_iff_add_lt.mpr hj)
        have hcast_j : Fin.castLE (Nat.sub_le n 1) jj = j := by
          -- Casting the interior column back up recovers the original column.
          ext
          rfl
        have hpair_mem :=
          isotropic_global_minimizer_gives_interior_pair_prox_membership lam p q y hy i jj
        rw [two_dimensional_total_variation_pair_prox_eq_singleton lam hlam
          (p (Fin.castLE (Nat.sub_le m 1) i) jj)
          (q i (Fin.castLE (Nat.sub_le n 1) jj))] at hpair_mem
        have hpair_eq :
            toLp 2 ![y.fst (Fin.castLE (Nat.sub_le m 1) i) jj, y.snd i j] =
              toLp 2
                ![two_dimensional_total_variation_isotropic_shrink_factor lam
                    (p (Fin.castLE (Nat.sub_le m 1) i) jj) (q i j) *
                      p (Fin.castLE (Nat.sub_le m 1) i) jj,
                  two_dimensional_total_variation_isotropic_shrink_factor lam
                    (p (Fin.castLE (Nat.sub_le m 1) i) jj) (q i j) * q i j] := by
          -- The interior prox membership identifies the current pair with the unique paired
          -- shrinkage point.
          simpa [jj, hcast_j] using hpair_mem
        have hcoord :
            y.snd i j =
              two_dimensional_total_variation_isotropic_shrink_factor lam
                (p (Fin.castLE (Nat.sub_le m 1) i) jj) (q i j) * q i j := by
          -- Project the paired equality to the vertical coordinate.
          simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 1) hpair_eq
        have htarget :
            (two_dimensional_total_variation_isotropic_prox_point lam p q).snd i j =
              two_dimensional_total_variation_isotropic_shrink_factor lam
                (p (Fin.castLE (Nat.sub_le m 1) i) jj) (q i j) * q i j := by
          -- On an interior column, the explicit point uses the isotropic shrinkage formula.
          simpa [jj, hj] using
            (two_dimensional_total_variation_isotropic_prox_point_snd_apply lam p q i j)
        exact hcoord.trans htarget.symm
      · have hmem :=
          isotropic_global_minimizer_gives_boundary_vertical_prox_membership
            lam p q y hy i j hj
        rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (q i j)] at hmem
        have hyij : y.snd i j = 𝒯[lam] (q i j) := by
          -- The last-column scalar prox is unique, so the vertical boundary coordinate is fixed.
          simpa using hmem
        have htarget :
            (two_dimensional_total_variation_isotropic_prox_point lam p q).snd i j =
              𝒯[lam] (q i j) := by
          -- On the boundary column, the explicit point uses soft-thresholding.
          simpa [hj] using
            (two_dimensional_total_variation_isotropic_prox_point_snd_apply lam p q i j)
        exact hyij.trans htarget.symm
    apply (WithLp.equiv 2 (HorizontalSpace m n × VerticalSpace m n)).injective
    -- Equality in the `WithLp` product reduces to coordinatewise equality of the horizontal and
    -- vertical matrix components.
    simpa using
      (Prod.ext
        (by
          ext i j
          exact hhorizontal_eq i j)
        (by
          ext i j
          exact hvertical_eq i j))

/-- Proposition 12.4 (3): for `0 ≤ λ`, the proximal mapping of the scaled anisotropic regularizer
`λ g_{ℓ¹}`, evaluated at the canonical `L²` product point corresponding to `(p, q)`, is the
singleton given by entrywise soft-thresholding. -/
theorem prox_two_dimensional_total_variation_anisotropic_regularizer_eq_singleton
    (lam : ℝ) (hlam : 0 ≤ lam) (p : HorizontalSpace m n) (q : VerticalSpace m n) :
    prox[fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z)]
      (toLp 2 (p, q)) = {two_dimensional_total_variation_anisotropic_prox_point lam p q} := by
  refine Set.eq_singleton_iff_unique_mem.2 ?_
  constructor
  · have hu_mem :
        two_dimensional_total_variation_anisotropic_prox_point lam p q ∈
          prox[fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z)]
            (toLp 2 (p, q)) := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro y
      have hhorizontal_term
          (i : Fin m) (j : Fin (n - 1)) :
          lam * |𝒯[lam] (p i j)| + (1 / 2 : ℝ) * (𝒯[lam] (p i j) - p i j) ^ (2 : ℕ) ≤
            lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) := by
        have hsoft_mem : 𝒯[lam] (p i j) ∈ prox[absolute_value_penalty lam] (p i j) := by
          rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (p i j)]
          simp
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hsoft_mem
        have hsoft_le := hsoft_mem (y.fst i j)
        have hsoft_le' :
            (((lam * |𝒯[lam] (p i j)| +
                  (1 / 2 : ℝ) * (𝒯[lam] (p i j) - p i j) ^ (2 : ℕ) : ℝ)) : EReal) ≤
              (((lam * |y.fst i j| +
                  (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
          simpa [proximal_objective_apply, absolute_value_penalty_apply] using hsoft_le
        exact_mod_cast hsoft_le'
      have hvertical_term
          (i : Fin (m - 1)) (j : Fin n) :
          lam * |𝒯[lam] (q i j)| + (1 / 2 : ℝ) * (𝒯[lam] (q i j) - q i j) ^ (2 : ℕ) ≤
            lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) := by
        have hsoft_mem : 𝒯[lam] (q i j) ∈ prox[absolute_value_penalty lam] (q i j) := by
          rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (q i j)]
          simp
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hsoft_mem
        have hsoft_le := hsoft_mem (y.snd i j)
        have hsoft_le' :
            (((lam * |𝒯[lam] (q i j)| +
                  (1 / 2 : ℝ) * (𝒯[lam] (q i j) - q i j) ^ (2 : ℕ) : ℝ)) : EReal) ≤
              (((lam * |y.snd i j| +
                  (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
          simpa [proximal_objective_apply, absolute_value_penalty_apply] using hsoft_le
        exact_mod_cast hsoft_le'
      have hhorizontal_sum :
          ∑ i : Fin m, ∑ j : Fin (n - 1),
              (lam * |𝒯[lam] (p i j)| + (1 / 2 : ℝ) * (𝒯[lam] (p i j) - p i j) ^ (2 : ℕ) : ℝ) ≤
            ∑ i : Fin m, ∑ j : Fin (n - 1),
              (lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        refine Finset.sum_le_sum ?_
        intro j hj
        exact hhorizontal_term i j
      have hvertical_sum :
          ∑ i : Fin (m - 1), ∑ j : Fin n,
              (lam * |𝒯[lam] (q i j)| + (1 / 2 : ℝ) * (𝒯[lam] (q i j) - q i j) ^ (2 : ℕ) : ℝ) ≤
            ∑ i : Fin (m - 1), ∑ j : Fin n,
              (lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        refine Finset.sum_le_sum ?_
        intro j hj
        exact hvertical_term i j
      have htarget_obj :
          proximal_objective
              (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
              (toLp 2 (p, q)) (two_dimensional_total_variation_anisotropic_prox_point lam p q) =
            ((((∑ i : Fin m, ∑ j : Fin (n - 1),
                  (lam * |𝒯[lam] (p i j)| +
                    (1 / 2 : ℝ) * (𝒯[lam] (p i j) - p i j) ^ (2 : ℕ) : ℝ)) +
                ∑ i : Fin (m - 1), ∑ j : Fin n,
                  (lam * |𝒯[lam] (q i j)| +
                    (1 / 2 : ℝ) * (𝒯[lam] (q i j) - q i j) ^ (2 : ℕ) : ℝ) : ℝ)) : EReal) := by
        -- Expand the explicit prox point and split the anisotropic objective into scalar terms.
        simpa [two_dimensional_total_variation_anisotropic_prox_point] using
          (anisotropic_proximal_objective_sum_formula
            lam p (fun i j ↦ 𝒯[lam] (p i j)) q (fun i j ↦ 𝒯[lam] (q i j)))
      have hy_obj :
          proximal_objective
              (fun z : DualSpace m n ↦ ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
              (toLp 2 (p, q)) y =
            ((((∑ i : Fin m, ∑ j : Fin (n - 1),
                  (lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) +
                ∑ i : Fin (m - 1), ∑ j : Fin n,
                  (lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ) : ℝ)) :
              EReal) := by
        -- Read `y` as the canonical `WithLp` pair and apply the global sum formula.
        rw [show y = toLp 2 (y.fst, y.snd) by cases y; rfl]
        simpa using anisotropic_proximal_objective_sum_formula lam p y.fst q y.snd
      rw [htarget_obj, hy_obj]
      exact_mod_cast add_le_add hhorizontal_sum hvertical_sum
    simpa using hu_mem
  · intro y hy
    have hy_min :
        ∀ z : DualSpace m n,
          proximal_objective
              (fun z : DualSpace m n ↦
                ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
              (toLp 2 (p, q)) y ≤
            proximal_objective
              (fun z : DualSpace m n ↦
                ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
              (toLp 2 (p, q)) z := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
      exact hy
    have hhorizontal_mem
        (i : Fin m) (j : Fin (n - 1)) :
        y.fst i j ∈ prox[absolute_value_penalty lam] (p i j) := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro a
      let remainder : ℝ :=
        Finset.sum (Finset.univ.erase j) (fun j' : Fin (n - 1) ↦
          (lam * |y.fst i j'| + (1 / 2 : ℝ) * (y.fst i j' - p i j') ^ (2 : ℕ) : ℝ)) +
        Finset.sum (Finset.univ.erase i) (fun i' : Fin m ↦
          ∑ j' : Fin (n - 1),
            (lam * |y.fst i' j'| + (1 / 2 : ℝ) * (y.fst i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
        ∑ i' : Fin (m - 1), ∑ j' : Fin n,
          (lam * |y.snd i' j'| + (1 / 2 : ℝ) * (y.snd i' j' - q i' j') ^ (2 : ℕ) : ℝ)
      have hy_self :
          proximal_objective
              (fun z : DualSpace m n ↦
                ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
              (toLp 2 (p, q)) y =
            (((lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) :
              EReal) + (remainder : EReal) := by
        -- Rewrite the untouched point as a self-update so the same remainder appears on both sides.
        simpa [remainder, horizontal_update] using
          (anisotropic_horizontal_update_objective_eq_scalar_objective_add_const
            lam p y.fst q y.snd i j (y.fst i j))
      have hy_replaced :
          proximal_objective
              (fun z : DualSpace m n ↦
                ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
              (toLp 2 (p, q)) (toLp 2 (horizontal_update y.fst i j a, y.snd)) =
            (((lam * |a| + (1 / 2 : ℝ) * (a - p i j) ^ (2 : ℕ) : ℝ)) : EReal) +
              (remainder : EReal) := by
        -- Replacing a single horizontal coordinate isolates exactly the scalar objective.
        simpa [remainder] using
          (anisotropic_horizontal_update_objective_eq_scalar_objective_add_const
            lam p y.fst q y.snd i j a)
      have hcompare := hy_min (toLp 2 (horizontal_update y.fst i j a, y.snd))
      rw [hy_self, hy_replaced] at hcompare
      have hscalar :
          (((lam * |y.fst i j| + (1 / 2 : ℝ) * (y.fst i j - p i j) ^ (2 : ℕ) : ℝ)) : EReal) ≤
            (((lam * |a| + (1 / 2 : ℝ) * (a - p i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
        exact ((EReal.addLECancellable_coe remainder).add_le_add_iff_right).mp hcompare
      simpa [proximal_objective_apply, absolute_value_penalty_apply] using hscalar
    have hvertical_mem
        (i : Fin (m - 1)) (j : Fin n) :
        y.snd i j ∈ prox[absolute_value_penalty lam] (q i j) := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro a
      let remainder : ℝ :=
        (∑ i' : Fin m, ∑ j' : Fin (n - 1),
            (lam * |y.fst i' j'| + (1 / 2 : ℝ) * (y.fst i' j' - p i' j') ^ (2 : ℕ) : ℝ)) +
        Finset.sum (Finset.univ.erase j) (fun j' : Fin n ↦
          (lam * |y.snd i j'| + (1 / 2 : ℝ) * (y.snd i j' - q i j') ^ (2 : ℕ) : ℝ)) +
        Finset.sum (Finset.univ.erase i) (fun i' : Fin (m - 1) ↦
          ∑ j' : Fin n,
            (lam * |y.snd i' j'| + (1 / 2 : ℝ) * (y.snd i' j' - q i' j') ^ (2 : ℕ) : ℝ))
      have hy_self :
          proximal_objective
              (fun z : DualSpace m n ↦
                ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
              (toLp 2 (p, q)) y =
            (((lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ)) :
              EReal) + (remainder : EReal) := by
        -- Rewrite the untouched point as a self-update so the same remainder appears on both sides.
        simpa [remainder, vertical_update] using
          (anisotropic_vertical_update_objective_eq_scalar_objective_add_const
            lam p y.fst q y.snd i j (y.snd i j))
      have hy_replaced :
          proximal_objective
              (fun z : DualSpace m n ↦
                ↑(lam * two_dimensional_total_variation_anisotropic_regularizer z))
              (toLp 2 (p, q)) (toLp 2 (y.fst, vertical_update y.snd i j a)) =
            (((lam * |a| + (1 / 2 : ℝ) * (a - q i j) ^ (2 : ℕ) : ℝ)) : EReal) +
              (remainder : EReal) := by
        -- Replacing a single vertical coordinate isolates exactly the scalar objective.
        simpa [remainder] using
          (anisotropic_vertical_update_objective_eq_scalar_objective_add_const
            lam p y.fst q y.snd i j a)
      have hcompare := hy_min (toLp 2 (y.fst, vertical_update y.snd i j a))
      rw [hy_self, hy_replaced] at hcompare
      have hscalar :
          (((lam * |y.snd i j| + (1 / 2 : ℝ) * (y.snd i j - q i j) ^ (2 : ℕ) : ℝ)) : EReal) ≤
            (((lam * |a| + (1 / 2 : ℝ) * (a - q i j) ^ (2 : ℕ) : ℝ)) : EReal) := by
        exact ((EReal.addLECancellable_coe remainder).add_le_add_iff_right).mp hcompare
      simpa [proximal_objective_apply, absolute_value_penalty_apply] using hscalar
    have hhorizontal_eq
        (i : Fin m) (j : Fin (n - 1)) :
        y.fst i j = 𝒯[lam] (p i j) := by
      have hmem := hhorizontal_mem i j
      rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (p i j)] at hmem
      simpa using hmem
    have hvertical_eq
        (i : Fin (m - 1)) (j : Fin n) :
        y.snd i j = 𝒯[lam] (q i j) := by
      have hmem := hvertical_mem i j
      rw [prox_absolute_value_penalty_eq_singleton_soft_thresholding lam hlam (q i j)] at hmem
      simpa using hmem
    apply (WithLp.equiv 2 (HorizontalSpace m n × VerticalSpace m n)).injective
    -- Equality in `WithLp 2 (HorizontalSpace m n × VerticalSpace m n)` reduces to equality of the underlying pair.
    simpa [two_dimensional_total_variation_anisotropic_prox_point] using
      (Prod.ext
        (by
          ext i j
          exact hhorizontal_eq i j)
        (by
          ext i j
          exact hvertical_eq i j))

end
