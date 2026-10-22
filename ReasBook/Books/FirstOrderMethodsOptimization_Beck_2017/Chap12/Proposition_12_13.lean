/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_68

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProduct

section

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/- Proposition 12.13 is `source-facing` in the Chapter 6 proximal-norm-composition API.

Domain sampling against Definition 6.1, Example 6.19, Lemma 6.68, and the Euclidean-space
adjoint API shows the following owner split.

- `source-facing`: the fixed three-point-star difference matrix and the resulting inactive/active
  proximal branch formulas from Proposition 12.13.
- `core/canonical`: `prox[...]`, `norm_penalty`, the adjoint notation `†`, and the Gram operator
  `A ∘L A†`.
- `bridge/view`: the concrete Euclidean matrix realization
  `three_point_star_difference_matrix.toEuclideanLin.toContinuousLinearMap`.

The generic shifted-Gram root existence/uniqueness and proximal singleton formulas already live in
`Lemma_6_68`. This file therefore keeps only the fixed matrix/operator data and the proposition's
branch-local specialization of those Chapter 6 owner theorems, instead of duplicating a parallel
local chosen-root API. -/

/-- The fixed matrix `A = !![1, -1, 0; 1, 0, -1]` appearing in Proposition 12.13. -/
def three_point_star_difference_matrix : Matrix (Fin 2) (Fin 3) ℝ :=
  !![(1 : ℝ), -1, 0;
      1, 0, -1]

/-- The continuous linear map `x ↦ A x` attached to the fixed matrix of Proposition 12.13. -/
def three_point_star_difference_operator : E3 →L[ℝ] E2 :=
  three_point_star_difference_matrix.toEuclideanLin.toContinuousLinearMap

local notation "A" => three_point_star_difference_operator
local notation "AT" =>
  LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin three_point_star_difference_matrix.transpose)

/-- The Gram operator `A A†` attached to the fixed three-point-star difference map. -/
def three_point_star_difference_gram : E2 →L[ℝ] E2 :=
  A ∘L A†

local notation "G" => three_point_star_difference_gram

/-- The penalty `h(z) = ‖A z‖₂` attached to the fixed matrix in Proposition 12.13. -/
def three_point_star_difference_penalty : E3 → EReal :=
  norm_penalty 1 ∘ A

/-- Evaluating the penalty gives the textbook formula `h(z) = ‖A z‖₂`. -/
@[simp] theorem three_point_star_difference_penalty_eq (z : E3) :
    three_point_star_difference_penalty z = ((‖A z‖ : ℝ) : EReal) := by
  simp [three_point_star_difference_penalty, norm_penalty_apply]

/-- Helper for Proposition 12.13: the adjoint of the fixed operator is the transpose-matrix action
on `E2`. -/
lemma three_point_star_difference_operator_adjoint_eq_transpose :
    A† = AT := by
  -- Identify the Hilbert-space adjoint with the transpose matrix on Euclidean coordinates.
  calc
    A† =
        LinearMap.toContinuousLinearMap
          ((Matrix.toEuclideanLin three_point_star_difference_matrix).adjoint) := by
      simpa [three_point_star_difference_operator] using
        (LinearMap.adjoint_toContinuousLinearMap
          (Matrix.toEuclideanLin three_point_star_difference_matrix)).symm
    _ = AT := by
      simpa using
        congrArg LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint
            three_point_star_difference_matrix).symm

/-- Helper for Proposition 12.13: the Gram operator `A A†` is the Euclidean action of the concrete
matrix `AAᵀ = !![2, 1; 1, 2]`. -/
lemma three_point_star_difference_gram_eq_concrete_matrix_operator :
    G =
      ((!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin.toContinuousLinearMap) := by
  -- Route correction: rewrite the abstract Gram operator into the concrete textbook matrix `AAᵀ`.
  have hgram :
      three_point_star_difference_matrix * three_point_star_difference_matrix.transpose =
        (!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) := by
    -- The fixed `2 × 3` matrix gives the displayed `2 × 2` Gram matrix by coordinate calculation.
    ext i j
    fin_cases i <;> fin_cases j
    · simp [three_point_star_difference_matrix, Matrix.mul_apply, Fin.sum_univ_three]
      norm_num
    · simp [three_point_star_difference_matrix, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [three_point_star_difference_matrix, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [three_point_star_difference_matrix, Matrix.mul_apply, Fin.sum_univ_three]
      norm_num
  -- Push the matrix identity through `Matrix.toEuclideanLin`.
  calc
    G =
        LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin
            (three_point_star_difference_matrix *
              three_point_star_difference_matrix.transpose)) := by
          rw [three_point_star_difference_gram,
            three_point_star_difference_operator_adjoint_eq_transpose]
          ext v i
          simp [three_point_star_difference_operator, Matrix.mulVec_mulVec]
    _ =
        LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin
            (!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)) := by
          simp [hgram]

/-- Helper for Proposition 12.13: the concrete Gram matrix `!![2, 1; 1, 2]` has inverse
`(1 / 3) • !![2, -1; -1, 2]`. -/
lemma three_point_star_difference_gram_matrix_inverse_formula :
    (((!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) *
        ((1 / 3 : ℝ) • (!![(2 : ℝ), -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ))) = 1) ∧
      ((((1 / 3 : ℝ) • (!![(2 : ℝ), -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ)) *
        (!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)) = 1) := by
  constructor
  · -- Verify the left inverse entrywise.
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · -- Verify the right inverse entrywise.
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Helper for Proposition 12.13: the concrete Gram operator is the Euclidean action of the matrix
`!![2, 1; 1, 2]`. -/
def three_point_star_difference_concrete_gram_operator : E2 →L[ℝ] E2 :=
  ((!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin.toContinuousLinearMap)

/-- Helper for Proposition 12.13: the explicit inverse candidate is the Euclidean action of
`(1 / 3) • !![2, -1; -1, 2]`. -/
def three_point_star_difference_concrete_gram_inverse_operator : E2 →L[ℝ] E2 :=
  LinearMap.toContinuousLinearMap <|
    Matrix.toEuclideanLin
      (((1 / 3 : ℝ) • (!![(2 : ℝ), -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ)))

/-- Helper for Proposition 12.13: the explicit inverse candidate is a left inverse of the concrete
Gram operator. -/
lemma three_point_star_difference_concrete_gram_left_inverse :
    three_point_star_difference_concrete_gram_operator ∘L
        three_point_star_difference_concrete_gram_inverse_operator =
      1 := by
  -- Evaluate the two coordinates directly and simplify the resulting linear expressions.
  ext v i
  fin_cases i
  · simp [three_point_star_difference_concrete_gram_operator,
      three_point_star_difference_concrete_gram_inverse_operator]
    ring_nf
    simp [Matrix.vecHead]
  · simp [three_point_star_difference_concrete_gram_operator,
      three_point_star_difference_concrete_gram_inverse_operator]
    ring_nf
    simp [Matrix.vecHead, Matrix.vecTail]

/-- Helper for Proposition 12.13: the explicit inverse candidate is also a right inverse of the
concrete Gram operator. -/
lemma three_point_star_difference_concrete_gram_right_inverse :
    three_point_star_difference_concrete_gram_inverse_operator ∘L
        three_point_star_difference_concrete_gram_operator =
      1 := by
  -- The reverse composition has the same coordinate verification.
  ext v i
  fin_cases i
  · simp [three_point_star_difference_concrete_gram_operator,
      three_point_star_difference_concrete_gram_inverse_operator]
    ring_nf
    simp [Matrix.vecHead]
  · simp [three_point_star_difference_concrete_gram_operator,
      three_point_star_difference_concrete_gram_inverse_operator]
    ring_nf
    simp [Matrix.vecHead, Matrix.vecTail]

/-- The Gram operator `A A†` of the fixed three-point-star difference map is invertible. -/
theorem three_point_star_difference_gram_isInvertible :
    three_point_star_difference_gram.IsInvertible := by
  let u : Units (E2 →L[ℝ] E2) :=
    { val := three_point_star_difference_concrete_gram_operator
      inv := three_point_star_difference_concrete_gram_inverse_operator
      val_inv := three_point_star_difference_concrete_gram_left_inverse
      inv_val := three_point_star_difference_concrete_gram_right_inverse }
  -- Repackage the explicit unit as a continuous linear equivalence for the Gram operator.
  rw [three_point_star_difference_gram_eq_concrete_matrix_operator]
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E2 u, rfl⟩

/-- Scaling the fixed penalty by `λ` recovers the Chapter 6 owner `norm_penalty lam ∘ A`. -/
theorem scaled_three_point_star_difference_penalty_eq_norm_penalty_comp (lam : ℝ) :
    (fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)) =
      norm_penalty lam ∘ A := by
  funext z
  simp [three_point_star_difference_penalty, norm_penalty_apply]

/-- The active-branch scalar residual from Proposition 12.13,
`g(α) = ‖(A A† + α I)⁻¹ (A x)‖₂² - λ²`. -/
def three_point_star_difference_shift_residual (x : E3) (lam : ℝ) (α : ℝ) : ℝ :=
  ‖(G + α • 1).inverse (A x)‖ ^ 2 - lam ^ 2

/-- Expanding the active-branch scalar residual gives the textbook formula
`g(α) = ‖(A A† + α I)⁻¹ (A x)‖₂² - λ²`. -/
@[simp] theorem three_point_star_difference_shift_residual_eq
    (x : E3) (lam α : ℝ) :
    three_point_star_difference_shift_residual x lam α =
      ‖(G + α • 1).inverse (A x)‖ ^ 2 - lam ^ 2 :=
  rfl

/-- On the active branch, the scalar residual `g(α)` from Proposition 12.13 is strictly
decreasing on `[0, ∞)`. -/
theorem three_point_star_difference_shift_residual_strictAntiOn_nonneg
    (x : E3) (lam : ℝ) (hx : A x ≠ 0) :
    StrictAntiOn (three_point_star_difference_shift_residual x lam) (Set.Ici 0) := by
  intro α hα β hβ hlt
  dsimp [three_point_star_difference_shift_residual]
  exact sub_lt_sub_right
    ((gram_shift_inverse_norm_sq_strictAntiOn_nonneg
      A three_point_star_difference_gram_isInvertible x hx) hα hβ hlt) _

/-- Active-branch root equation used in Proposition 12.13: when
`λ < ‖(A A†)⁻¹ (A x)‖₂`, the decreasing residual
`g(α) = ‖(A A† + α I)⁻¹ (A x)‖₂² - λ²` has a unique positive root. -/
theorem existsUnique_three_point_star_difference_shift_residual_root
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    ∃! α : ℝ,
      0 < α ∧ three_point_star_difference_shift_residual x lam α = 0 := by
  rcases
      existsUnique_linear_image_norm_prox_shift
        A three_point_star_difference_gram_isInvertible lam hlam x hlarge with
    ⟨α, hα, hαuniq⟩
  refine ⟨α, ?_, ?_⟩
  · refine ⟨hα.1, ?_⟩
    have hsq :
        ‖(G + α • 1).inverse (A x)‖ ^ 2 = lam ^ 2 :=
      by
        simpa [three_point_star_difference_gram] using
          (gram_shift_inverse_norm_eq_iff_sq_eq A lam hlam x α).1 hα.2
    dsimp [three_point_star_difference_shift_residual]
    linarith
  · intro β hβ
    have hsq : ‖(G + β • 1).inverse (A x)‖ ^ 2 = lam ^ 2 := by
      have hzero := hβ.2
      dsimp [three_point_star_difference_shift_residual] at hzero
      linarith
    have hβnorm :
        ‖(A ∘L A† + β • 1).inverse (A x)‖ = lam := by
      exact (gram_shift_inverse_norm_eq_iff_sq_eq A lam hlam x β).2 <| by
        simpa [three_point_star_difference_gram] using hsq
    exact hαuniq β ⟨hβ.1, hβnorm⟩

/-- The unique positive root `α*` of the active-branch scalar residual from Proposition 12.13. -/
noncomputable def three_point_star_difference_active_shift
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) : ℝ :=
  (existsUnique_three_point_star_difference_shift_residual_root x lam hlam hlarge).choose

/-- The active-branch root `α*` is the unique positive zero of the residual `g`. -/
theorem three_point_star_difference_active_shift_spec
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    0 < three_point_star_difference_active_shift x lam hlam hlarge ∧
      three_point_star_difference_shift_residual x lam
        (three_point_star_difference_active_shift x lam hlam hlarge) = 0 := by
  let hroot :=
    existsUnique_three_point_star_difference_shift_residual_root x lam hlam hlarge
  exact hroot.choose_spec.1

/-- The active-branch root `α*` from Proposition 12.13 is positive. -/
theorem three_point_star_difference_active_shift_pos
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    0 < three_point_star_difference_active_shift x lam hlam hlarge := by
  exact (three_point_star_difference_active_shift_spec x lam hlam hlarge).1

/-- The active-branch root `α*` solves the residual equation `g(α*) = 0`. -/
theorem three_point_star_difference_shift_residual_active_shift_eq_zero
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    three_point_star_difference_shift_residual x lam
      (three_point_star_difference_active_shift x lam hlam hlarge) = 0 := by
  exact (three_point_star_difference_active_shift_spec x lam hlam hlarge).2

/-- The active-branch root `α*` satisfies the textbook norm equation
`‖(A A† + α* I)⁻¹ (A x)‖₂ = λ`. -/
theorem three_point_star_difference_active_shift_norm_eq
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    ‖(G + three_point_star_difference_active_shift x lam hlam hlarge • 1).inverse (A x)‖ = lam := by
  have hzero :=
    three_point_star_difference_shift_residual_active_shift_eq_zero x lam hlam hlarge
  have hsq :
      ‖(G + three_point_star_difference_active_shift x lam hlam hlarge • 1).inverse (A x)‖ ^ 2 =
        lam ^ 2 := by
    dsimp [three_point_star_difference_shift_residual] at hzero
    linarith
  exact
    (gram_shift_inverse_norm_eq_iff_sq_eq
      A lam hlam x (three_point_star_difference_active_shift x lam hlam hlarge)).2 hsq

/-- Inactive branch of Proposition 12.13: if `‖(A A†)⁻¹ (A x)‖₂ ≤ λ`, then the proximal mapping of
`λ h` with `h(z) = ‖A z‖₂` is the singleton `{x - A† (A A†)⁻¹ A x}`. -/
theorem prox_three_point_star_difference_penalty_eq_inactive_singleton
    (x : E3) (lam : ℝ)
    (hsmall : ‖(G).inverse (A x)‖ ≤ lam) :
    prox[fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)] x =
      {x - (A†) ((G).inverse (A x))} := by
  rw [scaled_three_point_star_difference_penalty_eq_norm_penalty_comp]
  simpa [three_point_star_difference_gram] using
    prox_linear_image_norm_eq_singleton_of_le
      A three_point_star_difference_gram_isInvertible lam x hsmall

/-- Active branch of Proposition 12.13: if `λ < ‖(A A†)⁻¹ (A x)‖₂`, then the proximal mapping of
`λ h` with `h(z) = ‖A z‖₂` is the singleton
`{x - A† (A A† + α* I)⁻¹ A x}`, where `α*` is the unique positive root of the residual
equation from `existsUnique_three_point_star_difference_shift_residual_root`. -/
theorem prox_three_point_star_difference_penalty_eq_active_singleton
    (x : E3) (lam : ℝ) (hlam : 0 < lam)
    (hlarge : lam < ‖(G).inverse (A x)‖) :
    prox[fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)] x =
      {x - (A†) ((G + three_point_star_difference_active_shift x lam hlam hlarge • 1).inverse
        (A x))} := by
  rw [scaled_three_point_star_difference_penalty_eq_norm_penalty_comp]
  simpa [three_point_star_difference_gram] using
    prox_linear_image_norm_eq_singleton_of_shift
      A lam x
      (three_point_star_difference_active_shift x lam hlam hlarge)
      (three_point_star_difference_active_shift_pos x lam hlam hlarge)
      (three_point_star_difference_active_shift_norm_eq x lam hlam hlarge)

/-- Proposition 12.13: for the fixed three-point-star matrix `A`, the proximal mapping of the
scaled penalty `λ h` with `h(z) = ‖A z‖₂` is the singleton
`{x - A† (A A†)⁻¹ A x}` on the branch `‖(A A†)⁻¹ A x‖₂ ≤ λ`. On the complementary branch
`λ < ‖(A A†)⁻¹ A x‖₂`, the active-branch shift is the unique positive root `α*` of the
decreasing scalar residual `g(α) = ‖(A A† + α I)⁻¹ (A x)‖₂² - λ²`, and the proximal mapping is
the singleton `{x - A† (A A† + α* I)⁻¹ A x}`. In this Euclidean model, `A†` is the transpose
action `Aᵀ`. -/
theorem prox_three_point_star_difference_penalty_eq_piecewise
    (x : E3) (lam : ℝ) (hlam : 0 < lam) :
    (‖(G).inverse (A x)‖ ≤ lam →
      prox[fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)] x =
        {x - (A†) ((G).inverse (A x))}) ∧
    (∀ hlarge : lam < ‖(G).inverse (A x)‖,
      prox[fun z : E3 ↦ ((lam : EReal) * three_point_star_difference_penalty z)] x =
        {x - (A†) ((G + three_point_star_difference_active_shift x lam hlam hlarge • 1).inverse
          (A x))}) := by
  refine ⟨?_, ?_⟩
  · intro hsmall
    exact prox_three_point_star_difference_penalty_eq_inactive_singleton x lam hsmall
  · intro hlarge
    exact prox_three_point_star_difference_penalty_eq_active_singleton x lam hlam hlarge

end
