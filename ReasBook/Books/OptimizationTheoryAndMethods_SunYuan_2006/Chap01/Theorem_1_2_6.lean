/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_5

-- Semantic recall: this perturbation result reuses the chapter's source-facing
-- matrix norm owners from Definition 1.2.2 rather than introducing a second
-- local norm hierarchy.

variable {n : ℕ}

section VonNeumannLemma

variable {N : Matrix (Fin n) (Fin n) ℝ → ℝ}

/-- Helper for Chapter01 Theorem 1.2.6: swapping the order of a matrix difference preserves the
same norm bound. -/
lemma matrixNorm_sub_swap_le
    (hNorm : IsMatrixNorm N) {A B : Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hAB : N (A - B) ≤ β) :
    N (B - A) ≤ β := by
  -- Rewrite the swapped difference as multiplication by `-1`, then use absolute homogeneity.
  have hswap : N (B - A) = N (A - B) := by
    calc
      N (B - A) = N ((-1 : ℝ) • (A - B)) := by
        congr 1
        ext i j
        simp [sub_eq_add_neg]
      _ = |(-1 : ℝ)| * N (A - B) := hNorm.smul (-1) (A - B)
      _ = N (A - B) := by norm_num
  rw [hswap]
  exact hAB

/-- Helper for Chapter01 Theorem 1.2.6: the textbook perturbation bound implies
`N (A⁻¹ * (B - A)) < 1`. -/
lemma perturbationNorm_lt_one_of_norm_sub_le
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N)
    {A B : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}
    (hAinv : N A⁻¹ ≤ α) (hAB : N (A - B) ≤ β) (hαβ : α * β < 1) :
    N (A⁻¹ * (B - A)) < 1 := by
  -- First convert the source hypothesis to the `B - A` spelling used by Theorem 1.2.5.
  have hBA : N (B - A) ≤ β := matrixNorm_sub_swap_le hNorm hAB
  have hα_nonneg : 0 ≤ α := le_trans (hNorm.nonneg A⁻¹) hAinv
  have hPert_le : N (A⁻¹ * (B - A)) ≤ α * β := by
    calc
      N (A⁻¹ * (B - A)) ≤ N A⁻¹ * N (B - A) := hSub.mul_le A⁻¹ (B - A)
      _ ≤ α * N (B - A) := by
        exact mul_le_mul_of_nonneg_right hAinv (hNorm.nonneg (B - A))
      _ ≤ α * β := by
        exact mul_le_mul_of_nonneg_left hBA hα_nonneg
  -- The numerical smallness hypothesis closes the perturbation estimate.
  exact lt_of_le_of_lt hPert_le hαβ

/-- Helper for Chapter01 Theorem 1.2.6: the perturbation-theorem denominator bound is controlled
by the textbook bound `α / (1 - α * β)`. -/
lemma perturbationInvBound_le_textbookBound
    {x e α β : ℝ} (hx_nonneg : 0 ≤ x) (hx : x ≤ α) (he : e ≤ α * β) (hαβ : α * β < 1) :
    x / (1 - e) ≤ α / (1 - α * β) := by
  -- Turn the hypotheses into positive denominators so cross-multiplication is valid.
  have he_lt_one : e < 1 := lt_of_le_of_lt he hαβ
  have hden_left_pos : 0 < 1 - e := sub_pos.mpr he_lt_one
  have hden_right_pos : 0 < 1 - α * β := sub_pos.mpr hαβ
  -- Once denominators are cleared, monotonicity in the numerator and denominator is enough.
  rw [div_le_div_iff₀ hden_left_pos hden_right_pos]
  have hstep1 : x * (1 - α * β) ≤ x * (1 - e) := by
    apply mul_le_mul_of_nonneg_left ?_ hx_nonneg
    linarith
  have hstep2 : x * (1 - e) ≤ α * (1 - e) := by
    exact mul_le_mul_of_nonneg_right hx hden_left_pos.le
  exact hstep1.trans hstep2

/-- Chapter01 Theorem 1.2.6: if `N` is a matrix norm on
`Matrix (Fin n) (Fin n) ℝ` and is submultiplicative with `N 1 = 1`, if `A` is
invertible with `N A⁻¹ ≤ α`, if `N (A - B) ≤ β`, and if `α * β < 1`, then `B`
is invertible and `N B⁻¹ ≤ α / (1 - α * β)`. -/
theorem vonNeumannLemma_isUnit_and_inv_norm_le_of_norm_sub_le
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N) (hN_one : N 1 = 1)
    {A B : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}
    (hA : IsUnit A) (hAinv : N A⁻¹ ≤ α) (hAB : N (A - B) ≤ β) (hαβ : α * β < 1) :
    IsUnit B ∧ N B⁻¹ ≤ α / (1 - α * β) := by
  -- Build the perturbation estimate needed to invoke the previous von Neumann lemma.
  have hPert : N (A⁻¹ * (B - A)) < 1 :=
    perturbationNorm_lt_one_of_norm_sub_le hNorm hSub hAinv hAB hαβ
  have hBA : N (B - A) ≤ β := matrixNorm_sub_swap_le hNorm hAB
  have hα_nonneg : 0 ≤ α := le_trans (hNorm.nonneg A⁻¹) hAinv
  have hPert_le : N (A⁻¹ * (B - A)) ≤ α * β := by
    calc
      N (A⁻¹ * (B - A)) ≤ N A⁻¹ * N (B - A) := hSub.mul_le A⁻¹ (B - A)
      _ ≤ α * N (B - A) := by
        exact mul_le_mul_of_nonneg_right hAinv (hNorm.nonneg (B - A))
      _ ≤ α * β := by
        exact mul_le_mul_of_nonneg_left hBA hα_nonneg
  -- Reuse Theorem 1.2.5 for invertibility and its intermediate inverse-norm estimate.
  have hB : IsUnit B :=
    vonNeumannLemma_perturbation_isUnit hNorm hSub hN_one A B hA hPert
  have hInvBound :
      N B⁻¹ ≤ N A⁻¹ / (1 - N (A⁻¹ * (B - A))) :=
    vonNeumannLemma_perturbation_norm_inv_le hNorm hSub hN_one A B hA hPert
  -- Compare the predecessor bound with the textbook bound using only scalar inequalities.
  have hTextbook :
      N A⁻¹ / (1 - N (A⁻¹ * (B - A))) ≤ α / (1 - α * β) :=
    perturbationInvBound_le_textbookBound (hNorm.nonneg A⁻¹) hAinv hPert_le hαβ
  exact ⟨hB, hInvBound.trans hTextbook⟩

/-- Under the hypotheses of Theorem 1.2.6, the perturbed matrix `B` is invertible. -/
theorem vonNeumannLemma_isUnit_of_norm_sub_le
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N) (hN_one : N 1 = 1)
    {A B : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}
    (hA : IsUnit A) (hAinv : N A⁻¹ ≤ α) (hAB : N (A - B) ≤ β) (hαβ : α * β < 1) :
    IsUnit B :=
  (vonNeumannLemma_isUnit_and_inv_norm_le_of_norm_sub_le hNorm hSub hN_one hA hAinv hAB hαβ).1

/-- Under the hypotheses of Theorem 1.2.6, the inverse of `B` satisfies the
stability bound `N B⁻¹ ≤ α / (1 - α * β)`. -/
theorem vonNeumannLemma_inv_norm_le_of_norm_sub_le
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N) (hN_one : N 1 = 1)
    {A B : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}
    (hA : IsUnit A) (hAinv : N A⁻¹ ≤ α) (hAB : N (A - B) ≤ β) (hαβ : α * β < 1) :
    N B⁻¹ ≤ α / (1 - α * β) :=
  (vonNeumannLemma_isUnit_and_inv_norm_le_of_norm_sub_le hNorm hSub hN_one hA hAinv hAB hαβ).2

end VonNeumannLemma
