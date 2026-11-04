/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_theorem_3_1

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

variable {𝕜 : Type*}

section LinearOrderRing

variable [Ring 𝕜] [LinearOrder 𝕜]

/-- Remark 3.2 (1): one Fourier elimination step introduces one new inequality for each pair of
positive and negative last-column rows. -/
theorem fourier_pair_index_card {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) 𝕜) :
    Fintype.card (FourierPositiveIndex A × FourierNegativeIndex A) =
      Fintype.card (FourierPositiveIndex A) * Fintype.card (FourierNegativeIndex A) := by
  simp

/-- Remark 3.2 (1): the one-step Fourier-Motzkin system is indexed by the new positive-negative
pairs together with the rows whose last coefficient already vanishes. -/
theorem fourier_step_index_card {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) 𝕜) :
    Fintype.card (FourierStepIndex A) =
      Fintype.card (FourierPositiveIndex A) * Fintype.card (FourierNegativeIndex A) +
        Fintype.card (FourierZeroIndex A) := by
  simp

/-- Remark 3.2 (3): the canonical nonnegative row multiplier producing the step row `s`. -/
def fourier_step_row_multiplier
    {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) 𝕜) (s : FourierStepIndex A) : Fin m → 𝕜 :=
  match s with
  | Sum.inl ⟨i, k⟩ =>
      Pi.single i.1 (-A k.1 (Fin.last n)) + Pi.single k.1 (A i.1 (Fin.last n))
  | Sum.inr i =>
      Pi.single i.1 1

end LinearOrderRing

section OrderedRing

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Remark 3.2 (3): the canonical multiplier for a step row is componentwise nonnegative. -/
theorem fourier_step_row_multiplier_nonneg
    {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) 𝕜) (s : FourierStepIndex A) :
    0 ≤ fourier_step_row_multiplier A s := by
  rcases s with ⟨i, k⟩ | i
  · have hik : i.1 ≠ k.1 := by
      intro h
      have hk : A i.1 (Fin.last n) < 0 := by simpa [h] using k.2
      exact lt_asymm hk i.2
    intro l
    by_cases hl : l = i.1
    · subst hl
      simp [fourier_step_row_multiplier, hik, le_of_lt (neg_pos.mpr k.2)]
    · by_cases hk : l = k.1
      · subst hk
        simp [fourier_step_row_multiplier, hl, i.2.le]
      · simp [fourier_step_row_multiplier, hl, hk]
  · intro l
    by_cases hl : l = i.1
    · subst hl
      simp [fourier_step_row_multiplier]
    · simp [fourier_step_row_multiplier, Pi.single, hl]

end OrderedRing

section LinearOrderedCommRing

variable [CommRing 𝕜] [LinearOrder 𝕜]

/-- Remark 3.2 (3): the canonical multiplier reproduces the corresponding step row, with zero
coefficient on the eliminated coordinate. -/
theorem fourier_step_row_multiplier_vecMul
    {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) 𝕜) (s : FourierStepIndex A) :
    fourier_step_row_multiplier A s ᵥ* A =
      (Fin.lastCases (0 : 𝕜) (fourier_step_matrix A s) : Fin (n + 1) → 𝕜) := by
  rcases s with ⟨i, k⟩ | i
  · have hwA :
        fourier_step_row_multiplier A (Sum.inl (i, k)) ᵥ* A =
          (-A k.1 (Fin.last n)) • A.row i.1 + A i.1 (Fin.last n) • A.row k.1 := by
      simp [fourier_step_row_multiplier, Matrix.add_vecMul, Matrix.single_vecMul]
    ext j
    refine Fin.lastCases ?_ ?_ j
    · rw [hwA]
      simp [Matrix.row, mul_comm]
    · intro j'
      rw [hwA]
      simp [Matrix.row, fourier_step_matrix, Fin.lastCases_castSucc, sub_eq_add_neg, add_comm]
  · ext j
    refine Fin.lastCases ?_ ?_ j
    · simp [fourier_step_row_multiplier, Fin.lastCases_last, i.2]
    · intro j'
      simp [fourier_step_row_multiplier, fourier_step_matrix, Fin.lastCases_castSucc]

/-- Remark 3.2 (3): evaluating the canonical multiplier on the original right-hand side produces
the step right-hand side. -/
theorem fourier_step_row_multiplier_dot_rhs
    {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) 𝕜) (b : Fin m → 𝕜) (s : FourierStepIndex A) :
    fourier_step_row_multiplier A s ⬝ᵥ b = fourier_step_rhs A b s := by
  rcases s with ⟨i, k⟩ | i
  · calc
      fourier_step_row_multiplier A (Sum.inl (i, k)) ⬝ᵥ b =
          (Pi.single i.1 (-A k.1 (Fin.last n)) + Pi.single k.1 (A i.1 (Fin.last n))) ⬝ᵥ b := by
            rfl
      _ = Pi.single i.1 (-A k.1 (Fin.last n)) ⬝ᵥ b +
            Pi.single k.1 (A i.1 (Fin.last n)) ⬝ᵥ b := by
            rw [add_dotProduct]
      _ = (-A k.1 (Fin.last n)) * b i.1 + A i.1 (Fin.last n) * b k.1 := by
            rw [single_dotProduct, single_dotProduct]
      _ = fourier_step_rhs A b (Sum.inl (i, k)) := by
            simp [fourier_step_rhs, sub_eq_add_neg, add_comm]
  · simp [fourier_step_row_multiplier, fourier_step_rhs]

end LinearOrderedCommRing
