/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

open scoped Matrix

namespace LinearGaussian

universe u v

section

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- Exercise 4.17. The covariance-form gain
`ΓXX * Kᵀ * (K * ΓXX * Kᵀ + C_N)⁻¹` agrees with the precision-form gain
`(Kᵀ * C_N⁻¹ * K + ΓXX⁻¹)⁻¹ * Kᵀ * C_N⁻¹` when the displayed inverses exist. -/
theorem covarianceGain_eq_precisionGain
    (K : Matrix m n ℝ) (ΓXX : Matrix n n ℝ) (C_N : Matrix m m ℝ)
    (hΓXX : IsUnit ΓXX) (hC_N : IsUnit C_N)
    (h_precision : IsUnit (Kᵀ * C_N⁻¹ * K + ΓXX⁻¹)) :
    ΓXX * Kᵀ * (K * ΓXX * Kᵀ + C_N)⁻¹ =
      (Kᵀ * C_N⁻¹ * K + ΓXX⁻¹)⁻¹ * Kᵀ * C_N⁻¹ := by
  let G : Matrix n m ℝ := Kᵀ * C_N⁻¹
  let P : Matrix n n ℝ := Kᵀ * C_N⁻¹ * K + ΓXX⁻¹
  obtain ⟨_⟩ := hΓXX.nonempty_invertible
  obtain ⟨_⟩ := hC_N.nonempty_invertible
  obtain ⟨_⟩ := h_precision.nonempty_invertible
  have h_precision' : IsUnit (ΓXX⁻¹ + Kᵀ * C_N⁻¹ * K) := by
    simpa [add_comm] using h_precision
  have h_woodbury :
      (C_N + K * ΓXX * Kᵀ)⁻¹ =
        C_N⁻¹ - C_N⁻¹ * K * P⁻¹ * Kᵀ * C_N⁻¹ := by
    simpa [P, Matrix.mul_assoc, add_comm] using
      Matrix.add_mul_mul_inv_eq_sub C_N K ΓXX Kᵀ hC_N hΓXX h_precision'
  have h_ΓXX_mul_P : ΓXX * P = 1 + ΓXX * G * K := by
    simp [G, P, Matrix.mul_add, Matrix.mul_assoc, add_comm]
  have h_ΓXX_split : ΓXX = P⁻¹ + ΓXX * G * K * P⁻¹ := by
    calc
      ΓXX = ΓXX * (P * P⁻¹) := by simp
      _ = (ΓXX * P) * P⁻¹ := by simp [Matrix.mul_assoc]
      _ = (1 + ΓXX * G * K) * P⁻¹ := by rw [h_ΓXX_mul_P]
      _ = P⁻¹ + ΓXX * G * K * P⁻¹ := by
        simp [Matrix.add_mul, Matrix.mul_assoc]
  have h_cancel : ΓXX - ΓXX * G * K * P⁻¹ = P⁻¹ := by
    have h :=
      congrArg (fun Y ↦ Y - ΓXX * G * K * P⁻¹) h_ΓXX_split
    simpa [sub_eq_add_neg, add_assoc] using h
  calc
    ΓXX * Kᵀ * (K * ΓXX * Kᵀ + C_N)⁻¹
        = ΓXX * Kᵀ * (C_N + K * ΓXX * Kᵀ)⁻¹ := by simp [add_comm]
    _ = ΓXX * Kᵀ * (C_N⁻¹ - C_N⁻¹ * K * P⁻¹ * Kᵀ * C_N⁻¹) := by rw [h_woodbury]
    _ = ΓXX * G - ΓXX * G * K * P⁻¹ * G := by
      simp [G, Matrix.mul_sub, Matrix.mul_assoc]
    _ = ΓXX * G - (ΓXX * G * K * P⁻¹) * G := by
      simp [Matrix.mul_assoc]
    _ = (ΓXX - ΓXX * G * K * P⁻¹) * G := by
      exact (Matrix.sub_mul ΓXX (ΓXX * G * K * P⁻¹) G).symm
    _ = P⁻¹ * G := by rw [h_cancel]
    _ = P⁻¹ * Kᵀ * C_N⁻¹ := by
      simp [G, Matrix.mul_assoc]

end

end LinearGaussian
