/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

noncomputable section

open ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

private lemma half_symmetric_derivative
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm) (x : H) :
    (1 / 2 : ℝ) •
        (((B.precompR H) x) (ContinuousLinearMap.id ℝ H) +
          ((B.precompL H) (ContinuousLinearMap.id ℝ H)) x) =
      B x := by
  ext y
  simp [Pi.smul_apply]
  rw [show (B y) x = (B x) y by simpa using hB.eq y x]
  ring_nf

/-- Example 2.59: for a symmetric continuous bilinear form `B`, the functional
`y ↦ (1 / 2) B(y, y) - ℓ(y)` is Fréchet differentiable at `x` with derivative `B(x, ·) - ℓ`. -/
theorem hasFDerivAt_half_bilinear_self_sub_linear
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm)
    (ℓ : H →L[ℝ] ℝ) (x : H) :
    HasFDerivAt
      (fun y : H ↦ (1 / 2 : ℝ) * B y y - ℓ y)
      (B x - ℓ) x := by
  have hQuad : HasFDerivAt (fun y : H ↦ B y y)
      ((((B.precompR H) x) (ContinuousLinearMap.id ℝ H) +
          ((B.precompL H) (ContinuousLinearMap.id ℝ H)) x)) x := by
    simpa using
      (B.hasFDerivAt_of_bilinear
        (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.id ℝ H))
        (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.id ℝ H)))
  have hHalfScaled : HasFDerivAt
      (fun y : H ↦ (1 / 2 : ℝ) * B y y)
      ((1 / 2 : ℝ) •
        ((((B.precompR H) x) (ContinuousLinearMap.id ℝ H) +
          ((B.precompL H) (ContinuousLinearMap.id ℝ H)) x))) x := by
    simpa [Pi.smul_apply] using hQuad.const_smul (1 / 2 : ℝ)
  have hHalf : HasFDerivAt (fun y : H ↦ (1 / 2 : ℝ) * B y y) (B x) x := by
    convert hHalfScaled using 1
    exact (half_symmetric_derivative B hB x).symm
  simpa [sub_eq_add_neg] using hHalf.sub ℓ.hasFDerivAt

/-- The Fréchet derivative of the quadratic perturbation associated to a symmetric continuous
bilinear form is `B(x, ·) - ℓ`. -/
theorem fderiv_half_bilinear_self_sub_linear
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm)
    (ℓ : H →L[ℝ] ℝ) (x : H) :
    fderiv ℝ (fun y : H ↦ (1 / 2 : ℝ) * B y y - ℓ y) x =
      B x - ℓ := by
  simpa using (hasFDerivAt_half_bilinear_self_sub_linear B hB ℓ x).fderiv
