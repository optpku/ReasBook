/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1

noncomputable section

open Matrix

/-
Domain sampling for this file:
- primary domain: inverse-form quasi-Newton matrix updates on the Chapter 5 Euclidean matrix
  model;
- sampled same-domain owners: `dfpInverseUpdate`, `bfgsInverseUpdate`,
  `broydenClassInverseUpdate`, and `ssvmInverseUpdate`;
- best owner abstraction: the existing Chapter 5 update owners themselves, with
  `Matrix.IsSymm` as the natural owner surface for source-faithful identification of the
  `γ = 1` SSVM formula with the Broyden class;
- primitive data here: a current inverse-Hessian approximation `H`, secant data `s y`, and the
  scalar parameter `φ`;
- derived API here: only the `γ = 1` SSVM specialization theorem. The DFP/Broyden `φ = 0`
  identity is already owned upstream.

This file is therefore a bridge file: it deletes no owner-level mathematics and keeps only the
specialization that genuinely needs a local statement.
-/

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/- Chapter05 Exercise 5.9 (1): the canonical inverse DFP update is the `φ = 0`
specialization of the inverse-Hessian Broyden class. This is already the upstream owner
`broydenClassInverseUpdate_zero`, so the exercise reuses that result directly. -/
#check broydenClassInverseUpdate_zero

/-- Chapter05 Exercise 5.9 (2): if the current inverse-Hessian approximation `H` is symmetric,
then setting `γ = 1` in the self-scaling variable-metric inverse update recovers the ordinary
inverse-Hessian Broyden update. This is the source-faithful owner surface: for nonsymmetric `H`,
the BFGS side of the Broyden class is not represented by the same expanded `H y` cross terms. -/
theorem ssvmInverseUpdate_gamma_one_eq_broydenClassInverseUpdate
    {H : MatrixN} (hH : H.IsSymm) (s y : Point) (φ : ℝ)
    (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    ssvmInverseUpdate H s y φ 1 = broydenClassInverseUpdate H s y φ := by
  have hyH : y ᵥ* H = H *ᵥ y := by
    simpa [hH.eq] using (Matrix.vecMul_transpose H y)
  have hcorr :
      (dotProduct y (H.mulVec y)) •
          Matrix.vecMulVec (ssvmCorrectionVector H s y) (ssvmCorrectionVector H s y) =
        (dotProduct y (H.mulVec y) * (dotProduct s y)⁻¹ * (dotProduct s y)⁻¹) •
            Matrix.vecMulVec s s
          - (dotProduct s y)⁻¹ •
              (Matrix.vecMulVec s (H.mulVec y) + Matrix.vecMulVec (H.mulVec y) s)
          + (dotProduct y (H.mulVec y))⁻¹ •
              Matrix.vecMulVec (H.mulVec y) (H.mulVec y) := by
    by_cases hsy : dotProduct s y = 0
    · ext i j
      simp [ssvmCorrectionVector, Matrix.vecMulVec_apply, hsy]
      field_simp [hyHy]
    · ext i j
      simp [ssvmCorrectionVector, Matrix.vecMulVec_apply]
      field_simp [hsy, hyHy]
      ring_nf
  rw [ssvmInverseUpdate_eq_dfpInverseUpdate_add]
  rw [broydenClassInverseUpdate, bfgsInverseUpdate_eq_expandedForm]
  rw [Matrix.vecMulVec_mul, hyH, Matrix.mul_vecMulVec]
  rw [dfpInverseUpdate, ← smul_smul, hcorr]
  ext i j
  simp [Matrix.vecMulVec_apply]
  ring

end
