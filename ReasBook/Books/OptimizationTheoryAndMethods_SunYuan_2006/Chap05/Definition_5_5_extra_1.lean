/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1

noncomputable section

-- Domain sampling:
-- * primary domain: Chapter 5 inverse-form quasi-Newton / self-scaling variable-metric updates.
-- * sampled same-domain Chapter 5 owners: `dfpInverseUpdate`, `broydenClassDirection`, and
--   `broydenClassInverseUpdate`.
-- * core/canonical owners kept here: `ssvmCorrectionVector` and `ssvmInverseUpdate`.
-- * bridge/view layer kept here: the textbook square-root direction is reused through the
--   existing Chapter 5 owner `broydenClassDirection`, rather than introducing a second SSVM
--   direction owner.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The correction vector
`(sᵀ y)⁻¹ • s - (yᵀ H y)⁻¹ • H y`
appearing in the inverse self-scaling variable-metric update. -/
def ssvmCorrectionVector (H : MatrixN) (s y : Point) : Point :=
  (dotProduct s y)⁻¹ • s - (dotProduct y (H.mulVec y))⁻¹ • Matrix.toEuclideanLin H y

/-- Unfolding formula for `ssvmCorrectionVector`. -/
theorem ssvmCorrectionVector_eq (H : MatrixN) (s y : Point) :
    ssvmCorrectionVector H s y =
      (dotProduct s y)⁻¹ • s - (dotProduct y (H.mulVec y))⁻¹ • Matrix.toEuclideanLin H y := rfl

/-- The inverse self-scaling variable-metric update
`Hₖ₊₁^(φ, γ) = γ • (Hₖ - (yᵀ Hₖ y)⁻¹ • (Hₖ y) (Hₖ y)ᵀ
  + φ * (yᵀ Hₖ y) • v vᵀ) + (sᵀ y)⁻¹ • s sᵀ`,
where `v = ssvmCorrectionVector H s y`. -/
def ssvmInverseUpdate
    (H : MatrixN) (s y : Point) (φ γ : ℝ) : MatrixN :=
  let v := ssvmCorrectionVector H s y
  γ • (dfpInverseUpdate H s y + (φ * dotProduct y (H.mulVec y)) • Matrix.vecMulVec v v) +
    ((1 - γ) * (dotProduct s y)⁻¹) • Matrix.vecMulVec s s

/-- The SSVM owner is the self-scaled DFP update plus the rank-one correction built from
`ssvmCorrectionVector`. -/
theorem ssvmInverseUpdate_eq_dfpInverseUpdate_add
    (H : MatrixN) (s y : Point) (φ γ : ℝ) :
    ssvmInverseUpdate H s y φ γ =
      γ •
          (dfpInverseUpdate H s y
            + (φ * dotProduct y (H.mulVec y)) •
                Matrix.vecMulVec (ssvmCorrectionVector H s y) (ssvmCorrectionVector H s y))
        + ((1 - γ) * (dotProduct s y)⁻¹) • Matrix.vecMulVec s s := rfl

/-- Expanding `ssvmInverseUpdate` recovers the textbook matrix formula. -/
theorem ssvmInverseUpdate_eq
    (H : MatrixN) (s y : Point) (φ γ : ℝ) :
    ssvmInverseUpdate H s y φ γ =
      γ •
          (H
            - (dotProduct y (H.mulVec y))⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y)
            + (φ * dotProduct y (H.mulVec y)) •
                Matrix.vecMulVec (ssvmCorrectionVector H s y) (ssvmCorrectionVector H s y))
        + (dotProduct s y)⁻¹ • Matrix.vecMulVec s s := by
  ext i j
  simp [ssvmInverseUpdate, ssvmCorrectionVector, dfpInverseUpdate]
  ring

/-- The textbook square-root direction in `(5.5.19)` is exactly the earlier Chapter 5 Broyden
direction. -/
theorem broydenClassDirection_eq_sqrt_smul_ssvmCorrectionVector (H : MatrixN) (s y : Point) :
    broydenClassDirection H s y =
      Real.sqrt (dotProduct y (H.mulVec y)) • ssvmCorrectionVector H s y := by
  rfl

/-- Chapter05 Definition 5.5-extra-1: on the curvature domain
`0 ≤ dotProduct y (H.mulVec y)`, the canonical owner `ssvmInverseUpdate` can be written in the
book's source-facing form with the earlier Chapter 5 direction owner
`broydenClassDirection H s y`. -/
theorem ssvmInverseUpdate_eq_broydenClassDirection
    (H : MatrixN) (s y : Point) (φ γ : ℝ)
    (hyHy : 0 ≤ dotProduct y (H.mulVec y)) :
    ssvmInverseUpdate H s y φ γ =
      γ •
          (H
            - (dotProduct y (H.mulVec y))⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y)
            + φ •
                Matrix.vecMulVec
                  (broydenClassDirection H s y)
                  (broydenClassDirection H s y))
        + (dotProduct s y)⁻¹ • Matrix.vecMulVec s s := by
  have hdirection :
      Matrix.vecMulVec
          (broydenClassDirection H s y)
          (broydenClassDirection H s y) =
        dotProduct y (H.mulVec y) •
          Matrix.vecMulVec (ssvmCorrectionVector H s y) (ssvmCorrectionVector H s y) := by
    ext i j
    have hsqrt :
        Real.sqrt (dotProduct y (H.mulVec y)) * Real.sqrt (dotProduct y (H.mulVec y)) =
          dotProduct y (H.mulVec y) := by
      simpa [pow_two] using Real.sq_sqrt hyHy
    simp only [Matrix.vecMulVec_apply, broydenClassDirection_eq_sqrt_smul_ssvmCorrectionVector]
    calc
      Real.sqrt (dotProduct y (H.mulVec y)) * (ssvmCorrectionVector H s y).ofLp i *
          (Real.sqrt (dotProduct y (H.mulVec y)) * (ssvmCorrectionVector H s y).ofLp j)
          =
        (Real.sqrt (dotProduct y (H.mulVec y)) * Real.sqrt (dotProduct y (H.mulVec y))) *
          ((ssvmCorrectionVector H s y).ofLp i * (ssvmCorrectionVector H s y).ofLp j) := by
            ring
      _ = dotProduct y (H.mulVec y) *
            ((ssvmCorrectionVector H s y).ofLp i * (ssvmCorrectionVector H s y).ofLp j) := by
            rw [hsqrt]
  rw [ssvmInverseUpdate_eq, hdirection]
  simp [smul_smul, mul_left_comm]

/-- Setting `γ = 1` in the canonical SSVM owner recovers the source-facing Broyden-class shape
with the earlier Chapter 5 direction owner `broydenClassDirection H s y`. -/
theorem ssvmInverseUpdate_one_eq_broydenClassDirection
    (H : MatrixN) (s y : Point) (φ : ℝ)
    (hyHy : 0 ≤ dotProduct y (H.mulVec y)) :
    ssvmInverseUpdate H s y φ 1 =
      H
        + (dotProduct s y)⁻¹ • Matrix.vecMulVec s s
        - (dotProduct y (H.mulVec y))⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y)
        + φ •
            Matrix.vecMulVec
              (broydenClassDirection H s y)
              (broydenClassDirection H s y) := by
  rw [ssvmInverseUpdate_eq_broydenClassDirection H s y φ 1 hyHy]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end
