/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

open Matrix

/-
Domain sampling for this file:
- primary domain: positive-definite inverse-Hessian Broyden-class updates on the Chapter 5
  Euclidean-space matrix model;
- sampled project owners in this domain:
  `broydenClassInverseUpdate`,
  `broydenClassInverseUpdate_mulVec`,
  `right_ne_zero_of_dotProduct_ne_zero`,
  `posDef_dotProduct_mulVec_ne_zero`,
  `Matrix.PosDef.dotProduct_mulVec_pos`;
- best owner abstraction: the Chapter 5 inverse-form Broyden-class owner
  `broydenClassInverseUpdate`;
- primitive data here: a positive-definite current matrix `H`, secant data `s y`, and the
  Broyden parameter `φ`;
- derived API here: only the positive-definiteness criterion in Theorem 5.2.2, expressed as a
  bridge theorem over the existing update owner and the denominator lemmas now exposed by that
  same Chapter 5 owner file.

This file therefore reuses the established Chapter 5 Broyden update and curvature/nonvanishing
API directly instead of keeping a second local denominator lemma.
-/

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Chapter05 Theorem 5.2.2: a nonnegative scalar multiple of the Broyden
direction outer product is positive semidefinite. -/
lemma broydenClassDirectionOuter_posSemidef
    (H : MatrixN) (s y : Point) (φ : ℝ) (hφ : 0 ≤ φ) :
    (φ •
        Matrix.vecMulVec
          (broydenClassDirection H s y).ofLp
          (broydenClassDirection H s y).ofLp).PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- The Broyden correction is symmetric because it is a scaled self-outer product.
    simpa [isHermitian_iff_isSymm] using
      (outerSelf_isSymm (broydenClassDirection H s y)).smul φ
  · intro x
    let v := (broydenClassDirection H s y).ofLp
    have hQuadraticRewrite :
        x.sum (fun i xi ↦ x.sum fun j xj ↦
          xi * (φ * (v i * v j)) * xj) =
          x.sum (fun i xi ↦ x.sum fun j xj ↦ φ * (xi * (xj * (v i * v j)))) := by
      simp [mul_left_comm, mul_comm]
    have hExpand :
        x.sum (fun i xi ↦ x.sum fun j xj ↦ φ * (xi * (xj * (v i * v j)))) =
          φ * (x.sum fun i xi ↦ xi * v i) ^ (2 : ℕ) := by
      simp [pow_two, Finsupp.sum, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    have hQuadratic :
        x.sum (fun i xi ↦ x.sum fun j xj ↦
          star xi * (φ • Matrix.vecMulVec v v) i j * xj) =
          φ * (x.sum fun i xi ↦ xi * v i) ^ (2 : ℕ) := by
      calc
        x.sum (fun i xi ↦ x.sum fun j xj ↦
            star xi * (φ • Matrix.vecMulVec v v) i j * xj)
            = x.sum (fun i xi ↦ x.sum fun j xj ↦
                xi * (φ * (v i * v j)) * xj) := by
                  simp only [star_trivial, Matrix.smul_apply, Matrix.vecMulVec_apply,
                    smul_eq_mul]
        _ = x.sum (fun i xi ↦ x.sum fun j xj ↦
              φ * (xi * (xj * (v i * v j)))) := hQuadraticRewrite
        _ = φ * (x.sum fun i xi ↦ xi * v i) ^ (2 : ℕ) := hExpand
    have hQuadNonneg :
        0 ≤ φ * (x.sum fun i xi ↦ xi * v i) ^ (2 : ℕ) :=
      mul_nonneg hφ (sq_nonneg _)
    -- The quadratic form reduces to `φ * (linear form)^2`, hence is nonnegative.
    exact hQuadratic ▸ hQuadNonneg

/-- Helper for Chapter05 Theorem 5.2.2: once `0 ≤ φ` and `0 < dotProduct s y`, the Broyden
inverse update stays positive definite. -/
lemma broydenClassInverseUpdate_posDef_of_nonnegativeParameter
    (H : MatrixN) (hH : H.PosDef) (s y : Point) (φ : ℝ)
    (hφ : 0 ≤ φ) (hcurv : 0 < dotProduct s y) :
    (broydenClassInverseUpdate H s y φ).PosDef := by
  have hHsymm : Matrix.IsSymm H := by
    simpa [isHermitian_iff_isSymm] using hH.isHermitian
  have hsy : dotProduct s y ≠ 0 := ne_of_gt hcurv
  have hy : y ≠ 0 := right_ne_zero_of_dotProduct_ne_zero hsy
  have hyLp : y.ofLp ≠ 0 := by
    simpa using hy
  have hyHy : 0 < dotProduct y (H.mulVec y) := by
    -- Positive definiteness of `H` provides the second Broyden denominator.
    simpa using hH.dotProduct_mulVec_pos hyLp
  have hDfp :
      (dfpInverseUpdate H s y).PosDef :=
    dfpInverseUpdate_posDef_of_posDef_of_curvature_local H hH s y hcurv
  have hCorrection :
      (φ •
          Matrix.vecMulVec
            (broydenClassDirection H s y).ofLp
            (broydenClassDirection H s y).ofLp).PosSemidef :=
    broydenClassDirectionOuter_posSemidef H s y φ hφ
  -- Route correction: use the existing `DFP + φ • v vᵀ` normal form instead of a spectral
  -- smallest-eigenvalue comparison.
  rw [broydenClassInverseUpdate_eq_dfpInverseUpdate_add H hHsymm s y φ hsy hyHy]
  simpa using hDfp.add_posSemidef hCorrection

/-- Chapter05 Theorem 5.2.2 (Positive Definiteness of Broyden Class of Update): let `φ ≥ 0`.
For a positive-definite inverse-Hessian approximation `H`, on the Broyden-class inverse-update
domain `dotProduct s y ≠ 0`, the canonical Chapter 5 Broyden update remains positive definite
if and only if `0 < dotProduct s y`. -/
theorem broydenClassInverseUpdate_posDef_iff
    (H : MatrixN) (hH : H.PosDef) (s y : Point) (φ : ℝ)
    (hφ : 0 ≤ φ) (hsy : dotProduct s y ≠ 0) :
    let hyHy :=
      posDef_dotProduct_mulVec_ne_zero hH (right_ne_zero_of_dotProduct_ne_zero hsy)
    (broydenClassInverseUpdate H s y φ).PosDef ↔ 0 < dotProduct s y := by
  dsimp
  constructor
  · intro hUpdate
    have hy : y ≠ 0 := right_ne_zero_of_dotProduct_ne_zero hsy
    have hyLp : y.ofLp ≠ 0 := by
      simpa using hy
    have hyHy : dotProduct y (H.mulVec y) ≠ 0 :=
      posDef_dotProduct_mulVec_ne_zero hH hy
    have hQuadPos :
        0 < dotProduct y ((broydenClassInverseUpdate H s y φ).mulVec y) := by
      -- Positive definiteness of the updated matrix makes its quadratic form positive on `y`.
      simpa using hUpdate.dotProduct_mulVec_pos hyLp
    -- The inverse secant equation identifies the updated quadratic form with the curvature
    -- pairing `dotProduct s y`.
    simpa [dotProduct_comm, broydenClassInverseUpdate_mulVec H s y φ hsy hyHy] using hQuadPos
  · intro hcurv
    -- The reverse direction is the `DFP + PosSemidef correction` argument packaged above.
    exact broydenClassInverseUpdate_posDef_of_nonnegativeParameter H hH s y φ hφ hcurv

end
