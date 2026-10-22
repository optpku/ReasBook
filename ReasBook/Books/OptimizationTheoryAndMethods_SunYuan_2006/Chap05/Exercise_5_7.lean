/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_2

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * primary domain: inverse-Hessian Broyden/Huang updates on the concrete Chapter 5 matrix
--   model;
-- * sampled project owners:
--   `broydenClassInverseUpdate`,
--   `broydenClassInverseUpdate_mulVec`,
--   `broydenClassInverseUpdate_isSymm`,
--   `IsHuangUpdate.satisfiesQuasiNewtonEquation`;
-- * best owner abstraction inside the minimal closure: the source-facing owner
--   `broydenClassInverseUpdate` from `Definition_5_2_extra_1`;
-- * source/core/bridge triage for this file:
--   source-facing: the exercise theorem asserting that the Broyden update is a Huang update;
--   core/canonical: `broydenClassInverseUpdate` and `satisfiesQuasiNewtonEquation`;
--   bridge/view: `IsHuangUpdate` from `Definition_5_2_extra_2`;
-- * primitive data is owned upstream in `Definition_5_2_extra_1` and
--   `Definition_5_2_extra_2`; this file keeps only derived exercise-level API.

/- Exercise 5.7: the inverse-Hessian Broyden owner is already defined canonically in
`Definition_5_2_extra_1`. -/
#check broydenClassInverseUpdate

/-- Exercise 5.7 (1): every inverse-Hessian Broyden-class update satisfies the
inverse-form quasi-Newton equation `Hnext.mulVec y = s`. -/
theorem broydenClassInverseUpdate_satisfiesQuasiNewtonEquation
    (H : MatrixN) (s y : Point) (φ : ℝ)
    (hsy : dotProduct s y ≠ 0) (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    satisfiesQuasiNewtonEquation
      (broydenClassInverseUpdate H s y φ).toEuclideanLin y s := by
  rw [satisfiesQuasiNewtonEquation_toEuclideanLin_iff]
  simpa using broydenClassInverseUpdate_mulVec H s y φ hsy hyHy

/- Exercise 5.7 (2): the symmetry theorem for the Broyden owner is already owned
canonically by `Definition_5_2_extra_1`. -/
#check broydenClassInverseUpdate_isSymm

/- Exercise 5.7 (3): the Huang owner already exposes the generalized inverse-form
quasi-Newton equation on the canonical operator-valued surface. -/
#check IsHuangUpdate.satisfiesQuasiNewtonEquation

/-
Exercise 5.7 (4): every symmetric inverse-Hessian Broyden-class update with the
ordinary secant denominators `dotProduct s y ≠ 0` and `dotProduct y (H.mulVec y) ≠ 0` is a
Huang update with generalized secant parameter `ρ = 1`.
-/
/-- Helper for Exercise 5.7: the symmetric inverse-Hessian Broyden update has the
same rank-two form as a Huang update with the canonical Exercise 5.7 coefficients. -/
lemma broydenClassInverseUpdate_eq_huangUpdate
    {H : MatrixN} (hH : Matrix.IsSymm H) (s y : Point) (φ : ℝ)
    (hsy : dotProduct s y ≠ 0) (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    broydenClassInverseUpdate H s y φ =
      huangUpdate H s y
        ((dotProduct s y)⁻¹ + φ * dotProduct y (H.mulVec y) / (dotProduct s y) ^ 2)
        (-φ / dotProduct s y)
        (-φ / dotProduct s y)
        ((φ - 1) / dotProduct y (H.mulVec y)) := by
  -- Normalize the Broyden and Huang owners to the same `s`/`H y` outer-product basis.
  rw [broydenClassInverseUpdate, bfgsInverseUpdate_eq_residualForm H s y hH,
    huangUpdate_eq_of_isSymm hH, dfpInverseUpdate]
  -- Expand the residual `s - H y` and compare the resulting coefficients entrywise.
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, sub_eq_add_neg,
    div_eq_mul_inv, dotProduct_comm]
  field_simp [hsy, hyHy]
  ring_nf

/-- Helper for Exercise 5.7: the Exercise 5.7 Huang `u`-vector has
`dotProduct (huangUpdateU ...) y = 1`. -/
lemma huangUpdateU_dotProduct_eq_one_for_broydenClass
    {H : MatrixN} (hH : Matrix.IsSymm H) (s y : Point) (φ : ℝ)
    (hsy : dotProduct s y ≠ 0) :
    dotProduct
        (huangUpdateU
          ((dotProduct s y)⁻¹ + φ * dotProduct y (H.mulVec y) / (dotProduct s y) ^ 2)
          (-φ / dotProduct s y) H s y)
        y = 1 := by
  -- Expand `u` and use symmetry to replace `Hᵀ y` by `H y`.
  rw [huangUpdateU_eq]
  -- The chosen coefficients are designed so the two normalized pairings cancel to `1`.
  simp [hH.eq, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_add, dotProduct_smul,
    dotProduct_comm, div_eq_mul_inv]
  field_simp [hsy]
  ring_nf

/-- Helper for Exercise 5.7: the Exercise 5.7 Huang `v`-vector has
`dotProduct (huangUpdateV ...) y = -1`. -/
lemma huangUpdateV_dotProduct_eq_neg_one_for_broydenClass
    {H : MatrixN} (hH : Matrix.IsSymm H) (s y : Point) (φ : ℝ)
    (hsy : dotProduct s y ≠ 0) (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    dotProduct
        (huangUpdateV
          (-φ / dotProduct s y)
          ((φ - 1) / dotProduct y (H.mulVec y)) H s y)
        y = -1 := by
  -- Expand `v` and rewrite the transpose action with the symmetry of `H`.
  rw [huangUpdateV_eq]
  -- The chosen coefficients force the two scalar pairings to combine to `-1`.
  simp [hH.eq, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_add, dotProduct_smul,
    dotProduct_comm, div_eq_mul_inv]
  field_simp [hsy, hyHy]
  ring_nf

/-- Chapter05 Exercise 5.7: every symmetric inverse-Hessian Broyden-class update with the
ordinary secant denominators `dotProduct s y ≠ 0` and `dotProduct y (H.mulVec y) ≠ 0` is a
Huang update with generalized secant parameter `ρ = 1`. -/
theorem broydenClassInverseUpdate_isHuangUpdate
    {H : MatrixN} (hH : Matrix.IsSymm H) (s y : Point) (φ : ℝ)
    (hsy : dotProduct s y ≠ 0) (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    IsHuangUpdate H (broydenClassInverseUpdate H s y φ) s y 1 := by
  -- Rewrite the Broyden owner to the Huang normal form supplied by the explicit coefficients.
  rw [broydenClassInverseUpdate_eq_huangUpdate hH s y φ hsy hyHy]
  -- The Huang witnesses are now certified by the two scalar auxiliary-vector identities.
  exact isHuangUpdate_huangUpdate H s y
    ((dotProduct s y)⁻¹ + φ * dotProduct y (H.mulVec y) / (dotProduct s y) ^ 2)
    (-φ / dotProduct s y)
    (-φ / dotProduct s y)
    ((φ - 1) / dotProduct y (H.mulVec y))
    1
    (huangUpdateU_dotProduct_eq_one_for_broydenClass hH s y φ hsy)
    (huangUpdateV_dotProduct_eq_neg_one_for_broydenClass hH s y φ hsy hyHy)
