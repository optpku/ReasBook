/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1.Direction
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1.Parameters
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric

open Matrix

noncomputable section

-- Semantic recall: the Chapter 5 inverse-update owners `dfpInverseUpdate` and
-- `bfgsInverseUpdate`, together with `Matrix.toEuclideanLin`, `Matrix.vecMulVec`, and
-- `Matrix.PosDef`, are the relevant canonical APIs here. This item stays on the source-facing
-- matrix surface for the inverse- and Hessian-form Broyden updates.

section

variable {n : ℕ}

-- Local declaration justification (source-local notation): the source formulas in this item are
-- written repeatedly on the fixed Euclidean space `ℝ^n`, and this file keeps that notation local
-- rather than introducing a reusable owner-level alias.
local notation "Point" => EuclideanSpace ℝ (Fin n)
-- Local declaration justification (source-local notation): the source formulas in this item are
-- stated on one fixed real `n × n` matrix space, and the alias is used only to keep those local
-- source-facing statements readable.
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- `broydenStep` and `broydenSecant` are reused from `Algorithm_5_1_1`, the owner file of the
-- quasi-Newton run data.

/-- Chapter05 Definition 5.2-extra-1: on the source denominator domain
`dotProduct s y ≠ 0` and `dotProduct y (H.mulVec y) ≠ 0`, the inverse-Hessian Broyden class
update is the weighted combination
`(1 - φ) • dfpInverseUpdate H s y + φ • bfgsInverseUpdate H s y`. When `0 ≤ φ ≤ 1`, this is
the Broyden convex class. -/
def broydenClassInverseUpdate (H : MatrixN) (s y : Point) (φ : ℝ) : MatrixN :=
  (1 - φ) • dfpInverseUpdate H s y + φ • bfgsInverseUpdate H s y

/-- The Broyden class can be written as `dfpInverseUpdate H s y + φ • v vᵀ`. -/
theorem broydenClassInverseUpdate_eq_dfpInverseUpdate_add
    (H : MatrixN) (hH : Matrix.IsSymm H) (s y : Point) (φ : ℝ) (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y)) :
    broydenClassInverseUpdate H s y φ =
      dfpInverseUpdate H s y
        + φ • Matrix.vecMulVec
            (broydenClassDirection H s y)
            (broydenClassDirection H s y) := by
  -- Rewrite the BFGS summand through the imported `dfp + v vᵀ` bridge.
  rw [broydenClassInverseUpdate,
    bfgsInverseUpdate_eq_dfpInverseUpdate_add_broydenClassDirection H hH s y hsy hyHy]
  -- Collect the two `dfpInverseUpdate` coefficients and the remaining rank-one term.
  ext i j
  simp [sub_eq_add_neg]
  ring

/-- The Broyden class can also be written as `bfgsInverseUpdate H s y + (φ - 1) • v vᵀ`. -/
theorem broydenClassInverseUpdate_eq_bfgsInverseUpdate_add
    (H : MatrixN) (hH : Matrix.IsSymm H) (s y : Point) (φ : ℝ) (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y)) :
    broydenClassInverseUpdate H s y φ =
      bfgsInverseUpdate H s y
        + (φ - 1) •
            Matrix.vecMulVec
              (broydenClassDirection H s y)
              (broydenClassDirection H s y) := by
  -- Route correction: expand first through the already normalized `dfp + v vᵀ` form.
  rw [broydenClassInverseUpdate_eq_dfpInverseUpdate_add H hH s y φ hsy hyHy,
    bfgsInverseUpdate_eq_dfpInverseUpdate_add_broydenClassDirection H hH s y hsy hyHy]
  -- The remaining algebra is just regrouping the `v vᵀ` coefficient.
  ext i j
  simp [sub_eq_add_neg]
  ring

/-- Expanding `dfpInverseUpdate` gives the explicit rank-two formula
`H + (sᵀ y)⁻¹ • s sᵀ - (yᵀ H y)⁻¹ • (H y) (H y)ᵀ + φ • v vᵀ`. -/
theorem broydenClassInverseUpdate_eq_explicit
    (H : MatrixN) (hH : Matrix.IsSymm H) (s y : Point) (φ : ℝ) (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y)) :
    broydenClassInverseUpdate H s y φ =
      H
        + (dotProduct s y)⁻¹ • Matrix.vecMulVec s s
        - (dotProduct y (H.mulVec y))⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y)
        + φ • Matrix.vecMulVec
            (broydenClassDirection H s y)
            (broydenClassDirection H s y) := by
  -- Expand the DFP base update and keep the Broyden rank-one correction unchanged.
  rw [broydenClassInverseUpdate_eq_dfpInverseUpdate_add H hH s y φ hsy hyHy, dfpInverseUpdate]

/-- Helper for Chapter05 Definition 5.2-extra-1: the DFP inverse update satisfies the inverse
secant equation whenever its two source denominators are nonzero. -/
theorem dfpInverseUpdate_mulVec
    (H : MatrixN) (s y : Point) (hsy : dotProduct s y ≠ 0)
    (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    (dfpInverseUpdate H s y).mulVec y = s := by
  have hsTerm :
      ((dotProduct s y)⁻¹ • Matrix.vecMulVec s s).mulVec y = s := by
    ext i
    simp [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hsy]
  have hyTerm :
      ((dotProduct y (H.mulVec y))⁻¹ •
          Matrix.vecMulVec (H.mulVec y) (H.mulVec y)).mulVec y =
        H.mulVec y := by
    ext i
    simp [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_comm, hyHy]
  -- Expand the DFP matrix and evaluate each rank-one term on the secant vector `y`.
  calc
    (dfpInverseUpdate H s y).mulVec y
        = H.mulVec y
            + ((dotProduct s y)⁻¹ • Matrix.vecMulVec s s).mulVec y
            - ((dotProduct y (H.mulVec y))⁻¹ •
                Matrix.vecMulVec (H.mulVec y) (H.mulVec y)).mulVec y := by
              simp [dfpInverseUpdate, sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec]
    _ = H.mulVec y + s - H.mulVec y := by
          rw [hsTerm, hyTerm]
    _ = s := by
          abel

/-- The source SR1 specialization parameter from `(5.2.4)`,
`φ = (sᵀ y) / ((s - H y)ᵀ y)`. -/
def broydenClassSR1Parameter (H : MatrixN) (s y : Point) : ℝ :=
  dotProduct s y / dotProduct (s - H.toEuclideanLin y) y

/-- Expanding `broydenClassSR1Parameter` recovers the source quotient
`(sᵀ y) / ((s - H y)ᵀ y)`. -/
theorem broydenClassSR1Parameter_eq (H : MatrixN) (s y : Point) :
    broydenClassSR1Parameter H s y =
      dotProduct s y / dotProduct (s - H.toEuclideanLin y) y := by
  rfl

/-- Helper for Chapter05 Definition 5.2-extra-1: the Broyden direction outer product expands
into the common `s sᵀ`, mixed, and `(H y) (H y)ᵀ` basis used by the rank-two formulas. -/
theorem broydenClassDirection_outer_eq
    (H : MatrixN) (s y : Point) (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y)) :
    Matrix.vecMulVec (broydenClassDirection H s y) (broydenClassDirection H s y) =
      (dotProduct y (H.mulVec y) / (dotProduct s y) ^ (2 : ℕ)) • Matrix.vecMulVec s s
        - (dotProduct s y)⁻¹ •
            (Matrix.vecMulVec (H.mulVec y) s + Matrix.vecMulVec s (H.mulVec y))
        + (dotProduct y (H.mulVec y))⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y) := by
  -- Expand the correction direction and normalize its rank-one outer product entrywise.
  ext i j
  simp [broydenClassDirection, Matrix.vecMulVec_apply, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, sub_eq_add_neg, pow_two]
  field_simp [hsy, hyHy.ne']
  simp [pow_two, Real.sq_sqrt (le_of_lt hyHy)]
  ring_nf

/-- Helper for Chapter05 Definition 5.2-extra-1: the SR1 residual outer product expands into
the same outer-product basis as the Broyden correction term. -/
theorem sr1Residual_outer_eq
    (H : MatrixN) (s y : Point) :
    Matrix.vecMulVec (sr1Residual H y s) (sr1Residual H y s) =
      Matrix.vecMulVec s s
        - (Matrix.vecMulVec (H.mulVec y) s + Matrix.vecMulVec s (H.mulVec y))
        + Matrix.vecMulVec (H.mulVec y) (H.mulVec y) := by
  -- Expand the residual `s - H y` and collect the resulting outer-product terms.
  ext i j
  simp [sr1Residual, Matrix.vecMulVec_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    sub_eq_add_neg]
  ring

/-- The general rank-two ansatz `(5.2.7)` together with the quasi-Newton scalar relations
`1 = a * sᵀ y + b * yᵀ H y`, `0 = 1 + b * sᵀ y + c * yᵀ H y`, and
`b = -φ / (sᵀ y)` yields the Broyden explicit formula `(5.2.4)`. -/
theorem rankTwoUpdate_eq_broydenClassInverseUpdate
    (H : MatrixN) (hH : Matrix.IsSymm H) (s y : Point) (a b c φ : ℝ)
    (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y)) (hb : b = -φ / dotProduct s y)
    (ha : 1 = a * dotProduct s y + b * dotProduct y (H.mulVec y))
    (hc : 0 = 1 + b * dotProduct s y + c * dotProduct y (H.mulVec y)) :
    H
        + a • Matrix.vecMulVec s s
        + b • (Matrix.vecMulVec (H.mulVec y) s + Matrix.vecMulVec s (H.mulVec y))
        + c • Matrix.vecMulVec (H.mulVec y) (H.mulVec y) =
      broydenClassInverseUpdate H s y φ := by
  have ha' :
      a = (dotProduct s y)⁻¹ + φ * dotProduct y (H.mulVec y) / (dotProduct s y) ^ (2 : ℕ) := by
    -- Solve the `s sᵀ` coefficient from the first scalar quasi-Newton relation.
    rw [hb] at ha
    field_simp [hsy] at ha ⊢
    linarith
  have hc' : c = (φ - 1) / dotProduct y (H.mulVec y) := by
    -- Solve the `(H y) (H y)ᵀ` coefficient from the second scalar relation.
    have hcCoef : c * dotProduct y (H.mulVec y) = φ - 1 := by
      rw [hb] at hc
      field_simp [hsy] at hc
      nlinarith
    exact (eq_div_iff hyHy.ne').2 hcCoef
  -- Route correction: first rewrite the Broyden correction into the common outer-product basis.
  rw [broydenClassInverseUpdate_eq_explicit H hH s y φ hsy hyHy,
    broydenClassDirection_outer_eq H s y hsy hyHy, ha', hb, hc']
  -- Once all rank-one terms share the same basis, the statement is a scalar coefficient check.
  ext i j
  simp [Matrix.vecMulVec_apply, sub_eq_add_neg, pow_two]
  field_simp [hsy, hyHy.ne']
  ring_nf

/-- The Broyden correction vector is orthogonal to `y` when the secant denominators are
well-defined. -/
theorem broydenClassDirection_dotProduct_right
    (H : MatrixN) (s y : Point) (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y)) :
    dotProduct (broydenClassDirection H s y) y = 0 := by
  -- Expand the direction formula and cancel the two normalized unit pairings with `y`.
  simp [broydenClassDirection, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_sub,
    dotProduct_smul, dotProduct_comm, hsy, hyHy.ne']

/-- Setting `φ = 0` in the Broyden class recovers the canonical DFP inverse update. -/
theorem broydenClassInverseUpdate_zero (H : MatrixN) (s y : Point) :
    broydenClassInverseUpdate H s y 0 = dfpInverseUpdate H s y := by
  -- Substitute `φ = 0` into the defining convex combination.
  simp [broydenClassInverseUpdate]

/-- Setting `φ = 1` in the Broyden class recovers the canonical BFGS inverse update. -/
theorem broydenClassInverseUpdate_one (H : MatrixN) (s y : Point) :
    broydenClassInverseUpdate H s y 1 = bfgsInverseUpdate H s y := by
  -- Substitute `φ = 1` into the defining convex combination.
  simp [broydenClassInverseUpdate]

/-- Setting `φ = (sᵀ y) / ((s - H y)ᵀ y)` in `(5.2.4)` gives the source SR1
specialization. -/
theorem broydenClassInverseUpdate_eq_sr1Specialization
    (H : MatrixN) (hH : Matrix.IsSymm H) (s y : Point) (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y))
    (hsr1 : dotProduct (s - H.toEuclideanLin y) y ≠ 0) :
    broydenClassInverseUpdate H s y (broydenClassSR1Parameter H s y) = sr1Update H s y := by
  let p := dotProduct s y
  let q := dotProduct y (H.mulVec y)
  let r := dotProduct (s - H.toEuclideanLin y) y
  have hp : p ≠ 0 := by
    simpa [p] using hsy
  have hr : r ≠ 0 := by
    simpa [r] using hsr1
  have hDenom : r = p - q := by
    simp [p, q, r, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_sub, dotProduct_comm]
  have hParam : broydenClassSR1Parameter H s y = p / r := by
    simp [broydenClassSR1Parameter, p, r]
  have hSr1Expand :
      sr1Update H s y =
        H
          + r⁻¹ • Matrix.vecMulVec s s
          + (-r⁻¹) • (Matrix.vecMulVec (H.mulVec y) s + Matrix.vecMulVec s (H.mulVec y))
          + r⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y) := by
    have hResidualDenom : dotProduct (sr1Residual H y s) y = r := by
      simp [sr1Residual, r]
    rw [sr1Update, hResidualDenom, sr1Residual_outer_eq H s y]
    -- Expand the SR1 residual outer product into the common rank-two basis.
    ext i j
    simp [Matrix.vecMulVec_apply, sub_eq_add_neg]
    ring
  have hb : -r⁻¹ = -(p / r) / p := by
    field_simp [hp, hr]
  have ha : 1 = r⁻¹ * p + (-r⁻¹) * q := by
    rw [hDenom]
    have hr' : p - q ≠ 0 := by
      simpa [hDenom] using hr
    have hmul : (p - q) * (p - q)⁻¹ = 1 := mul_inv_cancel₀ hr'
    nlinarith
  have hc : 0 = 1 + (-r⁻¹) * p + r⁻¹ * q := by
    rw [hDenom]
    have hr' : p - q ≠ 0 := by
      simpa [hDenom] using hr
    have hmul : (p - q) * (p - q)⁻¹ = 1 := mul_inv_cancel₀ hr'
    nlinarith
  have hRankTwo :
      H
          + r⁻¹ • Matrix.vecMulVec s s
          + (-r⁻¹) • (Matrix.vecMulVec (H.mulVec y) s + Matrix.vecMulVec s (H.mulVec y))
          + r⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y) =
        broydenClassInverseUpdate H s y (p / r) :=
    rankTwoUpdate_eq_broydenClassInverseUpdate H hH s y r⁻¹ (-r⁻¹) r⁻¹ (p / r) hsy hyHy hb ha hc
  -- Route correction: identify SR1 with the generic rank-two ansatz and then invoke the Broyden
  -- rank-two characterization at the SR1 parameter.
  calc
    broydenClassInverseUpdate H s y (broydenClassSR1Parameter H s y)
        = broydenClassInverseUpdate H s y (p / r) := by
            rw [hParam]
    _ = H
          + r⁻¹ • Matrix.vecMulVec s s
          + (-r⁻¹) • (Matrix.vecMulVec (H.mulVec y) s + Matrix.vecMulVec s (H.mulVec y))
          + r⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y) := by
            simpa using hRankTwo.symm
    _ = sr1Update H s y := by
          simpa using hSr1Expand.symm

/-- Helper for Chapter05 Definition 5.2-extra-1: the two sign branches in the Hoshino
parameter formula `(5.2.6)`. -/
inductive BroydenClassHoshinoBranch where
  | plus
  | minus

namespace BroydenClassHoshinoBranch

/-- Helper for Chapter05 Definition 5.2-extra-1: the real sign `±1` attached to a Hoshino
branch. -/
def toReal : BroydenClassHoshinoBranch → ℝ
  | plus => 1
  | minus => -1

/-- Helper for Chapter05 Definition 5.2-extra-1: the `plus` branch contributes the sign `1`. -/
@[simp] theorem toReal_plus : BroydenClassHoshinoBranch.plus.toReal = (1 : ℝ) := rfl

/-- Helper for Chapter05 Definition 5.2-extra-1: the `minus` branch contributes the sign `-1`. -/
@[simp] theorem toReal_minus : BroydenClassHoshinoBranch.minus.toReal = (-1 : ℝ) := rfl

end BroydenClassHoshinoBranch

/-- The source Hoshino specialization parameter from `(5.2.6)`,
`φ = 1 / (1 ∓ (yᵀ H y / sᵀ y))`, encoded by the two source branches
`BroydenClassHoshinoBranch.plus` and `BroydenClassHoshinoBranch.minus`. -/
def broydenClassHoshinoParameter
    (H : MatrixN) (s y : Point) (σ : BroydenClassHoshinoBranch) : ℝ :=
  (1 - σ.toReal * (dotProduct y (H.mulVec y) / dotProduct s y))⁻¹

/-- Expanding `broydenClassHoshinoParameter` gives the source formula `(5.2.6)` after fixing
one of the two Hoshino sign branches. -/
theorem broydenClassHoshinoParameter_eq
    (H : MatrixN) (s y : Point) (σ : BroydenClassHoshinoBranch) :
    broydenClassHoshinoParameter H s y σ =
      (1 - σ.toReal * (dotProduct y (H.mulVec y) / dotProduct s y))⁻¹ := by
  rfl

/-- Substituting the Hoshino parameter from `(5.2.6)` gives the corresponding source
Broyden-class member for one of the two textbook sign branches. -/
theorem broydenClassInverseUpdate_eq_hoshinoSpecialization
    (H : MatrixN) (hH : Matrix.IsSymm H) (s y : Point) (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y)) (σ : BroydenClassHoshinoBranch) :
    broydenClassInverseUpdate H s y (broydenClassHoshinoParameter H s y σ) =
      H
        + (dotProduct s y)⁻¹ • Matrix.vecMulVec s s
        - (dotProduct y (H.mulVec y))⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y)
        + broydenClassHoshinoParameter H s y σ • Matrix.vecMulVec
            (broydenClassDirection H s y)
            (broydenClassDirection H s y) := by
  -- This is exactly the explicit Broyden formula with the Hoshino parameter substituted in.
  simpa using
    broydenClassInverseUpdate_eq_explicit H hH s y
      (broydenClassHoshinoParameter H s y σ) hsy hyHy

/-- Helper for Chapter05 Definition 5.2-extra-1: the symmetrized outer-product sum
`u vᵀ + v uᵀ` is symmetric. -/
theorem pairOuter_add_swap_isSymm (u v : Point) :
    Matrix.IsSymm (Matrix.vecMulVec u v + Matrix.vecMulVec v u) := by
  -- Swap the two entries across the transpose; the two summands exchange places.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [Matrix.vecMulVec_apply, add_comm, mul_comm]

/-- Helper for Chapter05 Definition 5.2-extra-1: every self-outer-product `u uᵀ` is symmetric. -/
theorem outerSelf_isSymm (u : Point) :
    Matrix.IsSymm (Matrix.vecMulVec u u) := by
  -- The two transposed entries coincide because they are the same scalar product.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- For symmetric `H`, the inverse-Hessian Broyden class update is symmetric for every `φ`. -/
theorem broydenClassInverseUpdate_isSymm
    {H : MatrixN} (hH : Matrix.IsSymm H) (s y : Point) (φ : ℝ) :
    Matrix.IsSymm (broydenClassInverseUpdate H s y φ) := by
  have hDfp : Matrix.IsSymm (dfpInverseUpdate H s y) := by
    -- Expand the DFP base formula; each summand is a symmetric rank-one matrix.
    simpa [dfpInverseUpdate, sub_eq_add_neg, add_assoc] using
      hH.add
        (((outerSelf_isSymm s).smul ((dotProduct s y)⁻¹)).add
          ((outerSelf_isSymm (H.toEuclideanLin y)).smul (-(dotProduct y (H.mulVec y))⁻¹)))
  have hBfgs : Matrix.IsSymm (bfgsInverseUpdate H s y) := by
    let r := s - Matrix.toEuclideanLin H y
    have hCross : Matrix.IsSymm (Matrix.vecMulVec r s + Matrix.vecMulVec s r) :=
      pairOuter_add_swap_isSymm r s
    -- Route correction: use the residual form so the BFGS symmetry reduces to two symmetric
    -- rank-one blocks and one symmetric crossed pair.
    rw [bfgsInverseUpdate_eq_residualForm H s y hH]
    simpa [r, sub_eq_add_neg, add_assoc] using
      hH.add
        ((hCross.smul ((dotProduct s y)⁻¹)).add
          ((outerSelf_isSymm s).smul
            (-(dotProduct r y * (dotProduct s y)⁻¹ * (dotProduct s y)⁻¹)))
          )
  -- The Broyden class is an affine combination of the symmetric DFP and BFGS endpoints.
  simpa [broydenClassInverseUpdate] using
    (hDfp.smul (1 - φ)).add (hBfgs.smul φ)

/-- A nonzero curvature pairing `dotProduct s y` forces the secant vector `y` to be nonzero. -/
theorem right_ne_zero_of_dotProduct_ne_zero {s y : Point} (hsy : dotProduct s y ≠ 0) :
    y ≠ 0 := by
  -- If `y = 0`, then the curvature pairing `sᵀ y` vanishes as well.
  intro hy
  apply hsy
  simp [hy]

/-- A positive-definite matrix has nonvanishing quadratic form on every nonzero vector. -/
theorem posDef_dotProduct_mulVec_ne_zero
    {H : MatrixN} (hH : H.PosDef) {y : Point} (hy : y ≠ 0) :
    dotProduct y (H.mulVec y) ≠ 0 := by
  -- Positive definiteness gives strict positivity of the quadratic form on every nonzero vector.
  have hy' : y.ofLp ≠ 0 := by
    simpa using hy
  exact ne_of_gt <| by
    simpa using hH.dotProduct_mulVec_pos hy'

/-- Helper for Chapter05 Definition 5.2-extra-1: the DFP quadratic form is the completed square
against `H` plus the secant rank-one correction. -/
theorem dfpInverseUpdate_dotProduct_mulVec_eq_completedSquare
    (H : MatrixN) (s y x : Point) (hHsymm : Matrix.IsSymm H) (hsy : dotProduct s y ≠ 0)
    (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    let α := dotProduct x (H.mulVec y) / dotProduct y (H.mulVec y)
    dotProduct x ((dfpInverseUpdate H s y).mulVec x) =
      dotProduct (x - α • y) (H.mulVec (x - α • y))
        + (dotProduct s x)^2 / dotProduct s y := by
  have _ : dotProduct s y ≠ 0 := hsy
  let α := dotProduct x (H.mulVec y) / dotProduct y (H.mulVec y)
  have hxy : dotProduct y (H.mulVec x) = dotProduct x (H.mulVec y) := by
    -- Symmetry lets us move `H` between the two slots of the quadratic form.
    simpa [hHsymm.eq] using Matrix.dotProduct_transpose_mulVec H y x
  have hLhs :
      dotProduct x ((dfpInverseUpdate H s y).mulVec x) =
        dotProduct x (H.mulVec x)
          + (dotProduct s x)^2 / dotProduct s y
          - (dotProduct x (H.mulVec y))^2 / dotProduct y (H.mulVec y) := by
    -- Evaluate the two rank-one DFP corrections on `x`.
    simp [dfpInverseUpdate, sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec,
      Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_comm, div_eq_mul_inv, pow_two,
      mul_comm, mul_assoc]
  have hRhs :
      dotProduct (x - α • y) (H.mulVec (x - α • y)) =
        dotProduct x (H.mulVec x)
          - (dotProduct x (H.mulVec y))^2 / dotProduct y (H.mulVec y) := by
    -- Expand the completed square and identify the two cross terms using symmetry of `H`.
    have hMul :
        H.mulVec (x - α • y) = H.mulVec x - α • H.mulVec y := by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg WithLp.ofLp ((Matrix.toEuclideanLin H).map_sub x (α • y))
    calc
      dotProduct (x - α • y) (H.mulVec (x - α • y))
          = dotProduct (x - α • y) (H.mulVec x - α • H.mulVec y) := by
              rw [hMul]
      _ = dotProduct x (H.mulVec x)
            - α * dotProduct x (H.mulVec y)
            - α * dotProduct y (H.mulVec x)
            + α ^ (2 : ℕ) * dotProduct y (H.mulVec y) := by
            simp [dotProduct_smul, smul_dotProduct, sub_eq_add_neg, pow_two, mul_comm]
            ring_nf
      _ = dotProduct x (H.mulVec x)
            - (dotProduct x (H.mulVec y))^2 / dotProduct y (H.mulVec y) := by
            rw [hxy]
            unfold α
            field_simp [hyHy]
            ring_nf
  -- Both sides are now written in the same quadratic-form normal form.
  calc
    dotProduct x ((dfpInverseUpdate H s y).mulVec x)
        = dotProduct x (H.mulVec x)
            + (dotProduct s x)^2 / dotProduct s y
            - (dotProduct x (H.mulVec y))^2 / dotProduct y (H.mulVec y) := hLhs
    _ = dotProduct (x - α • y) (H.mulVec (x - α • y))
          + (dotProduct s x)^2 / dotProduct s y := by
          rw [hRhs]
          ring_nf

/-- Helper for Chapter05 Definition 5.2-extra-1: positive definiteness of `H` and positive
curvature imply positive definiteness of the DFP inverse update. -/
theorem dfpInverseUpdate_posDef_of_posDef_of_curvature_local
    (H : MatrixN) (hH : H.PosDef) (s y : Point) (hcurv : 0 < dotProduct s y) :
    (dfpInverseUpdate H s y).PosDef := by
  have hsy : dotProduct s y ≠ 0 := ne_of_gt hcurv
  have hy : y ≠ 0 := right_ne_zero_of_dotProduct_ne_zero hsy
  have hyLp : y.ofLp ≠ 0 := by
    simpa using hy
  have hyHy : 0 < dotProduct y (H.mulVec y) := by
    -- Positive definiteness of `H` makes the metric denominator strictly positive on `y`.
    simpa using hH.dotProduct_mulVec_pos hyLp
  have hHsymm : Matrix.IsSymm H := by
    simpa [isHermitian_iff_isSymm] using hH.isHermitian
  have hDfpSymm : Matrix.IsSymm (dfpInverseUpdate H s y) := by
    -- Expand the DFP formula; each summand is a symmetric rank-one matrix.
    simpa [dfpInverseUpdate, sub_eq_add_neg, add_assoc] using
      hHsymm.add
        (((outerSelf_isSymm s).smul ((dotProduct s y)⁻¹)).add
          ((outerSelf_isSymm (H.toEuclideanLin y)).smul (-(dotProduct y (H.mulVec y))⁻¹)))
  have hDfpHerm : (dfpInverseUpdate H s y).IsHermitian := by
    simpa [isHermitian_iff_isSymm] using hDfpSymm
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hDfpHerm ?_
  intro x hx
  let xPt : Point := (EuclideanSpace.equiv (Fin n) ℝ).symm x
  have hxPt : xPt ≠ 0 := by
    simpa [xPt] using hx
  let α := dotProduct xPt (H.mulVec y) / dotProduct y (H.mulVec y)
  have hQuad :
      dotProduct xPt ((dfpInverseUpdate H s y).mulVec xPt) =
        dotProduct (xPt - α • y) (H.mulVec (xPt - α • y))
          + (dotProduct s xPt)^2 / dotProduct s y := by
    simpa [xPt, α] using
      dfpInverseUpdate_dotProduct_mulVec_eq_completedSquare H s y xPt hHsymm hsy hyHy.ne'
  have hCorrNonneg : 0 ≤ (dotProduct s xPt)^2 / dotProduct s y := by
    -- The secant rank-one contribution is nonnegative because `dotProduct s y > 0`.
    simpa [xPt] using div_nonneg (sq_nonneg (dotProduct s xPt)) hcurv.le
  by_cases hz : xPt - α • y = 0
  · have hx_eq : xPt = α • y := sub_eq_zero.mp hz
    have hαne : α ≠ 0 := by
      intro hα
      apply hxPt
      rw [hx_eq, hα]
      simp
    have hsx_ne : dotProduct s xPt ≠ 0 := by
      rw [hx_eq]
      simp [dotProduct_smul, hαne, hsy]
    have hCorrPos : 0 < (dotProduct s xPt)^2 / dotProduct s y := by
      exact div_pos (sq_pos_of_ne_zero hsx_ne) hcurv
    -- When the completed-square term vanishes, the secant correction stays strictly positive.
    have hGoal : 0 < dotProduct xPt ((dfpInverseUpdate H s y).mulVec xPt) := by
      rw [hQuad, hz]
      simpa [xPt] using hCorrPos
    simpa [xPt] using hGoal
  · have hzLp : (xPt - α • y).ofLp ≠ 0 := by
      intro hZero
      apply hz
      exact WithLp.ofLp_injective (p := 2) hZero
    have hBasePos : 0 < dotProduct (xPt - α • y) (H.mulVec (xPt - α • y)) := by
      -- The completed-square base is positive on every nonzero residual vector.
      simpa using hH.dotProduct_mulVec_pos hzLp
    have hGoal : 0 < dotProduct xPt ((dfpInverseUpdate H s y).mulVec xPt) := by
      rw [hQuad]
      exact add_pos_of_pos_of_nonneg hBasePos (by simpa [xPt] using hCorrNonneg)
    -- In the generic case, positivity comes from the completed square plus a nonnegative
    -- secant correction.
    simpa [xPt] using hGoal

/-- If `H` is positive definite, the curvature condition holds, and `φ ∈ [0, 1]`, then the
Broyden convex class update is positive definite. -/
theorem broydenClassInverseUpdate_posDef
    (H : MatrixN) (hH : H.PosDef) (s y : Point) (φ : ℝ)
    (hφ : 0 ≤ φ ∧ φ ≤ 1) (hcurv : 0 < dotProduct s y) :
    (broydenClassInverseUpdate H s y φ).PosDef := by
  have hHsymm : Matrix.IsSymm H := by
    simpa [isHermitian_iff_isSymm] using hH.isHermitian
  have hsy : dotProduct s y ≠ 0 := ne_of_gt hcurv
  have hy : y ≠ 0 := right_ne_zero_of_dotProduct_ne_zero hsy
  have hyLp : y.ofLp ≠ 0 := by
    simpa using hy
  have hyHy : 0 < dotProduct y (H.mulVec y) := by
    -- Positive definiteness of `H` supplies the second Broyden denominator.
    simpa using hH.dotProduct_mulVec_pos hyLp
  have hDfp : (dfpInverseUpdate H s y).PosDef :=
    dfpInverseUpdate_posDef_of_posDef_of_curvature_local H hH s y hcurv
  have hCorrection :
      (φ •
          Matrix.vecMulVec
            (broydenClassDirection H s y).ofLp
            (broydenClassDirection H s y).ofLp).PosSemidef := by
    refine ⟨?_, ?_⟩
    · simpa [isHermitian_iff_isSymm] using
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
        mul_nonneg hφ.1 (sq_nonneg _)
      exact hQuadratic ▸ hQuadNonneg
  -- Rewrite the Broyden update as the DFP base plus a positive semidefinite correction.
  rw [broydenClassInverseUpdate_eq_dfpInverseUpdate_add H hHsymm s y φ hsy hyHy]
  simpa using hDfp.add_posSemidef hCorrection

/-- The Broyden class satisfies the inverse-form quasi-Newton equation
`Hₖ₊₁ y = s` for every `φ` once the secant denominators are nonzero. -/
theorem broydenClassInverseUpdate_mulVec
    (H : MatrixN) (s y : Point) (φ : ℝ)
    (hsy : dotProduct s y ≠ 0) (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    (broydenClassInverseUpdate H s y φ).mulVec y = s := by
  have hDfp : (dfpInverseUpdate H s y).mulVec y = s :=
    dfpInverseUpdate_mulVec H s y hsy hyHy
  have hBfgs : (bfgsInverseUpdate H s y).mulVec y = s := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
      congrArg WithLp.ofLp (bfgsInverseUpdate_mulVec H s y hsy)
  -- Evaluate the affine combination on `y` and use the secant equation for both endpoints.
  calc
    (broydenClassInverseUpdate H s y φ).mulVec y
        = (1 - φ) • (dfpInverseUpdate H s y).mulVec y
            + φ • (bfgsInverseUpdate H s y).mulVec y := by
              simp [broydenClassInverseUpdate, Matrix.add_mulVec, Matrix.smul_mulVec]
    _ = (1 - φ) • s + φ • s := by
          rw [hDfp, hBfgs]
    _ = s := by
          ext i
          simp
          ring

/-- The Hessian-form Broyden correction vector
`w = (sᵀ B s)^(1 / 2) • ((sᵀ y)⁻¹ • y - (sᵀ B s)⁻¹ • B.mulVec s)` from `(5.2.15)`,
used below on the source denominator domain `dotProduct s y ≠ 0` and
`0 < dotProduct s (B.mulVec s)`. -/
def broydenClassHessianDirection (B : MatrixN) (s y : Point) : Point :=
  Real.sqrt (dotProduct s (B.mulVec s)) •
    ((dotProduct s y)⁻¹ • y - (dotProduct s (B.mulVec s))⁻¹ • B.toEuclideanLin s)

/-- Expanding `broydenClassHessianDirection` recovers the source formula `(5.2.15)`. -/
theorem broydenClassHessianDirection_eq (B : MatrixN) (s y : Point) :
    broydenClassHessianDirection B s y =
      Real.sqrt (dotProduct s (B.mulVec s)) •
        ((dotProduct s y)⁻¹ • y - (dotProduct s (B.mulVec s))⁻¹ • B.toEuclideanLin s) := by
  rfl

/-- The outer-product form of the Hessian-form Broyden update
`B + (sᵀ y)⁻¹ • y yᵀ - (sᵀ B s)⁻¹ • (B s) (B s)ᵀ + θ • w wᵀ`.
In the symmetric Hessian setting of `(5.2.14)`, this agrees with the source sandwich term
`B * (s sᵀ) * B`. -/
def broydenClassHessianExplicitUpdate (B : MatrixN) (s y : Point) (θ : ℝ) : MatrixN :=
  B
    + (dotProduct s y)⁻¹ • Matrix.vecMulVec y y
    - (dotProduct s (B.mulVec s))⁻¹ • Matrix.vecMulVec (B.mulVec s) (B.mulVec s)
    + θ •
        Matrix.vecMulVec
          (broydenClassHessianDirection B s y)
          (broydenClassHessianDirection B s y)

/-- The source-facing Hessian-form Broyden class `(5.2.11)` is the weighted combination
`θ • B_{k+1}^{DFP} + (1 - θ) • B_{k+1}^{BFGS}`, realized here by the canonical
Chapter 5 Hessian-side owners `dfpDualHessianUpdate` and `bfgsHessianUpdate`. -/
def broydenClassHessianUpdate (B : MatrixN) (s y : Point) (θ : ℝ) : MatrixN :=
  θ • dfpDualHessianUpdate B s y + (1 - θ) • bfgsHessianUpdate B s y

/-- Helper for Chapter05 Definition 5.2-extra-1: under symmetry of `B`, the canonical BFGS
Hessian update has the outer-product base form from `(5.2.14)`. -/
theorem bfgsHessianUpdate_eq_explicitBase
    (B : MatrixN) (hB : Matrix.IsSymm B) (s y : Point) :
    bfgsHessianUpdate B s y =
      B + (dotProduct s y)⁻¹ • Matrix.vecMulVec y y
        - (dotProduct s (B.mulVec s))⁻¹ • Matrix.vecMulVec (B.mulVec s) (B.mulVec s) := by
  -- Rewrite the symmetric sandwich term as the outer product of `B s` with itself.
  rw [bfgsHessianUpdate, symmetricSandwich_eq_rankOneOfMulVec hB s]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_comm]

/-- Helper for Chapter05 Definition 5.2-extra-1: after swapping `(s, y)` in the inverse-side
rank-one bridge, the dual DFP Hessian update is `bfgsHessianUpdate B s y + w wᵀ`. -/
theorem dfpDualHessianUpdate_eq_bfgsHessianUpdate_add_hessianDirection
    (B : MatrixN) (hB : Matrix.IsSymm B) (s y : Point) (hsy : dotProduct s y ≠ 0)
    (hsBs : 0 < dotProduct s (B.mulVec s)) :
    dfpDualHessianUpdate B s y =
      bfgsHessianUpdate B s y
        + Matrix.vecMulVec
            (broydenClassHessianDirection B s y)
            (broydenClassHessianDirection B s y) := by
  have hSwap :
      bfgsInverseUpdate B y s =
        dfpInverseUpdate B y s
          + Matrix.vecMulVec
              (broydenClassDirection B y s)
              (broydenClassDirection B y s) := by
    simpa [dotProduct_comm] using
      bfgsInverseUpdate_eq_dfpInverseUpdate_add_broydenClassDirection
        B hB y s (by simpa [dotProduct_comm] using hsy) hsBs
  have hBase : dfpInverseUpdate B y s = bfgsHessianUpdate B s y := by
    -- The swapped DFP base is exactly the symmetric BFGS Hessian explicit formula.
    simpa [dfpInverseUpdate, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_comm] using
      (bfgsHessianUpdate_eq_explicitBase B hB s y).symm
  have hDirection :
      broydenClassDirection B y s = broydenClassHessianDirection B s y := by
    -- Swapping the secant data also swaps the correction-direction owner definition.
    simp [broydenClassDirection, broydenClassHessianDirection, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, dotProduct_comm]
  -- Translate the inverse-side bridge term-by-term into the Hessian-side owners.
  calc
    dfpDualHessianUpdate B s y = bfgsInverseUpdate B y s := by
      rw [dfpDualHessianUpdate_eq_bfgsInverseUpdate]
    _ = dfpInverseUpdate B y s
          + Matrix.vecMulVec
              (broydenClassDirection B y s)
              (broydenClassDirection B y s) := hSwap
    _ = bfgsHessianUpdate B s y
          + Matrix.vecMulVec
              (broydenClassHessianDirection B s y)
              (broydenClassHessianDirection B s y) := by
          rw [hBase, hDirection]

/-- Setting `θ = 1` in the Hessian-form Broyden class `(5.2.11)` recovers the
canonical DFP Hessian-side owner `dfpDualHessianUpdate`. -/
theorem broydenClassHessianUpdate_one_eq_dfpDualHessianUpdate
    (B : MatrixN) (s y : Point) :
    broydenClassHessianUpdate B s y 1 = dfpDualHessianUpdate B s y := by
  -- Substitute `θ = 1` into the defining Hessian-form convex combination.
  simp [broydenClassHessianUpdate]

/-- Setting `θ = 0` in the Hessian-form Broyden class `(5.2.11)` recovers the
canonical BFGS Hessian-side owner `bfgsHessianUpdate`. -/
theorem broydenClassHessianUpdate_zero_eq_bfgsHessianUpdate
    (B : MatrixN) (s y : Point) :
    broydenClassHessianUpdate B s y 0 = bfgsHessianUpdate B s y := by
  -- Substitute `θ = 0` into the defining Hessian-form convex combination.
  simp [broydenClassHessianUpdate]

/-- In the symmetric Hessian setting of the source, on the denominator domain
`dotProduct s y ≠ 0` and `0 < dotProduct s (B.mulVec s)`, the source-facing Hessian-form
Broyden class `(5.2.11)` agrees with the outer-product version of the explicit rank-two
formula `(5.2.14)`. -/
theorem broydenClassHessianUpdate_eq_explicitUpdate
    (B : MatrixN) (hB : Matrix.IsSymm B) (s y : Point) (θ : ℝ) (hsy : dotProduct s y ≠ 0)
    (hsBs : 0 < dotProduct s (B.mulVec s)) :
    broydenClassHessianUpdate B s y θ =
      broydenClassHessianExplicitUpdate B s y θ := by
  -- Rewrite the DFP endpoint through the swapped inverse-side rank-one bridge.
  rw [broydenClassHessianUpdate,
    dfpDualHessianUpdate_eq_bfgsHessianUpdate_add_hessianDirection B hB s y hsy hsBs,
    bfgsHessianUpdate_eq_explicitBase B hB s y, broydenClassHessianExplicitUpdate]
  -- The remaining algebra is the same coefficient collection as on the inverse side.
  ext i j
  simp [sub_eq_add_neg]
  ring

/-- The Hessian-form Broyden correction vector is orthogonal to `s` when the secant
denominators are well-defined. -/
theorem broydenClassHessianDirection_dotProduct_left
    (B : MatrixN) (s y : Point) (hsy : dotProduct s y ≠ 0)
    (hsBs : 0 < dotProduct s (B.mulVec s)) :
    dotProduct (broydenClassHessianDirection B s y) s = 0 := by
  -- Expand the Hessian-side direction and cancel the two normalized unit pairings with `s`.
  simp [broydenClassHessianDirection, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    dotProduct_sub, dotProduct_smul, dotProduct_comm, hsy, hsBs.ne']

/-- The Hessian-form Broyden class update satisfies the Hessian-form quasi-Newton equation
`Bₖ₊₁ s = y` for every parameter `θ` once the ordinary secant denominators are nonzero. -/
theorem broydenClassHessianUpdate_mulVec
    (B : MatrixN) (s y : Point) (θ : ℝ) (hsy : dotProduct s y ≠ 0)
    (hsBs : dotProduct s (B.mulVec s) ≠ 0) :
    (broydenClassHessianUpdate B s y θ).mulVec s = y := by
  have hDfp : (dfpDualHessianUpdate B s y).mulVec s = y := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_comm] using
      congrArg WithLp.ofLp
        (dfpDualHessianUpdate_mulVec B s y (by simpa [dotProduct_comm] using hsy))
  have hBfgs : (bfgsHessianUpdate B s y).mulVec s = y := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_comm] using
      congrArg WithLp.ofLp
        (bfgsHessianUpdate_mulVec B s y (by simpa [dotProduct_comm] using hsy) hsBs)
  -- Evaluate the Hessian-form affine combination on `s` and collapse both endpoint secant laws.
  calc
    (broydenClassHessianUpdate B s y θ).mulVec s
        = θ • (dfpDualHessianUpdate B s y).mulVec s
            + (1 - θ) • (bfgsHessianUpdate B s y).mulVec s := by
              simp [broydenClassHessianUpdate, Matrix.add_mulVec, Matrix.smul_mulVec]
    _ = θ • y + (1 - θ) • y := by
          rw [hDfp, hBfgs]
    _ = y := by
          ext i
          simp
          ring

end
