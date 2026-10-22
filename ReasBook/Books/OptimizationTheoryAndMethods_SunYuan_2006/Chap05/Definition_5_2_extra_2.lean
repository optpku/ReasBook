/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Symmetric

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this item:
-- * primary domain: Huang rank-two inverse-Hessian updates on the Chapter 5 Euclidean matrix
--   model;
-- * sampled canonical declarations in this domain:
--   `satisfiesQuasiNewtonEquation`,
--   `satisfiesQuasiNewtonEquation_toEuclideanLin_iff`,
--   `broydenClassInverseUpdate`,
--   `Matrix.toEuclideanLin`;
-- * best owner abstraction in the minimal closure: the Chapter 5 Euclidean point model together
--   with the operator-valued secant owner from `Definition_5_1_extra_1`;
-- * source/core/bridge triage for this file:
--   source-facing: `huangUpdateU`, `huangUpdateV`, `huangUpdate`, `IsHuangUpdate`;
--   core/canonical: `satisfiesQuasiNewtonEquation`;
--   bridge/view: the concrete matrix-model secant theorem
--   `satisfiesQuasiNewtonEquation_toEuclideanLin_smul_iff`;
-- * primitive data: the Huang auxiliary vectors, the raw Huang rank-two matrix formula, and the
--   source predicate `IsHuangUpdate`;
-- * derived API: the secant theorem and the symmetric specialization.
-- The public surface therefore stays on the chapter's canonical Euclidean owner and uses the
-- matrix/Euclidean conversion only as a thin bridge.

/-- Helper for Chapter05 Definition 5.2-extra-2: on the Chapter 5 Euclidean matrix model, the
generalized quasi-Newton equation with parameter `ρ` is the canonical secant owner applied to
the scaled target `ρ • s`. -/
theorem satisfiesQuasiNewtonEquation_toEuclideanLin_smul_iff
    (Hnext : MatrixN) (y s : Point) (ρ : ℝ) :
    satisfiesQuasiNewtonEquation Hnext.toEuclideanLin y (ρ • s) ↔
      Hnext.mulVec y = ρ • s := by
  simpa using
    (satisfiesQuasiNewtonEquation_toEuclideanLin_iff :
      satisfiesQuasiNewtonEquation Hnext.toEuclideanLin y (ρ • s) ↔
        Hnext.mulVec y.ofLp = (ρ • s).ofLp)

/-- The matrix-vector product `H.mulVec x.ofLp` viewed again as a point of `Point`. -/
private def matrixMulVecPoint (H : MatrixN) (x : Point) : Point :=
  WithLp.toLp 2 (H.mulVec x.ofLp)

/-- The Huang auxiliary vector `u = a11 • s + a12 • Hᵀ y`. -/
def huangUpdateU (a11 a12 : ℝ) (H : MatrixN) (s y : Point) : Point :=
  a11 • s + a12 • matrixMulVecPoint H.transpose y

/-- The defining formula for `huangUpdateU`. -/
theorem huangUpdateU_eq (a11 a12 : ℝ) (H : MatrixN) (s y : Point) :
    huangUpdateU a11 a12 H s y = a11 • s + a12 • H.transpose.toEuclideanLin y := by
  rfl

/-- The Huang auxiliary vector `v = a21 • s + a22 • Hᵀ y`. -/
def huangUpdateV (a21 a22 : ℝ) (H : MatrixN) (s y : Point) : Point :=
  a21 • s + a22 • matrixMulVecPoint H.transpose y

/-- The defining formula for `huangUpdateV`. -/
theorem huangUpdateV_eq (a21 a22 : ℝ) (H : MatrixN) (s y : Point) :
    huangUpdateV a21 a22 H s y = a21 • s + a22 • H.transpose.toEuclideanLin y := by
  rfl

/-- The raw Huang rank-two update formula attached to `H`, `s`, `y`, and coefficients
`a11`, `a12`, `a21`, `a22`. -/
def huangUpdate
    (H : MatrixN) (s y : Point) (a11 a12 a21 a22 : ℝ) : MatrixN :=
  H + Matrix.vecMulVec s (huangUpdateU a11 a12 H s y) +
    Matrix.vecMulVec (matrixMulVecPoint H y) (huangUpdateV a21 a22 H s y)

/-- The defining formula for `huangUpdate`. -/
theorem huangUpdate_eq
    (H : MatrixN) (s y : Point) (a11 a12 a21 a22 : ℝ) :
    huangUpdate H s y a11 a12 a21 a22 =
      H + Matrix.vecMulVec s (huangUpdateU a11 a12 H s y) +
        Matrix.vecMulVec (H.toEuclideanLin y) (huangUpdateV a21 a22 H s y) := by
  rfl

/-- Helper for Chapter05 Definition 5.2-extra-2: `IsHuangUpdate H Hnext s y ρ` means that
`Hnext` is a Huang-class update of `H` along `s` and `y` with parameter `ρ`, so there are
coefficients
`a11`, `a12`, `a21`, `a22` for which the raw Huang formula holds together with
`uᵀ y = ρ` and `vᵀ y = -1`. -/
def IsHuangUpdate
    (H Hnext : MatrixN) (s y : Point) (ρ : ℝ) : Prop :=
  ∃ a11 a12 a21 a22,
    Hnext = huangUpdate H s y a11 a12 a21 a22 ∧
      dotProduct (huangUpdateU a11 a12 H s y) y = ρ ∧
      dotProduct (huangUpdateV a21 a22 H s y) y = -1

/-- The Huang-update property is proposition-valued, so its witnesses are subsingletons. -/
instance isHuangUpdate_subsingleton
    (H Hnext : MatrixN) (s y : Point) (ρ : ℝ) :
    Subsingleton (IsHuangUpdate H Hnext s y ρ) := inferInstance

/-- Expanding `IsHuangUpdate` gives the Huang rank-two formula together with the source side
conditions on the auxiliary vectors. -/
theorem isHuangUpdate_iff
    (H Hnext : MatrixN) (s y : Point) (ρ : ℝ) :
    IsHuangUpdate H Hnext s y ρ ↔
      ∃ a11 a12 a21 a22,
        Hnext = huangUpdate H s y a11 a12 a21 a22 ∧
          dotProduct (huangUpdateU a11 a12 H s y) y = ρ ∧
          dotProduct (huangUpdateV a21 a22 H s y) y = -1 := Iff.rfl

/-- The raw Huang rank-two formula together with `uᵀ y = ρ` and `vᵀ y = -1` yields a Huang
update in the source sense. -/
theorem isHuangUpdate_huangUpdate
    (H : MatrixN) (s y : Point) (a11 a12 a21 a22 ρ : ℝ)
    (hu : dotProduct (huangUpdateU a11 a12 H s y) y = ρ)
    (hv : dotProduct (huangUpdateV a21 a22 H s y) y = -1) :
    IsHuangUpdate H (huangUpdate H s y a11 a12 a21 a22) s y ρ :=
  ⟨a11, a12, a21, a22, rfl, hu, hv⟩

/-- Helper for Chapter05 Definition 5.2-extra-2: expanding the Huang rank-two update on the
secant vector `y` isolates the two scalar correction factors carried by the auxiliary vectors. -/
theorem huangUpdate_mulVec_expand
    (H : MatrixN) (s y : Point) (a11 a12 a21 a22 : ℝ) :
    (huangUpdate H s y a11 a12 a21 a22).mulVec y =
      H.mulVec y +
        dotProduct (huangUpdateU a11 a12 H s y) y • s +
        dotProduct (huangUpdateV a21 a22 H s y) y • H.mulVec y := by
  -- Expand the rank-two update and evaluate each rank-one term on the secant vector `y`.
  simp [huangUpdate, matrixMulVecPoint, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, add_assoc]

/-- The raw Huang update satisfies the Chapter 5 secant owner with scaled target `ρ • s` once the
source side conditions `uᵀ y = ρ` and `vᵀ y = -1` are imposed on the auxiliary vectors. -/
theorem huangUpdate_satisfiesQuasiNewtonEquation
    (H : MatrixN) (s y : Point) (a11 a12 a21 a22 ρ : ℝ)
    (hu : dotProduct (huangUpdateU a11 a12 H s y) y = ρ)
    (hv : dotProduct (huangUpdateV a21 a22 H s y) y = -1) :
    satisfiesQuasiNewtonEquation
      (huangUpdate H s y a11 a12 a21 a22).toEuclideanLin y (ρ • s) := by
  -- Bridge the operator-valued statement to the concrete matrix action on `y`.
  rw [satisfiesQuasiNewtonEquation_toEuclideanLin_smul_iff]
  -- After expansion, the side conditions rewrite the two scalar corrections to `ρ` and `-1`.
  simp [huangUpdate_mulVec_expand, hu, hv, add_assoc]

/-- The raw Huang update satisfies the concrete matrix secant equation `Hnext.mulVec y = ρ • s`
on the Chapter 5 point model. -/
theorem huangUpdate_mulVec
    (H : MatrixN) (s y : Point) (a11 a12 a21 a22 ρ : ℝ)
    (hu : dotProduct (huangUpdateU a11 a12 H s y) y = ρ)
    (hv : dotProduct (huangUpdateV a21 a22 H s y) y = -1) :
    (huangUpdate H s y a11 a12 a21 a22).mulVec y = ρ • s := by
  rw [← satisfiesQuasiNewtonEquation_toEuclideanLin_smul_iff]
  exact huangUpdate_satisfiesQuasiNewtonEquation H s y a11 a12 a21 a22 ρ hu hv

/-- Chapter05 Definition 5.2-extra-2: every Huang update satisfies the Chapter 5 secant owner
with scaled target `ρ • s`, hence `Hnext.mulVec y = ρ • s` on the concrete matrix model. -/
theorem IsHuangUpdate.satisfiesQuasiNewtonEquation
    {H Hnext : MatrixN} {s y : Point} {ρ : ℝ}
    (hHuang : IsHuangUpdate H Hnext s y ρ) :
    satisfiesQuasiNewtonEquation Hnext.toEuclideanLin y (ρ • s) := by
  -- Unpack the Huang witnesses so the goal matches the raw update theorem directly.
  rcases hHuang with ⟨a11, a12, a21, a22, rfl, hu, hv⟩
  exact huangUpdate_satisfiesQuasiNewtonEquation H s y a11 a12 a21 a22 ρ hu hv

/-- Every Huang update satisfies the concrete matrix secant equation `Hnext.mulVec y = ρ • s`
without exposing the underlying `ofLp` representation. -/
theorem IsHuangUpdate.mulVec
    {H Hnext : MatrixN} {s y : Point} {ρ : ℝ}
    (hHuang : IsHuangUpdate H Hnext s y ρ) :
    Hnext.mulVec y = ρ • s := by
  rw [← satisfiesQuasiNewtonEquation_toEuclideanLin_smul_iff]
  exact hHuang.satisfiesQuasiNewtonEquation

/-- If `H` is symmetric, the Huang update can be written with `H.mulVec y` in both auxiliary
vectors, matching the symmetric specialization discussed in the source. -/
theorem huangUpdate_eq_of_isSymm
    {H : MatrixN} (hH : Matrix.IsSymm H) (s y : Point) (a11 a12 a21 a22 : ℝ) :
    huangUpdate H s y a11 a12 a21 a22 =
      H + Matrix.vecMulVec s (a11 • s + a12 • H.toEuclideanLin y) +
        Matrix.vecMulVec (H.toEuclideanLin y) (a21 • s + a22 • H.toEuclideanLin y) := by
  simp [huangUpdate, huangUpdateU, huangUpdateV, matrixMulVecPoint, hH.eq]
