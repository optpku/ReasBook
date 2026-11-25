/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed

public section
noncomputable section
open scoped Matrix.Norms.Frobenius
namespace Matrix

namespace Norms.Frobenius

/-- Helper for Proposition 5.20: view a complex matrix in the nested `WithLp` model carrying the
Frobenius inner product. -/
@[expose] def toFrobeniusVecComplex
    {m : Type*} {n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    WithLp 2 (m → WithLp 2 (n → ℂ)) :=
  WithLp.toLp 2 fun i ↦ WithLp.toLp 2 (A i)

/-- Helper for Proposition 5.20: the Frobenius-scoped inner product on complex matrices is the
nested finite-product `L²` inner product. -/
@[expose, instance_reducible] noncomputable def frobeniusInnerComplex
    {m : Type*} {n : Type*} [Fintype m] [Fintype n] : Inner ℂ (Matrix m n ℂ) where
  inner A B := inner ℂ (toFrobeniusVecComplex A) (toFrobeniusVecComplex B)

attribute [scoped instance] frobeniusInnerComplex

/-- Helper for Proposition 5.20: the Frobenius scope on complex matrices carries the corresponding
inner-product-space structure. -/
noncomputable scoped instance frobeniusInnerProductSpaceComplex
    {m : Type*} {n : Type*} [Fintype m] [Fintype n] :
    InnerProductSpace ℂ (Matrix m n ℂ) where
  inner := Matrix.Norms.Frobenius.frobeniusInnerComplex.inner
  norm_sq_eq_re_inner := by
    intro A
    -- Transport the Frobenius norm to the nested `PiLp` model.
    change ‖toFrobeniusVecComplex A‖ ^ 2 =
      RCLike.re (inner ℂ (toFrobeniusVecComplex A) (toFrobeniusVecComplex A))
    simpa using norm_sq_eq_re_inner (𝕜 := ℂ) (toFrobeniusVecComplex A)
  conj_inner_symm := by
    intro A B
    -- Hermitian symmetry is inherited from the ambient `PiLp` inner product.
    change star (inner ℂ (toFrobeniusVecComplex B) (toFrobeniusVecComplex A)) =
      inner ℂ (toFrobeniusVecComplex A) (toFrobeniusVecComplex B)
    exact inner_conj_symm (𝕜 := ℂ) (toFrobeniusVecComplex A) (toFrobeniusVecComplex B)
  add_left := by
    intro A B C
    -- Additivity is computed in the nested finite-product model.
    have hAdd :
        toFrobeniusVecComplex (A + B) =
          toFrobeniusVecComplex A + toFrobeniusVecComplex B := by
      ext i j
      simp [toFrobeniusVecComplex, Matrix.add_apply]
    change inner ℂ (toFrobeniusVecComplex (A + B)) (toFrobeniusVecComplex C) =
      inner ℂ (toFrobeniusVecComplex A) (toFrobeniusVecComplex C) +
        inner ℂ (toFrobeniusVecComplex B) (toFrobeniusVecComplex C)
    rw [hAdd]
    simpa using inner_add_left (𝕜 := ℂ)
      (toFrobeniusVecComplex A) (toFrobeniusVecComplex B) (toFrobeniusVecComplex C)
  smul_left := by
    intro A B a
    -- Scalar compatibility is likewise inherited from the ambient `PiLp` model.
    have hSmul :
        toFrobeniusVecComplex (a • A) = a • toFrobeniusVecComplex A := by
      ext i j
      simp [toFrobeniusVecComplex, Matrix.smul_apply]
    change inner ℂ (toFrobeniusVecComplex (a • A)) (toFrobeniusVecComplex B) =
      star a * inner ℂ (toFrobeniusVecComplex A) (toFrobeniusVecComplex B)
    rw [hSmul]
    simpa using inner_smul_left (𝕜 := ℂ) (toFrobeniusVecComplex A) (toFrobeniusVecComplex B) a

end Norms.Frobenius

end Matrix
