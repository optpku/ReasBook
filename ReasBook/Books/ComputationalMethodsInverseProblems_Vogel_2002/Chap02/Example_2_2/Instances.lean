/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Matrix.Normed

public section

open scoped ComplexConjugate

universe u v

namespace Matrix

/-- The Frobenius-scoped inner product on real matrices, transported from the canonical nested
finite-product `L²` inner product. -/
@[instance_reducible] noncomputable def frobeniusInner
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] : Inner ℝ (Matrix m n ℝ) where
  inner A B := inner ℝ (WithLp.toLp 2 fun i ↦ WithLp.toLp 2 (A i))
    (WithLp.toLp 2 fun i ↦ WithLp.toLp 2 (B i))

/-
Register `Matrix.frobeniusInner` with the Frobenius matrix scope.
-/
namespace Norms.Frobenius

attribute [scoped instance] Matrix.frobeniusInner

/-- The Frobenius-scoped real inner-product-space structure on finite matrices. -/
noncomputable scoped instance frobeniusInnerProductSpace
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] :
    InnerProductSpace ℝ (Matrix m n ℝ) where
  inner := Matrix.frobeniusInner.inner
  norm_sq_eq_re_inner A := by
    -- Transport the Frobenius norm and inner product to the nested `PiLp 2` model.
    change
      ‖WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i))‖ ^ 2 =
        RCLike.re
          (inner ℝ
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i))))
    exact
      InnerProductSpace.norm_sq_eq_re_inner
        (𝕜 := ℝ)
        (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))
  conj_inner_symm A B := by
    -- The transported Frobenius inner product is Hermitian because the `PiLp 2` one is.
    change
      conj
          (inner ℝ
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i)))
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))) =
        inner ℝ
          (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))
          (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i)))
    simpa using
      (inner_conj_symm
        (𝕜 := ℝ)
        (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))
        (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i))))
  add_left A B C := by
    -- Additivity is inherited from the ambient `PiLp 2` inner product.
    have hAdd :
        WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 ((A + B) i)) =
          WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)) +
            WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i)) := by
      ext i j
      simp [Matrix.add_apply]
    change
      inner ℝ
          (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 ((A + B) i)))
          (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (C i))) =
        inner ℝ
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (C i))) +
          inner ℝ
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i)))
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (C i)))
    rw [hAdd]
    simpa using
      (inner_add_left
        (𝕜 := ℝ)
        (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))
        (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i)))
        (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (C i))))
  smul_left A B r := by
    -- Scalar compatibility is likewise inherited from the nested `PiLp 2` model.
    have hSmul :
        WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 ((r • A) i)) =
          r • WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)) := by
      ext i j
      simp [Matrix.smul_apply]
    change
      inner ℝ
          (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 ((r • A) i)))
          (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i))) =
        conj r *
          inner ℝ
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))
            (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i)))
    rw [hSmul]
    simpa using
      (inner_smul_left
        (𝕜 := ℝ)
        (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i)))
        (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (B i)))
        r)

end Norms.Frobenius

end Matrix
