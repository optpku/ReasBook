/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_1.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Algebra.Module.FiniteDimension

public section

open scoped Matrix

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/- Exercise 2.1 (1). Specializing `LinearMap.continuous_of_finiteDimensional`
to `A.toEuclideanLin`, every real matrix induces a bounded linear map on
`EuclideanSpace ℝ n`. -/
#check LinearMap.continuous_of_finiteDimensional

/- Exercise 2.1 (2). For real matrices, self-adjointness of
`A.toEuclideanLin.toContinuousLinearMap` is the canonical composite of
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`,
`Matrix.isSymmetric_toEuclideanLin_iff`, and `Matrix.isHermitian_iff_isSymm`. -/
#check ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
#check Matrix.isSymmetric_toEuclideanLin_iff
#check Matrix.isHermitian_iff_isSymm

/- The Example 2.1 owner `Matrix.lambdaMin` is the Chapter 2 source quantity
`λ_min(A)`. -/
#check Matrix.lambdaMin

namespace Matrix

/-- Exercise 2.1 (3). For a Hermitian real matrix, the source quantity
`λ_min(A)` is attained at a normalized eigenvector of the induced operator.
Over `ℝ`, `Matrix.isHermitian_iff_isSymm` identifies this with the symmetric
case from the source. -/
theorem IsHermitian.exists_normalized_eigenvector_lambdaMin [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ f : EuclideanSpace ℝ n,
      ‖f‖ = 1 ∧
      inner ℝ (A.toEuclideanLin f) f = λ_min(A) ∧
      A.toEuclideanLin f = λ_min(A) • f := by
  obtain ⟨v, hv⟩ := hA.hasEigenvalue_lambdaMin.exists_hasEigenvector
  have hv_ne : v ≠ 0 := hv.2
  have hv_apply : A.toEuclideanLin v = λ_min(A) • v := hv.apply_eq_smul
  let f : EuclideanSpace ℝ n := NormedSpace.normalize v
  have hf_norm : ‖f‖ = 1 := by
    simpa [f] using NormedSpace.norm_normalize hv_ne
  have hf_eig : A.toEuclideanLin f = λ_min(A) • f := by
    calc
      A.toEuclideanLin f = A.toEuclideanLin (NormedSpace.normalize v) := by rfl
      _ = A.toEuclideanLin (‖v‖⁻¹ • v) := by rfl
      _ = ‖v‖⁻¹ • A.toEuclideanLin v := by rw [LinearMap.map_smul]
      _ = ‖v‖⁻¹ • (λ_min(A) • v) := by rw [hv_apply]
      _ = λ_min(A) • f := by
        simp [f, NormedSpace.normalize, smul_smul, mul_comm]
  refine ⟨f, hf_norm, ?_, hf_eig⟩
  calc
    inner ℝ (A.toEuclideanLin f) f = inner ℝ (λ_min(A) • f) f := by rw [hf_eig]
    _ = λ_min(A) * (‖f‖ * ‖f‖) := by rw [real_inner_smul_self_left]
    _ = λ_min(A) := by simp [hf_norm]

end Matrix

/- Exercise 2.1 (3). The normalized-eigenvector statement is exposed as a
companion theorem under the existing `Matrix.lambdaMin` owner layer. -/
#check Matrix.IsHermitian.exists_normalized_eigenvector_lambdaMin

end
