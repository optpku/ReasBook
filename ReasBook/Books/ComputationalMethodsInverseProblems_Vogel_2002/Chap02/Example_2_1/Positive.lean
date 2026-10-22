/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_1.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix

public section

noncomputable section

namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The continuous linear endomorphism of `EuclideanSpace ℝ n` induced by a real
matrix. This is the real specialization of `Matrix.toEuclideanCLM` with an
ordinary matrix argument, so it can appear in public theorem headers without
named-argument forwarding. -/
abbrev toEuclideanCLMReal (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  (toEuclideanCLM :
    Matrix n n ℝ ≃⋆ₐ[ℝ] (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)) A

@[simp] theorem toEuclideanCLMReal_toLinearMap (A : Matrix n n ℝ) :
    A.toEuclideanCLMReal.toLinearMap = A.toEuclideanLin :=
  coe_toEuclideanCLM_eq_toEuclideanLin (𝕜 := ℝ) A

/-- Example 2.1 (9): a positive-definite real matrix induces a self-adjoint
strongly positive operator on `EuclideanSpace ℝ n`. -/
theorem selfAdjointStronglyPositive_toEuclideanCLM
    (A : Matrix n n ℝ) (hA : A.PosDef) :
    ContinuousLinearMap.SelfAdjointStronglyPositive
      A.toEuclideanCLMReal := by
  refine ContinuousLinearMap.SelfAdjointStronglyPositive.ofSelfAdjoint_isStronglyPositive ?_ ?_
  · -- Route correction: package self-adjointness through the matrix-to-operator bridge once.
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr <| by
      simpa [Matrix.toEuclideanCLMReal_toLinearMap] using
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian)
  · -- Use the spectral lower bound with witness `c0 = λ_min(A)`.
    rw [ContinuousLinearMap.isStronglyPositive_iff]
    by_cases hn : Nonempty n
    · letI := hn
      refine ⟨Matrix.lambdaMin A, Matrix.lambdaMin_pos_of_posDef A hA, ?_⟩
      intro f
      have hbound :
          Matrix.lambdaMin A * ‖f‖ ^ 2 ≤ inner ℝ (A.toEuclideanCLMReal.toLinearMap f) f := by
        rw [Matrix.toEuclideanCLMReal_toLinearMap]
        exact Matrix.lambdaMin_mul_normSq_le_inner_toEuclideanLin A hA f
      change Matrix.lambdaMin A * ‖f‖ ^ 2 ≤ inner ℝ (A.toEuclideanCLMReal.toLinearMap f) f
      exact hbound
    · refine ⟨1, zero_lt_one, ?_⟩
      intro f
      -- Local instance justification (empty index branch): the branch
      -- assumption gives the temporary `IsEmpty n` instance needed to
      -- collapse `EuclideanSpace ℝ n` to a subsingleton.
      letI : IsEmpty n := not_nonempty_iff.mp hn
      have hf : f = 0 := Subsingleton.elim _ _
      simp [hf]

/-- Example 2.1 (9): for real matrices, positive definiteness is equivalent to
the induced continuous operator being self-adjoint and strongly positive. -/
theorem posDef_iff_selfAdjointStronglyPositive_toEuclideanCLM
    (A : Matrix n n ℝ) :
    A.PosDef ↔ ContinuousLinearMap.SelfAdjointStronglyPositive
      A.toEuclideanCLMReal := by
  constructor
  · -- The forward implication is the packaged coercivity theorem above.
    exact Matrix.selfAdjointStronglyPositive_toEuclideanCLM A
  · intro hL
    have hsymm : A.toEuclideanCLMReal.IsSymmetric :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hL.isSelfAdjoint
    have hHermitian : A.IsHermitian := by
      -- Translate operator symmetry back to the matrix Hermitian condition.
      apply Matrix.isSymmetric_toEuclideanLin_iff.mp
      simpa [Matrix.toEuclideanCLMReal_toLinearMap] using hsymm
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hHermitian ?_
    intro x hx
    have hxLp : (WithLp.toLp 2 x : EuclideanSpace ℝ n) ≠ 0 := by
      simpa using hx
    have hinner :
        0 < inner ℝ (A.toEuclideanCLMReal (WithLp.toLp 2 x)) (WithLp.toLp 2 x) :=
      hL.inner_pos hxLp
    -- Rewrite the operator quadratic form back to the matrix dot-product criterion.
    simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanCLMReal_toLinearMap,
      Matrix.toLpLin_toLp] using
      hinner

end Matrix
