module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Positive
public import ReasLib.Analysis.InnerProductSpace.Congruence

public section

/-!
# Positive matrix operators

This module exposes the continuous-linear-map bridge for real matrix positive semidefiniteness.
The bridge keeps coordinate-free operator statements separate from matrix specializations while
reusing the canonical Euclidean realization supplied by Mathlib.
-/

noncomputable section

universe u

namespace Matrix

/-- A real matrix is positive semidefinite exactly when its Euclidean operator is positive. -/
@[simp]
theorem isPositive_toEuclideanCLM_iff {n : Type u} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} :
    ((Matrix.toEuclideanCLM :
      Matrix n n ℝ ≃⋆ₐ[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) A).IsPositive ↔
      A.PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff,
    ← ContinuousLinearMap.isPositive_toLinearMap_iff,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]

/-- Positive definiteness is preserved by an isometric change of Euclidean
coordinates. The resulting matrix represents the transported operator in the
target's canonical basis. -/
theorem PosDef.congr_linearIsometryEquiv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    ((Matrix.toEuclideanCLM : Matrix κ κ ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ).symm
        (Q.toContinuousLinearEquiv.symm.toContinuousLinearMap.pushforward
          ((Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) A))).PosDef := by
  let Aop : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) A
  let Bop : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ :=
    Q.toContinuousLinearEquiv.symm.toContinuousLinearMap.pushforward Aop
  let B : Matrix κ κ ℝ :=
    (Matrix.toEuclideanCLM : Matrix κ κ ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ).symm Bop
  have hAopSelf : IsSelfAdjoint Aop := by
    dsimp only [Aop]
    exact hA.isHermitian.isSelfAdjoint.map Matrix.toEuclideanCLM
  have hBopSelf : IsSelfAdjoint Bop := by
    dsimp only [Bop]
    rw [ContinuousLinearMap.isSelfAdjoint_iff',
      ← ContinuousLinearMap.pushforward_adjoint,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hAopSelf]
  have hBhermitian : B.IsHermitian := by
    rw [← Matrix.isSymmetric_toEuclideanLin_iff]
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    have hself : IsSelfAdjoint
        ((Matrix.toEuclideanCLM : Matrix κ κ ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) B) := by
      simpa only [B, StarAlgEquiv.apply_symm_apply] using hBopSelf
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hBhermitian
  intro v hv
  let z : EuclideanSpace ℝ κ := WithLp.toLp 2 v
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    apply WithLp.toLp_injective 2
    simpa only [z, WithLp.toLp_zero] using hz0
  have hQz : Q z ≠ 0 := by
    simpa only [map_zero] using Q.injective.ne hz
  have hQv : WithLp.ofLp (Q z) ≠ 0 := by
    intro hzero
    apply hQz
    apply WithLp.ofLp_injective 2
    simpa only [WithLp.ofLp_zero] using hzero
  have hpositive := hA.dotProduct_mulVec_pos hQv
  have hoperatorPositive : 0 < inner ℝ (Q z) (Aop (Q z)) := by
    simpa only [Aop, Matrix.inner_toEuclideanCLM, star_trivial] using hpositive
  have hBop :
      (Matrix.toEuclideanCLM : Matrix κ κ ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) B = Bop := by
    simp only [B, StarAlgEquiv.apply_symm_apply]
  have hQsymm : Q.toContinuousLinearEquiv.symm.toContinuousLinearMap =
      (Q.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) := by
    ext x
    rfl
  simp only [star_trivial]
  change 0 < WithLp.ofLp z ⬝ᵥ B *ᵥ WithLp.ofLp z
  rw [← Matrix.inner_toEuclideanCLM B z z, hBop]
  simp only [Bop, ContinuousLinearMap.pushforward_apply]
  rw [hQsymm, Q.symm.adjoint_eq_symm]
  simp only [LinearIsometryEquiv.symm_symm]
  change 0 < inner ℝ z (Q.symm (Aop (Q z)))
  calc
    inner ℝ z (Q.symm (Aop (Q z))) =
        inner ℝ (Q.symm (Q z)) (Q.symm (Aop (Q z))) := by rw [Q.symm_apply_apply]
    _ = inner ℝ (Q z) (Aop (Q z)) := Q.symm.inner_map_map _ _
    _ > 0 := hoperatorPositive

end Matrix
