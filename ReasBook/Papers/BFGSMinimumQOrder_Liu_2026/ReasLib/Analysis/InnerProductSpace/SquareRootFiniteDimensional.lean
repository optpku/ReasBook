module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReasLib.Analysis.InnerProductSpace.PositiveLowerBound
public import ReasLib.Analysis.InnerProductSpace.SquareRootFinite

public section

/-!
# Square-root factorizations on finite-dimensional inner-product spaces

This file transports the matrix continuous-functional-calculus square root along a standard
orthonormal basis.  It supplies the coordinate-free finite-dimensional case without assuming
that real continuous endomorphisms carry a global C-star-algebra instance.
-/

noncomputable section

universe u

open scoped InnerProduct MatrixOrder
open Module

namespace ContinuousLinearMap

/-- A uniformly positive self-adjoint operator on a finite-dimensional real inner-product
space admits an invertible self-adjoint square-root factor. -/
theorem exists_sqrtEquiv_of_lowerBound_of_finiteDimensional
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : E →L[ℝ] E} {m : ℝ} (_selfAdjoint : IsSelfAdjoint H) (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ∃ L : E ≃L[ℝ] E,
      IsSelfAdjoint L.toContinuousLinearMap ∧
        H = L.toContinuousLinearMap.pushforward 1 := by
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    (stdOrthonormalBasis ℝ E).repr
  let U : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    e.toContinuousLinearEquiv
  have hUadj : U.toContinuousLinearMap† = U.symm.toContinuousLinearMap := by
    dsimp only [U]
    exact e.adjoint_eq_symm
  have hUone : U.toContinuousLinearMap.pushforward 1 = 1 := by
    ext x
    simp [ContinuousLinearMap.pushforward_apply, hUadj]
  let H' : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ]
      EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    U.toContinuousLinearMap.pushforward H
  have hH'lower : m • (1 : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ]
      EuclideanSpace ℝ (Fin (finrank ℝ E))) ≤ H' := by
    rw [← hUone, ← ContinuousLinearMap.pushforward_smul]
    exact ContinuousLinearMap.pushforward_mono U.toContinuousLinearMap lower
  have hH'pos : H'.IsPositive :=
    ContinuousLinearMap.isPositive_of_loewner_lowerBound hm.le hH'lower
  have hH'unit : IsUnit H' :=
    ContinuousLinearMap.isUnit_of_loewner_lowerBound hm hH'lower
  let A : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ :=
    (Matrix.toEuclideanCLM (n := Fin (finrank ℝ E)) (𝕜 := ℝ)).symm H'
  have hmapA :
      (Matrix.toEuclideanCLM (n := Fin (finrank ℝ E)) (𝕜 := ℝ)) A = H' := by
    exact (Matrix.toEuclideanCLM (n := Fin (finrank ℝ E)) (𝕜 := ℝ)).apply_symm_apply H'
  have hApos : A.PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanLin_iff]
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rw [hmapA]
    exact hH'pos.toLinearMap
  have hAunit : IsUnit A := by
    rw [← isUnit_map_iff
      (Matrix.toEuclideanCLM (n := Fin (finrank ℝ E)) (𝕜 := ℝ))]
    rw [hmapA]
    exact hH'unit
  have hA : A.PosDef := hApos.posDef_iff_isUnit.mpr hAunit
  let S : EuclideanSpace ℝ (Fin (finrank ℝ E)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (finrank ℝ E)) := hA.sqrtEquiv
  have hSadj : IsSelfAdjoint S.toContinuousLinearMap := by
    exact hA.sqrtEquiv_isSelfAdjoint
  have hH'S : H' = S.toContinuousLinearMap.pushforward 1 := by
    rw [← hmapA]
    exact hA.sqrtEquiv_pushforward_one
  let L : E ≃L[ℝ] E := (U.trans S).trans U.symm
  have hLapply (x : E) : L x = U.symm (S (U x)) := by
    rfl
  have hLadj : IsSelfAdjoint L.toContinuousLinearMap := by
    have hpull : IsSelfAdjoint
        (U.toContinuousLinearMap† ∘L S.toContinuousLinearMap ∘L
          U.toContinuousLinearMap) :=
      hSadj.adjoint_conj U.toContinuousLinearMap
    have hLmap : L.toContinuousLinearMap =
        U.toContinuousLinearMap† ∘L S.toContinuousLinearMap ∘L
          U.toContinuousLinearMap := by
      ext x
      simp [L, hUadj]
    rw [hLmap]
    exact hpull
  refine ⟨L, hLadj, ?_⟩
  ext x
  rw [ContinuousLinearMap.pushforward_one, hLadj.adjoint_eq]
  change H x = L (L x)
  simp only [hLapply]
  rw [U.apply_symm_apply]
  have hSsq : S (S (U x)) = H' (U x) := by
    have hx := congrArg
      (fun T : EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ]
          EuclideanSpace ℝ (Fin (finrank ℝ E)) ↦ T (U x)) hH'S
    simpa [ContinuousLinearMap.pushforward_apply, hSadj.adjoint_eq] using hx.symm
  rw [hSsq]
  simp [H', ContinuousLinearMap.pushforward_apply, hUadj]

/-- The inverse square-root coordinates normalize a uniformly positive operator to the
identity. -/
theorem exists_sqrtEquiv_normalizing_of_lowerBound_of_finiteDimensional
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : E →L[ℝ] E} {m : ℝ} (selfAdjoint : IsSelfAdjoint H) (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ∃ L : E ≃L[ℝ] E,
      IsSelfAdjoint L.toContinuousLinearMap ∧
        H = L.toContinuousLinearMap.pushforward 1 ∧
          L.symm.toContinuousLinearMap.pushforward H = 1 := by
  obtain ⟨L, hL, hH⟩ :=
    exists_sqrtEquiv_of_lowerBound_of_finiteDimensional selfAdjoint hm lower
  refine ⟨L, hL, hH, ?_⟩
  rw [hH]
  exact ContinuousLinearEquiv.symm_pushforward_pushforward_one L

end ContinuousLinearMap
