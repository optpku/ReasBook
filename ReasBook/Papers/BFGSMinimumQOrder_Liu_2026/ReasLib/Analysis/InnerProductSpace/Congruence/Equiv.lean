module

public import ReasLib.Analysis.InnerProductSpace.Congruence

public section

/-!
# Congruence cancellation along equivalences

The generic congruence operations cancel on either side of a continuous linear equivalence.
These identities are useful for coordinate normalization and avoid repeating adjoint plumbing in
matrix and quasi-Newton specializations.
-/

noncomputable section

universe u v

namespace ContinuousLinearEquiv

/-- Pushing an endomorphism forward and then back along an equivalence returns the original
endomorphism. -/
theorem symm_pushforward_pushforward
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (A : E →L[ℝ] E) :
    L.symm.toContinuousLinearMap.pushforward (L.toContinuousLinearMap.pushforward A) = A := by
  ext x
  simp only [ContinuousLinearMap.pushforward_apply, ContinuousLinearEquiv.coe_apply,
    L.symm_apply_apply, adjoint_apply_adjoint_symm]

/-- Pushing an endomorphism back and then forward along an equivalence returns the original
endomorphism. -/
theorem pushforward_symm_pushforward
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (B : F →L[ℝ] F) :
    L.toContinuousLinearMap.pushforward (L.symm.toContinuousLinearMap.pushforward B) = B := by
  ext y
  simp only [ContinuousLinearMap.pushforward_apply, ContinuousLinearEquiv.coe_apply,
    L.apply_symm_apply, adjoint_symm_apply_adjoint]

/-- Pulling an endomorphism back and then forward along an equivalence returns the original
endomorphism. -/
theorem symm_pullback_pullback
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (B : F →L[ℝ] F) :
    L.symm.toContinuousLinearMap.pullback (L.toContinuousLinearMap.pullback B) = B := by
  ext y
  simp only [ContinuousLinearMap.pullback_apply, ContinuousLinearEquiv.coe_apply,
    L.apply_symm_apply, adjoint_symm_apply_adjoint]

/-- Pulling an endomorphism forward and then back along an equivalence returns the original
endomorphism. -/
theorem pullback_symm_pullback
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (A : E →L[ℝ] E) :
    L.toContinuousLinearMap.pullback (L.symm.toContinuousLinearMap.pullback A) = A := by
  ext x
  simp only [ContinuousLinearMap.pullback_apply, ContinuousLinearEquiv.coe_apply,
    L.symm_apply_apply, adjoint_apply_adjoint_symm]

end ContinuousLinearEquiv
