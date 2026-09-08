module

public import Mathlib.Analysis.InnerProductSpace.Positive

public section

/-!
# Congruence of continuous linear endomorphisms

This module provides the two adjoint-congruence operations used by quadratic forms, Hessians,
inverse metrics, and quasi-Newton updates.
-/

noncomputable section

universe u v

open scoped InnerProduct

namespace ContinuousLinearMap

/-- Pull an endomorphism back along a continuous linear map: `L† ∘ A ∘ L`. -/
def pullback {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (A : F →L[ℝ] F) : E →L[ℝ] E :=
  L† ∘L A ∘L L

/-- Push an endomorphism forward along a continuous linear map: `L ∘ A ∘ L†`. -/
def pushforward {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (A : E →L[ℝ] E) : F →L[ℝ] F :=
  L ∘L A ∘L L†

/-- Operator pullback is adjoint congruence. -/
theorem pullback_def {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A : F →L[ℝ] F) :
    L.pullback A = L† ∘L A ∘L L := by
  rfl

/-- Operator pushforward is adjoint congruence. -/
theorem pushforward_def {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A : E →L[ℝ] E) :
    L.pushforward A = L ∘L A ∘L L† := by
  rfl

/-- Evaluation of an operator pullback. -/
@[simp]
theorem pullback_apply {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A : F →L[ℝ] F)
    (x : E) : L.pullback A x = (L†) (A (L x)) := by
  rfl

/-- Evaluation of an operator pushforward. -/
@[simp]
theorem pushforward_apply {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A : E →L[ℝ] E)
    (y : F) : L.pushforward A y = L (A ((L†) y)) := by
  rfl

/-- Pullback preserves zero. -/
@[simp]
theorem pullback_zero {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) :
    L.pullback 0 = 0 := by
  ext x
  simp

/-- Pushforward preserves zero. -/
@[simp]
theorem pushforward_zero {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) :
    L.pushforward 0 = 0 := by
  ext y
  simp

/-- Pullback preserves addition. -/
@[simp]
theorem pullback_add {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A B : F →L[ℝ] F) :
    L.pullback (A + B) = L.pullback A + L.pullback B := by
  ext x
  simp

/-- Pushforward preserves addition. -/
@[simp]
theorem pushforward_add {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A B : E →L[ℝ] E) :
    L.pushforward (A + B) = L.pushforward A + L.pushforward B := by
  ext y
  simp

/-- Pullback preserves subtraction. -/
@[simp]
theorem pullback_sub {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A B : F →L[ℝ] F) :
    L.pullback (A - B) = L.pullback A - L.pullback B := by
  ext x
  simp

/-- Pushforward preserves subtraction. -/
@[simp]
theorem pushforward_sub {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A B : E →L[ℝ] E) :
    L.pushforward (A - B) = L.pushforward A - L.pushforward B := by
  ext y
  simp

/-- Pullback commutes with real scalar multiplication. -/
@[simp]
theorem pullback_smul {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (c : ℝ)
    (A : F →L[ℝ] F) : L.pullback (c • A) = c • L.pullback A := by
  ext x
  simp

/-- Pushforward commutes with real scalar multiplication. -/
@[simp]
theorem pushforward_smul {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (c : ℝ)
    (A : E →L[ℝ] E) : L.pushforward (c • A) = c • L.pushforward A := by
  ext y
  simp

/-- The Riesz dual of an adjoint image is the original Riesz dual composed with the map. -/
theorem toDual_adjoint {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (y : F) :
    (InnerProductSpace.toDual ℝ E) ((L†) y) =
      ((InnerProductSpace.toDual ℝ F) y).comp L := by
  ext x
  simp [InnerProductSpace.toDual_apply_apply, L.adjoint_inner_left]

/-- Pullback preserves adjoints. -/
theorem pullback_adjoint {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A : F →L[ℝ] F) :
    L.pullback (A†) = (L.pullback A)† := by
  simp [pullback, adjoint_comp, comp_assoc]

/-- Pushforward preserves adjoints. -/
theorem pushforward_adjoint {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) (A : E →L[ℝ] E) :
    L.pushforward (A†) = (L.pushforward A)† := by
  simp [pushforward, adjoint_comp, comp_assoc]

/-- Pullback preserves positive operators. -/
theorem IsPositive.pullback {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {A : F →L[ℝ] F} (hA : A.IsPositive)
    (L : E →L[ℝ] F) : (L.pullback A).IsPositive := by
  exact hA.adjoint_conj L

/-- Pushforward preserves positive operators. -/
theorem IsPositive.pushforward {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {A : E →L[ℝ] E} (hA : A.IsPositive)
    (L : E →L[ℝ] F) : (L.pushforward A).IsPositive := by
  exact hA.conj_adjoint L

/-- Pullback is monotone for the Loewner order. -/
theorem pullback_mono {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) {A B : F →L[ℝ] F}
    (h : A ≤ B) : L.pullback A ≤ L.pullback B := by
  rw [le_def] at h ⊢
  simpa [pullback] using h.adjoint_conj L

/-- Pushforward is monotone for the Loewner order. -/
theorem pushforward_mono {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) {A B : E →L[ℝ] E}
    (h : A ≤ B) : L.pushforward A ≤ L.pushforward B := by
  rw [le_def] at h ⊢
  simpa [pushforward] using h.conj_adjoint L

/-- Nonnegative scalar multiplication is monotone for the Loewner order. -/
theorem smul_mono {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {A B : E →L[ℝ] E} {c : ℝ} (h : A ≤ B) (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  rw [le_def] at h ⊢
  simpa [smul_sub] using h.smul_of_nonneg hc

/-- Pulling back the identity gives the Gram operator `L† ∘ L`. -/
theorem pullback_one {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) :
    L.pullback 1 = L† ∘L L := by
  simp [pullback, one_def]

/-- Pushing forward the identity gives the Gram operator `L ∘ L†`. -/
theorem pushforward_one {E : Type u} {F : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) :
    L.pushforward 1 = L ∘L L† := by
  simp [pushforward, one_def]

/-- For a self-adjoint endomorphism, pullback and pushforward of the identity agree. -/
theorem pullback_one_eq_pushforward_one {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (L : E →L[ℝ] E)
    (hL : IsSelfAdjoint L) : L.pullback 1 = L.pushforward 1 := by
  rw [pullback_one, pushforward_one, hL.adjoint_eq]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

/-- Applying the adjoint and then the adjoint of the inverse cancels. -/
@[simp]
theorem adjoint_symm_apply_adjoint
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (y : F) :
    (L.symm.toContinuousLinearMap†) ((L.toContinuousLinearMap†) y) = y := by
  apply ext_inner_right ℝ
  intro z
  rw [L.symm.toContinuousLinearMap.adjoint_inner_left,
    L.toContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearEquiv.coe_apply, L.apply_symm_apply]

/-- Applying the adjoint of the inverse and then the adjoint cancels. -/
@[simp]
theorem adjoint_apply_adjoint_symm
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (x : E) :
    (L.toContinuousLinearMap†) ((L.symm.toContinuousLinearMap†) x) = x := by
  apply ext_inner_right ℝ
  intro z
  rw [L.toContinuousLinearMap.adjoint_inner_left,
    L.symm.toContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearEquiv.coe_apply, L.symm_apply_apply]

/-- An equivalence and its inverse normalize a pushed-forward identity. -/
theorem symm_pushforward_pushforward_one
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) :
    L.symm.toContinuousLinearMap.pushforward (L.toContinuousLinearMap.pushforward 1) = 1 := by
  ext x
  simp only [ContinuousLinearMap.pushforward_apply, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_apply, L.symm_apply_apply]
  apply ext_inner_right ℝ
  intro y
  rw [L.toContinuousLinearMap.adjoint_inner_left,
    L.symm.toContinuousLinearMap.adjoint_inner_left]
  simp

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- A lower Loewner bound on `L ∘ L†` gives the corresponding squared-norm lower bound
for the adjoint. -/
theorem norm_sq_adjoint_lower_bound {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) {a : ℝ} (h : a • (1 : F →L[ℝ] F) ≤ L.pushforward 1)
    (y : F) : a * ‖y‖ ^ 2 ≤ ‖(L†) y‖ ^ 2 := by
  rw [le_def] at h
  have hy := h.inner_nonneg_left y
  rw [sub_apply, inner_sub_left, pushforward_apply] at hy
  simpa [one_def, ← L.adjoint_inner_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq] using hy

/-- A nonnegative lower Loewner bound on `L ∘ L†` gives a norm lower bound for the
adjoint. -/
theorem norm_adjoint_lower_bound {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) {a : ℝ} (ha : 0 ≤ a)
    (h : a • (1 : F →L[ℝ] F) ≤ L.pushforward 1) (y : F) :
    √a * ‖y‖ ≤ ‖(L†) y‖ := by
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg y))
    (norm_nonneg ((L†) y))).mp
  rw [mul_pow, Real.sq_sqrt ha]
  exact L.norm_sq_adjoint_lower_bound h y

end ContinuousLinearMap
