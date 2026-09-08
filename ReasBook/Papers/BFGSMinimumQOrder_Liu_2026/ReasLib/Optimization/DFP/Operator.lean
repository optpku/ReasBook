module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import ReasLib.Analysis.InnerProductSpace.Congruence

public section

/-!
# DFP updates on real Hilbert spaces

This is the coordinate-free inverse-form DFP update.  Matrix formulas are adapters to this
operator API rather than the canonical representation.
-/

noncomputable section

universe u v

open scoped InnerProduct

namespace DFP.Operator

/-- The inverse-form DFP rank-two update of a continuous linear endomorphism. -/
def inverseUpdate {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (H : E →L[ℝ] E) (s y : E) : E →L[ℝ] E :=
  H - (inner ℝ y (H y))⁻¹ •
      InnerProductSpace.rankOne ℝ (H y) ((H†) y) +
    (inner ℝ s y)⁻¹ • InnerProductSpace.rankOne ℝ s s

/-- The search direction determined by an inverse-Hessian operator and a gradient. -/
def direction {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (g : E) : E :=
  -(H g)

/-- Evaluation of the search direction determined by an inverse-Hessian operator. -/
theorem direction_apply {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (g : E) : direction H g = -(H g) := by
  rfl

/-- The displacement obtained by scaling a search direction. -/
def step {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (alpha : ℝ) (H : E →L[ℝ] E) (g : E) : E :=
  alpha • direction H g

/-- Evaluation of a scaled inverse-Hessian search step. -/
theorem step_apply {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (alpha : ℝ) (H : E →L[ℝ] E) (g : E) :
    step alpha H g = alpha • direction H g := by
  rfl

/-- The secant vector between two gradient values. -/
def gradientChange {E : Type u} [AddCommGroup E] (gNext g : E) : E :=
  gNext - g

/-- Evaluation of the secant vector between two gradient values. -/
theorem gradientChange_apply {E : Type u} [AddCommGroup E] (gNext g : E) :
    gradientChange gNext g = gNext - g := by
  rfl

/-- Evaluation of the inverse-form DFP operator update. -/
theorem inverseUpdate_apply {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (H : E →L[ℝ] E) (s y x : E) :
    inverseUpdate H s y x =
      H x - ((inner ℝ y (H y))⁻¹ * inner ℝ ((H†) y) x) • H y +
        ((inner ℝ s y)⁻¹ * inner ℝ s x) • s := by
  simp [inverseUpdate, InnerProductSpace.rankOne_apply, smul_smul]

/-- A linear coordinate change preserves the secant pairing. -/
theorem secantPairing_change
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (s y : F) :
    inner ℝ (L.symm s) ((L.toContinuousLinearMap†) y) = inner ℝ s y := by
  rw [L.toContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_apply,
    L.apply_symm_apply]

/-- Search directions commute with an invertible linear coordinate change. -/
theorem direction_change
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (H : F →L[ℝ] F) (g : F) :
    direction (L.symm.toContinuousLinearMap.pushforward H)
        ((L.toContinuousLinearMap†) g) = L.symm (direction H g) := by
  simp [direction, ContinuousLinearMap.pushforward_apply, ContinuousLinearEquiv.coe_apply]

/-- A scaled search step commutes with pulling back an invertible linear coordinate change. -/
theorem step_change
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (alpha : ℝ) (H : F →L[ℝ] F) (g : F) :
    step alpha (L.symm.toContinuousLinearMap.pushforward H)
        ((L.toContinuousLinearMap†) g) = L.symm (step alpha H g) := by
  simp only [step]
  rw [direction_change, map_smul]

/-- A linear map commutes with the successive-gradient-difference operation. -/
theorem gradientChange_map
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (gNext g : E) :
    gradientChange (L gNext) (L g) = L (gradientChange gNext g) := by
  simp only [gradientChange, map_sub]

/-- The inverse-form DFP update is covariant under an invertible linear coordinate change. -/
theorem inverseUpdate_change
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (H : F →L[ℝ] F) (s y : F) :
    inverseUpdate (L.symm.toContinuousLinearMap.pushforward H) (L.symm s)
        ((L.toContinuousLinearMap†) y) =
      L.symm.toContinuousLinearMap.pushforward (inverseUpdate H s y) := by
  have hden_y :
      inner ℝ ((L.toContinuousLinearMap†) y) (L.symm (H y)) = inner ℝ y (H y) := by
    rw [L.toContinuousLinearMap.adjoint_inner_left]
    simp
  have hden_s :
      inner ℝ (L.symm s) ((L.toContinuousLinearMap†) y) = inner ℝ s y := by
    rw [L.toContinuousLinearMap.adjoint_inner_right]
    simp
  have hcoeff_s (x : E) :
      inner ℝ (L.symm s) x = inner ℝ s ((L.symm.toContinuousLinearMap†) x) := by
    rw [L.symm.toContinuousLinearMap.adjoint_inner_right]
    rfl
  have hcoeff_H (x : E) :
      inner ℝ (((L.symm.toContinuousLinearMap.pushforward H)†)
          ((L.toContinuousLinearMap†) y)) x =
        inner ℝ ((H†) y) ((L.symm.toContinuousLinearMap†) x) := by
    rw [← L.symm.toContinuousLinearMap.pushforward_adjoint]
    rw [ContinuousLinearMap.pushforward_apply]
    rw [ContinuousLinearEquiv.adjoint_symm_apply_adjoint]
    rw [L.symm.toContinuousLinearMap.adjoint_inner_right]
  ext x
  simp [inverseUpdate, ContinuousLinearMap.pushforward_apply,
    InnerProductSpace.rankOne_apply, hden_y, hden_s, hcoeff_s, hcoeff_H]

/-- A factorization `H = L ∘ L†` becomes the identity inverse Hessian after changing
coordinates by `L`. -/
theorem normalize_inverseHessian
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (H : F →L[ℝ] F)
    (factor : H = L.toContinuousLinearMap.pushforward 1) :
    L.symm.toContinuousLinearMap.pushforward H = 1 := by
  rw [factor, ContinuousLinearEquiv.symm_pushforward_pushforward_one]

end DFP.Operator
