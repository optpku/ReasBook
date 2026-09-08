module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import ReasLib.Analysis.Calculus.Gradient.CoordinateChange
public import ReasLib.Optimization.DFP.Operator

public section

/-!
# Coordinate-free DFP orbits
-/

noncomputable section

universe u v

open scoped InnerProduct

namespace DFP.Operator

/-- Search directions along an operator-valued DFP sequence. -/
def directions {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : ℕ → E →L[ℝ] E) (g : ℕ → E) (k : ℕ) : E :=
  direction (H k) (g k)

/-- Evaluation of the operator-valued search direction at an iteration index. -/
theorem directions_apply {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : ℕ → E →L[ℝ] E) (g : ℕ → E) (k : ℕ) :
    directions H g k = direction (H k) (g k) := by
  rfl

/-- Scaled displacements along an operator-valued DFP sequence. -/
def steps {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (alpha : ℕ → ℝ) (H : ℕ → E →L[ℝ] E) (g : ℕ → E) (k : ℕ) : E :=
  step (alpha k) (H k) (g k)

/-- Evaluation of the operator-valued scaled displacement at an iteration index. -/
theorem steps_apply {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (alpha : ℕ → ℝ) (H : ℕ → E →L[ℝ] E) (g : ℕ → E) (k : ℕ) :
    steps alpha H g k = step (alpha k) (H k) (g k) := by
  rfl

/-- Successive gradient differences along a sequence. -/
def gradientChanges {E : Type u} [AddCommGroup E] (g : ℕ → E) (k : ℕ) : E :=
  gradientChange (g (k + 1)) (g k)

/-- Evaluation of the successive gradient difference at an iteration index. -/
theorem gradientChanges_apply {E : Type u} [AddCommGroup E] (g : ℕ → E) (k : ℕ) :
    gradientChanges g k = gradientChange (g (k + 1)) (g k) := by
  rfl

/-- A coordinate-free orbit of the inverse-form DFP method. -/
structure IsOrbit {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (alpha : ℕ → ℝ) (x g : ℕ → E)
    (H : ℕ → E →L[ℝ] E) : Prop where
  stepLengthPos : ∀ k, 0 < alpha k
  gradientAt : ∀ k, HasGradientAt f (g k) (x k)
  pointSucc : ∀ k, x (k + 1) = x k + steps alpha H g k
  inverseHessianSucc : ∀ k,
    H (k + 1) = inverseUpdate (H k) (steps alpha H g k) (gradientChanges g k)

/-- Coordinate-free DFP orbits are invariant under an invertible linear change of variables. -/
theorem IsOrbit.pullback
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} {alpha : ℕ → ℝ} {x g : ℕ → F} {H : ℕ → F →L[ℝ] F}
    (h : IsOrbit f alpha x g H) (L : E ≃L[ℝ] F) :
    IsOrbit (f ∘ L) alpha (fun k ↦ L.symm (x k))
      (fun k ↦ (L.toContinuousLinearMap†) (g k))
      (fun k ↦ L.symm.toContinuousLinearMap.pushforward (H k)) := by
  constructor
  · intro k
    exact h.stepLengthPos k
  · intro k
    have hg : HasGradientAt f (g k) (L (L.symm (x k))) := by
      simpa only [L.apply_symm_apply] using h.gradientAt k
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      (hg.comp_continuousLinearEquiv L)
  · intro k
    rw [h.pointSucc k, map_add]
    congr 1
    dsimp only [steps]
    exact (step_change L (alpha k) (H k) (g k)).symm
  · intro k
    rw [h.inverseHessianSucc k]
    symm
    have hstep :
        steps alpha (fun j ↦ L.symm.toContinuousLinearMap.pushforward (H j))
            (fun j ↦ (L.toContinuousLinearMap†) (g j)) k =
          L.symm (steps alpha H g k) := by
      dsimp only [steps]
      exact step_change L (alpha k) (H k) (g k)
    have hgradient :
        gradientChanges (fun j ↦ (L.toContinuousLinearMap†) (g j)) k =
          (L.toContinuousLinearMap†) (gradientChanges g k) := by
      dsimp only [gradientChanges]
      exact gradientChange_map (L.toContinuousLinearMap†) (g (k + 1)) (g k)
    rw [hstep, hgradient]
    exact inverseUpdate_change L (H k) (steps alpha H g k) (gradientChanges g k)

/-- Pulling back an orbit with a factored initial inverse Hessian produces an orbit initialized
at the identity. -/
theorem IsOrbit.pullback_of_initialFactor
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} {alpha : ℕ → ℝ} {x g : ℕ → F} {H : ℕ → F →L[ℝ] F}
    (h : IsOrbit f alpha x g H) (L : E ≃L[ℝ] F)
    (factor : H 0 = L.toContinuousLinearMap.pushforward 1) :
    IsOrbit (f ∘ L) alpha (fun k ↦ L.symm (x k))
        (fun k ↦ (L.toContinuousLinearMap†) (g k))
        (fun k ↦ L.symm.toContinuousLinearMap.pushforward (H k)) ∧
      L.symm.toContinuousLinearMap.pushforward (H 0) = 1 := by
  constructor
  · exact h.pullback L
  · exact normalize_inverseHessian L (H 0) factor

end DFP.Operator
