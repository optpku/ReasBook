module

public import ReasLib.Optimization.DFP.Orbit

public section

/-!
# Component characterization of a DFP orbit

This companion exposes the structure fields of `DFP.IsOrbit` as a conjunction.  It is kept
separate from the I.31-owned wrapper so that downstream developments can reuse the proof
without sharing write ownership of that file.
-/

universe u

namespace DFP.IsOrbit

/-- A DFP orbit is equivalent to its four defining component conditions. -/
theorem components_iff {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ} :
    DFP.IsOrbit f α x g H ↔
      (∀ k, 0 < α k) ∧
      (∀ k, HasGradientAt f (g k) (x k)) ∧
      (∀ k, x (k + 1) = x k + DFP.steps α (DFP.directions H g) k) ∧
      (∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
        (WithLp.ofLp (DFP.steps α (DFP.directions H g) k))
        (WithLp.ofLp (DFP.gradientChanges g k))) := by
  constructor
  · intro h
    exact ⟨h.stepLengthPos, h.gradientAt, h.pointSucc, h.inverseHessianSucc⟩
  · rintro ⟨hStep, hGradient, hPoint, hHessian⟩
    exact DFP.IsOrbit.ofHasGradientAt hStep hGradient hPoint hHessian

end DFP.IsOrbit
