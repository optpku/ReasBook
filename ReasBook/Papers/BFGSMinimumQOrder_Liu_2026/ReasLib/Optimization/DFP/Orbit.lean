module

public import ReasLib.Optimization.DFP.Iteration
import Mathlib.Tactic.Abel

public section

universe u

namespace DFP

/-- The recurrence and certified gradients of an inverse-form DFP orbit in finite real
coordinates. -/
structure IsOrbit {ι : Type u} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (α : ℕ → ℝ)
    (x g : ℕ → EuclideanSpace ℝ ι) (H : ℕ → Matrix ι ι ℝ) : Prop where
  stepLengthPos : ∀ k, 0 < α k
  gradientAt : ∀ k, HasGradientAt f (g k) (x k)
  pointSucc : ∀ k, x (k + 1) = x k + steps α (directions H g) k
  inverseHessianSucc : ∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
    (WithLp.ofLp (steps α (directions H g) k))
    (WithLp.ofLp (gradientChanges g k))

namespace InverseIteration

/-- An inverse-form DFP iteration with positive step lengths gives the corresponding
certified orbit with its canonical gradient sequence. -/
theorem isOrbit {ι : Type u} [Fintype ι] (it : InverseIteration ι)
    (hStep : ∀ k, 0 < it.stepLength k) :
    IsOrbit it.objective it.stepLength it.point
      (gradients it.objective it.point) it.inverseHessian := by
  refine {
    stepLengthPos := hStep
    gradientAt := ?_
    pointSucc := it.pointSucc
    inverseHessianSucc := it.inverseHessianSucc
  }
  intro k
  simpa only [gradients_apply] using (it.differentiableAt k).hasGradientAt

end InverseIteration

namespace IsOrbit

/-- A certified orbit's prescribed gradient sequence is the canonical gradient
of its objective along its point sequence. -/
theorem gradients_eq {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H) : gradients f x = g := by
  funext k
  rw [gradients_apply]
  exact (h.gradientAt k).gradient

/-- Positive secant curvature along a certified orbit makes every DFP secant
denominator nonzero. -/
theorem secantDenominator_ne_of_secantCurvature_pos {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H)
    (hSecant : ∀ k, 0 < inner ℝ (g (k + 1) - g k) (x (k + 1) - x k)) :
    ∀ k,
      WithLp.ofLp (steps α (directions H g) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges g k) ≠ 0 := by
  classical
  intro k
  have hStep :
      steps α (directions H g) k = x (k + 1) - x k := by
    rw [h.pointSucc k]
    abel
  have hChange : gradientChanges g k = g (k + 1) - g k := by
    rw [gradientChanges_apply]
  have hCoordinate :
      inner ℝ (g (k + 1) - g k) (x (k + 1) - x k) =
        WithLp.ofLp (x (k + 1) - x k) ⬝ᵥ
          WithLp.ofLp (g (k + 1) - g k) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [star_trivial, dotProduct_comm]
  have hPositive := hSecant k
  rw [hCoordinate] at hPositive
  rw [hStep, hChange]
  exact ne_of_gt hPositive

/-- A certified orbit with positive-definite inverse Hessians and nonzero secant
denominators gives an inverse-form DFP iteration. -/
noncomputable def toInverseIteration {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H) (hPosDef : ∀ k, (H k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H g) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges g k) ≠ 0) :
    InverseIteration ι :=
  InverseIteration.ofSequences f α x H
    (fun k ↦ (h.gradientAt k).differentiableAt) hPosDef
    (fun k ↦ by simpa only [h.gradients_eq] using hDenominator k)
    (fun k ↦ by simpa only [h.gradients_eq] using h.pointSucc k)
    (fun k ↦ by simpa only [h.gradients_eq] using h.inverseHessianSucc k)

/-- The objective of the inverse iteration assembled from a certified orbit is unchanged. -/
@[simp]
theorem toInverseIteration_objective {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H) (hPosDef : ∀ k, (H k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H g) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges g k) ≠ 0) :
    (h.toInverseIteration hPosDef hDenominator).objective = f := by
  rw [toInverseIteration, InverseIteration.ofSequences_objective]

/-- The step-length sequence of the inverse iteration assembled from a certified orbit
is unchanged. -/
@[simp]
theorem toInverseIteration_stepLength {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H) (hPosDef : ∀ k, (H k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H g) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges g k) ≠ 0) :
    (h.toInverseIteration hPosDef hDenominator).stepLength = α := by
  rw [toInverseIteration, InverseIteration.ofSequences_stepLength]

/-- The point sequence of the inverse iteration assembled from a certified orbit is
unchanged. -/
@[simp]
theorem toInverseIteration_point {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H) (hPosDef : ∀ k, (H k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H g) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges g k) ≠ 0) (k : ℕ) :
    (h.toInverseIteration hPosDef hDenominator).point k = x k := by
  rw [toInverseIteration, InverseIteration.ofSequences_point]

/-- The point sequence of the inverse iteration assembled from a certified orbit is
unchanged. -/
@[simp]
theorem toInverseIteration_point_eq {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H) (hPosDef : ∀ k, (H k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H g) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges g k) ≠ 0) :
    (h.toInverseIteration hPosDef hDenominator).point = x := by
  funext k
  exact h.toInverseIteration_point hPosDef hDenominator k

/-- The inverse-Hessian sequence of the inverse iteration assembled from a certified
orbit is unchanged. -/
@[simp]
theorem toInverseIteration_inverseHessian {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H) (hPosDef : ∀ k, (H k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H g) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges g k) ≠ 0) (k : ℕ) :
    (h.toInverseIteration hPosDef hDenominator).inverseHessian k = H k := by
  rw [toInverseIteration, InverseIteration.ofSequences_inverseHessian]

/-- The inverse-Hessian sequence of the inverse iteration assembled from a certified
orbit is unchanged. -/
@[simp]
theorem toInverseIteration_inverseHessian_eq {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : IsOrbit f α x g H) (hPosDef : ∀ k, (H k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H g) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges g k) ≠ 0) :
    (h.toInverseIteration hPosDef hDenominator).inverseHessian = H := by
  funext k
  exact h.toInverseIteration_inverseHessian hPosDef hDenominator k

/-- Positive step lengths, certified gradients, and the two DFP recurrence equations
construct an inverse-form DFP orbit. -/
theorem ofHasGradientAt {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (hStep : ∀ k, 0 < α k) (hGradient : ∀ k, HasGradientAt f (g k) (x k))
    (hPoint : ∀ k, x (k + 1) = x k + steps α (directions H g) k)
    (hHessian : ∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
      (WithLp.ofLp (steps α (directions H g) k))
      (WithLp.ofLp (gradientChanges g k))) :
    IsOrbit f α x g H := {
  stepLengthPos := hStep
  gradientAt := hGradient
  pointSucc := hPoint
  inverseHessianSucc := hHessian
}

/-- An inverse-form DFP orbit is equivalent to its positivity, certified-gradient,
point-recurrence, and matrix-recurrence conditions. -/
theorem iff {ι : Type u} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ} :
    IsOrbit f α x g H ↔
      (∀ k, 0 < α k) ∧
      (∀ k, HasGradientAt f (g k) (x k)) ∧
      (∀ k, x (k + 1) = x k + steps α (directions H g) k) ∧
      (∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
        (WithLp.ofLp (steps α (directions H g) k))
        (WithLp.ofLp (gradientChanges g k))) := by
  constructor
  · intro h
    exact ⟨h.stepLengthPos, h.gradientAt, h.pointSucc, h.inverseHessianSucc⟩
  · rintro ⟨hStep, hGradient, hPoint, hHessian⟩
    exact ofHasGradientAt hStep hGradient hPoint hHessian

end IsOrbit

end DFP
