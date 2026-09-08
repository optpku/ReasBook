module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import ReasLib.Optimization.DFP.InverseUpdate

public section

open scoped Matrix

namespace DFP

/-- The sequence of gradients of `f` along the point sequence `x`. -/
noncomputable def gradients {n : Type u} [Fintype n]
    (f : EuclideanSpace ℝ n → ℝ) (x : ℕ → EuclideanSpace ℝ n) :
    ℕ → EuclideanSpace ℝ n :=
  fun k ↦ gradient f (x k)

/-- Evaluation of the gradient sequence at an iteration index. -/
theorem gradients_apply {n : Type u} [Fintype n] (f : EuclideanSpace ℝ n → ℝ)
    (x : ℕ → EuclideanSpace ℝ n) (k : ℕ) :
    gradients f x k = gradient f (x k) := by
  -- Unfolding the sequence evaluates its defining function at `k`.
  rfl

/-- The inverse-Hessian search directions `-Hₖgₖ`. -/
noncomputable def directions {n : Type u} [Fintype n] (H : ℕ → Matrix n n ℝ)
    (g : ℕ → EuclideanSpace ℝ n) : ℕ → EuclideanSpace ℝ n :=
  fun k ↦ -WithLp.toLp 2 (H k *ᵥ WithLp.ofLp (g k))

/-- Evaluation of the search-direction sequence at an iteration index. -/
theorem directions_apply {n : Type u} [Fintype n] (H : ℕ → Matrix n n ℝ)
    (g : ℕ → EuclideanSpace ℝ n) (k : ℕ) :
    directions H g k = -WithLp.toLp 2 (H k *ᵥ WithLp.ofLp (g k)) := by
  -- Evaluating the defining function at `k` gives the stated direction.
  rfl

/-- The scaled step sequence `αₖ • dₖ`. -/
def steps {n : Type u} [Fintype n] (α : ℕ → ℝ) (d : ℕ → EuclideanSpace ℝ n) :
    ℕ → EuclideanSpace ℝ n :=
  fun k ↦ α k • d k

/-- Evaluation of the scaled-step sequence at an iteration index. -/
theorem steps_apply {n : Type u} [Fintype n] (α : ℕ → ℝ)
    (d : ℕ → EuclideanSpace ℝ n) (k : ℕ) :
    steps α d k = α k • d k := by
  -- Evaluating the defining function at `k` gives the scaled direction.
  rfl

/-- The successive differences `gₖ₊₁ - gₖ` of a gradient sequence. -/
def gradientChanges {n : Type u} [Fintype n] (g : ℕ → EuclideanSpace ℝ n) :
    ℕ → EuclideanSpace ℝ n :=
  fun k ↦ g (k + 1) - g k

/-- Evaluation of the gradient-change sequence at an iteration index. -/
theorem gradientChanges_apply {n : Type u} [Fintype n]
    (g : ℕ → EuclideanSpace ℝ n) (k : ℕ) :
    gradientChanges g k = g (k + 1) - g k := by
  -- Evaluating the defining function at `k` gives the successive difference.
  rfl

/-- Flatten the boundary and intermediate data of a two-step iteration into one sequence. -/
def twoStepSequence {α : Type u} (boundary middle : ℕ → α) (k : ℕ) : α :=
  if k % 2 = 0 then boundary (k / 2) else middle (k / 2)

/-- The even terms of a flattened two-step sequence are its boundary data. -/
@[simp] theorem twoStepSequence_even {α : Type u} (boundary middle : ℕ → α) (j : ℕ) :
    twoStepSequence boundary middle (2 * j) = boundary j := by
  simp [twoStepSequence]

/-- The odd terms of a flattened two-step sequence are its intermediate data. -/
@[simp] theorem twoStepSequence_odd {α : Type u} (boundary middle : ℕ → α) (j : ℕ) :
    twoStepSequence boundary middle (2 * j + 1) = middle j := by
  have hdiv : (2 * j + 1) / 2 = j := by omega
  simp [twoStepSequence, hdiv]

/-- A complete classical inverse-form DFP trajectory in finite real coordinates. -/
structure InverseIteration (n : Type u) [Fintype n] where
  objective : EuclideanSpace ℝ n → ℝ
  stepLength : ℕ → ℝ
  point : ℕ → EuclideanSpace ℝ n
  inverseHessian : ℕ → Matrix n n ℝ
  differentiableAt : ∀ k, DifferentiableAt ℝ objective (point k)
  inverseHessianPosDef : ∀ k, (inverseHessian k).PosDef
  secantDenominatorNe : ∀ k,
    WithLp.ofLp (steps stepLength (directions inverseHessian (gradients objective point)) k) ⬝ᵥ
      WithLp.ofLp (gradientChanges (gradients objective point) k) ≠ 0
  pointSucc : ∀ k, point (k + 1) = point k +
    steps stepLength (directions inverseHessian (gradients objective point)) k
  inverseHessianSucc : ∀ k, inverseHessian (k + 1) = Matrix.inverseDFPUpdate
    (inverseHessian k)
    (WithLp.ofLp (steps stepLength (directions inverseHessian (gradients objective point)) k))
    (WithLp.ofLp (gradientChanges (gradients objective point) k))

namespace InverseIteration

/-- Construct an inverse-form DFP trajectory from explicit sequences satisfying its laws. -/
noncomputable def ofSequences {n : Type u} [Fintype n] (f : EuclideanSpace ℝ n → ℝ)
    (α : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ n) (H : ℕ → Matrix n n ℝ)
    (hDifferentiable : ∀ k, DifferentiableAt ℝ f (x k))
    (hPosDef : ∀ k, (H k).PosDef)
    (hSecantDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H (gradients f x)) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges (gradients f x) k) ≠ 0)
    (hPoint : ∀ k, x (k + 1) = x k + steps α (directions H (gradients f x)) k)
    (hHessian : ∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
      (WithLp.ofLp (steps α (directions H (gradients f x)) k))
      (WithLp.ofLp (gradientChanges (gradients f x) k))) :
    InverseIteration n where
  objective := f
  stepLength := α
  point := x
  inverseHessian := H
  differentiableAt := hDifferentiable
  inverseHessianPosDef := hPosDef
  secantDenominatorNe := hSecantDenominator
  pointSucc := hPoint
  inverseHessianSucc := hHessian

/-- The objective of an iteration constructed by `ofSequences`. -/
@[simp]
theorem ofSequences_objective {n : Type u} [Fintype n] (f : EuclideanSpace ℝ n → ℝ)
    (α : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ n) (H : ℕ → Matrix n n ℝ)
    (hDifferentiable : ∀ k, DifferentiableAt ℝ f (x k)) (hPosDef : ∀ k, (H k).PosDef)
    (hSecantDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H (gradients f x)) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges (gradients f x) k) ≠ 0)
    (hPoint : ∀ k, x (k + 1) = x k + steps α (directions H (gradients f x)) k)
    (hHessian : ∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
      (WithLp.ofLp (steps α (directions H (gradients f x)) k))
      (WithLp.ofLp (gradientChanges (gradients f x) k))) :
    (ofSequences f α x H hDifferentiable hPosDef hSecantDenominator hPoint hHessian).objective =
      f := by
  rfl

/-- The step-length sequence of an iteration constructed by `ofSequences`. -/
@[simp]
theorem ofSequences_stepLength {n : Type u} [Fintype n] (f : EuclideanSpace ℝ n → ℝ)
    (α : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ n) (H : ℕ → Matrix n n ℝ)
    (hDifferentiable : ∀ k, DifferentiableAt ℝ f (x k)) (hPosDef : ∀ k, (H k).PosDef)
    (hSecantDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H (gradients f x)) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges (gradients f x) k) ≠ 0)
    (hPoint : ∀ k, x (k + 1) = x k + steps α (directions H (gradients f x)) k)
    (hHessian : ∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
      (WithLp.ofLp (steps α (directions H (gradients f x)) k))
      (WithLp.ofLp (gradientChanges (gradients f x) k))) :
    (ofSequences f α x H hDifferentiable hPosDef hSecantDenominator hPoint
      hHessian).stepLength = α := by
  rfl

/-- The point sequence of an iteration constructed by `ofSequences`. -/
theorem ofSequences_point {n : Type u} [Fintype n] (f : EuclideanSpace ℝ n → ℝ)
    (α : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ n) (H : ℕ → Matrix n n ℝ)
    (hDifferentiable : ∀ k, DifferentiableAt ℝ f (x k)) (hPosDef : ∀ k, (H k).PosDef)
    (hSecantDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H (gradients f x)) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges (gradients f x) k) ≠ 0)
    (hPoint : ∀ k, x (k + 1) = x k + steps α (directions H (gradients f x)) k)
    (hHessian : ∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
      (WithLp.ofLp (steps α (directions H (gradients f x)) k))
      (WithLp.ofLp (gradientChanges (gradients f x) k)))
    (k : ℕ) :
    (ofSequences f α x H hDifferentiable hPosDef hSecantDenominator hPoint hHessian).point k =
      x k := by
  -- The constructor stores `x` directly as its point sequence.
  rfl

/-- The inverse-Hessian sequence of an iteration constructed by `ofSequences`. -/
theorem ofSequences_inverseHessian {n : Type u} [Fintype n] (f : EuclideanSpace ℝ n → ℝ)
    (α : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ n) (H : ℕ → Matrix n n ℝ)
    (hDifferentiable : ∀ k, DifferentiableAt ℝ f (x k)) (hPosDef : ∀ k, (H k).PosDef)
    (hSecantDenominator : ∀ k,
      WithLp.ofLp (steps α (directions H (gradients f x)) k) ⬝ᵥ
        WithLp.ofLp (gradientChanges (gradients f x) k) ≠ 0)
    (hPoint : ∀ k, x (k + 1) = x k + steps α (directions H (gradients f x)) k)
    (hHessian : ∀ k, H (k + 1) = Matrix.inverseDFPUpdate (H k)
      (WithLp.ofLp (steps α (directions H (gradients f x)) k))
      (WithLp.ofLp (gradientChanges (gradients f x) k)))
    (k : ℕ) :
    (ofSequences f α x H hDifferentiable hPosDef hSecantDenominator hPoint
      hHessian).inverseHessian k = H k := by
  -- The constructor stores `H` directly as its inverse-Hessian sequence.
  rfl

/-- Differentiability and positive definiteness at one index of a DFP trajectory. -/
theorem analytic_spec {n : Type u} [Fintype n] (it : InverseIteration n) (k : ℕ) :
    DifferentiableAt ℝ it.objective (it.point k) ∧ (it.inverseHessian k).PosDef := by
  -- Package the two analytic invariants stored by the trajectory.
  exact ⟨it.differentiableAt k, it.inverseHessianPosDef k⟩

/-- Both scalar denominators in the inverse-form DFP update are nonzero. -/
theorem denominators_spec {n : Type u} [Fintype n] (it : InverseIteration n) (k : ℕ) :
    let y := WithLp.ofLp (gradientChanges (gradients it.objective it.point) k)
    let s := WithLp.ofLp
      (steps it.stepLength (directions it.inverseHessian (gradients it.objective it.point)) k)
    y ⬝ᵥ (it.inverseHessian k *ᵥ y) ≠ 0 ∧ s ⬝ᵥ y ≠ 0 := by
  -- Expose the secant pair and retain its certified nonzero denominator.
  dsimp only
  have hs := it.secantDenominatorNe k
  -- A zero gradient change would force the certified secant denominator to vanish.
  have hy : WithLp.ofLp (gradientChanges (gradients it.objective it.point) k) ≠ 0 := by
    intro hy
    apply hs
    rw [hy, dotProduct_zero]
  -- Positive definiteness makes the remaining quadratic denominator strictly positive.
  have hpositive : 0 <
      WithLp.ofLp (gradientChanges (gradients it.objective it.point) k) ⬝ᵥ
        (it.inverseHessian k *ᵥ
          WithLp.ofLp (gradientChanges (gradients it.objective it.point) k)) := by
    simpa using (it.inverseHessianPosDef k).dotProduct_mulVec_pos hy
  exact ⟨ne_of_gt hpositive, hs⟩

/-- The point and inverse-Hessian successor equations at one index of a DFP trajectory. -/
theorem recurrence_spec {n : Type u} [Fintype n] (it : InverseIteration n) (k : ℕ) :
    it.point (k + 1) = it.point k +
        steps it.stepLength (directions it.inverseHessian (gradients it.objective it.point)) k ∧
      it.inverseHessian (k + 1) = Matrix.inverseDFPUpdate (it.inverseHessian k)
        (WithLp.ofLp (steps it.stepLength
          (directions it.inverseHessian (gradients it.objective it.point)) k))
        (WithLp.ofLp (gradientChanges (gradients it.objective it.point) k)) := by
  -- Package the two recurrence laws stored by the trajectory.
  exact ⟨it.pointSucc k, it.inverseHessianSucc k⟩

end InverseIteration

end DFP
