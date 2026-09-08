module

public import ReasLib.Optimization.DFP.Operator.Matrix
public import ReasLib.Optimization.DFP.WolfeCounterexample
public import ReasLib.Analysis.InnerProductSpace.FiniteDimensionalOperatorLowerBound
public import ReasLib.Optimization.LineSearch.Wolfe.CoordinateChange
public import ReasLib.Optimization.LineSearch.Wolfe.WeakLegacy

public section

noncomputable section

open Filter
open scoped Topology InnerProduct

namespace DFP.WolfeCounterexample

/-!
This module records the affine-normalization interface for the fixed weak-Wolfe
counterexample.  The certificate is intentionally operator-valued: converting the
pulled-back operators to matrices is a separate representation step.
-/

/-- Infrastructure I.16a: A weak-Wolfe operator orbit with identity initialization.

The Hessian bounds and the positive gradient tail are explicit fields, so a
non-isometric coordinate change cannot silently be treated as an isometry. -/
structure IdentityInitializedOperatorCertificate (ι : Type u) [Fintype ι]
    (m M c₁ c₂ : ℝ) where
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  objective : EuclideanSpace ℝ ι → ℝ
  stepLength : ℕ → ℝ
  point : ℕ → EuclideanSpace ℝ ι
  gradient : ℕ → EuclideanSpace ℝ ι
  inverseHessian : ℕ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι
  orbit : DFP.Operator.IsOrbit objective stepLength point gradient inverseHessian
  objectiveContDiff : ContDiff ℝ 2 objective
  hessianBounds : HasHessianBounds m M objective
  weakWolfe : ∀ k, LineSearch.Wolfe.IsWeak
      { c₁ := c₁, c₂ := c₂, c₁_pos := c₁_pos, c₁_lt_c₂ := c₁_lt_c₂,
        c₂_lt_one := c₂_lt_one } objective (point k)
        (DFP.Operator.steps stepLength inverseHessian gradient k)
  weakWolfeLegacy : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ objective
      (point k) (point (k + 1) - point k)
  initialInverseHessian_eq_one : inverseHessian 0 = 1
  gradientLimit : ℝ
  gradientLimitPos : 0 < gradientLimit
  gradientNormEventuallyPositive : ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ k in atTop, δ ≤ ‖gradient k‖

/-- Infrastructure I.16a: The matrix orbit of a certified inverse iteration has
an operator orbit whose initial factor can be normalized by a continuous linear
equivalence. -/
theorem factorInitialInverseHessian_and_pullback
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {m M c₁ c₂ : ℝ} (c : DFP.WolfeCounterexample ι m M c₁ c₂)
    (L : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (factor : (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (c.iteration.inverseHessian 0) =
      L.toContinuousLinearMap.pushforward 1) :
    DFP.Operator.IsOrbit (c.iteration.objective ∘ L) c.iteration.stepLength
        (fun k ↦ L.symm (c.iteration.point k))
        (fun k ↦ (L.toContinuousLinearMap†)
          (DFP.gradients c.iteration.objective c.iteration.point k))
        (fun k ↦ L.symm.toContinuousLinearMap.pushforward
          ((Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
            (c.iteration.inverseHessian k))) ∧
      L.symm.toContinuousLinearMap.pushforward
        ((Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
          (c.iteration.inverseHessian 0)) = 1 := by
  have hMatrix := c.iteration.isOrbit c.stepLengthPos
  have hOperator := hMatrix.toOperator
  simpa using hOperator.pullback_of_initialFactor L factor

/-- Infrastructure I.16a: Pulling back a fixed weak-Wolfe certificate through a
factorized initial inverse Hessian yields an identity-initialized operator
certificate.  The parameters `a` and `b` are the explicit lower and upper
Loewner distortion constants for the Hessian bounds. -/
theorem identityInitialized_of_factorized
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {m M c₁ c₂ a b q : ℝ}
    (c : DFP.WolfeCounterexample ι m M c₁ c₂)
    (L : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (factor : (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (c.iteration.inverseHessian 0) =
      L.toContinuousLinearMap.pushforward 1)
    (hm : 0 ≤ m) (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc₁_pos : 0 < c₁) (hc₁_lt_c₂ : c₁ < c₂) (hc₂_lt_one : c₂ < 1)
    (lowerMap : a • (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ≤
      L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤
      b • (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι))
    (hq : 0 < q)
    (gradientMapLower : q • (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ≤
      L.toContinuousLinearMap.pushforward 1) :
    Nonempty (IdentityInitializedOperatorCertificate ι (m * a) (M * b) c₁ c₂) := by
  let f' : EuclideanSpace ℝ ι → ℝ := c.iteration.objective ∘ L
  let α' : ℕ → ℝ := c.iteration.stepLength
  let x' : ℕ → EuclideanSpace ℝ ι := fun k ↦ L.symm (c.iteration.point k)
  let g' : ℕ → EuclideanSpace ℝ ι := fun k ↦
    (L.toContinuousLinearMap†)
      (DFP.gradients c.iteration.objective c.iteration.point k)
  let H' : ℕ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι := fun k ↦
    L.symm.toContinuousLinearMap.pushforward
      ((Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (c.iteration.inverseHessian k))
  have hMatrix := c.iteration.isOrbit c.stepLengthPos
  have hOperator := hMatrix.toOperator
  have hPulled := hOperator.pullback_of_initialFactor L factor
  let orbit' := hPulled.1
  have hOrbit' : DFP.Operator.IsOrbit f' α' x' g' H' := by
    simpa only [f', α', x', g', H', Function.comp_apply] using orbit'
  have hInitial : H' 0 = 1 := by
    simpa only [H'] using hPulled.2
  have hGradientDifferentiable :
      Differentiable ℝ (gradient c.iteration.objective) :=
    (c.objectiveContDiff.gradient_succ (n := 1)).differentiable_one
  have hObjectiveContDiff : ContDiff ℝ 2 f' := by
    simpa only [f'] using c.objectiveContDiff.comp L.contDiff
  have hHessianBounds : HasHessianBounds (m * a) (M * b) f' := by
    exact c.hessianBounds.comp_continuousLinearEquiv L
      hGradientDifferentiable hm hM lowerMap upperMap
  have hStep (k : ℕ) :
      DFP.Operator.steps α' H' g' k =
        L.symm (DFP.Operator.steps c.iteration.stepLength
          (fun j ↦ (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
            (c.iteration.inverseHessian j))
          (DFP.gradients c.iteration.objective c.iteration.point) k) := by
    simpa only [DFP.Operator.steps_apply, α', H', g'] using
      (DFP.Operator.step_change L (c.iteration.stepLength k)
        ((Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
          (c.iteration.inverseHessian k))
        (DFP.gradients c.iteration.objective c.iteration.point k))
  have hWeak (k : ℕ) :
      LineSearch.Wolfe.IsWeak
        { c₁ := c₁, c₂ := c₂, c₁_pos := hc₁_pos, c₁_lt_c₂ := hc₁_lt_c₂,
          c₂_lt_one := hc₂_lt_one } f' (x' k)
        (DFP.Operator.steps α' H' g' k) := by
    apply (LineSearch.Wolfe.IsWeak.comp_continuousLinearEquiv_iff
      L (x' k) (DFP.Operator.steps α' H' g' k)).2
    let p : LineSearch.Wolfe.Coefficients :=
      { c₁ := c₁, c₂ := c₂, c₁_pos := hc₁_pos,
        c₁_lt_c₂ := hc₁_lt_c₂, c₂_lt_one := hc₂_lt_one }
    have hOld := LineSearch.Wolfe.IsWeak.ofIsWeakWolfe (p := p) (c.weakWolfe k)
    have hOldStep :
        DFP.Operator.steps c.iteration.stepLength
            (fun j ↦ (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
              EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
              (c.iteration.inverseHessian j))
            (DFP.gradients c.iteration.objective c.iteration.point) k =
          c.iteration.point (k + 1) - c.iteration.point k := by
      rw [hOperator.pointSucc k]
      abel
    simpa only [p, f', x', Function.comp_apply, L.apply_symm_apply, hStep,
      hOldStep] using hOld
  have hLegacy (k : ℕ) :
      LineSearch.IsWeakWolfe c₁ c₂ f' (x' k)
        (x' (k + 1) - x' k) := by
    have hPointStep := hOrbit'.pointSucc k
    have hStepEq : x' k + DFP.Operator.steps α' H' g' k = x' (k + 1) :=
      hPointStep.symm
    have hNext : HasGradientAt f' (g' (k + 1))
        (x' k + DFP.Operator.steps α' H' g' k) := by
      simpa only [hStepEq] using hOrbit'.gradientAt (k + 1)
    have hLegacyStep := (hWeak k).toIsWeakWolfe
      (hOrbit'.gradientAt k) hNext
    have hDisplacement : x' (k + 1) - x' k =
        DFP.Operator.steps α' H' g' k := by
      rw [hOrbit'.pointSucc k]
      abel
    simpa only [hDisplacement] using hLegacyStep
  have hHalf : ∀ᶠ k in atTop,
      c.gradientLimit / 2 ≤
        ‖DFP.gradients c.iteration.objective c.iteration.point k‖ := by
    have hlt : c.gradientLimit / 2 < c.gradientLimit := by
      nlinarith [c.gradientLimitPos]
    exact ((tendsto_order.1 c.gradientNormTendsto).1 _ hlt).mono
      (fun _ h ↦ le_of_lt h)
  let δ : ℝ := √q * (c.gradientLimit / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos (Real.sqrt_pos.2 hq) (half_pos c.gradientLimitPos)
  have hGradientTail : ∀ᶠ k in atTop, δ ≤ ‖g' k‖ := by
    filter_upwards [hHalf] with k hk
    have hnorm := ContinuousLinearMap.norm_adjoint_lower_bound
      L.toContinuousLinearMap hq.le gradientMapLower
      (DFP.gradients c.iteration.objective c.iteration.point k)
    dsimp only [δ, g']
    exact le_trans
      (mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg q)) hnorm
  let result : IdentityInitializedOperatorCertificate ι (m * a) (M * b) c₁ c₂ := {
    objective := f'
    stepLength := α'
    point := x'
    gradient := g'
    inverseHessian := H'
    orbit := hOrbit'
    objectiveContDiff := hObjectiveContDiff
    hessianBounds := hHessianBounds
    weakWolfe := hWeak
    weakWolfeLegacy := hLegacy
    initialInverseHessian_eq_one := hInitial
    gradientLimit := δ
    gradientLimitPos := hδ
    gradientNormEventuallyPositive := ⟨δ, hδ, hGradientTail⟩
    c₁_pos := hc₁_pos
    c₁_lt_c₂ := hc₁_lt_c₂
    c₂_lt_one := hc₂_lt_one
  }
  exact ⟨result⟩

/-- Infrastructure I.16a: Fixed-constant weak-Wolfe specialization of
`identityInitialized_of_factorized`.  The output bounds remain the explicitly
transported `(a / 2, 3 * b / 2)` bounds rather than the original constants. -/
theorem identityInitialized_fixedWeakWolfe_of_factorized
    {a b q : ℝ}
    (c : DFP.WolfeCounterexample (Fin 2) (1 / 2) (3 / 2) (1 / 4) (3 / 4))
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (factor : (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
        (c.iteration.inverseHessian 0) =
      L.toContinuousLinearMap.pushforward 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (lowerMap : a • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin 2)) ≤ L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤
      b • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
    (hq : 0 < q)
    (gradientMapLower : q • (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin 2)) ≤ L.toContinuousLinearMap.pushforward 1) :
    Nonempty (IdentityInitializedOperatorCertificate (Fin 2)
      ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) (1 / 4) (3 / 4)) := by
  have hm : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hM : (0 : ℝ) ≤ 3 / 2 := by norm_num
  have hc₁_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have hc₁_lt_c₂ : (1 / 4 : ℝ) < 3 / 4 := by norm_num
  have hc₂_lt_one : (3 / 4 : ℝ) < 1 := by norm_num
  exact identityInitialized_of_factorized c L factor
    hm hM ha hb hc₁_pos hc₁_lt_c₂ hc₂_lt_one
    lowerMap upperMap hq gradientMapLower

end DFP.WolfeCounterexample
