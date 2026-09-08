module

public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedTransport
public import ReasLib.Optimization.DFP.WolfeCounterexample.IdentityInitialization
public import ReasLib.Optimization.DFP.StrongWolfeCounterexample
public import ReasLib.Optimization.LineSearch.Wolfe.CoordinateChange
public import ReasLib.Optimization.LineSearch.Wolfe.Gradient
import Mathlib.Tactic

/-!
# Parameterized identity initialization

This module gives the affine-normalization corollary at the operator level.  A
factorization of the initial inverse Hessian and explicit Loewner bounds on its
pullback/pushforward are hypotheses of the theorem.  Thus the result does not
silently identify a non-isometric coordinate change with an orthogonal one.

The output records the strong-Wolfe steps and the identity initial operator.
The passage from this operator certificate to a matrix presentation, and the
construction of the factor and its spectral bounds from a matrix square root,
are separate representation lemmas.
 -/

public section

noncomputable section

universe u

open Filter
open scoped Topology InnerProduct

namespace LineSearch.IsStrongWolfe

/-- Helper for TASK-10: Strong-Wolfe endpoint certificates pull back through an
arbitrary continuous linear equivalence when the transformed gradients are
used, not only through an isometry. -/
theorem comp_continuousLinearEquiv
    {E : Type u} {F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {c₁ c₂ : ℝ} {f : F → ℝ} {x s : F}
    (h : LineSearch.IsStrongWolfe c₁ c₂ f x s)
    (L : E ≃L[ℝ] F) :
    LineSearch.IsStrongWolfe c₁ c₂ (f ∘ L) (L.symm x) (L.symm s) := by
  let p : LineSearch.Wolfe.Coefficients := {
    c₁ := c₁
    c₂ := c₂
    c₁_pos := h.c₁_pos
    c₁_lt_c₂ := h.c₁_lt_c₂
    c₂_lt_one := h.c₂_lt_one
  }
  have hOld : LineSearch.Wolfe.IsStrong p f x s := by
    have hStart := h.differentiableAt.hasGradientAt
    have hNext := h.differentiableAtNext.hasGradientAt
    exact LineSearch.Wolfe.IsStrong.ofHasGradientAt hStart hNext
      (LineSearch.Wolfe.isArmijo_iff.mpr h.armijo)
      (LineSearch.Wolfe.isStrongCurvature_iff.mpr h.strongCurvature)
  have hNew : LineSearch.Wolfe.IsStrong p (f ∘ L) (L.symm x) (L.symm s) := by
    apply (LineSearch.Wolfe.IsStrong.comp_continuousLinearEquiv_iff
      L (L.symm x) (L.symm s)).2
    simpa only [L.apply_symm_apply] using hOld
  have hStart : HasGradientAt (f ∘ L)
      ((L.toContinuousLinearMap†) (gradient f x)) (L.symm x) := by
    apply HasGradientAt.comp_continuousLinearEquiv L
    simpa only [L.apply_symm_apply] using h.differentiableAt.hasGradientAt
  have hNext : HasGradientAt (f ∘ L)
      ((L.toContinuousLinearMap†) (gradient f (x + s)))
      (L.symm x + L.symm s) := by
    apply HasGradientAt.comp_continuousLinearEquiv L
    simpa only [map_add, L.apply_symm_apply] using h.differentiableAtNext.hasGradientAt
  have hStartLine : lineDeriv ℝ (f ∘ L) (L.symm x) (L.symm s) =
      inner ℝ ((L.toContinuousLinearMap†) (gradient f x)) (L.symm s) := by
    rw [hStart.differentiableAt.lineDeriv_eq_fderiv, hStart.fderiv_apply]
  have hNextLine : lineDeriv ℝ (f ∘ L)
      (L.symm x + L.symm s) (L.symm s) =
      inner ℝ ((L.toContinuousLinearMap†) (gradient f (x + s))) (L.symm s) := by
    rw [hNext.differentiableAt.lineDeriv_eq_fderiv, hNext.fderiv_apply]
  apply LineSearch.IsStrongWolfe.ofHasGradientAt h.c₁_pos h.c₁_lt_c₂ h.c₂_lt_one
    hStart hNext
  · simpa only [p, LineSearch.Wolfe.isArmijo_iff, hStartLine] using hNew.armijo
  · simpa only [p, LineSearch.Wolfe.isStrongCurvature_iff, hStartLine, hNextLine] using
      hNew.strongCurvature

end LineSearch.IsStrongWolfe

namespace DFP.WolfeCounterexample

/-- TASK-10: An identity-initialized operator certificate retaining the
strong-Wolfe field of the underlying trajectory.  The inherited Hessian bounds
are the explicitly transported `(m * a, M * b)` bounds. -/
structure IdentityInitializedStrongWolfeOperatorCertificate
    (ι : Type u) [Fintype ι] (m M c₁ c₂ : ℝ)
    extends IdentityInitializedOperatorCertificate ι m M c₁ c₂ where
  strongWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ objective
    (point k) (point (k + 1) - point k)

/-- Helper for TASK-10: the transformed strong-Wolfe step is expressed using
the operator orbit's canonical search step. -/
private theorem strongWolfe_operatorStep_of_factorized
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {m M c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample ι m M c₁ c₂)
    (L : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (f' : EuclideanSpace ℝ ι → ℝ)
    (α' : ℕ → ℝ)
    (x' : ℕ → EuclideanSpace ℝ ι)
    (g' : ℕ → EuclideanSpace ℝ ι)
    (H' : ℕ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hf' : f' = c.iteration.objective ∘ L)
    (hx' : ∀ k, x' k = L.symm (c.iteration.point k))
    (hStep : ∀ k, DFP.Operator.steps α' H' g' k =
      L.symm (DFP.Operator.steps c.iteration.stepLength
        (fun j ↦ (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
          (c.iteration.inverseHessian j))
        (DFP.gradients c.iteration.objective c.iteration.point) k)) :
    ∀ k, LineSearch.IsStrongWolfe c₁ c₂ f' (x' k)
      (DFP.Operator.steps α' H' g' k) := by
  intro k
  have hOld := LineSearch.IsStrongWolfe.comp_continuousLinearEquiv
    (c.strongWolfe k) L
  have hOldStep :
      DFP.Operator.steps c.iteration.stepLength
          (fun j ↦ (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
            (c.iteration.inverseHessian j))
          (DFP.gradients c.iteration.objective c.iteration.point) k =
        c.iteration.point (k + 1) - c.iteration.point k := by
    have hMatrix := c.iteration.isOrbit c.stepLengthPos
    have hOperator := hMatrix.toOperator
    rw [hOperator.pointSucc k]
    abel
  rw [hf', hx' k]
  simpa only [Function.comp_apply, L.apply_symm_apply, hStep k, hOldStep] using hOld

/-- TASK-10: A strong-Wolfe counterexample with an explicitly factorized
initial inverse Hessian can be affinely normalized to identity initialization.
The parameters `a`, `b`, and `q` are explicit lower/upper Loewner bounds for
the Hessian pullback and gradient pushforward, respectively. -/
theorem identityInitializedStrongWolfe_of_factorized
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {m M c₁ c₂ a b q : ℝ}
    (c : DFP.StrongWolfeCounterexample ι m M c₁ c₂)
    (L : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (factor : (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (c.iteration.inverseHessian 0) =
      L.toContinuousLinearMap.pushforward 1)
    (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hc₁_pos : 0 < c₁) (hc₁_lt_c₂ : c₁ < c₂) (hc₂_lt_one : c₂ < 1)
    (lowerMap : a • (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ≤
      L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤
      b • (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι))
    (hq : 0 < q)
    (gradientMapLower : q • (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ≤
      L.toContinuousLinearMap.pushforward 1) :
    Nonempty (IdentityInitializedStrongWolfeOperatorCertificate ι
      (m * a) (M * b) c₁ c₂) := by
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
  let p : LineSearch.Wolfe.Coefficients := {
    c₁ := c₁
    c₂ := c₂
    c₁_pos := hc₁_pos
    c₁_lt_c₂ := hc₁_lt_c₂
    c₂_lt_one := hc₂_lt_one
  }
  have hWeak (k : ℕ) :
      LineSearch.Wolfe.IsWeak p f' (x' k)
        (DFP.Operator.steps α' H' g' k) := by
    apply (LineSearch.Wolfe.IsWeak.comp_continuousLinearEquiv_iff
      L (x' k) (DFP.Operator.steps α' H' g' k)).2
    have hOld := LineSearch.Wolfe.IsWeak.ofIsWeakWolfe
      (p := p) (c.weakWolfe k)
    have hOldStep :
        DFP.Operator.steps c.iteration.stepLength
            (fun j ↦ (Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
              EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
              (c.iteration.inverseHessian j))
            (DFP.gradients c.iteration.objective c.iteration.point) k =
          c.iteration.point (k + 1) - c.iteration.point k := by
      rw [hOperator.pointSucc k]
      abel
    simpa only [p, f', x', Function.comp_apply, L.apply_symm_apply,
      hStep k, hOldStep] using hOld
  have hWeakOutput (k : ℕ) :
      LineSearch.Wolfe.IsWeak
        { c₁ := c₁, c₂ := c₂, c₁_pos := hc₁_pos,
          c₁_lt_c₂ := hc₁_lt_c₂, c₂_lt_one := hc₂_lt_one }
        f' (x' k) (DFP.Operator.steps α' H' g' k) := by
    simpa only [p] using hWeak k
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
    simpa only [p, hDisplacement] using hLegacyStep
  have hStrongOperator : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ f' (x' k)
      (DFP.Operator.steps α' H' g' k) := by
    have hf' : f' = c.iteration.objective ∘ L := by
      rfl
    have hx' : ∀ k, x' k = L.symm (c.iteration.point k) := by
      intro k
      rfl
    exact strongWolfe_operatorStep_of_factorized c L f' α' x' g' H'
      hf' hx' hStep
  have hStrongLegacy (k : ℕ) :
      LineSearch.IsStrongWolfe c₁ c₂ f' (x' k)
        (x' (k + 1) - x' k) := by
    have hDisplacement : x' (k + 1) - x' k =
        DFP.Operator.steps α' H' g' k := by
      rw [hOrbit'.pointSucc k]
      abel
    simpa only [hDisplacement] using hStrongOperator k
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
  have hGradientTailPackage : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ k in atTop, δ ≤ ‖g' k‖ := by
    exact ⟨δ, hδ, hGradientTail⟩
  let base : IdentityInitializedOperatorCertificate ι (m * a) (M * b) c₁ c₂ := {
    c₁_pos := hc₁_pos
    c₁_lt_c₂ := hc₁_lt_c₂
    c₂_lt_one := hc₂_lt_one
    objective := f'
    stepLength := α'
    point := x'
    gradient := g'
    inverseHessian := H'
    orbit := hOrbit'
    objectiveContDiff := hObjectiveContDiff
    hessianBounds := hHessianBounds
    weakWolfe := hWeakOutput
    weakWolfeLegacy := hLegacy
    initialInverseHessian_eq_one := hInitial
    gradientLimit := δ
    gradientLimitPos := hδ
    gradientNormEventuallyPositive := hGradientTailPackage
  }
  let result : IdentityInitializedStrongWolfeOperatorCertificate ι
      (m * a) (M * b) c₁ c₂ := {
    toIdentityInitializedOperatorCertificate := base
    strongWolfe := hStrongLegacy
  }
  exact ⟨result⟩

/-! The all-dimensional convenience theorem is intentionally left to a
downstream wrapper: its factorization must refer to the particular witness
chosen by `existsStrongWolfeCounterexample_of_dimension_ge_two`.  The generic
theorem above accepts that witness explicitly, so no choice-dependent factor
is hidden in this module. -/

/-- TASK-10: A dimension-indexed strong certificate in the paper's Wolfe range
can be normalized once its concrete witness and factorization are supplied.
The witness is an explicit argument so that the factor equation refers to the
same trajectory used by the conclusion. -/
theorem identityInitializedStrongWolfe_of_dimension_ge_two
    (n : ℕ) {c₁ c₂ a b q : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (factor : (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (c.iteration.inverseHessian 0) =
      L.toContinuousLinearMap.pushforward 1)
    (lowerMap : a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) ≤ L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤
      b • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hq : 0 < q)
    (gradientMapLower : q • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) ≤ L.toContinuousLinearMap.pushforward 1) :
    Nonempty (IdentityInitializedStrongWolfeOperatorCertificate (Fin n)
      ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) c₁ c₂) := by
  have hm : (0 : ℝ) ≤ 1 / 2 := by
    norm_num
  have hM : (0 : ℝ) ≤ 3 / 2 := by
    norm_num
  have hc₁_lt_c₂ : c₁ < c₂ :=
    lt_of_lt_of_le hc₁_lt_two_thirds hc₂_ge_two_thirds
  exact identityInitializedStrongWolfe_of_factorized c L factor hm hM
    hc₁_pos hc₁_lt_c₂ hc₂_lt_one lowerMap upperMap hq gradientMapLower

end DFP.WolfeCounterexample
