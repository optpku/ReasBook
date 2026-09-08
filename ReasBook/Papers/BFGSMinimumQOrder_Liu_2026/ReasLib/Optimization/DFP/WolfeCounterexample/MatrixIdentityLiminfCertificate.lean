module

public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedIdentityInitialization
public import ReasLib.Optimization.DFP.WolfeCounterexample.MatrixIdentityInitialization
public import ReasLib.Optimization.DFP.Operator.Matrix
public import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Matrix identity initialization with a positive gradient liminf

This module records the matrix-facing formulation of the identity
initialization corollary.  Unlike the older convergence-oriented certificate,
the gradient hypothesis here is exactly the paper-facing statement
`0 < liminf ‖∇f(xₖ)‖`; no convergence of the gradient norms is required.

The operator-to-matrix constructor keeps the representation obligations
explicit: positive definiteness of the canonical matrix sequence, nonzero DFP
secant denominators, and the gradient liminf are inputs.  Thus the constructor
does not hide a matrix/continuous-linear-map identification behind an
unproved coercion.
 -/

public section

noncomputable section

universe u

open Filter
open scoped InnerProduct MatrixOrder Topology

namespace DFP.WolfeCounterexample

/-- Helper for TASK-15: identify the canonical matrix sequence with its
explicit `Matrix.toEuclideanCLM.symm` pointwise representation. -/
theorem canonicalMatrixSequence_eq_explicit
    {n : ℕ}
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    canonicalMatrixSequence H =
      (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm (H k)) := by
  funext k
  exact canonicalMatrixSequence_apply H k

/-- TASK-16: a classical matrix DFP trajectory satisfying the identity-initialization
corollary with the exact paper-facing positive gradient-liminf conclusion.

The `gradientNormEventuallyPositive` field is retained as a useful quantitative
tail, but the semantic conclusion is the independent `gradientNormLiminfPos`
field. -/
structure MatrixIdentityLiminfStrongWolfeCertificate
    (n : ℕ) (m M c₁ c₂ : ℝ) where
  iteration : DFP.InverseIteration (Fin n)
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1
  hessianLowerPos : 0 < m
  hessianLowerLeUpper : m ≤ M
  objectiveContDiff : ContDiff ℝ 2 iteration.objective
  stepLengthPos : ∀ k, 0 < iteration.stepLength k
  hessianBounds : HasHessianBounds m M iteration.objective
  strongWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ iteration.objective
    (iteration.point k) (iteration.point (k + 1) - iteration.point k)
  initialInverseHessian_eq_one : iteration.inverseHessian 0 =
    (1 : Matrix (Fin n) (Fin n) ℝ)
  gradientNormLiminfPos : 0 < liminf
    (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖) atTop
  gradientNormEventuallyPositive : ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients iteration.objective iteration.point k‖

/-- Helper for TASK-16: the matrix certificate exposes its paper-facing positive gradient liminf. -/
theorem MatrixIdentityLiminfStrongWolfeCertificate.gradientNorm_liminf_pos
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂) :
    0 < liminf
      (fun k ↦ ‖DFP.gradients c.iteration.objective c.iteration.point k‖) atTop :=
  c.gradientNormLiminfPos

/-- Helper for TASK-16: the matrix certificate exposes the ordered positive Hessian bounds required
by the identity corollary. -/
theorem MatrixIdentityLiminfStrongWolfeCertificate.hessianBounds_pos_le
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂) :
    0 < m ∧ m ≤ M :=
  ⟨c.hessianLowerPos, c.hessianLowerLeUpper⟩

/-- Helper for TASK-16: assemble the matrix-facing certificate from an identity-initialized
operator certificate.  The matrix positive-definiteness, secant denominator,
and gradient-liminf obligations are explicit hypotheses of this bridge. -/
theorem MatrixIdentityLiminfStrongWolfeCertificate.ofOperator
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate (Fin n) m M c₁ c₂)
    (hm : 0 < m) (hmM : m ≤ M)
    (hGradientNormLiminf : 0 < liminf (fun k ↦ ‖c.gradient k‖) atTop)
    (hPosDef : ∀ k, (canonicalMatrixSequence c.inverseHessian k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp
          (DFP.steps c.stepLength
            (DFP.directions (canonicalMatrixSequence c.inverseHessian) c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0) :
    Nonempty (MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂) := by
  let H : ℕ → Matrix (Fin n) (Fin n) ℝ := canonicalMatrixSequence c.inverseHessian
  have hPosDef' : ∀ k, (H k).PosDef := by
    intro k
    exact hPosDef k
  have hDenominator' : ∀ k,
      WithLp.ofLp
          (DFP.steps c.stepLength (DFP.directions H c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0 := by
    intro k
    exact hDenominator k
  have hOrbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H := by
    have hOrbitExplicit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient
      (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (c.inverseHessian k)) :=
      c.toIdentityInitializedOperatorCertificate.orbit.toMatrix
    have hSequenceEq : canonicalMatrixSequence c.inverseHessian =
        (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
          (c.inverseHessian k)) := by
      exact canonicalMatrixSequence_eq_explicit c.inverseHessian
    dsimp only [H]
    rw [hSequenceEq]
    exact hOrbitExplicit
  let iteration : DFP.InverseIteration (Fin n) :=
    hOrbit.toInverseIteration hPosDef' hDenominator'
  have hObjective : iteration.objective = c.objective := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective] using rfl
  have hStepLength : ∀ k, iteration.stepLength k = c.stepLength k := by
    intro k
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_stepLength] using rfl
  have hPoint : ∀ k, iteration.point k = c.point k := by
    intro k
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_point] using rfl
  have hGradientEq :
      DFP.gradients iteration.objective iteration.point = c.gradient := by
    have hOrbitGradient : DFP.gradients c.objective c.point = c.gradient :=
      hOrbit.gradients_eq
    rw [hObjective]
    have hPointEq : iteration.point = c.point := by
      simpa only [iteration, DFP.IsOrbit.toInverseIteration_point_eq] using rfl
    rw [hPointEq]
    exact hOrbitGradient
  have hContDiff : ContDiff ℝ 2 iteration.objective := by
    rw [hObjective]
    exact c.objectiveContDiff
  have hStepPos : ∀ k, 0 < iteration.stepLength k := by
    intro k
    rw [hStepLength k]
    exact c.toIdentityInitializedOperatorCertificate.orbit.stepLengthPos k
  have hHessianBounds : HasHessianBounds m M iteration.objective := by
    rw [hObjective]
    exact c.hessianBounds
  have hStrongWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    intro k
    rw [hObjective, hPoint k, hPoint (k + 1)]
    have hStepEq :
        DFP.Operator.steps c.stepLength
            c.inverseHessian
            c.gradient k = c.point (k + 1) - c.point k := by
      have hOperator := c.toIdentityInitializedOperatorCertificate.orbit
      rw [hOperator.pointSucc k]
      abel
    have hStrong := c.strongWolfe k
    simpa only [hStepEq] using hStrong
  have hInitial : iteration.inverseHessian 0 =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have hMatrixInitial := canonicalMatrixSequence_zero_eq_one
      (H := c.inverseHessian) c.initialInverseHessian_eq_one
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_inverseHessian] using
      hMatrixInitial
  have hTail : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients iteration.objective iteration.point k‖ := by
    obtain ⟨δ, hδ, htail⟩ := c.gradientNormEventuallyPositive
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [htail] with k hk
    rw [hGradientEq]
    exact hk
  have hLiminf : 0 < liminf
      (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖) atTop := by
    rw [hGradientEq]
    exact hGradientNormLiminf
  let result : MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂ := {
    iteration := iteration
    c₁_pos := c.c₁_pos
    c₁_lt_c₂ := c.c₁_lt_c₂
    c₂_lt_one := c.c₂_lt_one
    hessianLowerPos := hm
    hessianLowerLeUpper := hmM
    objectiveContDiff := hContDiff
    stepLengthPos := hStepPos
    hessianBounds := hHessianBounds
    strongWolfe := hStrongWolfe
    initialInverseHessian_eq_one := hInitial
    gradientNormLiminfPos := hLiminf
    gradientNormEventuallyPositive := hTail
  }
  exact ⟨result⟩

/-- Helper for TASK-16: a convenience bridge deriving the matrix denominator hypothesis from
strict positive secant curvature of the operator orbit. -/
theorem MatrixIdentityLiminfStrongWolfeCertificate.ofOperator_ofSecantCurvature
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate (Fin n) m M c₁ c₂)
    (hm : 0 < m) (hmM : m ≤ M)
    (hGradientNormLiminf : 0 < liminf (fun k ↦ ‖c.gradient k‖) atTop)
    (hPosDef : ∀ k, (canonicalMatrixSequence c.inverseHessian k).PosDef)
    (hSecant : ∀ k,
      0 < inner ℝ (c.gradient (k + 1) - c.gradient k)
        (c.point (k + 1) - c.point k)) :
    Nonempty (MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂) := by
  let H : ℕ → Matrix (Fin n) (Fin n) ℝ := canonicalMatrixSequence c.inverseHessian
  have hOrbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H := by
    have hOrbitExplicit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient
      (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (c.inverseHessian k)) :=
      c.toIdentityInitializedOperatorCertificate.orbit.toMatrix
    have hSequenceEq : canonicalMatrixSequence c.inverseHessian =
        (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
          (c.inverseHessian k)) := by
      exact canonicalMatrixSequence_eq_explicit c.inverseHessian
    dsimp only [H]
    rw [hSequenceEq]
    exact hOrbitExplicit
  have hDenominator : ∀ k,
      WithLp.ofLp (DFP.steps c.stepLength (DFP.directions H c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0 := by
    exact hOrbit.secantDenominator_ne_of_secantCurvature_pos hSecant
  have hDenominator' : ∀ k,
      WithLp.ofLp
          (DFP.steps c.stepLength
            (DFP.directions (canonicalMatrixSequence c.inverseHessian) c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0 := by
    intro k
    simpa only [H] using hDenominator k
  exact MatrixIdentityLiminfStrongWolfeCertificate.ofOperator c hm hmM
    hGradientNormLiminf hPosDef hDenominator'

/-- Helper for TASK-16: assemble the matrix-facing liminf certificate from identity initialization
and strict positive secant curvature.  The existing matrix bridge derives
positive definiteness and all nonzero DFP denominators; no gradient-norm
convergence hypothesis is used. -/
theorem MatrixIdentityLiminfStrongWolfeCertificate.ofOperator_ofIdentityAndSecantCurvature
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate (Fin n) m M c₁ c₂)
    (hm : 0 < m) (hmM : m ≤ M)
    (hGradientNormLiminf : 0 < liminf (fun k ↦ ‖c.gradient k‖) atTop)
    (hSecant : ∀ k,
      0 < inner ℝ (c.gradient (k + 1) - c.gradient k)
        (c.point (k + 1) - c.point k)) :
    Nonempty (MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂) := by
  have hPosDefCanonical : ∀ k,
      (canonicalMatrixSequence c.inverseHessian k).PosDef :=
    canonicalMatrixSequence_posDef_of_identityOrbit c hSecant
  have hPosDef : ∀ k,
      (canonicalMatrixSequence c.inverseHessian k).PosDef :=
    hPosDefCanonical
  have hDenominatorCanonical : ∀ k,
      WithLp.ofLp
          (DFP.steps c.stepLength
            (DFP.directions (canonicalMatrixSequence c.inverseHessian) c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0 :=
    canonicalMatrixSequence_denominator_ne_of_operatorOrbit c.orbit hSecant
  have hDenominator : ∀ k,
      WithLp.ofLp
          (DFP.steps c.stepLength
          (DFP.directions (canonicalMatrixSequence c.inverseHessian) c.gradient) k) ⬝ᵥ
      WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0 :=
    hDenominatorCanonical
  exact MatrixIdentityLiminfStrongWolfeCertificate.ofOperator c hm hmM
    hGradientNormLiminf hPosDef hDenominator

end DFP.WolfeCounterexample

end
