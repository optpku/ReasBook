module

public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedIdentityInitialization
public import ReasLib.Optimization.DFP.Operator.Matrix
public import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
/-!
# Matrix-facing identity initialization

This module is the representation bridge for the identity-initialized
operator certificate.  The canonical Euclidean matrix sequence is obtained by
the existing `Matrix.toEuclideanCLM` equivalence, and the existing orbit
adapter then supplies a classical `DFP.InverseIteration`.  Positivity and
secant nondegeneracy are explicit inputs to this bridge: the operator-level
certificate deliberately does not claim either property for every later
iterate.
-/

public section

noncomputable section

universe u

open Filter
open scoped InnerProduct MatrixOrder Topology

namespace DFP.WolfeCounterexample

/- The canonical matrix representation of an operator sequence. -/

/-- Represent an operator sequence in the canonical
orthonormal Euclidean basis. -/
noncomputable def canonicalMatrixSequence
    {n : ℕ} (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ℕ → Matrix (Fin n) (Fin n) ℝ :=
  fun k ↦
    (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm (H k)

/-- Evaluation of the canonical matrix representation at
an iteration index. -/
theorem canonicalMatrixSequence_apply
    {n : ℕ}
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (k : ℕ) :
    canonicalMatrixSequence H k =
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm (H k) := by
  rfl

/-- An operator initialized at the identity has identity as its initial canonical
matrix representation. -/
theorem canonicalMatrixSequence_zero_eq_one
    {n : ℕ}
    {H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hH : H 0 = 1) :
    canonicalMatrixSequence H 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [canonicalMatrixSequence_apply, hH, map_one]

/-- A classical matrix DFP counterexample with identity initialization and an
explicit positive lower tail for its gradient norm. -/
structure MatrixIdentityStrongWolfeCertificate
    (n : ℕ) (m M c₁ c₂ : ℝ)
    extends DFP.StrongWolfeCounterexample (Fin n) m M c₁ c₂ where
  initialInverseHessian_eq_one : iteration.inverseHessian 0 =
    (1 : Matrix (Fin n) (Fin n) ℝ)
  gradientNormEventuallyPositive : ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients iteration.objective iteration.point k‖

/-- The positive gradient-norm limit of a matrix certificate is also its filter liminf. -/
theorem MatrixIdentityStrongWolfeCertificate.gradientNormLiminf_pos
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : MatrixIdentityStrongWolfeCertificate n m M c₁ c₂) :
    0 < liminf
      (fun k ↦ ‖DFP.gradients c.iteration.objective c.iteration.point k‖) atTop := by
  rw [c.gradientNormTendsto.liminf_eq]
  exact c.gradientLimitPos

/-- Strict positivity of a self-adjoint operator implies positive
definiteness of its canonical real matrix. -/
theorem canonicalMatrix_posDef_of_operatorStrictPositive
    {n : ℕ} {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hAself : IsSelfAdjoint A)
    (hApos : ∀ z ≠ 0, 0 < inner ℝ z (A z)) :
    (canonicalMatrixSequence (fun _ ↦ A) 0).PosDef := by
  let B : Matrix (Fin n) (Fin n) ℝ := canonicalMatrixSequence (fun _ ↦ A) 0
  have hBoperator :
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) B = A := by
    dsimp only [B, canonicalMatrixSequence]
    simp only [StarAlgEquiv.apply_symm_apply]
  have hBhermitian : B.IsHermitian := by
    rw [← Matrix.isSymmetric_toEuclideanLin_iff]
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    have hself : IsSelfAdjoint
        ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) B) := by
      rw [hBoperator]
      exact hAself
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hBhermitian
  intro v hv
  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    apply WithLp.toLp_injective 2
    simpa only [z, WithLp.toLp_zero] using hz0
  have hpositive : 0 < inner ℝ z
      ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) B z) := by
    rw [hBoperator]
    exact hApos z hz
  simpa only [Matrix.inner_toEuclideanCLM, star_trivial] using hpositive

/-- An identity-initialized operator orbit has positive-definite canonical
matrices at every step when its secant curvature is strictly positive. -/
theorem canonicalMatrixSequence_posDef_of_identityOrbit
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate (Fin n) m M c₁ c₂)
    (hSecant : ∀ k,
      0 < inner ℝ (c.gradient (k + 1) - c.gradient k)
        (c.point (k + 1) - c.point k)) :
    ∀ k, (canonicalMatrixSequence c.inverseHessian k).PosDef := by
  let H : ℕ → Matrix (Fin n) (Fin n) ℝ := canonicalMatrixSequence c.inverseHessian
  have hOrbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H :=
    c.orbit.toMatrix
  have hCurvature (k : ℕ) :
      0 <
        WithLp.ofLp (DFP.steps c.stepLength (DFP.directions H c.gradient) k) ⬝ᵥ
          WithLp.ofLp (DFP.gradientChanges c.gradient k) := by
    have hStep : DFP.steps c.stepLength (DFP.directions H c.gradient) k =
        c.point (k + 1) - c.point k := by
      rw [hOrbit.pointSucc k]
      abel
    have hChange : DFP.gradientChanges c.gradient k =
        c.gradient (k + 1) - c.gradient k := by
      rw [DFP.gradientChanges_apply]
    have hInner :
        inner ℝ (c.gradient (k + 1) - c.gradient k)
            (c.point (k + 1) - c.point k) =
          WithLp.ofLp (c.point (k + 1) - c.point k) ⬝ᵥ
            WithLp.ofLp (c.gradient (k + 1) - c.gradient k) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [star_trivial, dotProduct_comm]
    rw [hStep, hChange]
    rw [← hInner]
    exact hSecant k
  intro k
  induction k with
  | zero =>
      have hInitial := canonicalMatrixSequence_zero_eq_one
        (H := c.inverseHessian) c.initialInverseHessian_eq_one
      simpa only [H] using hInitial ▸ (Matrix.PosDef.one :
        (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)
  | succ k ih =>
      have hRec := hOrbit.inverseHessianSucc k
      change (H (k + 1)).PosDef
      rw [hRec]
      exact Matrix.PosDef.inverseDFPUpdate ih (hCurvature k)

/-- Helper for an arbitrary invertible coordinate factor sends the identity operator to a
strictly positive canonical matrix. -/
theorem canonicalMatrix_posDef_of_pushforward_one
    {n : ℕ} (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (canonicalMatrixSequence
      (fun _ ↦ L.toContinuousLinearMap.pushforward 1) 0).PosDef := by
  apply canonicalMatrix_posDef_of_operatorStrictPositive
  · rw [ContinuousLinearMap.pushforward_one]
    exact (ContinuousLinearMap.isPositive_self_comp_adjoint
      L.toContinuousLinearMap).isSelfAdjoint
  · intro z hz
    have hAdjoint : (L.toContinuousLinearMap†) z ≠ 0 := by
      intro hzero
      have hcancel := congrArg
        (fun w ↦ (L.symm.toContinuousLinearMap†) w) hzero
      have hzero' : z = 0 := by
        simpa only [ContinuousLinearMap.map_zero,
          ContinuousLinearEquiv.adjoint_symm_apply_adjoint] using hcancel
      exact hz hzero'
    rw [ContinuousLinearMap.pushforward_one]
    change 0 < inner ℝ z
      (L.toContinuousLinearMap ((L.toContinuousLinearMap†) z))
    rw [← L.toContinuousLinearMap.adjoint_inner_left]
    exact real_inner_self_pos.mpr hAdjoint

/-- A strictly positive secant pairing along an operator orbit supplies the
nonzero denominator for its canonical matrix orbit. -/
theorem canonicalMatrixSequence_denominator_ne_of_operatorOrbit
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin n)}
    {H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hOrbit : DFP.Operator.IsOrbit f α x g H)
    (hSecant : ∀ k,
      0 < inner ℝ (g (k + 1) - g k) (x (k + 1) - x k)) :
    ∀ k,
      WithLp.ofLp
          (DFP.steps α (DFP.directions (canonicalMatrixSequence H) g) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges g k) ≠ 0 := by
  have hMatrixOrbit : DFP.IsOrbit f α x g (canonicalMatrixSequence H) := hOrbit.toMatrix
  exact hMatrixOrbit.secantDenominator_ne_of_secantCurvature_pos hSecant

/-- Helper for cor:identity-initialization: an operator certificate with positive-definite
canonical matrices and nonzero secant denominators yields a matrix identity certificate. -/
theorem MatrixIdentityStrongWolfeCertificate.ofOperator
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate (Fin n) m M c₁ c₂)
    (hGradientNormTendsto : Tendsto (fun k ↦ ‖c.gradient k‖) atTop
      (𝓝 c.gradientLimit))
    (hPosDef : ∀ k, (canonicalMatrixSequence c.inverseHessian k).PosDef)
    (hDenominator : ∀ k,
      WithLp.ofLp
          (DFP.steps c.stepLength
            (DFP.directions (canonicalMatrixSequence c.inverseHessian) c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0) :
    Nonempty (MatrixIdentityStrongWolfeCertificate n m M c₁ c₂) := by
  let H : ℕ → Matrix (Fin n) (Fin n) ℝ := canonicalMatrixSequence c.inverseHessian
  have hOrbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H :=
    c.orbit.toMatrix
  let iteration : DFP.InverseIteration (Fin n) :=
    hOrbit.toInverseIteration hPosDef hDenominator
  have hObjective : iteration.objective = c.objective :=
    hOrbit.toInverseIteration_objective hPosDef hDenominator
  have hStepLength : iteration.stepLength = c.stepLength :=
    hOrbit.toInverseIteration_stepLength hPosDef hDenominator
  have hPoint : iteration.point = c.point :=
    hOrbit.toInverseIteration_point_eq hPosDef hDenominator
  have hGradientEq : DFP.gradients iteration.objective iteration.point = c.gradient := by
    rw [hObjective, hPoint]
    exact hOrbit.gradients_eq
  have hContDiff : ContDiff ℝ 2 iteration.objective := by
    rw [hObjective]
    exact c.objectiveContDiff
  have hStepPos : ∀ k, 0 < iteration.stepLength k := by
    intro k
    rw [hStepLength]
    exact c.orbit.stepLengthPos k
  have hWeakWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    intro k
    rw [hObjective, hPoint]
    exact c.weakWolfeLegacy k
  have hStrongWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    intro k
    rw [hObjective, hPoint]
    exact c.strongWolfe k
  have hGradientNormTendsto' : Tendsto
      (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖)
      atTop (𝓝 c.gradientLimit) := by
    rw [hGradientEq]
    exact hGradientNormTendsto
  have hInitial : iteration.inverseHessian 0 =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hOrbit.toInverseIteration_inverseHessian]
    exact canonicalMatrixSequence_zero_eq_one c.initialInverseHessian_eq_one
  have hTail : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients iteration.objective iteration.point k‖ := by
    rw [hGradientEq]
    exact c.gradientNormEventuallyPositive
  have hHessianBounds : HasHessianBounds m M iteration.objective := by
    rw [hObjective]
    exact c.hessianBounds
  let weak : DFP.WolfeCounterexample (Fin n) m M c₁ c₂ := {
    iteration := iteration
    gradientLimit := c.gradientLimit
    objectiveContDiff := hContDiff
    stepLengthPos := hStepPos
    hessianBounds := hHessianBounds
    weakWolfe := hWeakWolfe
    gradientLimitPos := c.gradientLimitPos
    gradientNormTendsto := hGradientNormTendsto'
  }
  let strong : DFP.StrongWolfeCounterexample (Fin n) m M c₁ c₂ :=
    { toWolfeCounterexample := weak
      strongWolfe := hStrongWolfe }
  exact ⟨{
    toStrongWolfeCounterexample := strong
    initialInverseHessian_eq_one := hInitial
    gradientNormEventuallyPositive := hTail
  }⟩

/-- Helper for cor:identity-initialization: positive secant curvature supplies the
nonzero denominators required by the matrix identity certificate. -/
theorem MatrixIdentityStrongWolfeCertificate.ofOperator_ofSecantCurvature
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate (Fin n) m M c₁ c₂)
    (hGradientNormTendsto : Tendsto (fun k ↦ ‖c.gradient k‖) atTop
      (𝓝 c.gradientLimit))
    (hPosDef : ∀ k, (canonicalMatrixSequence c.inverseHessian k).PosDef)
    (hSecant : ∀ k,
      0 < inner ℝ (c.gradient (k + 1) - c.gradient k)
        (c.point (k + 1) - c.point k)) :
    Nonempty (MatrixIdentityStrongWolfeCertificate n m M c₁ c₂) := by
  exact MatrixIdentityStrongWolfeCertificate.ofOperator c hGradientNormTendsto hPosDef
    (canonicalMatrixSequence_denominator_ne_of_operatorOrbit c.orbit hSecant)

/-- Helper for cor:identity-initialization: identity initialization and positive secant
curvature give positive-definite matrices and a matrix identity certificate. -/
theorem MatrixIdentityStrongWolfeCertificate.ofOperator_ofIdentityAndSecantCurvature
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate (Fin n) m M c₁ c₂)
    (hGradientNormTendsto : Tendsto (fun k ↦ ‖c.gradient k‖) atTop
      (𝓝 c.gradientLimit))
    (hSecant : ∀ k,
      0 < inner ℝ (c.gradient (k + 1) - c.gradient k)
        (c.point (k + 1) - c.point k)) :
    Nonempty (MatrixIdentityStrongWolfeCertificate n m M c₁ c₂) := by
  have hPosDef : ∀ k,
      (canonicalMatrixSequence c.inverseHessian k).PosDef :=
    canonicalMatrixSequence_posDef_of_identityOrbit c hSecant
  have hDenominator : ∀ k,
      WithLp.ofLp
          (DFP.steps c.stepLength
            (DFP.directions (canonicalMatrixSequence c.inverseHessian) c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0 :=
    canonicalMatrixSequence_denominator_ne_of_operatorOrbit c.orbit hSecant
  exact MatrixIdentityStrongWolfeCertificate.ofOperator c hGradientNormTendsto hPosDef
    hDenominator

end DFP.WolfeCounterexample
