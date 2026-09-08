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

/-- Helper for TASK-13: represent an operator sequence in the canonical
orthonormal Euclidean basis. -/
noncomputable def canonicalMatrixSequence
    {n : ℕ} (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ℕ → Matrix (Fin n) (Fin n) ℝ :=
  fun k ↦
    (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm (H k)

/-- Helper for TASK-13: evaluation of the canonical matrix representation at
an iteration index. -/
theorem canonicalMatrixSequence_apply
    {n : ℕ}
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (k : ℕ) :
    canonicalMatrixSequence H k =
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm (H k) := by
  rfl

/-- Helper for TASK-13: identity of an operator is identity of its canonical
matrix representation. -/
theorem canonicalMatrixSequence_zero_eq_one
    {n : ℕ}
    {H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hH : H 0 = 1) :
    canonicalMatrixSequence H 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  apply EquivLike.injective
    (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  change (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm (H 0)) =
    (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) 1
  rw [StarAlgEquiv.apply_symm_apply, hH]
  simp only [map_one]

/-- TASK-13: a classical matrix DFP counterexample with identity initialization and an
explicit positive lower tail for its gradient norm. -/
structure MatrixIdentityStrongWolfeCertificate
    (n : ℕ) (m M c₁ c₂ : ℝ)
    extends DFP.StrongWolfeCounterexample (Fin n) m M c₁ c₂ where
  initialInverseHessian_eq_one : iteration.inverseHessian 0 =
    (1 : Matrix (Fin n) (Fin n) ℝ)
  gradientNormEventuallyPositive : ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients iteration.objective iteration.point k‖

/-- Helper for TASK-13: the eventual positive gradient tail of a matrix certificate implies the
corresponding strict positivity of its filter liminf. -/
theorem MatrixIdentityStrongWolfeCertificate.gradientNormLiminf_pos
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : MatrixIdentityStrongWolfeCertificate n m M c₁ c₂) :
    0 < liminf
      (fun k ↦ ‖DFP.gradients c.iteration.objective c.iteration.point k‖) atTop := by
  obtain ⟨δ, hδ, htail⟩ := c.gradientNormEventuallyPositive
  have hTendsto : Tendsto
      (fun k ↦ ‖DFP.gradients c.iteration.objective c.iteration.point k‖)
      atTop (𝓝 c.gradientLimit) := c.gradientNormTendsto
  have hbounded : atTop.IsBoundedUnder (· ≤ ·)
      (fun k ↦ ‖DFP.gradients c.iteration.objective c.iteration.point k‖) :=
    hTendsto.isBoundedUnder_le
  have hcobounded : atTop.IsCoboundedUnder (· ≥ ·)
      (fun k ↦ ‖DFP.gradients c.iteration.objective c.iteration.point k‖) :=
    hbounded.isCoboundedUnder_ge
  have hδlim : δ ≤ liminf
      (fun k ↦ ‖DFP.gradients c.iteration.objective c.iteration.point k‖) atTop :=
    le_liminf_of_le hcobounded htail
  exact lt_of_lt_of_le hδ hδlim

/-- Helper for TASK-13: convert strict positivity of a self-adjoint operator into positive
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

/-- Helper for TASK-13: the identity-initialized operator orbit has positive-definite canonical
matrices at every step when its secant curvature is strictly positive. -/
theorem canonicalMatrixSequence_posDef_of_identityOrbit
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate (Fin n) m M c₁ c₂)
    (hSecant : ∀ k,
      0 < inner ℝ (c.gradient (k + 1) - c.gradient k)
        (c.point (k + 1) - c.point k)) :
    ∀ k, (canonicalMatrixSequence c.inverseHessian k).PosDef := by
  let H : ℕ → Matrix (Fin n) (Fin n) ℝ := canonicalMatrixSequence c.inverseHessian
  have hOrbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H := by
    change DFP.IsOrbit c.objective c.stepLength c.point c.gradient
      (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (c.inverseHessian k))
    exact c.toIdentityInitializedOperatorCertificate.orbit.toMatrix
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

/-- Helper for TASK-13: an arbitrary invertible coordinate factor sends the identity operator to a
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

/-- Helper for TASK-13: a strictly positive secant pairing along an operator orbit supplies the
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
  let Hmat : ℕ → Matrix (Fin n) (Fin n) ℝ := canonicalMatrixSequence H
  have hMatrixOrbit : DFP.IsOrbit f α x g Hmat := by
    change DFP.IsOrbit f α x g
      (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (H k))
    exact hOrbit.toMatrix
  have hDenominator : ∀ k,
      WithLp.ofLp (DFP.steps α (DFP.directions Hmat g) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges g k) ≠ 0 :=
    hMatrixOrbit.secantDenominator_ne_of_secantCurvature_pos hSecant
  intro k
  simpa only [Hmat] using hDenominator k

/-- Helper for TASK-13: assemble a matrix-facing identity certificate from an operator certificate
when the canonical matrix sequence has the required positive definiteness and
nonzero DFP secant denominators. -/
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
  have hOrbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H := by
    change DFP.IsOrbit c.objective c.stepLength c.point c.gradient
      (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (c.inverseHessian k))
    exact c.toIdentityInitializedOperatorCertificate.orbit.toMatrix
  let orbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H := hOrbit
  let iteration : DFP.InverseIteration (Fin n) :=
    orbit.toInverseIteration hPosDef hDenominator
  have hObjective : iteration.objective = c.objective := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective] using rfl
  have hStepLength : ∀ k, iteration.stepLength k = c.stepLength k := by
    intro k
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_stepLength] using rfl
  have hPoint : ∀ k, iteration.point k = c.point k := by
    intro k
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_point] using rfl
  have hContDiff : ContDiff ℝ 2 iteration.objective := by
    rw [hObjective]
    exact c.objectiveContDiff
  have hStepPos : ∀ k, 0 < iteration.stepLength k := by
    intro k
    rw [hStepLength k]
    exact c.toIdentityInitializedOperatorCertificate.orbit.stepLengthPos k
  have hWeakWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    intro k
    rw [hObjective, hPoint k, hPoint (k + 1)]
    exact c.weakWolfeLegacy k
  have hStrongWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    intro k
    rw [hObjective, hPoint k, hPoint (k + 1)]
    exact c.strongWolfe k
  have hGradientNormTendsto' : Tendsto
      (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖)
      atTop (𝓝 c.gradientLimit) := by
    have hGradientEq : DFP.gradients c.objective c.point = c.gradient :=
      orbit.gradients_eq
    have hObjectiveEq : iteration.objective = c.objective := hObjective
    have hPointEq : iteration.point = c.point := by
      simpa only [iteration, DFP.IsOrbit.toInverseIteration_point_eq] using rfl
    have hGradientCanonical :
        DFP.gradients iteration.objective iteration.point = c.gradient := by
      rw [hObjectiveEq, hPointEq]
      exact hGradientEq
    have hNormEq :
        (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖) =
          (fun k ↦ ‖c.gradient k‖) := by
      funext k
      rw [hGradientCanonical]
    rw [hNormEq]
    exact hGradientNormTendsto
  have hInitial : iteration.inverseHessian 0 =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have hMatrixInitial := canonicalMatrixSequence_zero_eq_one
      (H := c.inverseHessian) c.initialInverseHessian_eq_one
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_inverseHessian] using hMatrixInitial
  have hTail : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients iteration.objective iteration.point k‖ := by
    obtain ⟨δ, hδ, htail⟩ := c.gradientNormEventuallyPositive
    refine ⟨δ, hδ, ?_⟩
    have hGradientEq : DFP.gradients c.objective c.point = c.gradient :=
      orbit.gradients_eq
    have hObjectiveEq : iteration.objective = c.objective := hObjective
    have hPointEq : iteration.point = c.point := by
      simpa only [iteration, DFP.IsOrbit.toInverseIteration_point_eq] using rfl
    have hGradientCanonical :
        DFP.gradients iteration.objective iteration.point = c.gradient := by
      rw [hObjectiveEq, hPointEq]
      exact hGradientEq
    filter_upwards [htail] with k hk
    rw [hGradientCanonical]
    exact hk
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
  have hStrongLegacy : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ weak.iteration.objective
      (weak.iteration.point k)
      (weak.iteration.point (k + 1) - weak.iteration.point k) := by
    intro k
    simpa only [weak] using hStrongWolfe k
  let strong : DFP.StrongWolfeCounterexample (Fin n) m M c₁ c₂ :=
    { toWolfeCounterexample := weak
      strongWolfe := hStrongLegacy }
  have hInitialStrong : strong.iteration.inverseHessian 0 =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    dsimp only [strong]
    exact hInitial
  have hTailStrong : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients strong.iteration.objective strong.iteration.point k‖ := by
    dsimp only [strong]
    exact hTail
  exact ⟨{
    toStrongWolfeCounterexample := strong
    initialInverseHessian_eq_one := hInitialStrong
    gradientNormEventuallyPositive := hTailStrong
  }⟩

/-- Helper for TASK-13: assemble a matrix-facing identity certificate from positive secant
curvature; the curvature lemma supplies the denominator side condition needed
by `InverseIteration`. -/
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
  let H : ℕ → Matrix (Fin n) (Fin n) ℝ := canonicalMatrixSequence c.inverseHessian
  have hOrbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H := by
    change DFP.IsOrbit c.objective c.stepLength c.point c.gradient
      (fun k ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).symm
        (c.inverseHessian k))
    exact c.toIdentityInitializedOperatorCertificate.orbit.toMatrix
  let orbit : DFP.IsOrbit c.objective c.stepLength c.point c.gradient H := hOrbit
  have hDenominator : ∀ k,
      WithLp.ofLp (DFP.steps c.stepLength (DFP.directions H c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0 :=
    orbit.secantDenominator_ne_of_secantCurvature_pos hSecant
  have hDenominator' : ∀ k,
      WithLp.ofLp
          (DFP.steps c.stepLength
            (DFP.directions (canonicalMatrixSequence c.inverseHessian) c.gradient) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges c.gradient k) ≠ 0 := by
    intro k
    simpa only [H] using hDenominator k
  exact MatrixIdentityStrongWolfeCertificate.ofOperator c hGradientNormTendsto hPosDef
    hDenominator'

/-- Helper for TASK-13: assemble the matrix-facing certificate using only the operator orbit's
strict secant curvature.  The preceding identity-orbit lemmas derive both the
matrix positive-definiteness and the DFP denominator conditions. -/
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
