/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Order.Filter.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Notation_7_1_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2.DifferentialData
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2.NormalEquation
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_6.ArmijoSequence

noncomputable section

open Filter Matrix
open scoped LeastSquares

section

variable {m n : ℕ}

-- Local declaration justification (source-local notation): the theorem uses the chapter's fixed
-- Euclidean parameter space notation while the reusable least-squares owners now come from
-- `Theorem_7_2_2`.
local notation "Point" => EuclideanSpace ℝ (Fin n)
-- Local declaration justification (source-local notation): the residual codomain shorthand is
-- kept local to preserve the source-facing theorem text.
local notation "Residual" => EuclideanSpace ℝ (Fin m)

/-- Helper for Chapter07 Theorem 7.3.6: composing two Euclidean matrix actions is the same as
acting by the product matrix. -/
private theorem toEuclideanLin_mul_apply
    {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) =
      Matrix.toEuclideanLin (A * B) v := by
  -- Move once to coordinates, where this is the standard `mulVec` associativity identity.
  apply WithLp.ofLp_injective
  simp [Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal)), Matrix.mulVec_mulVec]

/-- Helper for Chapter07 Theorem 7.3.6: the scaled Levenberg-Marquardt direction is the negative
inverse regularized normal matrix applied to the Chapter 7 gradient. -/
private theorem scaledDirection_eq_neg_inv_apply_gradient
    (r : Point → Residual) (D : Point → MatrixN n) (μ : ℝ) (x : Point) :
    scaledLevenbergMarquardtDirection (residualJacobianMatrix r) r D μ x =
      -Matrix.toEuclideanLin
        ((gaussNewtonNormalMatrix r x + μ • D x)⁻¹)
        (g[r](x)) := by
  -- Route correction: normalize the step once through `g[r](x) = J(x)ᵀ r(x)` so later proofs
  -- compare only against the inverse regularized normal matrix.
  rw [scaledLevenbergMarquardtDirection_eq, gaussNewtonNormalMatrix_eq]
  congr 1
  rw [← toEuclideanLin_mul_apply]
  simp [leastSquaresGradient, scaledLevenbergMarquardtRegularizedNormalMatrix]

/-- Helper for Chapter07 Theorem 7.3.6: the Chapter 7 gradient owner is the adjoint of the
residual derivative applied to the residual vector. -/
private theorem leastSquaresGradient_eq_fderivAdjoint_apply
    (r : Point → Residual) (x : Point) :
    g[r](x) = (fderiv ℝ r x).adjoint (r x) := by
  let pointBasis := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let residualBasis := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  have hJacobianLin :
      Matrix.toEuclideanLin (J[r](x)) = (fderiv ℝ r x).toLinearMap := by
    -- The stored Jacobian matrix is exactly the matrix representation of `fderiv r x`.
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    simpa [pointBasis, residualBasis, residualJacobianMatrix] using
      (Matrix.toLin_toMatrix pointBasis residualBasis (fderiv ℝ r x).toLinearMap)
  calc
    g[r](x) = Matrix.toEuclideanLin ((J[r](x))ᵀ) (r x) := by rfl
    _ = ((Matrix.toEuclideanLin (J[r](x))).adjoint) (r x) := by
          simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
            congrArg (fun L : Residual →ₗ[ℝ] Point ↦ L (r x))
              (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := J[r](x)))
    _ = ((fderiv ℝ r x).toLinearMap.adjoint) (r x) := by rw [hJacobianLin]
    _ = ((fderiv ℝ r x).adjoint.toLinearMap) (r x) := by
          rw [ContinuousLinearMap.adjoint_toLinearMap]
    _ = (fderiv ℝ r x).adjoint (r x) := rfl

/-- Helper for Chapter07 Theorem 7.3.6: a `C¹` residual map induces a differentiable nonlinear
least-squares objective. -/
private theorem leastSquaresObjective_differentiableAt_of_contDiffAt
    (r : Point → Residual) {x : Point} (hr : ContDiffAt ℝ 1 r x) :
    DifferentiableAt ℝ (nonlinearLeastSquaresObjective r) x := by
  -- Differentiate the half-squared residual norm through the local `C¹` residual map.
  have hResidualDiff : DifferentiableAt ℝ r x := hr.differentiableAt (by norm_num)
  have hResidualDeriv : HasFDerivAt r (fderiv ℝ r x) x := hResidualDiff.hasFDerivAt
  have hNormSq :
      HasFDerivAt (fun y : Point ↦ ‖r y‖ ^ (2 : ℕ))
        (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x) x := by
    simpa using hResidualDeriv.norm_sq
  have hObjectiveRaw :
      HasFDerivAt (fun y : Point ↦ ((1 : ℝ) / 2) * ‖r y‖ ^ (2 : ℕ))
        (((1 / 2 : ℝ) : ℝ) • (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x)) x := by
    simpa using hNormSq.const_mul ((1 / 2 : ℝ))
  have hObjectiveEq :
      nonlinearLeastSquaresObjective r = fun y : Point ↦ ((1 : ℝ) / 2) * ‖r y‖ ^ (2 : ℕ) := by
    ext y
    rw [nonlinearLeastSquaresObjective_eq_half_norm_sq]
  have hObjectiveDeriv :
      HasFDerivAt (nonlinearLeastSquaresObjective r)
        (((1 / 2 : ℝ) : ℝ) • (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x)) x := by
    -- Rewrite the objective once into the norm-square form used by the derivative rule.
    simpa [hObjectiveEq] using hObjectiveRaw
  exact hObjectiveDeriv.differentiableAt

/-- Helper for Chapter07 Theorem 7.3.6: the scaled Levenberg-Marquardt direction has nonpositive
pairing with the Chapter 7 least-squares gradient whenever the regularized normal matrix is
positive definite. -/
private theorem inner_gradient_scaledDirection_nonpos
    (r : Point → Residual) (D : Point → MatrixN n) {μ : ℝ} {x : Point}
    (hPosDef : (gaussNewtonNormalMatrix r x + μ • D x).PosDef) :
    inner ℝ (g[r](x))
      (scaledLevenbergMarquardtDirection (residualJacobianMatrix r) r D μ x) ≤ 0 := by
  have hDirEq :
      scaledLevenbergMarquardtDirection
          (residualJacobianMatrix r) r D μ x =
        -Matrix.toEuclideanLin
          ((gaussNewtonNormalMatrix r x + μ • D x)⁻¹)
          (g[r](x)) :=
    scaledDirection_eq_neg_inv_apply_gradient (r := r) (D := D) (μ := μ) (x := x)
  -- Normalize the direction once to the inverse-matrix action on the gradient vector.
  rw [hDirEq]
  by_cases hgx : g[r](x) = 0
  · simp [hgx]
  · have hgx' : (g[r](x)).ofLp ≠ 0 := by simpa using hgx
    have hquad :
        0 <
          dotProduct (g[r](x)).ofLp
            (((gaussNewtonNormalMatrix r x + μ • D x)⁻¹).mulVec
              (g[r](x)).ofLp) := by
      simpa [scaledLevenbergMarquardtRegularizedNormalMatrix, gaussNewtonNormalMatrix_eq] using
        hPosDef.inv.dotProduct_mulVec_pos hgx'
    have hInner :
        inner ℝ (g[r](x))
          (-Matrix.toEuclideanLin
            ((gaussNewtonNormalMatrix r x + μ • D x)⁻¹)
            (g[r](x))) <
          0 := by
      calc
        inner ℝ (g[r](x))
            (-Matrix.toEuclideanLin
              ((gaussNewtonNormalMatrix r x + μ • D x)⁻¹)
              (g[r](x)))
            =
              -dotProduct (g[r](x)).ofLp
                (((gaussNewtonNormalMatrix r x + μ • D x)⁻¹).mulVec
                  (g[r](x)).ofLp) := by
                    rw [PiLp.inner_apply, Matrix.toEuclideanLin_apply]
                    simp [dotProduct, mul_comm]
      _ < 0 := by
        exact neg_neg_of_pos hquad
    exact hInner.le

/-- Helper for Chapter07 Theorem 7.3.6: the Chapter 7 least-squares gradient converges along the
given convergent subsequence. -/
private theorem leastSquaresGradientSubseqTendsto
    (r : Point → Residual) (x : ℕ → Point) (φ : ℕ → ℕ) {xStar : Point}
    (hxStar : Tendsto (x ∘ φ) atTop (nhds xStar))
    (hr : ContDiffAt ℝ 1 r xStar) :
    Tendsto (fun i : ℕ ↦ g[r](x (φ i))) atTop (nhds (g[r](xStar))) := by
  have hResidual :
      Tendsto (fun i : ℕ ↦ r (x (φ i))) atTop (nhds (r xStar)) :=
    hr.continuousAt.tendsto.comp hxStar
  have hFDeriv :
      Tendsto (fun i : ℕ ↦ fderiv ℝ r (x (φ i))) atTop (nhds (fderiv ℝ r xStar)) :=
    (hr.continuousAt_fderiv (by norm_num)).tendsto.comp hxStar
  have hAdjoint :
      Tendsto (fun i : ℕ ↦ (fderiv ℝ r (x (φ i))).adjoint) atTop
        (nhds ((fderiv ℝ r xStar).adjoint)) := by
    -- Move the derivative through the continuous adjoint operator once.
    exact (ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp hFDeriv)
  have hApply :
      Tendsto
        (fun i : ℕ ↦ (fderiv ℝ r (x (φ i))).adjoint (r (x (φ i))))
        atTop
        (nhds ((fderiv ℝ r xStar).adjoint (r xStar))) := by
    -- Evaluate the convergent adjoint operators on the convergent residual vectors.
    exact
      (Continuous.clm_apply continuous_fst continuous_snd).continuousAt.tendsto.comp
        (hAdjoint.prodMk_nhds hResidual)
  simpa [leastSquaresGradient_eq_fderivAdjoint_apply] using hApply

/-- Helper for Chapter07 Theorem 7.3.6: inversion is continuous along any subsequence of
regularized normal matrices converging to a positive definite limit. -/
private theorem regularizedNormalInverseSubseqTendsto
    (A : ℕ → MatrixN n) {P : MatrixN n}
    (hP : P.PosDef) (hP_lim : Tendsto A atTop (nhds P)) :
    Tendsto (fun i : ℕ ↦ (A i)⁻¹) atTop (nhds P⁻¹) := by
  have hdet_ne : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit).ne_zero
  have hInvCont : ContinuousAt (fun M : MatrixN n ↦ M⁻¹) P := by
    -- Positive definiteness gives invertibility, so matrix inversion is continuous at `P`.
    refine continuousAt_matrix_inv P ?_
    simpa [Ring.inverse] using (continuousAt_inv₀ (x := P.det) hdet_ne)
  exact hInvCont.tendsto.comp hP_lim

/-- Helper for Chapter07 Theorem 7.3.6: the scaled Levenberg-Marquardt directions converge along
the chosen subsequence to the limit inverse action `-P⁻¹ g(xStar)`. -/
private theorem scaledDirectionSubseqTendsto
    (r : Point → Residual) (D : Point → MatrixN n)
    (x : ℕ → Point) (μ : ℕ → ℝ) (φ : ℕ → ℕ)
    {xStar : Point} {P : MatrixN n}
    (hxStar : Tendsto (x ∘ φ) atTop (nhds xStar))
    (hr : ContDiffAt ℝ 1 r xStar)
    (hP : P.PosDef)
    (hP_lim :
      Tendsto
        (fun i : ℕ ↦
          gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))
        atTop (nhds P)) :
    Tendsto
      (fun i : ℕ ↦
        scaledLevenbergMarquardtDirection
          (residualJacobianMatrix r) r D (μ (φ i)) (x (φ i)))
      atTop
      (nhds (-Matrix.toEuclideanLin P⁻¹ (g[r](xStar)))) := by
  have hGrad :
      Tendsto (fun i : ℕ ↦ g[r](x (φ i))) atTop (nhds (g[r](xStar))) :=
    leastSquaresGradientSubseqTendsto (r := r) (x := x) (φ := φ) hxStar hr
  have hInv :
      Tendsto
        (fun i : ℕ ↦
          (gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))⁻¹)
        atTop (nhds P⁻¹) :=
    regularizedNormalInverseSubseqTendsto
      (A := fun i : ℕ ↦ gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))
      hP hP_lim
  have hGradCoord :
      Tendsto
        (fun i : ℕ ↦ (g[r](x (φ i))).ofLp)
        atTop
        (nhds (g[r](xStar)).ofLp) := by
    -- Pass the Euclidean gradient limit through the coordinate chart once.
    change Tendsto (WithLp.ofLp ∘ fun i : ℕ ↦ g[r](x (φ i))) atTop (nhds (g[r](xStar)).ofLp)
    exact
      ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n ↦ ℝ)).tendsto _).comp hGrad
  have hCoord :
      Tendsto
        (fun i : ℕ ↦
          -((gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))⁻¹).mulVec
            ((g[r](x (φ i))).ofLp))
        atTop
        (nhds (-(P⁻¹).mulVec (g[r](xStar)).ofLp)) := by
    -- Compare the varying inverse matrices and gradient vectors at the raw coordinate level.
    exact
      ((Continuous.matrix_mulVec continuous_fst continuous_snd).neg.continuousAt.tendsto).comp
        (hInv.prodMk_nhds hGradCoord)
  have hExplicit :
      Tendsto
        (fun i : ℕ ↦
          -Matrix.toEuclideanLin
            ((gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))⁻¹)
            (g[r](x (φ i))))
        atTop
        (nhds (-Matrix.toEuclideanLin P⁻¹ (g[r](xStar)))) := by
    -- Transfer the coordinatewise convergence back to the Euclidean-point notation.
    have hToLp :
        Tendsto
          (fun i : ℕ ↦
            WithLp.toLp 2
              (-((gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))⁻¹).mulVec
                ((g[r](x (φ i))).ofLp)))
          atTop
          (nhds (WithLp.toLp 2 (-(P⁻¹).mulVec (g[r](xStar)).ofLp))) :=
      ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n ↦ ℝ)).tendsto _).comp hCoord
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hToLp
  have hEq :
      (fun i : ℕ ↦
        scaledLevenbergMarquardtDirection
          (residualJacobianMatrix r) r D (μ (φ i)) (x (φ i))) =ᶠ[atTop]
        (fun i : ℕ ↦
          -Matrix.toEuclideanLin
            ((gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))⁻¹)
            (g[r](x (φ i)))) :=
    Filter.Eventually.of_forall fun i : ℕ ↦
      scaledDirection_eq_neg_inv_apply_gradient
        (r := r) (D := D) (μ := μ (φ i)) (x := x (φ i))
  exact Tendsto.congr' hEq.symm hExplicit

/-- Helper for Chapter07 Theorem 7.3.6: the successor objective values along the chosen
subsequence are squeezed between two subsequences converging to the same limit. -/
private theorem successorObjectiveSubseqTendsto
    (f : Point → ℝ) (x : ℕ → Point) {xStar : Point} (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (hxStar : Tendsto (x ∘ φ) atTop (nhds xStar))
    (hfCont : ContinuousAt f xStar)
    (hStepMonotone : ∀ k : ℕ, f (x (k + 1)) ≤ f (x k)) :
    Tendsto (fun i : ℕ ↦ f (x (φ i + 1))) atTop (nhds (f xStar)) := by
  have hObjectiveSubseq :
      Tendsto (fun i : ℕ ↦ f (x (φ i))) atTop (nhds (f xStar)) :=
    hfCont.tendsto.comp hxStar
  have hObjectiveSubseqSucc :
      Tendsto (fun i : ℕ ↦ f (x (φ (i + 1)))) atTop (nhds (f xStar)) :=
    hObjectiveSubseq.comp (tendsto_add_atTop_nat 1)
  have hObjectiveAntitone : Antitone (fun k : ℕ ↦ f (x k)) :=
    antitone_nat_of_succ_le hStepMonotone
  -- Squeeze the intermediate successor term between two subsequences with the same limit.
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hObjectiveSubseqSucc hObjectiveSubseq ?_ ?_
  · intro i
    exact hObjectiveAntitone (Nat.succ_le_of_lt (hφ (Nat.lt_succ_self i)))
  · intro i
    exact hObjectiveAntitone (Nat.le_succ (φ i))

/-- Chapter07 Theorem 7.3.6: let `x_k` be a sequence generated by the scaled
Levenberg-Marquardt method with Armijo rule for the nonlinear least-squares objective attached to
`r`, using the canonical Chapter 7 Jacobian owner. If a subsequence `x ∘ φ` converges to `xStar`,
and the corresponding subsequence of regularized normal matrices
`gaussNewtonNormalMatrix r (x_(φ i)) + μ_(φ i) • D(x_(φ i))` converges to a positive definite
matrix `P`, the residual map is `C¹` at `xStar`, and each iterate `x_k` carries an actual
Jacobian in the source sense used by the Levenberg-Marquardt update, then the canonical
least-squares gradient at the
accumulation point vanishes: `g[r](xStar) = 0`. -/
theorem scaledLevenbergMarquardtArmijo_accumulationPoint_g_eq_zero
    (r : Point → Residual) (D : Point → MatrixN n)
    (x : ℕ → Point) (μ α : ℕ → ℝ) (mIndex : ℕ → ℕ)
    (run :
      IsScaledLevenbergMarquardtArmijoSequence
        (nonlinearLeastSquaresObjective r)
        (leastSquaresGradient r)
        (residualJacobianMatrix r) r D x μ α mIndex)
    {xStar : Point} {φ : ℕ → ℕ} {P : MatrixN n}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (x ∘ φ) atTop (nhds xStar))
    (hr : ContDiffAt ℝ 1 r xStar)
    (hJacobian_run : ∀ k : ℕ, DifferentiableAt ℝ r (x k))
    (hP : P.PosDef)
    (hP_lim :
      Tendsto
        (fun i : ℕ ↦
          gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))
        atTop (nhds P)) :
    g[r](xStar) = 0 := by
  let f : Point → ℝ := nonlinearLeastSquaresObjective r
  let A : ℕ → MatrixN n := fun i ↦
    gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i))
  let s : ℕ → Point := fun i ↦
    scaledLevenbergMarquardtDirection
      (residualJacobianMatrix r) r D (μ (φ i)) (x (φ i))
  have hObjectiveDiffAt (k : ℕ) : DifferentiableAt ℝ r (x k) := hJacobian_run k
  have hObjectiveGradientEq (k : ℕ) :
      gradient f (x k) = g[r](x k) :=
    leastSquaresObjective_gradient_eq (r := r) (x := x k) (hObjectiveDiffAt k)
  have hStepMonotone :
      ∀ k : ℕ, f (x (k + 1)) ≤ f (x k) := by
    intro k
    have hAccepts := run.acceptsAtExponent k
    rw [armijoAcceptsAtExponent_iff] at hAccepts
    have hParams := run.armijoParameters k
    have hDirEq :
        scaledLevenbergMarquardtDirection
            (residualJacobianMatrix r) r D (μ k) (x k) =
          -Matrix.toEuclideanLin
            ((gaussNewtonNormalMatrix r (x k) + μ k • D (x k))⁻¹)
            (g[r](x k)) :=
      scaledDirection_eq_neg_inv_apply_gradient (r := r) (D := D) (μ := μ k) (x := x k)
    have hInnerNonpos :
        inner ℝ (g[r](x k))
          (scaledLevenbergMarquardtDirection
            (residualJacobianMatrix r) r D (μ k) (x k)) ≤ 0 := by
      -- The helper isolates the positivity-to-descent calculation away from the Armijo algebra.
      exact
        inner_gradient_scaledDirection_nonpos
          (r := r) (D := D) (μ := μ k) (x := x k) (run.normalMatrix_posDef k)
    have hCorrectionNonpos :
        run.σ * (run.β ^ mIndex k) * 1 *
            inner ℝ (g[r](x k))
              (scaledLevenbergMarquardtDirection
                (residualJacobianMatrix r) r D (μ k) (x k)) ≤
          0 := by
      have hBetaNonneg : 0 ≤ run.β ^ mIndex k := le_of_lt (pow_pos hParams.beta_pos _)
      have hSigmaNonneg : 0 ≤ run.σ := le_of_lt hParams.rho_pos
      have hProdNonneg : 0 ≤ run.σ * (run.β ^ mIndex k) * 1 := by
        positivity
      exact mul_nonpos_of_nonneg_of_nonpos hProdNonneg hInnerNonpos
    have hUpdate :
        f (x (k + 1)) =
          f (x k + ((run.β ^ mIndex k) * 1) •
            scaledLevenbergMarquardtDirection
              (residualJacobianMatrix r) r D (μ k) (x k)) := by
      -- The stored update uses `α k = β^(m_k)` and the Armijo owner has `τ = 1`.
      simpa [run.step_length k, one_mul] using congrArg f (run.update_eq k)
    have hAccepts' :
        f (x (k + 1)) ≤
          f (x k) +
            run.σ * (run.β ^ mIndex k) * 1 *
              inner ℝ (g[r](x k))
                (scaledLevenbergMarquardtDirection
                  (residualJacobianMatrix r) r D (μ k) (x k)) := by
      simpa [hUpdate, one_mul, mul_assoc, mul_left_comm, mul_comm] using hAccepts
    linarith
  by_contra hgStar
  let gStar : Point := g[r](xStar)
  let sStar : Point := -Matrix.toEuclideanLin P⁻¹ gStar
  have hParams := run.armijoParameters 0
  have hObjectiveDiffAtStar :
      DifferentiableAt ℝ f xStar :=
    leastSquaresObjective_differentiableAt_of_contDiffAt (r := r) hr
  have hObjectiveContAtStar : ContinuousAt f xStar := hObjectiveDiffAtStar.continuousAt
  have hGradientEqStar : gradient f xStar = gStar := by
    -- Identify the objective gradient with the Chapter 7 least-squares gradient at `xStar`.
    simpa [gStar] using
      (leastSquaresObjective_gradient_eq
        (r := r) (x := xStar) (hr.differentiableAt (by norm_num)))
  have hGradAtStar : HasGradientAt f gStar xStar := by
    -- Reuse differentiability of the objective and rewrite the gradient through `gStar`.
    simpa [gStar, hGradientEqStar] using hObjectiveDiffAtStar.hasGradientAt
  have hGradientTendsto :
      Tendsto (fun i : ℕ ↦ g[r](x (φ i))) atTop (nhds gStar) :=
    leastSquaresGradientSubseqTendsto (r := r) (x := x) (φ := φ) hxStar hr
  have hDirectionTendsto :
      Tendsto (fun i : ℕ ↦ s i) atTop (nhds sStar) := by
    -- Package the inverse-matrix and gradient transports before entering the Armijo scalar route.
    simpa [A, s, sStar] using
      scaledDirectionSubseqTendsto
        (r := r) (D := D) (x := x) (μ := μ) (φ := φ)
        (hxStar := hxStar) (hr := hr) (hP := hP) (hP_lim := hP_lim)
  have hgStar_ne : gStar ≠ 0 := by
    simpa [gStar] using hgStar
  have hgStar_ne' : gStar.ofLp ≠ 0 := by
    simpa [gStar] using hgStar_ne
  have hDescent :
      inner ℝ gStar sStar < 0 := by
    -- Positive definiteness of `P⁻¹` turns the limiting search direction into a strict descent
    -- direction whenever `gStar ≠ 0`.
    have hquad :
        0 < dotProduct gStar.ofLp ((P⁻¹).mulVec gStar.ofLp) := by
      simpa [gStar] using hP.inv.dotProduct_mulVec_pos hgStar_ne'
    calc
      inner ℝ gStar sStar
          = -dotProduct gStar.ofLp ((P⁻¹).mulVec gStar.ofLp) := by
              show inner ℝ gStar (-Matrix.toEuclideanLin P⁻¹ gStar) =
                -dotProduct gStar.ofLp ((P⁻¹).mulVec gStar.ofLp)
              rw [PiLp.inner_apply, Matrix.toEuclideanLin_apply]
              simp [dotProduct, mul_comm, gStar]
      _ < 0 := by
        exact neg_neg_of_pos hquad
  let ψ : ℝ → ℝ :=
    lineSearchObjective f xStar sStar -
      fun t ↦ f xStar + t * (run.σ * inner ℝ gStar sStar)
  have hLineDeriv :
      HasDerivAt (lineSearchObjective f xStar sStar) (inner ℝ gStar sStar) 0 := by
    have hRay :
        HasDerivAt (fun t : ℝ ↦ xStar + t • sStar) sStar 0 := by
      simpa [one_smul] using ((hasDerivAt_id' (0 : ℝ)).smul_const sStar).const_add xStar
    have hGradAtZero : HasGradientAt f gStar (xStar + (0 : ℝ) • sStar) := by
      simpa [zero_smul] using hGradAtStar
    -- Differentiate the one-dimensional profile through the gradient witness at the limit point.
    change HasDerivAt (f ∘ fun t : ℝ ↦ xStar + t • sStar) (inner ℝ gStar sStar) 0
    simpa [InnerProductSpace.toDual_apply_apply] using
      hGradAtZero.hasFDerivAt.comp_hasDerivAt 0 hRay
  have hAffineDeriv :
      HasDerivAt (fun t : ℝ ↦ f xStar + t * (run.σ * inner ℝ gStar sStar))
        (run.σ * inner ℝ gStar sStar) 0 := by
    -- The Armijo comparison line is affine, so its slope is immediate.
    simpa using
      (((hasDerivAt_id' (0 : ℝ)).mul_const (run.σ * inner ℝ gStar sStar)).const_add (f xStar))
  have hψ :
      HasDerivAt ψ ((1 - run.σ) * inner ℝ gStar sStar) 0 := by
    have hSlope :
        inner ℝ gStar sStar - run.σ * inner ℝ gStar sStar =
          (1 - run.σ) * inner ℝ gStar sStar := by
      ring
    -- Subtract the affine comparison line from the line-search profile and normalize the slope.
    simpa [ψ, hSlope] using hLineDeriv.sub hAffineDeriv
  have hψ_neg : ((1 - run.σ) * inner ℝ gStar sStar) < 0 := by
    have hSigmaLtOne : run.σ < 1 := by linarith [hParams.rho_lt_half]
    nlinarith [hDescent]
  have hψ_zero : ψ 0 = 0 := by
    simp [ψ, lineSearchObjective_zero]
  obtain ⟨δ, hδ_pos, hδ_neg⟩ :=
    exists_posInterval_lt_zero_of_hasDerivAt_neg_zero hψ hψ_neg hψ_zero
  have hPowTendsto :
      Tendsto (fun m : ℕ ↦ run.β ^ m) atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hParams.beta_pos) hParams.beta_lt_one
  have hShiftContDiffNearZero :
      ∀ᶠ t : ℝ in nhds (0 : ℝ), ContDiffAt ℝ 1 r (xStar + t • sStar) := by
    have hLineCont :
        ContinuousAt (fun t : ℝ ↦ xStar + t • sStar) 0 := by
      simpa [one_smul] using
        (((hasDerivAt_id' (0 : ℝ)).smul_const sStar).const_add xStar).continuousAt
    have hContDiffAtZero :
        ∀ᶠ y : Point in nhds (xStar + (0 : ℝ) • sStar), ContDiffAt ℝ 1 r y := by
      simpa [zero_smul] using hr.eventually (by simp)
    exact hLineCont.tendsto.eventually hContDiffAtZero
  have hShiftContDiffPow :
      ∀ᶠ m : ℕ in atTop, ContDiffAt ℝ 1 r (xStar + run.β ^ m • sStar) := by
    exact hPowTendsto.eventually hShiftContDiffNearZero
  have hPowSmall :
      ∀ᶠ m : ℕ in atTop, run.β ^ m < δ := by
    exact hPowTendsto.eventually (Iio_mem_nhds hδ_pos)
  obtain ⟨mStar, hmSmall, hmShiftContDiff⟩ := (hPowSmall.and hShiftContDiffPow).exists
  have hPowPos : 0 < run.β ^ mStar := pow_pos hParams.beta_pos _
  have hTrialStrict :
      f (xStar + (run.β ^ mStar) • sStar) <
        f xStar + run.σ * (run.β ^ mStar) * inner ℝ gStar sStar := by
    -- The derivative argument gives a strict Armijo decrease at one fixed exponent `mStar`.
    have hψm : ψ (run.β ^ mStar) < 0 := hδ_neg (run.β ^ mStar) hPowPos hmSmall
    simpa [ψ, lineSearchObjective_apply, mul_assoc, mul_left_comm, mul_comm] using hψm
  have hAcceptsAtLimit :
      armijoAcceptsAtExponent f xStar sStar gStar run.β run.σ 1 mStar := by
    -- Strict decrease at the limit point implies Armijo acceptance at the frozen exponent.
    rw [armijoAcceptsAtExponent_iff]
    have hTrialStrict' :
        f (xStar + ((run.β ^ mStar) * 1) • sStar) <
          f xStar + run.σ * (run.β ^ mStar) * 1 * inner ℝ gStar sStar := by
      simpa [one_mul] using hTrialStrict
    linarith
  have hObjectiveContAtShift :
      ContinuousAt f (xStar + (run.β ^ mStar) • sStar) :=
    (leastSquaresObjective_differentiableAt_of_contDiffAt (r := r) hmShiftContDiff).continuousAt
  have hObjectiveSubseq :
      Tendsto (fun i : ℕ ↦ f (x (φ i))) atTop (nhds (f xStar)) :=
    hObjectiveContAtStar.tendsto.comp hxStar
  have hShiftObjectiveSubseq :
      Tendsto
        (fun i : ℕ ↦ f (x (φ i) + (run.β ^ mStar) • s i))
        atTop
        (nhds (f (xStar + (run.β ^ mStar) • sStar))) := by
    have hShiftPoints :
        Tendsto
          (fun i : ℕ ↦ x (φ i) + (run.β ^ mStar) • s i)
          atTop
          (nhds (xStar + (run.β ^ mStar) • sStar)) := by
      exact hxStar.add (hDirectionTendsto.const_smul (run.β ^ mStar))
    exact hObjectiveContAtShift.tendsto.comp hShiftPoints
  have hInnerSubseq :
      Tendsto
        (fun i : ℕ ↦ inner ℝ (g[r](x (φ i))) (s i))
        atTop
        (nhds (inner ℝ gStar sStar)) := by
    -- The gradient and direction limits give the limiting directional derivative term.
    exact
      continuous_inner.continuousAt.tendsto.comp
        (hGradientTendsto.prodMk_nhds hDirectionTendsto)
  have hGapSubseq :
      Tendsto
        (fun i : ℕ ↦
          f (x (φ i) + (run.β ^ mStar) • s i) -
            (f (x (φ i)) +
              run.σ * (run.β ^ mStar) * inner ℝ (g[r](x (φ i))) (s i)))
        atTop
        (nhds
          (f (xStar + (run.β ^ mStar) • sStar) -
            (f xStar + run.σ * (run.β ^ mStar) * inner ℝ gStar sStar))) := by
    -- Transport the fixed-exponent Armijo gap to the subsequence and subtract the limit terms.
    exact
      hShiftObjectiveSubseq.sub
        (hObjectiveSubseq.add
          (hInnerSubseq.const_mul (run.σ * (run.β ^ mStar))))
  have hGapEventuallyNeg :
      ∀ᶠ i : ℕ in atTop,
        f (x (φ i) + (run.β ^ mStar) • s i) -
            (f (x (φ i)) +
              run.σ * (run.β ^ mStar) * inner ℝ (g[r](x (φ i))) (s i)) < 0 := by
    have hGapLimitNeg :
        f (xStar + (run.β ^ mStar) • sStar) -
            (f xStar + run.σ * (run.β ^ mStar) * inner ℝ gStar sStar) < 0 := by
      linarith
    exact hGapSubseq.eventually (Iio_mem_nhds hGapLimitNeg)
  have hAcceptsEventually :
      ∀ᶠ i : ℕ in atTop,
        armijoAcceptsAtExponent
          f (x (φ i)) (s i) (g[r](x (φ i))) run.β run.σ 1 mStar := by
    -- The strict gap at the limit point persists along the subsequence by continuity.
    filter_upwards [hGapEventuallyNeg] with i hi
    rw [armijoAcceptsAtExponent_iff]
    have hi' :
        f (x (φ i) + ((run.β ^ mStar) * 1) • s i) <
          f (x (φ i)) +
            run.σ * (run.β ^ mStar) * 1 * inner ℝ (g[r](x (φ i))) (s i) := by
      simpa [one_mul] using hi
    linarith
  have hFrozenIndexBound :
      ∀ᶠ i : ℕ in atTop, mIndex (φ i) ≤ mStar := by
    -- Least acceptance of `mIndex (φ i)` forces it below the fixed accepted exponent `mStar`.
    filter_upwards [hAcceptsEventually] with i hi
    exact (run.armijoIndex (φ i)).le_of_accepts hi
  have hFrozenArmijo :
      ∀ᶠ i : ℕ in atTop,
        f (x (φ i + 1)) ≤
          f (x (φ i)) +
            run.σ * (run.β ^ mStar) * 1 * inner ℝ (g[r](x (φ i))) (s i) := by
    -- Compare the actual accepted exponent with the fixed one using the nonpositive descent
    -- pairing along the subsequence.
    filter_upwards [hFrozenIndexBound] with i hiBound
    have hAccepts := run.acceptsAtExponent (φ i)
    rw [armijoAcceptsAtExponent_iff] at hAccepts
    have hUpdate :
        f (x (φ i + 1)) =
          f (x (φ i) + ((run.β ^ mIndex (φ i)) * 1) • s i) := by
      simpa [s, run.step_length (φ i), one_mul] using congrArg f (run.update_eq (φ i))
    have hAcceptsStep :
        f (x (φ i + 1)) ≤
          f (x (φ i)) +
            run.σ * (run.β ^ mIndex (φ i)) * 1 *
              inner ℝ (g[r](x (φ i))) (s i) := by
      simpa [hUpdate, s, one_mul, mul_assoc, mul_left_comm, mul_comm] using hAccepts
    have hInnerNonpos :
        inner ℝ (g[r](x (φ i))) (s i) ≤ 0 := by
      simpa [s] using
        inner_gradient_scaledDirection_nonpos
          (r := r) (D := D) (μ := μ (φ i)) (x := x (φ i))
          (run.normalMatrix_posDef (φ i))
    have hPowLe :
        run.β ^ mStar ≤ run.β ^ mIndex (φ i) :=
      (pow_right_strictAnti₀ hParams.beta_pos hParams.beta_lt_one).le_iff_ge.2 hiBound
    have hFrozenCorrection :
        run.σ * (run.β ^ mIndex (φ i)) * 1 *
            inner ℝ (g[r](x (φ i))) (s i) ≤
          run.σ * (run.β ^ mStar) * 1 *
            inner ℝ (g[r](x (φ i))) (s i) := by
      have hScaledNonpos :
          run.σ * inner ℝ (g[r](x (φ i))) (s i) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hParams.rho_pos) hInnerNonpos
      nlinarith
    linarith
  have hSuccessorObjectiveSubseq :
      Tendsto (fun i : ℕ ↦ f (x (φ i + 1))) atTop (nhds (f xStar)) :=
    successorObjectiveSubseqTendsto
      (f := f) (x := x) (φ := φ) hφ hxStar hObjectiveContAtStar hStepMonotone
  have hRightHandSide :
      Tendsto
        (fun i : ℕ ↦
          f (x (φ i)) +
            run.σ * (run.β ^ mStar) * 1 * inner ℝ (g[r](x (φ i))) (s i))
        atTop
        (nhds (f xStar + run.σ * (run.β ^ mStar) * 1 * inner ℝ gStar sStar)) := by
    exact hObjectiveSubseq.add ((hInnerSubseq.const_mul (run.σ * (run.β ^ mStar) * 1)))
  have hLimitLe :
      f xStar ≤ f xStar + run.σ * (run.β ^ mStar) * 1 * inner ℝ gStar sStar :=
    le_of_tendsto_of_tendsto hSuccessorObjectiveSubseq hRightHandSide hFrozenArmijo
  have hStrictUpper :
      f xStar + run.σ * (run.β ^ mStar) * 1 * inner ℝ gStar sStar < f xStar := by
    have hScalePos : 0 < run.σ * (run.β ^ mStar) * 1 := by
      nlinarith [hParams.rho_pos, hPowPos]
    have hCorrectionNeg :
        run.σ * (run.β ^ mStar) * 1 * inner ℝ gStar sStar < 0 :=
      mul_neg_of_pos_of_neg hScalePos hDescent
    linarith
  linarith

namespace ScaledLevenbergMarquardtArmijo

/-- Under the same limit-point `C¹` bridge and run-level Jacobian regularity hypotheses as
Theorem 7.3.6, the canonical stationary-point conclusion holds for the least-squares objective. -/
theorem stationary
    (r : Point → Residual) (D : Point → MatrixN n)
    (x : ℕ → Point) (μ α : ℕ → ℝ) (mIndex : ℕ → ℕ)
    (run :
      IsScaledLevenbergMarquardtArmijoSequence
        (nonlinearLeastSquaresObjective r) (leastSquaresGradient r)
        (residualJacobianMatrix r) r D x μ α mIndex)
    {xStar : Point} {φ : ℕ → ℕ} {P : MatrixN n}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (x ∘ φ) atTop (nhds xStar))
    (hr : ContDiffAt ℝ 1 r xStar)
    (hJacobian_run : ∀ k : ℕ, DifferentiableAt ℝ r (x k))
    (hP : P.PosDef)
    (hP_lim :
      Tendsto
        (fun i : ℕ ↦
          gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))
        atTop (nhds P)) :
    IsStationaryPoint (nonlinearLeastSquaresObjective r) xStar := by
  -- The main theorem gives the Chapter 7 gradient zero condition at the accumulation point.
  have hgZero :
      g[r](xStar) = 0 :=
    scaledLevenbergMarquardtArmijo_accumulationPoint_g_eq_zero
      r D x μ α mIndex run hφ hxStar hr hJacobian_run hP hP_lim
  have hResidualDiff : DifferentiableAt ℝ r xStar := hr.differentiableAt (by norm_num)
  have hGradientZero :
      gradient (nonlinearLeastSquaresObjective r) xStar = 0 := by
    -- Rewrite the canonical gradient back to the Chapter 7 owner.
    rw [leastSquaresObjective_gradient_eq (r := r) (x := xStar) hResidualDiff]
    exact hgZero
  have hObjectiveDiff :
      DifferentiableAt ℝ (nonlinearLeastSquaresObjective r) xStar := by
    have hResidualDeriv : HasFDerivAt r (fderiv ℝ r xStar) xStar := hResidualDiff.hasFDerivAt
    have hNormSq :
        HasFDerivAt (fun y : Point ↦ ‖r y‖ ^ (2 : ℕ))
          (2 • (innerSL ℝ) (r xStar) ∘SL fderiv ℝ r xStar) xStar := by
      -- Differentiate the squared residual norm before scaling by `1 / 2`.
      simpa using hResidualDeriv.norm_sq
    have hObjectiveRaw :
        HasFDerivAt (fun y : Point ↦ ((1 : ℝ) / 2) * ‖r y‖ ^ (2 : ℕ))
          (((1 / 2 : ℝ) : ℝ) • (2 • (innerSL ℝ) (r xStar) ∘SL fderiv ℝ r xStar)) xStar := by
      -- The objective is exactly half the squared residual norm.
      simpa using hNormSq.const_mul ((1 / 2 : ℝ))
    have hObjectiveEq :
        nonlinearLeastSquaresObjective r = fun y : Point ↦ ((1 : ℝ) / 2) * ‖r y‖ ^ (2 : ℕ) := by
      ext y
      rw [nonlinearLeastSquaresObjective_eq_half_norm_sq]
    have hObjectiveDeriv :
        HasFDerivAt (nonlinearLeastSquaresObjective r)
          (((1 / 2 : ℝ) : ℝ) • (2 • (innerSL ℝ) (r xStar) ∘SL fderiv ℝ r xStar)) xStar := by
      -- Rewrite the objective once into the norm-square form used by the derivative rule.
      simpa [hObjectiveEq] using hObjectiveRaw
    exact hObjectiveDeriv.differentiableAt
  exact (isStationaryPoint_iff (nonlinearLeastSquaresObjective r) xStar).2
    ⟨hGradientZero, hObjectiveDiff⟩

/-- Under the same limit-point `C¹` bridge and run-level Jacobian regularity hypotheses, the
stationary-point companion yields vanishing of the canonical objective gradient. -/
theorem objectiveGradient_eq_zero
    (r : Point → Residual) (D : Point → MatrixN n)
    (x : ℕ → Point) (μ α : ℕ → ℝ) (mIndex : ℕ → ℕ)
    (run :
      IsScaledLevenbergMarquardtArmijoSequence
        (nonlinearLeastSquaresObjective r) (leastSquaresGradient r)
        (residualJacobianMatrix r) r D x μ α mIndex)
    {xStar : Point} {φ : ℕ → ℕ} {P : MatrixN n}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (x ∘ φ) atTop (nhds xStar))
    (hr : ContDiffAt ℝ 1 r xStar)
    (hJacobian_run : ∀ k : ℕ, DifferentiableAt ℝ r (x k))
    (hP : P.PosDef)
    (hP_lim :
      Tendsto
        (fun i : ℕ ↦
          gaussNewtonNormalMatrix r (x (φ i)) + μ (φ i) • D (x (φ i)))
        atTop (nhds P)) :
    gradient (nonlinearLeastSquaresObjective r) xStar = 0 := by
  -- Apply the stationary-point wrapper and then read off the vanishing canonical gradient.
  exact
    (stationary r D x μ α mIndex run hφ hxStar hr hJacobian_run hP hP_lim).gradient_eq_zero

end ScaledLevenbergMarquardtArmijo

end
