module

public import ReasLib.Optimization.DFP.WolfeCounterexample.AutomaticIdentityFactor
public import ReasLib.Optimization.DFP.WolfeCounterexample.MatrixIdentityLiminfCertificate
public import ReasLib.Optimization.DFP.WolfeCounterexample.SemanticProjections
public import ReasLib.Optimization.DFP.LevelSetGlobalConvergence
import Mathlib.Tactic

/-!
# Automatic matrix identity initialization with a positive gradient liminf

This module closes the paper-facing representation bridge: a strong-Wolfe
counterexample with positive-definite initial inverse Hessian is normalized by
a square-root factor, then converted to a classical matrix DFP certificate
whose gradient norms have a strictly positive liminf.
 -/

public section
noncomputable section
open Filter
open scoped InnerProduct MatrixOrder Topology
namespace DFP.WolfeCounterexample

/-- Helper for TASK-16: scalar lower and upper Loewner bounds on the identity operator are ordered
on every Euclidean space whose coordinate index has at least two elements. -/
theorem scalar_le_of_identity_loewner_bounds
    {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (lowerMap : a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) ≤
      b • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :
    a ≤ b := by
  have hzero_lt_two : (0 : ℕ) < 2 := by norm_num
  have hzero_lt_n : 0 < n := lt_of_lt_of_le hzero_lt_two hn
  let i : Fin n := ⟨0, hzero_lt_n⟩
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have hv : v ≠ 0 := by
    intro h
    have hv' := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) h
    dsimp [v, i] at hv'
    simp at hv'
  have hq := (ContinuousLinearMap.le_def _ _).mp lowerMap |>.inner_nonneg_left v
  have hq' : a * ‖v‖ ^ 2 ≤ b * ‖v‖ ^ 2 := by
    have hq'' : 0 ≤ b * ‖v‖ ^ 2 - a * ‖v‖ ^ 2 := by
      simpa only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq] using hq
    linarith
  have hvnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  nlinarith

/-- Helper for TASK-16: an explicit factorized strong-Wolfe trajectory yields a classical matrix
identity-initialized certificate with the paper-facing positive gradient liminf. -/
theorem matrixIdentityLiminfStrongWolfe_of_factorized
    {n : ℕ} (hn : 2 ≤ n) {c₁ c₂ a b q : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (factor : (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (c.iteration.inverseHessian 0) =
      L.toContinuousLinearMap.pushforward 1)
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hc₁_pos : 0 < c₁) (hc₁_lt_c₂ : c₁ < c₂) (hc₂_lt_one : c₂ < 1)
    (lowerMap : a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
      L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤
      b • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (gradientMapLower : q • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≤
      L.toContinuousLinearMap.pushforward 1) :
    Nonempty (MatrixIdentityLiminfStrongWolfeCertificate n
      ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) c₁ c₂) := by
  let f' : EuclideanSpace ℝ (Fin n) → ℝ := c.iteration.objective ∘ L
  let α' : ℕ → ℝ := c.iteration.stepLength
  let x' : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ L.symm (c.iteration.point k)
  let g' : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦
    (L.toContinuousLinearMap†)
      (DFP.gradients c.iteration.objective c.iteration.point k)
  let H' : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := fun k ↦
    L.symm.toContinuousLinearMap.pushforward
      ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (c.iteration.inverseHessian k))
  have hMatrix := c.iteration.isOrbit c.stepLengthPos
  have hOperator := hMatrix.toOperator
  have hPulled := hOperator.pullback_of_initialFactor L factor
  have hOrbit' : DFP.Operator.IsOrbit f' α' x' g' H' := by
    simpa only [f', α', x', g', H', Function.comp_apply] using hPulled.1
  have hInitial : H' 0 = 1 := by
    simpa only [H'] using hPulled.2
  have hGradientDifferentiable : Differentiable ℝ (gradient c.iteration.objective) :=
    (c.objectiveContDiff.gradient_succ (n := 1)).differentiable_one
  have hObjectiveContDiff : ContDiff ℝ 2 f' := by
    simpa only [f'] using c.objectiveContDiff.comp L.contDiff
  have hm0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hM0 : (0 : ℝ) ≤ 3 / 2 := by norm_num
  have hHessianBounds : HasHessianBounds ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) f' := by
    exact c.hessianBounds.comp_continuousLinearEquiv L
      hGradientDifferentiable hm0 hM0 lowerMap upperMap
  have hStep (k : ℕ) :
      DFP.Operator.steps α' H' g' k =
        L.symm (DFP.Operator.steps c.iteration.stepLength
          (fun j ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
            (c.iteration.inverseHessian j))
          (DFP.gradients c.iteration.objective c.iteration.point) k) := by
    simpa only [DFP.Operator.steps_apply, α', H', g'] using
      (DFP.Operator.step_change L (c.iteration.stepLength k)
        ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (c.iteration.inverseHessian k))
        (DFP.gradients c.iteration.objective c.iteration.point k))
  have hDisplacement (k : ℕ) : x' (k + 1) - x' k =
      DFP.Operator.steps α' H' g' k := by
    rw [hOrbit'.pointSucc k]
    abel
  have hSourceDescent (k : ℕ) :
      inner ℝ (DFP.gradients c.iteration.objective c.iteration.point k)
        (c.iteration.point (k + 1) - c.iteration.point k) < 0 :=
    c.iteration.gradientInnerDisplacementNeg k (c.stepLengthPos k)
  have hTransformedDescent (k : ℕ) :
      inner ℝ (g' k) (x' (k + 1) - x' k) < 0 := by
    have hsourceStep :
        DFP.Operator.steps c.iteration.stepLength
          (fun j ↦ (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
            (c.iteration.inverseHessian j))
          (DFP.gradients c.iteration.objective c.iteration.point) k =
          c.iteration.point (k + 1) - c.iteration.point k := by
      rw [hOperator.pointSucc k]
      abel
    rw [hDisplacement k, hStep k, hsourceStep]
    rw [real_inner_comm]
    dsimp only [g']
    have hpair := DFP.Operator.secantPairing_change L
      (c.iteration.point (k + 1) - c.iteration.point k)
      (DFP.gradients c.iteration.objective c.iteration.point k)
    rw [hpair]
    simpa only [real_inner_comm] using hSourceDescent k
  have hStrongLegacy (k : ℕ) :
      LineSearch.IsStrongWolfe c₁ c₂ f' (x' k)
        (x' (k + 1) - x' k) := by
    have hOld := LineSearch.IsStrongWolfe.comp_continuousLinearEquiv
      (c.strongWolfe k) L
    simpa only [f', x', Function.comp_apply, L.apply_symm_apply, map_sub] using hOld
  have hSecant (k : ℕ) :
      0 < inner ℝ (g' (k + 1) - g' k) (x' (k + 1) - x' k) := by
    have hstrong := hStrongLegacy k
    have hgradStart : HasGradientAt f' (g' k) (x' k) := hOrbit'.gradientAt k
    have hgradNext : HasGradientAt f' (g' (k + 1))
        (x' k + (x' (k + 1) - x' k)) := by
      have hsum : x' k + (x' (k + 1) - x' k) = x' (k + 1) := by abel
      rw [hsum]
      exact hOrbit'.gradientAt (k + 1)
    have hCanonicalDescent :
        inner ℝ (gradient f' (x' k)) (x' (k + 1) - x' k) < 0 := by
      rw [hgradStart.gradient]
      exact hTransformedDescent k
    have hweak : LineSearch.IsWeakWolfe c₁ c₂ f' (x' k)
        (x' (k + 1) - x' k) := by
      exact hstrong.toWeakWolfe (le_of_lt hCanonicalDescent)
    have hcurv := hweak.secantCurvature_pos hCanonicalDescent
    rw [hgradStart.gradient, hgradNext.gradient] at hcurv
    exact hcurv
  let p : LineSearch.Wolfe.Coefficients := {
    c₁ := c₁
    c₂ := c₂
    c₁_pos := hc₁_pos
    c₁_lt_c₂ := hc₁_lt_c₂
    c₂_lt_one := hc₂_lt_one
  }
  have hWeakLegacy (k : ℕ) :
      LineSearch.IsWeakWolfe c₁ c₂ f' (x' k)
        (x' (k + 1) - x' k) := by
    have hgradStart : HasGradientAt f' (g' k) (x' k) := hOrbit'.gradientAt k
    have hCanonicalDescent :
        inner ℝ (gradient f' (x' k)) (x' (k + 1) - x' k) < 0 := by
      rw [hgradStart.gradient]
      exact hTransformedDescent k
    exact (hStrongLegacy k).toWeakWolfe hCanonicalDescent.le
  have hWeakOutput (k : ℕ) :
      LineSearch.Wolfe.IsWeak p f' (x' k)
        (DFP.Operator.steps α' H' g' k) := by
    have hweak := LineSearch.Wolfe.IsWeak.ofIsWeakWolfe
      (p := p) (hWeakLegacy k)
    simpa only [p, hDisplacement k] using hweak
  have hSourceLower : ∀ᶠ k in atTop,
      c.gradientLimit / 2 ≤
        ‖DFP.gradients c.iteration.objective c.iteration.point k‖ := by
    have hlt : c.gradientLimit / 2 < c.gradientLimit := by
      nlinarith [c.gradientLimitPos]
    exact ((tendsto_order.1 c.gradientNormTendsto).1 _ hlt).mono
      (fun _ h ↦ le_of_lt h)
  have hSourceUpper : ∀ᶠ k in atTop,
      ‖DFP.gradients c.iteration.objective c.iteration.point k‖ ≤
        2 * c.gradientLimit := by
    have hgt : c.gradientLimit < 2 * c.gradientLimit := by
      nlinarith [c.gradientLimitPos]
    exact ((tendsto_order.1 c.gradientNormTendsto).2 _ hgt).mono
      (fun _ h ↦ le_of_lt h)
  let δ : ℝ := √q * (c.gradientLimit / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos (Real.sqrt_pos.2 hq) (half_pos c.gradientLimitPos)
  have hGradientLower : ∀ᶠ k in atTop, δ ≤ ‖g' k‖ := by
    filter_upwards [hSourceLower] with k hk
    have hnorm := ContinuousLinearMap.norm_adjoint_lower_bound
      L.toContinuousLinearMap hq.le gradientMapLower
      (DFP.gradients c.iteration.objective c.iteration.point k)
    dsimp only [δ, g']
    exact le_trans
      (mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg q)) hnorm
  let B : ℝ := ‖L.toContinuousLinearMap†‖ * (2 * c.gradientLimit)
  have hGradientUpper : ∀ᶠ k in atTop, ‖g' k‖ ≤ B := by
    filter_upwards [hSourceUpper] with k hk
    dsimp only [g', B]
    exact (L.toContinuousLinearMap†).le_opNorm
      (DFP.gradients c.iteration.objective c.iteration.point k) |>.trans
        (mul_le_mul_of_nonneg_left hk (norm_nonneg _))
  have hGradientLiminf : 0 < liminf (fun k ↦ ‖g' k‖) atTop :=
    DFP.positive_liminf_of_eventually_lower_upper hδ hGradientLower hGradientUpper
  have hab : a ≤ b := scalar_le_of_identity_loewner_bounds hn
    (lowerMap.trans upperMap)
  have hmM : (1 / 2 : ℝ) * a ≤ (3 / 2 : ℝ) * b := by
    nlinarith
  have hGradientTailPackage : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ k in atTop, δ ≤ ‖g' k‖ := by
    exact ⟨δ, hδ, hGradientLower⟩
  let base : IdentityInitializedOperatorCertificate (Fin n)
      ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) c₁ c₂ := {
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
    weakWolfeLegacy := hWeakLegacy
    initialInverseHessian_eq_one := hInitial
    gradientLimit := δ
    gradientLimitPos := hδ
    gradientNormEventuallyPositive := hGradientTailPackage
  }
  let result : IdentityInitializedStrongWolfeOperatorCertificate (Fin n)
      ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) c₁ c₂ := {
    toIdentityInitializedOperatorCertificate := base
    strongWolfe := hStrongLegacy
  }
  have hResultPos : 0 < (1 / 2 : ℝ) * a := by positivity
  have hResultLiminf : 0 < liminf
      (fun k ↦ ‖result.gradient k‖) atTop := by
    simpa only [result, base] using hGradientLiminf
  have hResultSecant : ∀ k,
      0 < inner ℝ (result.gradient (k + 1) - result.gradient k)
        (result.point (k + 1) - result.point k) := by
    intro k
    simpa only [result, base] using hSecant k
  exact MatrixIdentityLiminfStrongWolfeCertificate.ofOperator_ofIdentityAndSecantCurvature
    result hResultPos hmM hResultLiminf hResultSecant

/-- TASK-16: every paper-range strong-Wolfe counterexample with positive-definite
initial inverse Hessian admits a matrix identity-initialized certificate with
some positive, ordered Hessian bounds and a strictly positive gradient liminf.
The bounds are generated from the positive square-root factor of the initial
matrix. -/
theorem exists_matrixIdentityLiminfStrongWolfe_of_initialPosDef
    {n : ℕ} (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      Nonempty (MatrixIdentityLiminfStrongWolfeCertificate n m M c₁ c₂) := by
  obtain ⟨L, a, b, q, ha, hb, hq, hfactor, hlower, hupper, hgradient⟩ :=
    factorAndBounds_of_initialPosDef c.initialInverseHessianPosDef
  have hc₁_lt_c₂ : c₁ < c₂ :=
    lt_of_lt_of_le hc₁_lt_two_thirds hc₂_ge_two_thirds
  have hcertificate := matrixIdentityLiminfStrongWolfe_of_factorized
    hn c L hfactor ha hb hq hc₁_pos hc₁_lt_c₂ hc₂_lt_one
      hlower hupper hgradient
  have hab : a ≤ b := scalar_le_of_identity_loewner_bounds hn
    (hlower.trans hupper)
  refine ⟨(1 / 2 : ℝ) * a, (3 / 2 : ℝ) * b, ?_, ?_, hcertificate⟩
  · positivity
  · nlinarith

end DFP.WolfeCounterexample
end
