/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.PlanarConvergence

/-!
# Degeneration of planar secant iterations

The search steps and secant equations suffice for degeneration. No DFP update
or Lipschitz regularity of the Hessian is included in these hypotheses.
-/

public section

open Filter
open scoped Topology Matrix InnerProduct

namespace DFP

/-- Helper for lem:planar-degeneration: a nonstationary positive-definite
search sequence satisfying the secant equation, with no matrix-update law. -/
structure SecantIteration (n : ℕ) where
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  stepLength : ℕ → ℝ
  point : ℕ → EuclideanSpace ℝ (Fin n)
  inverseHessian : ℕ → Matrix (Fin n) (Fin n) ℝ
  gradientNeZero : ∀ k, gradients objective point k ≠ 0
  inverseHessianPosDef : ∀ k, (inverseHessian k).PosDef
  pointSucc : ∀ k, point (k + 1) = point k +
    steps stepLength (directions inverseHessian (gradients objective point)) k
  secant : ∀ k, inverseHessian (k + 1) *ᵥ
    WithLp.ofLp (gradient objective (point (k + 1)) - gradient objective (point k)) =
      WithLp.ofLp (point (k + 1) - point k)

/-- Helper for lem:planar-degeneration: every nonstationary DFP iteration is
a secant search iteration after forgetting its specific matrix-update law. -/
def InverseIteration.toSecantIteration {n : ℕ}
    (iteration : InverseIteration (Fin n)) : SecantIteration n where
  objective := iteration.objective
  stepLength := iteration.stepLength
  point := iteration.point
  inverseHessian := iteration.inverseHessian
  gradientNeZero := iteration.gradientNeZeroOfSecantDenominator
  inverseHessianPosDef := iteration.inverseHessianPosDef
  pointSucc := iteration.pointSucc
  secant := PlanarConvergence.orbitSecantEquation iteration

namespace SecantIteration

open PlanarConvergence

/-- Helper for lem:planar-degeneration: the initial sublevel of a secant iteration. -/
def objectiveSublevel {n : ℕ} (iteration : SecantIteration n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | iteration.objective z ≤ iteration.objective (iteration.point 0)}

/-- Helper for lem:planar-degeneration: sublevel membership is an objective inequality. -/
theorem mem_objectiveSublevel_iff {n : ℕ}
    (iteration : SecantIteration n) (z : EuclideanSpace ℝ (Fin n)) :
    z ∈ objectiveSublevel iteration ↔
      iteration.objective z ≤ iteration.objective (iteration.point 0) := by
  rfl

/-- Helper for lem:planar-degeneration: a positive secant step length and a positive-definite
inverse Hessian make the actual displacement a strict descent step. -/
theorem gradientInnerDisplacementNeg {n : ℕ}
    (iteration : SecantIteration n) (k : ℕ)
    (hStep : 0 < iteration.stepLength k) :
    inner ℝ (gradients iteration.objective iteration.point k)
      (iteration.point (k + 1) - iteration.point k) < 0 := by
  have hGradient : gradients iteration.objective iteration.point k ≠ 0 :=
    iteration.gradientNeZero k
  have hEnergy : 0 <
      WithLp.ofLp (gradients iteration.objective iteration.point k) ⬝ᵥ
        (iteration.inverseHessian k *ᵥ
          WithLp.ofLp (gradients iteration.objective iteration.point k)) := by
    have hCoordinates :
        WithLp.ofLp (gradients iteration.objective iteration.point k) ≠ 0 := by
      intro hzero
      apply hGradient
      apply WithLp.ofLp_injective 2
      simpa only [WithLp.ofLp_zero] using hzero
    exact (iteration.inverseHessianPosDef k).dotProduct_mulVec_pos hCoordinates
  have hDirection :
      inner ℝ (gradients iteration.objective iteration.point k)
          (directions iteration.inverseHessian
            (gradients iteration.objective iteration.point) k) =
        -(WithLp.ofLp (gradients iteration.objective iteration.point k) ⬝ᵥ
          (iteration.inverseHessian k *ᵥ
            WithLp.ofLp (gradients iteration.objective iteration.point k))) := by
    rw [directions_apply, inner_neg_right,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    rw [dotProduct_comm]
  have hDisplacement :
      iteration.point (k + 1) - iteration.point k =
        steps iteration.stepLength
          (directions iteration.inverseHessian
            (gradients iteration.objective iteration.point)) k := by
    rw [iteration.pointSucc k]
    abel
  rw [hDisplacement, steps_apply, real_inner_smul_right, hDirection]
  nlinarith

/-- Helper for lem:planar-degeneration: Armijo along a positive inverse-form secant step makes the
objective value nonincreasing at that step. -/
theorem objectiveSuccLeOfWeakWolfe {n : ℕ}
    (iteration : SecantIteration n) {c₁ c₂ : ℝ} (k : ℕ)
    (hStep : 0 < iteration.stepLength k)
    (hWolfe : LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    iteration.objective (iteration.point (k + 1)) ≤
      iteration.objective (iteration.point k) := by
  have hDescent := iteration.gradientInnerDisplacementNeg k hStep
  have hCorrection :
      c₁ * inner ℝ (gradient iteration.objective (iteration.point k))
        (iteration.point (k + 1) - iteration.point k) ≤ 0 := by
    rw [← gradients_apply]
    exact mul_nonpos_of_nonneg_of_nonpos hWolfe.c₁_pos.le hDescent.le
  have hArmijo := hWolfe.armijo
  have hEndpoint :
      iteration.point k + (iteration.point (k + 1) - iteration.point k) =
        iteration.point (k + 1) := by
    abel
  rw [hEndpoint] at hArmijo
  exact hArmijo.trans (add_le_of_nonpos_right hCorrection)

/-- Helper for lem:planar-degeneration: positive inverse-form secant weak-Wolfe steps make the
objective values along the whole trajectory antitone. -/
theorem objectiveValuesAntitoneOfWeakWolfe {n : ℕ}
    (iteration : SecantIteration n) {c₁ c₂ : ℝ}
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    Antitone (fun k ↦ iteration.objective (iteration.point k)) := by
  apply antitone_nat_of_succ_le
  intro k
  exact iteration.objectiveSuccLeOfWeakWolfe k (hStep k) (hWolfe k)

/-- Helper for lem:planar-degeneration: every point of a positive-step inverse-form secant
weak-Wolfe trajectory stays in its initial objective sublevel set. -/
theorem pointMemObjectiveSublevelOfWeakWolfe {n : ℕ}
    (iteration : SecantIteration n) {c₁ c₂ : ℝ}
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∀ k, iteration.point k ∈ objectiveSublevel iteration := by
  have hAntitone := iteration.objectiveValuesAntitoneOfWeakWolfe hStep hWolfe
  intro k
  rw [mem_objectiveSublevel_iff]
  exact hAntitone (Nat.zero_le k)

/-- Helper for lem:planar-degeneration: the actual predicted decreases of
a positive-step weak-Wolfe secant orbit are summable under a global positive
Hessian lower bound. -/
theorem summablePredictedDecrease {n : ℕ}
    (iteration : SecantIteration n) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    Summable (fun k ↦ -inner ℝ (gradient iteration.objective (iteration.point k))
      (iteration.point (k + 1) - iteration.point k)) := by
  have hnonnegative : ∀ k, 0 ≤
      -inner ℝ (gradient iteration.objective (iteration.point k))
        (iteration.point (k + 1) - iteration.point k) := by
    intro k
    have hneg := iteration.gradientInnerDisplacementNeg k (hStep k)
    simpa only [DFP.gradients_apply] using (neg_pos.mpr hneg).le
  have hbelow := objectiveLowerBoundOfHessian iteration.objective hf hμ hHessian
  apply summableCostsOfDescent (F := fun k ↦ iteration.objective (iteration.point k))
    (hWolfe 0).c₁_pos hnonnegative
  · intro k
    exact hbelow (iteration.point k)
  · intro k
    have harmijo := (hWolfe k).armijo
    simpa only [add_sub_cancel, mul_neg, sub_neg_eq_add] using harmijo

/-- Helper for lem:planar-degeneration: the squared physical step lengths
of the classical secant orbit are summable. -/
theorem summableStepSquares {n : ℕ}
    (iteration : SecantIteration n) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    Summable (fun k ↦ ‖iteration.point (k + 1) - iteration.point k‖ ^ 2) := by
  have hsum := (summablePredictedDecrease iteration hf hμ hHessian hStep hWolfe).mul_left
    (2 * (1 - c₁) / μ)
  apply Summable.of_nonneg_of_le
    (fun k ↦ sq_nonneg ‖iteration.point (k + 1) - iteration.point k‖)
    (fun k ↦ stepSquareBound hf hμ hHessian (hWolfe k)) hsum

/-- Helper for lem:planar-degeneration: the physical secant step lengths tend
to zero, by square summability derived from strong convexity and Armijo. -/
theorem stepNormTendstoZero {n : ℕ}
    (iteration : SecantIteration n) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    Tendsto (fun k ↦ ‖iteration.point (k + 1) - iteration.point k‖) atTop (𝓝 0) := by
  have hsum := summableStepSquares iteration hf hμ hHessian hStep hWolfe
  have hsqrt := hsum.tendsto_atTop_zero.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- Helper for lem:planar-degeneration: objective values along an admissible
secant sequence decrease to a finite limit bounded above by every iterate value. -/
theorem objectiveValuesHaveLimit {n : ℕ}
    (iteration : SecantIteration n) {c₁ c₂ : ℝ}
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x) :
    ∃ F, Tendsto (fun k ↦ iteration.objective (iteration.point k)) atTop (𝓝 F) ∧
      iteration.objective xstar ≤ F ∧ ∀ k, F ≤ iteration.objective (iteration.point k) := by
  have hanti := iteration.objectiveValuesAntitoneOfWeakWolfe hStep hWolfe
  have hbounded : BddBelow (Set.range (fun k ↦ iteration.objective (iteration.point k))) := by
    refine ⟨iteration.objective xstar, ?_⟩
    rintro y ⟨k, rfl⟩
    exact hmin (iteration.point k)
  refine ⟨⨅ k, iteration.objective (iteration.point k),
    tendsto_atTop_ciInf hanti hbounded, ?_, ?_⟩
  · exact le_ciInf (fun k ↦ hmin (iteration.point k))
  · intro k
    exact ciInf_le hbounded k

/-- Helper for lem:planar-degeneration: a nonconvergent strongly convex
secant orbit has gradient norms bounded uniformly away from zero. -/
theorem gradientLowerBoundOfNonconvergence {n : ℕ}
    (iteration : SecantIteration n) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ Nmin > 0, ∀ k, Nmin ≤ ‖gradient iteration.objective (iteration.point k)‖ := by
  obtain ⟨F, hF, hminF, hFk⟩ := objectiveValuesHaveLimit iteration hStep hWolfe hmin
  have hstrict : iteration.objective xstar < F := by
    apply lt_of_le_of_ne hminF
    intro heq
    apply hnot
    apply pointTendstoOfObjectiveTendsto hf hμ hHessian (gradientZeroOfGlobalMinimizer hmin)
    rwa [← heq] at hF
  have hgap : 0 < 2 * μ * (F - iteration.objective xstar) := by positivity
  refine ⟨Real.sqrt (2 * μ * (F - iteration.objective xstar)),
    Real.sqrt_pos.mpr hgap, ?_⟩
  intro k
  have hbound := objectiveGapBoundByGradient hf hμ hHessian (iteration.point k) xstar
  have hfactor : 0 ≤ 2 * μ := by positivity
  have hvalue := mul_le_mul_of_nonneg_left (hFk k) hfactor
  have hsqrt := Real.sq_sqrt hgap.le
  nlinarith [norm_nonneg (gradient iteration.objective (iteration.point k))]

/-- Helper for lem:planar-degeneration: on the actual secant orbit, secant
norms and predicted decreases have common quadratic-scale bounds. -/
theorem secantBoundsAlongOrbit {n : ℕ}
    (iteration : SecantIteration n) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ M > 0, ∀ k,
      ‖gradient iteration.objective (iteration.point (k + 1)) -
        gradient iteration.objective (iteration.point k)‖ ≤
          M * ‖iteration.point (k + 1) - iteration.point k‖ ∧
      -inner ℝ (gradient iteration.objective (iteration.point k))
        (iteration.point (k + 1) - iteration.point k) ≤
          (M / (1 - c₂)) * ‖iteration.point (k + 1) - iteration.point k‖ ^ 2 := by
  obtain ⟨M, hM, hbound⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  have hconvex := convexInitialSublevel hf hμ hHessian (iteration.point 0)
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe
  have hfOrder : ContDiff ℝ ((1 : ℕ∞) + 1) iteration.objective := by
    convert hf using 1
    norm_num
  have hgradient : ContDiff ℝ 1 (gradient iteration.objective) :=
    hfOrder.gradient_succ (n := 1)
  refine ⟨M, hM, ?_⟩
  intro k
  have hsec : ‖gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)‖ ≤
        M * ‖iteration.point (k + 1) - iteration.point k‖ :=
    hconvex.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ ↦ hgradient.differentiable_one.differentiableAt)
      (fun x hx ↦ (hbound x hx).2)
      ((mem_objectiveSublevel_iff iteration (iteration.point k)).mp (hmem k))
      ((mem_objectiveSublevel_iff iteration (iteration.point (k + 1))).mp (hmem (k + 1)))
  refine ⟨hsec, ?_⟩
  have hcurvature := (hWolfe k).weakCurvature
  rw [add_sub_cancel] at hcurvature
  have hpair := real_inner_le_norm
    (gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k))
    (iteration.point (k + 1) - iteration.point k)
  rw [inner_sub_left] at hpair
  have hsecScaled := mul_le_mul_of_nonneg_right hsec
    (norm_nonneg (iteration.point (k + 1) - iteration.point k))
  have hden : 0 < 1 - c₂ := sub_pos.mpr (hWolfe k).c₂_lt_one
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  nlinarith

/-- Helper for lem:planar-degeneration: the weak-Wolfe upper descent
bound controls the actual inverse-Hessian energy relative to its direction norm. -/
theorem orbitEnergyDirectionBound {n : ℕ}
    (iteration : SecantIteration n) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ C > 0, ∀ k,
      let g := gradient iteration.objective (iteration.point k)
      let v : EuclideanSpace ℝ (Fin n) :=
        WithLp.toLp 2 (iteration.inverseHessian k *ᵥ WithLp.ofLp g)
      inner ℝ g v ≤ C * ‖iteration.point (k + 1) - iteration.point k‖ * ‖v‖ := by
  obtain ⟨M, hM, hbounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  have hden : 0 < 1 - c₂ := sub_pos.mpr (hWolfe 0).c₂_lt_one
  refine ⟨M / (1 - c₂), div_pos hM hden, ?_⟩
  intro k
  have hstep : iteration.point (k + 1) - iteration.point k =
      iteration.stepLength k •
        (-(WithLp.toLp 2 (iteration.inverseHessian k *ᵥ
          WithLp.ofLp (gradient iteration.objective (iteration.point k))) :
            EuclideanSpace ℝ (Fin n))) := by
    rw [iteration.pointSucc k, DFP.steps_apply, DFP.directions_apply, DFP.gradients_apply]
    abel
  exact energyDirectionBound (hStep k) hstep (hbounds k).2

/-- Helper for lem:planar-degeneration: every step of an infinite
positive-step secant orbit is nonzero. -/
theorem orbitStepNormPos {n : ℕ}
    (iteration : SecantIteration n) (k : ℕ)
    (hStep : 0 < iteration.stepLength k) :
    0 < ‖iteration.point (k + 1) - iteration.point k‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hdescent := iteration.gradientInnerDisplacementNeg k hStep
  rw [hzero, inner_zero_right] at hdescent
  exact lt_irrefl 0 hdescent

/-- Helper for lem:planar-degeneration: the secant hypothesis gives the exact
relation between point and gradient differences. -/
theorem orbitSecantEquation {n : ℕ}
    (iteration : SecantIteration n) (k : ℕ) :
    iteration.inverseHessian (k + 1) *ᵥ
        WithLp.ofLp (gradient iteration.objective (iteration.point (k + 1)) -
          gradient iteration.objective (iteration.point k)) =
      WithLp.ofLp (iteration.point (k + 1) - iteration.point k) := by
  exact iteration.secant k

/-- Helper for lem:planar-degeneration: normalizing the displacement and
gradient change by the same step length preserves the exact secant equation. -/
theorem normalizedOrbitSecantEquation {n : ℕ}
    (iteration : SecantIteration n) (k : ℕ) :
    iteration.inverseHessian (k + 1) *ᵥ
        WithLp.ofLp (‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
          (gradient iteration.objective (iteration.point (k + 1)) -
            gradient iteration.objective (iteration.point k))) =
      WithLp.ofLp (‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
        (iteration.point (k + 1) - iteration.point k)) := by
  simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, orbitSecantEquation]

/-- Helper for lem:planar-degeneration: on the actual secant orbit the
new gradient has a uniformly small component along the previous normalized step. -/
theorem orbitLongitudinalGradientBound {n : ℕ}
    (iteration : SecantIteration n) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ C > 0, ∀ k,
      |inner ℝ (‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
          (iteration.point (k + 1) - iteration.point k))
        (gradient iteration.objective (iteration.point (k + 1)))| ≤
      C * ‖iteration.point (k + 1) - iteration.point k‖ := by
  obtain ⟨M, hM, hbounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  have hden : 0 < 1 - c₂ := sub_pos.mpr (hWolfe 0).c₂_lt_one
  have hC : 0 < M / (1 - c₂) + M := add_pos (div_pos hM hden) hM
  refine ⟨M / (1 - c₂) + M, hC, ?_⟩
  intro k
  have hdescent : inner ℝ (gradient iteration.objective (iteration.point k))
      (iteration.point (k + 1) - iteration.point k) ≤ 0 := by
    simpa only [DFP.gradients_apply] using
      (iteration.gradientInnerDisplacementNeg k (hStep k)).le
  exact longitudinalGradientBound _ _ _ hdescent (hbounds k).2 (hbounds k).1

/-- Helper for lem:planar-degeneration: the normalized secant curvature
of every physical secant step is bounded below by the strong-convexity constant. -/
theorem normalizedOrbitCurvatureLowerBound {n : ℕ}
    (iteration : SecantIteration n) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (k : ℕ) (hStep : 0 < iteration.stepLength k) :
    let s := iteration.point (k + 1) - iteration.point k
    let y := gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)
    μ ≤ inner ℝ (‖s‖⁻¹ • s) (‖s‖⁻¹ • y) := by
  dsimp only
  rw [normalizedSecantCurvature]
  apply (le_div_iff₀ (sq_pos_of_pos (orbitStepNormPos iteration k hStep))).mpr
  exact inner_gradient_sub_ge_of_hessian_lower_bound iteration.objective μ hf hμ
    hHessian (iteration.point k) (iteration.point (k + 1))

/-- Helper for lem:planar-degeneration: in the previous-step frame, the
actual secant matrix satisfies the standard planar secant equation. -/
theorem orbitPlanarSecantFrameSpecification
    (iteration : SecantIteration 2) (k : ℕ)
    (hStep : 0 < iteration.stepLength k) :
    let s := iteration.point (k + 1) - iteration.point k
    let u := ‖s‖⁻¹ • s
    let v := ‖s‖⁻¹ • (gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k))
    ((EuclideanPlane.frame u).transpose * iteration.inverseHessian (k + 1) *
      EuclideanPlane.frame u) *ᵥ ![inner ℝ u v, inner ℝ (EuclideanPlane.perp u) v] =
        ![1, 0] := by
  dsimp only
  have hnorm : ‖‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
      (iteration.point (k + 1) - iteration.point k)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (orbitStepNormPos iteration k hStep).ne']
  exact planarSecantFrameSpecification _ _ _ hnorm (normalizedOrbitSecantEquation iteration k)

/-- Helper for lem:planar-degeneration: failure of convergence of the
actual planar secant orbit forces its free secant coefficient to vanish, with
an eventual bound by the product of adjacent physical step lengths.
The index `k` here represents the paper's coefficient at iteration `k + 1`. -/
theorem orbitFreeCoefficientDegeneration
    (iteration : SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    let s := fun k ↦ iteration.point (k + 1) - iteration.point k
    let y := fun k ↦ gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)
    let lam := fun k ↦ (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) *
      (iteration.inverseHessian (k + 1)).det
    (∃ K > 0, ∀ᶠ k in atTop, 0 < lam k ∧ lam k ≤ K * ‖s k‖ * ‖s (k + 1)‖) ∧
      Tendsto lam atTop (𝓝 0) := by
  let s := fun k ↦ iteration.point (k + 1) - iteration.point k
  let y := fun k ↦ gradient iteration.objective (iteration.point (k + 1)) -
    gradient iteration.objective (iteration.point k)
  let ell := fun k ↦ ‖s k‖
  let u := fun k ↦ (ell k)⁻¹ • s k
  let v := fun k ↦ (ell k)⁻¹ • y k
  let R := fun k ↦ EuclideanPlane.frame (u k)
  let K := fun k ↦ (R k).transpose * iteration.inverseHessian (k + 1) * R k
  let g := fun k ↦ (R k).transpose *ᵥ
    WithLp.ofLp (gradient iteration.objective (iteration.point (k + 1)))
  let κ := fun k ↦ inner ℝ (u k) (v k)
  let β := fun k ↦ inner ℝ (EuclideanPlane.perp (u k)) (v k)
  let lam := fun k ↦ (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) *
    (iteration.inverseHessian (k + 1)).det
  obtain ⟨M, hM, hsecBounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  obtain ⟨G, hG, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  obtain ⟨N, hN, hgradLower⟩ :=
    gradientLowerBoundOfNonconvergence iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨A, hA, hlongBound⟩ := orbitLongitudinalGradientBound iteration hf hμ hHessian hStep hWolfe
  obtain ⟨C, hC, henergyBound⟩ := orbitEnergyDirectionBound iteration hf hμ hHessian hStep hWolfe
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe
  have hellPos (k : ℕ) : 0 < ell k := orbitStepNormPos iteration k (hStep k)
  have hellLimit : Tendsto ell atTop (𝓝 0) :=
    stepNormTendstoZero iteration hf hμ hHessian hStep hWolfe
  have hu (k : ℕ) : ‖u k‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (hellPos k).ne'
  have hR (k : ℕ) : R k ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
    have hspecial := (EuclideanPlane.frame_mem_specialOrthogonalGroup_iff (u k)).mpr (hu k)
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hK (k : ℕ) : (K k).PosDef :=
    orthogonalCoordinatesPosDef (iteration.inverseHessianPosDef (k + 1)) (hR k)
  have hsec (k : ℕ) : K k *ᵥ ![κ k, β k] = ![1, 0] :=
    orbitPlanarSecantFrameSpecification iteration k (hStep k)
  have hκ (k : ℕ) : μ ≤ κ k :=
    normalizedOrbitCurvatureLowerBound iteration hf hμ hHessian k (hStep k)
  have hv (k : ℕ) : ‖v k‖ ≤ M := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hellPos k), ← div_eq_inv_mul]
    apply (div_le_iff₀ (hellPos k)).mpr
    exact (hsecBounds k).1
  have hβ (k : ℕ) : |β k| ≤ M := by
    have hpair := abs_real_inner_le_norm (EuclideanPlane.perp (u k)) (v k)
    rw [EuclideanPlane.perp.norm_map, hu k, one_mul] at hpair
    exact hpair.trans (hv k)
  have htilt (k : ℕ) : |β k / κ k| ≤ M / μ := secantTiltBound hμ (hκ k) (hβ k)
  have hgNorm (k : ℕ) : ‖(WithLp.toLp 2 (g k) : EuclideanSpace ℝ (Fin 2))‖ =
      ‖gradient iteration.objective (iteration.point (k + 1))‖ := by
    exact Matrix.norm_toLp_mulVec_eq_of_mem_orthogonalGroup (R k).transpose
      (orthogonalTranspose (hR k)) _
  have hgLower (k : ℕ) : N ≤ ‖(WithLp.toLp 2 (g k) : EuclideanSpace ℝ (Fin 2))‖ := by
    rw [hgNorm]
    exact hgradLower (k + 1)
  have hgUpper (k : ℕ) : ‖(WithLp.toLp 2 (g k) : EuclideanSpace ℝ (Fin 2))‖ ≤ G := by
    rw [hgNorm]
    have hlevel := (mem_objectiveSublevel_iff iteration _).mp (hmem (k + 1))
    exact (hdiffBounds _ hlevel).1
  have hgFirst (k : ℕ) : g k 0 =
      inner ℝ (u k) (gradient iteration.objective (iteration.point (k + 1))) := by
    have hcoordinates := congrFun (planarFrameCoordinates (u k)
      (gradient iteration.objective (iteration.point (k + 1)))) 0
    simpa only [Matrix.cons_val_zero] using hcoordinates
  have hlong (k : ℕ) : |g k 0| ≤ A * ell k := by
    rw [hgFirst]
    exact hlongBound k
  have henergy (k : ℕ) : g k ⬝ᵥ (K k *ᵥ g k) ≤ C * ell (k + 1) *
      ‖(WithLp.toLp 2 (K k *ᵥ g k) : EuclideanSpace ℝ (Fin 2))‖ := by
    dsimp only [g, K]
    rw [orthogonalCoordinatesEnergy _ _ (hR k), orthogonalCoordinatesActionNorm _ _ (hR k)]
    have hphysical := henergyBound (k + 1)
    dsimp only at hphysical
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hphysical
    simp only [star_trivial] at hphysical
    rw [dotProduct_comm] at hphysical
    exact hphysical
  have hfree (k : ℕ) : K k 1 1 = lam k := by
    calc
      K k 1 1 = κ k * (K k).det :=
        transverseEntry_eq_curvature_mul_det (hK k).isHermitian (hμ.trans_le (hκ k)).ne' (hsec k)
      _ = κ k * (iteration.inverseHessian (k + 1)).det := by
        rw [orthogonalCoordinatesDet _ _ (hR k)]
      _ = lam k := by
        dsimp only [κ, u, v, ell, lam]
        rw [normalizedSecantCurvature]
  have hresult := secantSequenceDegeneration K g κ β ell hμ hA (div_nonneg hM.le hμ.le)
    hG hN hC hK hκ hsec (fun k ↦ (hellPos k).le) hellLimit htilt hgLower hgUpper hlong henergy
  simpa only [hfree, lam, ell, s, y] using hresult

/-- Helper for lem:planar-degeneration: if a strongly convex planar secant
orbit fails to converge, its inverse-Hessian operators remain uniformly bounded. -/
theorem orbitInverseHessianBoundedOfNonconvergence
    (iteration : SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ B > 0, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian k)‖ ≤ B := by
  let s := fun k ↦ iteration.point (k + 1) - iteration.point k
  let y := fun k ↦ gradient iteration.objective (iteration.point (k + 1)) -
    gradient iteration.objective (iteration.point k)
  let lam := fun k ↦ (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) *
    (iteration.inverseHessian (k + 1)).det
  have hlim : Tendsto lam atTop (𝓝 0) :=
    (orbitFreeCoefficientDegeneration iteration hf hμ hHessian hStep hWolfe hmin hnot).2
  obtain ⟨L, hL⟩ := hlim.bddAbove_range
  obtain ⟨M, hM, hsecBounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  let a := 1 / μ + (1 + M / μ) ^ 2
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hsuccessor (k : ℕ) :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1))‖ ≤
        a * (1 + max 0 L) := by
    have hnorm : 0 < ‖s k‖ := orbitStepNormPos iteration k (hStep k)
    have hu : ‖‖s k‖⁻¹ • s k‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnorm.ne']
    have hv : ‖‖s k‖⁻¹ • y k‖ ≤ M := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, ← div_eq_inv_mul]
      apply (div_le_iff₀ hnorm).mpr
      exact (hsecBounds k).1
    have hκ : μ ≤ inner ℝ (‖s k‖⁻¹ • s k) (‖s k‖⁻¹ • y k) :=
      normalizedOrbitCurvatureLowerBound iteration hf hμ hHessian k (hStep k)
    have hbound := planarPhysicalSecantOperatorBound (iteration.inverseHessian (k + 1))
      (‖s k‖⁻¹ • s k) (‖s k‖⁻¹ • y k) (iteration.inverseHessianPosDef (k + 1)) hu
      (normalizedOrbitSecantEquation iteration k) hμ hκ hv
    have hbound' :
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1))‖ ≤
          a * (1 + lam k) := by
      simpa only [normalizedSecantCurvature] using hbound
    have hlam : lam k ≤ max 0 L := (hL (Set.mem_range_self k)).trans (le_max_right _ _)
    have hscaled := mul_le_mul_of_nonneg_left hlam ha.le
    nlinarith
  let B := max ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian 0)‖
    (a * (1 + max 0 L)) + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro k
  cases k with
  | zero =>
    have hmax := le_max_left ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian 0)‖
      (a * (1 + max 0 L))
    dsimp only [B]
    linarith
  | succ k =>
    have hmax := le_max_right ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian 0)‖
      (a * (1 + max 0 L))
    have hbound := hsuccessor k
    dsimp only [B]
    exact hbound.trans (hmax.trans (le_add_of_nonneg_right zero_le_one))

/-- Helper for lem:planar-degeneration: equal Hermitian matrices have equal
ordered eigenvalue lists, independently of their Hermitian certificates. -/
theorem orderedEigenvaluesCongr
    {A B : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  subst B
  rfl

/-- Helper for lem:planar-degeneration: the square of the smallest eigenvalue
of a positive-definite planar matrix is at most its determinant. -/
theorem smallestEigenvalueSquareBound
    {H : Matrix (Fin 2) (Fin 2) ℝ} (hH : H.PosDef) :
    0 ≤ hH.isHermitian.eigenvalues₀ 1 ∧
      (hH.isHermitian.eigenvalues₀ 1) ^ 2 ≤ H.det := by
  have hsym : H 1 0 = H 0 1 := by simpa using hH.isHermitian.apply 0 1
  have hrepr : H = RealSymmetric2.matrix (H 0 0) (H 0 1) (H 1 1) := by
    rw [RealSymmetric2.matrix_eq]
    ext i j
    fin_cases i
    · fin_cases j
      · rfl
      · rfl
    · fin_cases j
      · exact hsym
      · rfl
  have heigen : hH.isHermitian.eigenvalues₀ 1 =
      RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1) := by
    rw [orderedEigenvaluesCongr hH.isHermitian
      (RealSymmetric2.matrix_isHermitian _ _ _) hrepr]
    exact RealSymmetric2.eigenvalues_one _ _ _
  have hdet : H.det = H 0 0 * H 1 1 - (H 0 1) ^ 2 := by
    rw [Matrix.det_fin_two, hsym]
    ring
  have hproduct := RealSymmetric2.low_mul_high (H 0 0) (H 0 1) (H 1 1)
  have hhigh : 0 < RealSymmetric2.high (H 0 0) (H 0 1) (H 1 1) := by
    rw [RealSymmetric2.high_apply, RealSymmetric2.gap_apply]
    have ha : 0 < H 0 0 := hH.diag_pos
    have hd : 0 < H 1 1 := hH.diag_pos
    positivity
  have hlow : 0 < RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1) := by
    have hpos := hH.det_pos
    rw [hdet, ← hproduct] at hpos
    exact pos_of_mul_pos_left hpos hhigh.le
  have horder := RealSymmetric2.low_le_high (H 0 0) (H 0 1) (H 1 1)
  rw [heigen, hdet]
  constructor
  · exact hlow.le
  · nlinarith

/-- Helper for lem:planar-degeneration: nonconvergence forces the smallest
ordered eigenvalue of the secant matrices to tend to zero. -/
theorem smallestEigenvalueTendstoZero
    (iteration : SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    Tendsto (fun k ↦ (iteration.inverseHessianPosDef k).isHermitian.eigenvalues₀ 1)
      atTop (𝓝 0) := by
  let s := fun k ↦ iteration.point (k + 1) - iteration.point k
  let y := fun k ↦ gradient iteration.objective (iteration.point (k + 1)) -
    gradient iteration.objective (iteration.point k)
  let lam := fun k ↦ (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) *
    (iteration.inverseHessian (k + 1)).det
  have hlam : Tendsto lam atTop (𝓝 0) :=
    (orbitFreeCoefficientDegeneration iteration hf hμ hHessian hStep hWolfe hmin hnot).2
  have hdetBound (k : ℕ) : (iteration.inverseHessian (k + 1)).det ≤ lam k / μ := by
    have hκ := normalizedOrbitCurvatureLowerBound iteration hf hμ hHessian k (hStep k)
    dsimp only at hκ
    rw [normalizedSecantCurvature] at hκ
    apply (le_div_iff₀ hμ).mpr
    simpa only [lam, s, y, mul_comm] using
      mul_le_mul_of_nonneg_right hκ (iteration.inverseHessianPosDef (k + 1)).det_pos.le
  have hdet : Tendsto (fun k ↦ (iteration.inverseHessian (k + 1)).det) atTop (𝓝 0) := by
    have hupper : Tendsto (fun k ↦ lam k / μ) atTop (𝓝 0) := by
      simpa only [zero_div] using hlam.div_const μ
    exact squeeze_zero (fun k ↦ (iteration.inverseHessianPosDef (k + 1)).det_pos.le)
      hdetBound hupper
  have hsquare : Tendsto (fun k ↦
      ((iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 1) ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ sq_nonneg _)
      (fun k ↦ (smallestEigenvalueSquareBound (iteration.inverseHessianPosDef (k + 1))).2) hdet
  have hlow : Tendsto (fun k ↦
      (iteration.inverseHessianPosDef (k + 1)).isHermitian.eigenvalues₀ 1) atTop (𝓝 0) := by
    have hsqrt := hsquare.sqrt
    simpa only [Real.sqrt_sq
      (smallestEigenvalueSquareBound (iteration.inverseHessianPosDef _)).1,
      Real.sqrt_zero] using hsqrt
  exact (tendsto_add_atTop_iff_nat 1).mp hlow

/-- lem:planar-degeneration: positive-definite secant search matrices under
weak Wolfe degenerate along every nonconvergent planar strongly convex orbit.
The free coefficient is positive and bounded by adjacent step products, the
matrix sequence is bounded, and its smallest eigenvalue tends to zero. -/
theorem planarDegeneration
    (iteration : SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    let s := fun k ↦ iteration.point (k + 1) - iteration.point k
    let y := fun k ↦ gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)
    let lam := fun k ↦ (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) *
      (iteration.inverseHessian (k + 1)).det
    (∃ C > 0, ∀ᶠ k in atTop, 0 < lam k ∧ lam k ≤ C * ‖s k‖ * ‖s (k + 1)‖) ∧
      Tendsto lam atTop (𝓝 0) ∧
      (∃ B > 0, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian k)‖ ≤ B) ∧
      Tendsto (fun k ↦ (iteration.inverseHessianPosDef k).isHermitian.eigenvalues₀ 1)
        atTop (𝓝 0) := by
  have hfree := orbitFreeCoefficientDegeneration iteration hf hμ hHessian hStep hWolfe hmin hnot
  exact ⟨hfree.1, hfree.2,
    orbitInverseHessianBoundedOfNonconvergence iteration hf hμ hHessian hStep hWolfe hmin hnot,
    smallestEigenvalueTendstoZero iteration hf hμ hHessian hStep hWolfe hmin hnot⟩

end SecantIteration

/-- Helper for lem:planar-degeneration: along a nonconvergent strongly convex
planar DFP orbit, the smallest ordered inverse-Hessian eigenvalue tends to zero. -/
theorem PlanarConvergence.orbitSmallestEigenvalueTendstoZero
    (iteration : InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    Tendsto (fun k ↦ (iteration.inverseHessianPosDef k).isHermitian.eigenvalues₀ 1)
      atTop (𝓝 0) := by
  exact SecantIteration.smallestEigenvalueTendstoZero iteration.toSecantIteration
    hf hμ hHessian hStep hWolfe hmin hnot

end DFP
