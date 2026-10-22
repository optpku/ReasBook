/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Gradient

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "initialPoint" => EuclideanSpace.single 0 (1 : ℝ)

/- Primary domain:
* gradient-method dynamics for a concrete polynomial objective on `ℝ²`

Source/core/bridge triage:
* source-facing: the quartic objective and the convergence-to-a-saddle example
* core/canonical owners: `gradientMethod stepSize f x0`, `HasGradientAt f 0 xStar`, and
  `IsLocalMin f xStar`
* bridge/view: the later coordinate formulas for `∇ saddlePointConvergenceObjective` and its
  Hessian in `Proposition_1_6_12`

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `HasGradientAt f (0 : E) xBar` in `Definition_1_4_15.lean`
* `isLocalMin_hasGradientAt_zero_of_differentiableAt` in `Theorem_1_4_13.lean`
* `IsLocalMin` from mathlib

Primitive data:
* the quartic objective `saddlePointConvergenceObjective`

Derived API:
* the canonical start point and limit point of the example trajectory
* the stationary/local-minimum analysis, which is derived from the owner abstractions and
  developed later in `Proposition_1_6_12`

Example 1.6.11 itself therefore keeps only the source-facing quartic objective and the final
convergence statement, rather than a parallel local helper API for differentiability, stationarity,
and local minimality. -/

/-- The quartic example objective
`f(x₁, x₂) = (1 / 2) x₁² + (1 / 4) x₂⁴ - (1 / 2) x₂²`. -/
def saddlePointConvergenceObjective (x : E) : ℝ :=
  (1 / 2 : ℝ) * x 0 ^ 2 + (1 / 4 : ℝ) * x 1 ^ 4 - (1 / 2 : ℝ) * x 1 ^ 2

/-- Helper for Example 1.6.11: the quartic objective has gradient
`(x₁, x₂^3 - x₂)`. -/
private lemma saddlePointConvergenceObjective_hasGradientAt (x : E) :
    HasGradientAt saddlePointConvergenceObjective
      (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1 ^ 3 - x 1)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  change
    HasFDerivAt
      (fun y : E ↦
        (1 / 2 : ℝ) * y 0 ^ 2 + (1 / 4 : ℝ) * y 1 ^ 4 - (1 / 2 : ℝ) * y 1 ^ 2)
      ((InnerProductSpace.toDual ℝ E)
        (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1 ^ 3 - x 1)))
      x
  let proj0 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : E →L[ℝ] ℝ)
  let proj1 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : E →L[ℝ] ℝ)
  have h0 : HasFDerivAt (fun y : E ↦ y 0) proj0 x := by
    simpa [proj0] using (PiLp.hasFDerivAt_apply 2 x 0)
  have h1 : HasFDerivAt (fun y : E ↦ y 1) proj1 x := by
    simpa [proj1] using (PiLp.hasFDerivAt_apply 2 x 1)
  -- Differentiate the coordinate monomials and scale them by the objective coefficients.
  have hsq0 :
      HasFDerivAt (fun y : E ↦ y 0 ^ 2) (((2 : ℝ) * x 0) • proj0) x := by
    simpa [two_nsmul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using (h0.pow 2)
  have hpow4 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 4) (((4 : ℝ) * x 1 ^ 3) • proj1) x := by
    simpa [pow_succ, pow_succ', mul_comm, mul_left_comm, mul_assoc] using (h1.pow 4)
  have hsq1 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 2) (((2 : ℝ) * x 1) • proj1) x := by
    simpa [two_nsmul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using (h1.pow 2)
  have hmain :
      HasFDerivAt
        (fun y : E ↦
          (1 / 2 : ℝ) * y 0 ^ 2 + (1 / 4 : ℝ) * y 1 ^ 4 - (1 / 2 : ℝ) * y 1 ^ 2)
        ((x 0) • proj0 + (x 1 ^ 3 - x 1) • proj1) x := by
    -- Assemble the Fréchet derivative from the three scalar polynomial pieces.
    simpa [sub_eq_add_neg, proj0, proj1, smul_add, add_smul, mul_smul, mul_assoc, mul_comm,
      mul_left_comm, add_comm, add_left_comm, add_assoc] using
      (hsq0.const_smul (1 / 2 : ℝ)).add
        ((hpow4.const_smul (1 / 4 : ℝ)).sub (hsq1.const_smul (1 / 2 : ℝ)))
  have hdual :
      (x 0) • proj0 + (x 1 ^ 3 - x 1) • proj1 =
        (InnerProductSpace.toDual ℝ E)
          (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1 ^ 3 - x 1)) := by
    -- The coordinate linear form is exactly the inner-product pairing with the gradient vector.
    ext y
    have hinner0 : inner ℝ (EuclideanSpace.single 0 (x 0)) y = (x 0) * y 0 := by
      simpa using (EuclideanSpace.inner_single_left 0 (x 0) y)
    have hinner1 :
        inner ℝ (EuclideanSpace.single 1 (x 1 ^ 3 - x 1)) y = (x 1 ^ 3 - x 1) * y 1 := by
      simpa using (EuclideanSpace.inner_single_left 1 (x 1 ^ 3 - x 1) y)
    rw [InnerProductSpace.toDual_apply_apply, inner_add_left, hinner0, hinner1]
    simp [proj0, proj1]
  exact hmain.congr_fderiv hdual

/-- Helper for Example 1.6.11: with unit steps, every iterate after the first one is the
origin. -/
private lemma unitStepGradientMethod_eq_origin_succ (k : ℕ) :
    gradientMethod (fun _ : ℕ ↦ (1 : ℝ))
      saddlePointConvergenceObjective initialPoint (k + 1) = (0 : E) := by
  induction k with
  | zero =>
      -- The first unit step subtracts the gradient `(1, 0)` from the start point `(1, 0)`.
      rw [gradientMethod_succ, gradientMethod_zero]
      have hgrad :
          ∇ saddlePointConvergenceObjective initialPoint = initialPoint := by
        have hgrad_raw :=
          (saddlePointConvergenceObjective_hasGradientAt initialPoint).gradient
        have hcoord0 :
            (∇ saddlePointConvergenceObjective initialPoint) (0 : Fin 2) = 1 := by
          simpa using congrArg (fun v : E ↦ v (0 : Fin 2)) hgrad_raw
        have hcoord1 :
            (∇ saddlePointConvergenceObjective initialPoint) (1 : Fin 2) = 0 := by
          simpa using congrArg (fun v : E ↦ v (1 : Fin 2)) hgrad_raw
        ext i
        fin_cases i <;> simp [hcoord0, hcoord1]
      rw [hgrad]
      ext i
      fin_cases i <;> simp
  | succ k hk =>
      -- Once the trajectory reaches the origin, the vanishing gradient keeps it there.
      rw [gradientMethod_succ, hk]
      have hgrad0 : ∇ saddlePointConvergenceObjective (0 : E) = 0 := by
        have hgrad_raw :=
          (saddlePointConvergenceObjective_hasGradientAt (0 : E)).gradient
        have hcoord0 :
            (∇ saddlePointConvergenceObjective (0 : E)) (0 : Fin 2) = 0 := by
          simpa using congrArg (fun v : E ↦ v (0 : Fin 2)) hgrad_raw
        have hcoord1 :
            (∇ saddlePointConvergenceObjective (0 : E)) (1 : Fin 2) = 0 := by
          simpa using congrArg (fun v : E ↦ v (1 : Fin 2)) hgrad_raw
        ext i
        fin_cases i <;> simp [hcoord0, hcoord1]
      simp [hgrad0]

/-- Helper for Example 1.6.11: along the vertical axis, the quartic objective becomes the scalar
polynomial `(1 / 4) t^4 - (1 / 2) t^2`. -/
private lemma saddlePointConvergenceObjective_axis_slice_eq (t : ℝ) :
    saddlePointConvergenceObjective (EuclideanSpace.single 1 t) =
      (1 / 4 : ℝ) * t ^ 4 - (1 / 2 : ℝ) * t ^ 2 := by
  -- Restricting to `(0, t)` kills the first-coordinate term.
  simp [saddlePointConvergenceObjective]

/-- Helper for Example 1.6.11: the vertical-axis slice is strictly below the origin value for
small positive `t`. -/
private lemma saddlePointConvergenceObjective_axis_slice_neg_of_pos_lt_one
    {t : ℝ} (hpos : 0 < t) (hone : t < 1) :
    saddlePointConvergenceObjective (EuclideanSpace.single 1 t) <
      saddlePointConvergenceObjective (0 : E) := by
  have ht_sq_pos : 0 < t ^ 2 := by
    positivity
  have ht_sq_lt_one : t ^ 2 < 1 := by
    nlinarith
  -- The scalar slice equals `t^2 ((1/4) t^2 - 1/2)`, which is negative when `0 < t < 1`.
  simp [saddlePointConvergenceObjective]
  nlinarith [ht_sq_pos, ht_sq_lt_one]

-- Proof sketch: along the trajectory started at `(1, 0)` with unit step size, the second
-- coordinate stays equal to `0` because the second gradient component is `x₂^3 - x₂`, while the
-- first coordinate is sent from `1` to `0` in one step and then remains there. This makes the
-- iterate sequence eventually constant at `(0, 0)`.
/-- Example 1.6.11 (1): for
`f(x₁, x₂) = (1 / 2) x₁² + (1 / 4) x₂⁴ - (1 / 2) x₂²`, the unit-step gradient method started at
`(1, 0)` converges to `(0, 0)`. -/
theorem saddlePointConvergenceObjective_unitStepGradientMethod_tendsto_origin :
    Tendsto
      (gradientMethod (fun _ : ℕ ↦ (1 : ℝ))
        saddlePointConvergenceObjective initialPoint)
      atTop (nhds (0 : E)) := by
  -- The trajectory is eventually constant because every iterate with index at least `1` is `0`.
  refine tendsto_atTop_of_eventually_const (i₀ := 1) ?_
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  simpa [Nat.add_comm] using unitStepGradientMethod_eq_origin_succ k

-- Proof sketch: the polynomial objective has gradient `(x₁, x₂^3 - x₂)`, which vanishes at
-- `(0, 0)`.
/-- Example 1.6.11 (2): the limit point `(0, 0)` is a stationary point of
`saddlePointConvergenceObjective`. -/
theorem saddlePointConvergenceObjective_origin_is_stationary :
    HasGradientAt saddlePointConvergenceObjective 0 (0 : E) := by
  -- Evaluate the explicit gradient formula at the origin.
  convert saddlePointConvergenceObjective_hasGradientAt (0 : E) using 1
  ext i
  fin_cases i <;> simp

-- Proof sketch: compare the values of `saddlePointConvergenceObjective` along the line `(0, t)`
-- for small nonzero `t`, where the objective becomes negative.
/-- Example 1.6.11 (3): the stationary point `(0, 0)` is not a local minimum of
`saddlePointConvergenceObjective`. -/
theorem saddlePointConvergenceObjective_origin_is_not_localMin :
    ¬ IsLocalMin saddlePointConvergenceObjective (0 : E) := by
  intro hmin
  let g : ℝ → E := fun t ↦ t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hmin' : IsLocalMin saddlePointConvergenceObjective (g 0) := by
    simpa [g] using hmin
  have hcont : ContinuousAt g 0 := by
    -- The vertical-axis parameterization is an affine continuous map.
    simpa [g] using
      ((continuous_id.smul continuous_const).continuousAt :
        ContinuousAt (fun t : ℝ ↦ t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0)
  have hg :
      ∀ t : ℝ, g t = EuclideanSpace.single (1 : Fin 2) t := by
    intro t
    ext i
    fin_cases i <;> simp [g]
  have hcomp :
      (saddlePointConvergenceObjective ∘ g) =
        fun t : ℝ ↦ saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t) := by
    funext t
    simp [Function.comp, hg t]
  have hslice :
      IsLocalMin
        (fun t : ℝ ↦ saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t))
        0 := by
    -- Any local minimum at the origin would restrict to a local minimum on the vertical axis.
    simpa [hcomp] using hmin'.comp_continuous hcont
  have hset :
      {t : ℝ |
          saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) 0) ≤
            saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t)} ∈
        nhds (0 : ℝ) := by
    simpa [IsLocalMin, IsMinFilter] using hslice
  rcases Metric.mem_nhds_iff.mp hset with ⟨ε, hε, hεmem⟩
  let t : ℝ := min (ε / 2) (1 / 2)
  have ht_pos : 0 < t := by
    dsimp [t]
    have hε_half : 0 < ε / 2 := by
      positivity
    positivity
  have ht_lt_one : t < 1 := by
    have hhalf : (1 / 2 : ℝ) < 1 := by
      norm_num
    dsimp [t]
    exact (min_lt_iff.mpr (Or.inr hhalf))
  have ht_mem : t ∈ Metric.ball (0 : ℝ) ε := by
    have ht_lt_eps : t < ε := by
      dsimp [t]
      calc
        min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
        _ < ε := by
          nlinarith
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht_pos] using ht_lt_eps
  have hlocal :
      saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) 0) ≤
        saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t) :=
    hεmem ht_mem
  have hstrict :
      saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t) <
        saddlePointConvergenceObjective (0 : E) :=
    saddlePointConvergenceObjective_axis_slice_neg_of_pos_lt_one ht_pos ht_lt_one
  -- The local-minimum inequality contradicts the explicit nearby point with strictly smaller value.
  simpa using (not_lt_of_ge hlocal) hstrict

-- Proof sketch: combine the three atomic clauses of Example 1.6.11.
/-- The unit-step quartic-example trajectory converges to a stationary point that is not a local
minimum. -/
theorem unitStepGradientMethod_converges_to_nonminimizing_stationary_point :
    Tendsto
      (gradientMethod (fun _ : ℕ ↦ (1 : ℝ))
        saddlePointConvergenceObjective initialPoint)
      atTop (nhds (0 : E)) ∧
      HasGradientAt saddlePointConvergenceObjective 0 (0 : E) ∧
      ¬ IsLocalMin saddlePointConvergenceObjective (0 : E) := by
  -- Combine the three source-facing clauses of Example 1.6.11.
  exact ⟨saddlePointConvergenceObjective_unitStepGradientMethod_tendsto_origin,
    saddlePointConvergenceObjective_origin_is_stationary,
    saddlePointConvergenceObjective_origin_is_not_localMin⟩

end
