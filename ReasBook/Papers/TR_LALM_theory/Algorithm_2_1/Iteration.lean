/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Order.Filter.Extr
public import TR_LALM_theory.Algorithm_2_1.Model

public section

open scoped InnerProductSpace NNReal

namespace LALM

variable {n m : ℕ}

/-- Helper for Algorithm 2.1: the gradient of the quadratic step model with respect
to its step argument. -/
@[expose] noncomputable def stepModelGradient
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  gradient f x + EqualityConstrained.constraintGradient c x
    (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p

/-- Helper for Algorithm 2.1: the Fréchet derivative of the quadratic step model
is represented by its step gradient. -/
lemma hasFDerivAt_stepModel
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (stepModel f c ρ β x multiplier)
      (innerSL ℝ (stepModelGradient f c ρ β x multiplier p)) p := by
  -- Differentiate the affine constraint model once, then reuse it in both
  -- the multiplier and penalty terms.
  have haffine : HasFDerivAt
      (fun q ↦ c x + fderiv ℝ c x q) (fderiv ℝ c x) p := by
    fun_prop
  have hobjective : HasFDerivAt
      (fun q ↦ ⟪gradient f x, q⟫_ℝ) (innerSL ℝ (gradient f x)) p := by
    simpa only [coe_innerSL_apply] using (innerSL ℝ (gradient f x)).hasFDerivAt
  have hmultiplier : HasFDerivAt
      (fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ)
      (innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) p := by
    simpa only [Function.comp_def, innerSL_apply_apply,
      EqualityConstrained.constraintGradient_def, ContinuousLinearMap.innerSL_apply_comp] using
      (innerSL ℝ multiplier).hasFDerivAt.comp p haffine
  have hpenalty : HasFDerivAt
      (fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2)
      ((ρ / 2) • 2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))) p := by
    simpa only [EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
      haffine.norm_sq.const_mul (ρ / 2)
  have hproximal : HasFDerivAt (fun q ↦ (β / 2) * ‖q‖ ^ 2)
      ((β / 2) • 2 • innerSL ℝ p) p := by
    simpa only [id_eq,
      ContinuousLinearMap.comp_id] using (hasFDerivAt_id p).norm_sq.const_mul (β / 2)
  -- The sum rule now matches the stable gradient normal form.
  let modelDerivative : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ((innerSL ℝ (gradient f x) +
        innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) +
      ((ρ / 2) • (2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))))) + ((β / 2) • (2 • innerSL ℝ p))
  have hsum : HasFDerivAt
      ((((fun q ↦ ⟪gradient f x, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (β / 2) * ‖q‖ ^ 2) modelDerivative p := by
    simpa only [modelDerivative] using
      ((hobjective.add hmultiplier).add hpenalty).add hproximal
  have hderivativeEq : modelDerivative =
      innerSL ℝ (stepModelGradient f c ρ β x multiplier p) := by
    ext v
    simp only [stepModelGradient, map_add, map_smul, innerSL_apply_apply,
      add_apply, smul_apply, modelDerivative]
    ring
  have hfunctions : stepModel f c ρ β x multiplier =ᶠ[nhds p]
      (((fun q ↦ ⟪gradient f x, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (β / 2) * ‖q‖ ^ 2 := by
    filter_upwards with q
    exact stepModel_def f c ρ β x multiplier q
  have hstepModel : HasFDerivAt (stepModel f c ρ β x multiplier)
      modelDerivative p := hsum.congr_of_eventuallyEq hfunctions
  exact hstepModel.congr_fderiv hderivativeEq

/-- Helper for Algorithm 2.1: every global minimizer of the quadratic step model
has zero step gradient. -/
lemma stepModelGradient_eq_zero_of_minimizes
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (stepModel f c ρ β x multiplier) Set.univ p) :
    stepModelGradient f c ρ β x multiplier p = 0 := by
  -- Fermat's rule kills the continuous linear derivative at a global minimizer.
  have hderiv : innerSL ℝ (stepModelGradient f c ρ β x multiplier p) = 0 :=
    (hp.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero
      (hasFDerivAt_stepModel f c ρ β x multiplier p)
  have hnormSq : ‖stepModelGradient f c ρ β x multiplier p‖ ^ 2 = 0 := by
    simpa only [innerSL_apply_apply, real_inner_self_eq_norm_sq,
      zero_apply] using congrArg
        (fun A ↦ A (stepModelGradient f c ρ β x multiplier p)) hderiv
  -- Vanishing squared norm identifies the gradient vector itself.
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- Helper for Algorithm 2.1: differences of step-model gradients pair with step
differences as the sum of the penalty and proximal quadratic forms. -/
lemma stepModelGradientPairing
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p q : EuclideanSpace ℝ (Fin n)) :
    ⟪stepModelGradient f c ρ β x multiplier p -
        stepModelGradient f c ρ β x multiplier q, p - q⟫_ℝ =
      ρ * ‖fderiv ℝ c x (p - q)‖ ^ 2 + β * ‖p - q‖ ^ 2 := by
  -- Linearity cancels the constant gradient terms and exposes two self-pairings.
  have hgradientDiff :
      stepModelGradient f c ρ β x multiplier p -
          stepModelGradient f c ρ β x multiplier q =
        ρ • EqualityConstrained.constraintGradient c x (fderiv ℝ c x (p - q)) +
          β • (p - q) := by
    simp only [stepModelGradient, map_add, map_sub, map_smul]
    module
  rw [hgradientDiff, inner_add_left, inner_smul_left, inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  simp only [starRingEnd_apply, star_trivial]

/-- A fixed-penalty NR-LALM run, storing its generated points, multipliers, and steps
together with the model-minimization and update laws. -/
structure Run
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) where
  /-- The penalty parameter is positive. -/
  rho_pos : 0 < ρ
  /-- The proximal parameter is positive. -/
  beta_pos : 0 < β
  /-- The generated primal points. -/
  point : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The generated multipliers. -/
  multiplier : ℕ → EuclideanSpace ℝ (Fin m)
  /-- The generated primal steps. -/
  step : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The point sequence starts at the specified initial point. -/
  point_zero : point 0 = x₀
  /-- The multiplier sequence starts at the specified initial multiplier. -/
  multiplier_zero : multiplier 0 = multiplier₀
  /-- Each stored step globally minimizes the corresponding quadratic model. -/
  minimizes_step (k : ℕ) :
    IsMinOn (stepModel f c ρ β (point k) (multiplier k)) Set.univ (step k)
  /-- The next point is obtained by adding the current step. -/
  point_succ (k : ℕ) : point (k + 1) = point k + step k
  /-- The next multiplier uses the constraint value at the updated point. -/
  multiplier_succ (k : ℕ) :
    multiplier (k + 1) = multiplier k + ρ • c (point (k + 1))

namespace Run

/-- Construct a run from explicit sequences and certificates for all defining laws. -/
def ofSequences
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (rho_pos : 0 < ρ) (beta_pos : 0 < β)
    (point : ℕ → EuclideanSpace ℝ (Fin n))
    (multiplier : ℕ → EuclideanSpace ℝ (Fin m))
    (step : ℕ → EuclideanSpace ℝ (Fin n))
    (point_zero : point 0 = x₀) (multiplier_zero : multiplier 0 = multiplier₀)
    (minimizes_step : ∀ k, IsMinOn (stepModel f c ρ β (point k) (multiplier k))
      Set.univ (step k))
    (point_succ : ∀ k, point (k + 1) = point k + step k)
    (multiplier_succ : ∀ k,
      multiplier (k + 1) = multiplier k + ρ • c (point (k + 1))) :
    Run f c ρ β x₀ multiplier₀ :=
  { rho_pos
    beta_pos
    point
    multiplier
    step
    point_zero
    multiplier_zero
    minimizes_step
    point_succ
    multiplier_succ }

/-- A run exposes the positivity, initialization, minimization, and update laws of
Algorithm 2.1. -/
theorem spec
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀) :
    (0 < ρ ∧ 0 < β) ∧
      (run.point 0 = x₀ ∧ run.multiplier 0 = multiplier₀) ∧
      ((∀ k, IsMinOn (stepModel f c ρ β (run.point k) (run.multiplier k))
          Set.univ (run.step k)) ∧
        (∀ k, run.point (k + 1) = run.point k + run.step k) ∧
        ∀ k, run.multiplier (k + 1) =
          run.multiplier k + ρ • c (run.point (k + 1))) :=
  ⟨⟨run.rho_pos, run.beta_pos⟩,
    ⟨run.point_zero, run.multiplier_zero⟩,
    ⟨run.minimizes_step, run.point_succ, run.multiplier_succ⟩⟩

/-- Reconstructing a run from all of its explicit sequences and defining laws returns
that run. -/
theorem ofSequences_spec
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀) :
    ofSequences f c ρ β x₀ multiplier₀ run.rho_pos run.beta_pos
      run.point run.multiplier run.step run.point_zero run.multiplier_zero
      run.minimizes_step run.point_succ run.multiplier_succ = run := by
  -- Structure eta reduces reconstruction to reflexivity after exposing the fields.
  cases run
  rfl

/-- Any global minimizer of a run's step model is its uniquely determined stored step. -/
theorem eq_step_of_minimizes
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀)
    (k : ℕ) (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (stepModel f c ρ β (run.point k) (run.multiplier k)) Set.univ p) :
    p = run.step k := by
  -- Both minimizers are stationary for the same strongly convex quadratic model.
  have hpzero := stepModelGradient_eq_zero_of_minimizes f c ρ β
    (run.point k) (run.multiplier k) p hp
  have hstepzero := stepModelGradient_eq_zero_of_minimizes f c ρ β
    (run.point k) (run.multiplier k) (run.step k) (run.minimizes_step k)
  have hpair := stepModelGradientPairing f c ρ β (run.point k)
    (run.multiplier k) p (run.step k)
  rw [hpzero, hstepzero, sub_self, inner_zero_left] at hpair
  have hpenaltyNonneg :
      0 ≤ ρ * ‖fderiv ℝ c (run.point k) (p - run.step k)‖ ^ 2 :=
    mul_nonneg run.rho_pos.le (sq_nonneg _)
  have hproximalNonneg : 0 ≤ β * ‖p - run.step k‖ ^ 2 :=
    mul_nonneg run.beta_pos.le (sq_nonneg _)
  have hproximalZero : β * ‖p - run.step k‖ ^ 2 = 0 := by
    linarith
  have hstepNormSq : ‖p - run.step k‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hproximalZero).resolve_left run.beta_pos.ne'
  -- Positivity of β forces the two stationary points to coincide.
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hstepNormSq))

/-- The first-order equation equivalent to minimizing the quadratic step model. -/
theorem optimality
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    β • run.step k + ρ • EqualityConstrained.constraintGradient c (run.point k)
      (fderiv ℝ c (run.point k) (run.step k)) =
      -gradient f (run.point k) - EqualityConstrained.constraintGradient c (run.point k)
        (run.multiplier k + ρ • c (run.point k)) := by
  -- Fermat stationarity expands directly to the advertised linear system.
  have hstationary := stepModelGradient_eq_zero_of_minimizes f c ρ β
    (run.point k) (run.multiplier k) (run.step k) (run.minimizes_step k)
  simp only [stepModelGradient, map_add, map_smul] at hstationary
  simp only [map_add, map_smul, sub_eq_add_neg]
  rw [← neg_add, eq_neg_iff_add_eq_zero]
  linear_combination (norm := module) hstationary

/-- The constraint linearization error at a completed LALM iteration. -/
@[expose] noncomputable def error
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    EuclideanSpace ℝ (Fin m) :=
  c (run.point (k + 1)) - c (run.point k) - fderiv ℝ c (run.point k) (run.step k)

/-- The linearization error is the nonlinear constraint increment minus its derivative
prediction. -/
theorem error_def
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    run.error k =
      c (run.point (k + 1)) - c (run.point k) -
        fderiv ℝ c (run.point k) (run.step k) := rfl

end Run

end LALM

namespace LALM

/-- Helper for Algorithm 2.1: a Lipschitz derivative on a segment gives the
quadratic first-order Taylor remainder bound. -/
lemma norm_sub_sub_fderiv_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (L : ℝ≥0) (s : Set E) (x y : E)
    (hg : ∀ z ∈ s, DifferentiableAt ℝ g z)
    (hL : LipschitzOnWith L (fderiv ℝ g) s)
    (hsegment : segment ℝ x y ⊆ s) :
    ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤
      (L : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  -- Subtract the fixed linear prediction from the restriction of `g` to the segment.
  let d : E := y - x
  let baseDerivative : F := fderiv ℝ g x d
  let path : ℝ → F := fun t ↦ g (AffineMap.lineMap x y t) - t • baseDerivative
  have hpathDeriv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt path
      (fderiv ℝ g (AffineMap.lineMap x y t) d - baseDerivative) t := by
    have hlineMem : AffineMap.lineMap x y t ∈ s :=
      hsegment (lineMap_mem_segment ℝ x y ht)
    have hcomposition : HasDerivAt (g ∘ AffineMap.lineMap x y)
        (fderiv ℝ g (AffineMap.lineMap x y t) d) t := by
      simpa only [d] using
        (hg (AffineMap.lineMap x y t) hlineMem).hasFDerivAt.comp_hasDerivAt t
          AffineMap.hasDerivAt_lineMap
    have hlinear : HasDerivAt (fun u : ℝ ↦ u • baseDerivative) baseDerivative t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const baseDerivative
    have hsub := hcomposition.sub hlinear
    have hpathEq : path =ᶠ[nhds t]
        ((g ∘ AffineMap.lineMap x y) - fun u : ℝ ↦ u • baseDerivative) := by
      filter_upwards with u
      rfl
    exact hsub.congr_of_eventuallyEq hpathEq
  have hx : x ∈ s := hsegment (left_mem_segment ℝ x y)
  have hderivBound (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      ‖deriv path t‖ ≤ (L : ℝ) * (t * ‖d‖ ^ 2) := by
    have hlineMem : AffineMap.lineMap x y t ∈ s :=
      hsegment (lineMap_mem_segment ℝ x y ⟨ht.1.le, ht.2.le⟩)
    have hderivativeLip :
        ‖fderiv ℝ g (AffineMap.lineMap x y t) - fderiv ℝ g x‖ ≤
          (L : ℝ) * dist (AffineMap.lineMap x y t) x := by
      simpa only [dist_eq_norm] using
        hL.dist_le_mul (AffineMap.lineMap x y t) hlineMem x hx
    rw [(hpathDeriv t ⟨ht.1.le, ht.2.le⟩).deriv]
    calc
      ‖fderiv ℝ g (AffineMap.lineMap x y t) d - fderiv ℝ g x d‖ ≤
          ‖fderiv ℝ g (AffineMap.lineMap x y t) - fderiv ℝ g x‖ * ‖d‖ := by
        simpa only [sub_apply] using
          (fderiv ℝ g (AffineMap.lineMap x y t) - fderiv ℝ g x).le_opNorm d
      _ ≤ ((L : ℝ) * dist (AffineMap.lineMap x y t) x) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hderivativeLip (norm_nonneg d)
      _ = (L : ℝ) * (t * ‖d‖ ^ 2) := by
        rw [dist_lineMap_left]
        simp only [Real.norm_eq_abs, abs_of_pos ht.1, dist_eq_norm, d]
        rw [norm_sub_rev]
        ring
  have hpathContinuousOn : ContinuousOn path (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hpathDeriv t ht).continuousAt.continuousWithinAt
  have hpathDifferentiableOn : DifferentiableOn ℝ path (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact (hpathDeriv t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
  have hmajorantIntegrable : IntervalIntegrable
      (fun t : ℝ ↦ (L : ℝ) * (t * ‖d‖ ^ 2)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hdisplacement :
      ‖path 1 - path 0‖ ≤ ∫ t in 0..1, (L : ℝ) * (t * ‖d‖ ^ 2) := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le zero_le_one
    · exact hpathContinuousOn
    · exact hpathDifferentiableOn
    · filter_upwards with t
      exact fun ht ↦ hderivBound t ht
    · exact hmajorantIntegrable
  have hintegralId : (∫ t : ℝ in 0..1, t) = 1 / 2 := by
    have hprimitive (t : ℝ) : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) t t := by
      have hraw := ((hasDerivAt_id t).pow 2).div_const 2
      have hderivEq : ((2 : ℝ) * t ^ (2 - 1) * 1) / 2 = t := by
        ring
      have hderiv := hraw.congr_deriv hderivEq
      have hfunctionEq : (fun u : ℝ ↦ u ^ 2 / 2) =ᶠ[nhds t]
          (fun u : ℝ ↦ (id ^ 2) u / 2) := by
        filter_upwards with u
        rfl
      exact hderiv.congr_of_eventuallyEq hfunctionEq
    have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) (fun t _ ↦ hprimitive t)
      (continuous_id.intervalIntegrable 0 1)
    norm_num at heval ⊢
  -- The endpoints recover the Taylor remainder, and the scalar majorant integrates to `L / 2`.
  calc
    ‖g y - g x - fderiv ℝ g x (y - x)‖ = ‖path 1 - path 0‖ := by
      simp only [path, baseDerivative, d, AffineMap.lineMap_apply_one,
        AffineMap.lineMap_apply_zero, one_smul, zero_smul, sub_zero]
      congr 1
      module
    _ ≤ ∫ t in 0..1, (L : ℝ) * (t * ‖d‖ ^ 2) := hdisplacement
    _ = (L : ℝ) / 2 * ‖y - x‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
        hintegralId]
      simp only [d]
      ring

/-- Half of the constraint-gradient Lipschitz constant used in the quadratic
linearization-error estimate. -/
@[expose] noncomputable def linearizationConstant
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) : ℝ≥0 :=
  h.constraintGradientLipschitz / 2

/-- The linearization constant is `L_c / 2` for the regularity certificate's
constraint-gradient Lipschitz constant `L_c`. -/
theorem linearizationConstant_def
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (h : EqualityConstrained.Regularity f c) :
    linearizationConstant h = h.constraintGradientLipschitz / 2 := rfl

namespace Run

/-- Segment containment in the regularity region yields the quadratic constraint
linearization-error estimate for one completed iteration. -/
theorem error_le
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀)
    (h : EqualityConstrained.Regularity f c) (k : ℕ)
    (hsegment : segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region) :
    ‖run.error k‖ ≤ linearizationConstant h * ‖run.step k‖ ^ 2 := by
  -- Apply the segmentwise Taylor estimate to the constraint map.
  have hremainder := norm_sub_sub_fderiv_le c h.constraintGradientLipschitz h.region
    (run.point k) (run.point (k + 1))
    (fun _ hz ↦ h.differentiableAt_constraint hz) h.lipschitzOn_constraintFDeriv hsegment
  -- The point update identifies the segment displacement with the stored step.
  simpa only [run.error_def, run.point_succ, add_sub_cancel_left,
    linearizationConstant_def, NNReal.coe_div, NNReal.coe_ofNat] using hremainder

/-- A finite prefix is admissible when every completed iteration segment lies in the
regularity region. -/
def IsAdmissiblePrefix
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀)
    (h : EqualityConstrained.Regularity f c) (K : ℕ) : Prop :=
  ∀ k < K, segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region

/-- Admissibility of a finite prefix is exactly segment containment for every index
strictly below its number of completed iterations. -/
theorem isAdmissiblePrefix_iff
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ρ β : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (run : Run f c ρ β x₀ multiplier₀)
    (h : EqualityConstrained.Regularity f c) (K : ℕ) :
    run.IsAdmissiblePrefix h K ↔
      ∀ k < K, segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region := Iff.rfl

end Run

end LALM

end
