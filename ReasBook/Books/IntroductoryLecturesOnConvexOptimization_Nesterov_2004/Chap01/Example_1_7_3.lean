/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open NewtonSystem

/- Example 1.7.3 lives in the Chapter 1 Newton-system domain.

Primary domain:
* scalar Newton iteration for the equation `φ(t) = t / √(1 + t²)`

Sampled owner-style declarations:
* `NewtonSystem.step`
* `NewtonSystem.orbit`
* `NewtonSystem.step_scalar_def`

Source/core/bridge triage:
* source-facing: the specific scalar map `newtonUnivariateRootFunction` and the convergence,
  periodicity, and divergence statements of Example 1.7.3
* core/canonical: the admissible-point Newton owner API from `Algorithm_1_7_1`
* bridge/view: the scalar step formula `NewtonSystem.step_scalar_def`

Primitive data:
* the scalar map `newtonUnivariateRootFunction`
* the pointwise derivative-nonvanishing proof needed to place scalar points in the owner
  admissible domain

Derived API:
* the public scalar bridge `newtonUnivariateRootAdmissiblePoint` into the owner admissible domain
* the scalar Newton update `newtonUnivariateRootStep` and its canonical orbit
  `newtonUnivariateRootOrbit`, both obtained from the owner Newton constructions

This file therefore keeps the source-facing scalar example and its asymptotic theorems, but it
reuses the chapter owner step/orbit API directly. The only extra public declarations are the thin
scalar bridge names needed to keep the theorem surface free of private implementation scaffolding.
-/

/-- The scalar equation map `φ(t) = t / √(1 + t²)` used in the Newton root-finding example. -/
def newtonUnivariateRootFunction (t : ℝ) : ℝ :=
  t / Real.sqrt (1 + t ^ (2 : ℕ))

/-- Helper for Example 1.7.3: the square-root denominator has derivative `t / √(1 + t²)`. -/
private theorem hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.sqrt (1 + y ^ (2 : ℕ)))
      (x / Real.sqrt (1 + x ^ (2 : ℕ))) x := by
  -- Differentiate the inner quadratic first, then pass through `Real.sqrt`.
  have h_inner : HasDerivAt (fun y : ℝ ↦ 1 + y ^ (2 : ℕ)) (2 * x) x := by
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
      (((hasDerivAt_id x).pow 2).const_add 1)
  have hx : (1 + x ^ (2 : ℕ)) ≠ 0 := by
    nlinarith
  -- The square-root simplification uses that `1 + x²` is strictly positive.
  convert h_inner.sqrt hx using 1
  field_simp [hx]

/-- Helper for Example 1.7.3: the quotient `t / √(1 + t²)` has derivative
`((√(1 + t²))⁻¹)^3`. -/
private theorem hasDerivAt_newtonUnivariateRootFunction (x : ℝ) :
    HasDerivAt newtonUnivariateRootFunction
      ((Real.sqrt (1 + x ^ (2 : ℕ)))⁻¹ ^ (3 : ℕ)) x := by
  -- Differentiate the quotient `x / √(1 + x²)` using the previous square-root derivative.
  have hsqrt := hasDerivAt_sqrt_one_add_sq x
  have hx0 : Real.sqrt (1 + x ^ (2 : ℕ)) ≠ 0 := by
    exact (Real.sqrt_ne_zero (show 0 ≤ 1 + x ^ (2 : ℕ) by positivity)).2 (by nlinarith)
  have hdiv := (hasDerivAt_id x).div hsqrt hx0
  -- After clearing denominators, only the identity `(√(1 + x²))² = 1 + x²` remains.
  convert hdiv using 1
  · field_simp [hx0]
    simp only [id_eq]
    rw [Real.sq_sqrt (show 0 ≤ 1 + x ^ (2 : ℕ) by positivity)]
    ring_nf

/-- The derivative of `t ↦ t / √(1 + t²)` is `1 / (√(1 + t²))^3`. -/
-- Proof sketch: differentiate the quotient `t / √(1 + t²)` using the chain rule for
-- `t ↦ √(1 + t²)` and simplify the resulting expression.
theorem deriv_newtonUnivariateRootFunction (t : ℝ) :
    deriv newtonUnivariateRootFunction t =
      1 / (Real.sqrt (1 + t ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  -- Convert the `HasDerivAt` formula into the surface derivative expression used later.
  simpa [one_div] using (hasDerivAt_newtonUnivariateRootFunction t).deriv

/-- The derivative of `newtonUnivariateRootFunction` never vanishes. -/
theorem deriv_newtonUnivariateRootFunction_ne_zero (t : ℝ) :
    deriv newtonUnivariateRootFunction t ≠ 0 := by
  rw [deriv_newtonUnivariateRootFunction]
  positivity

/- The scalar point `t` viewed in the canonical admissible Newton domain of
`newtonUnivariateRootFunction`. This is internal bridge data used to specialize the chapter owner
API to the source-facing scalar example. -/
private abbrev newtonUnivariateRootAdmissiblePoint (t : ℝ) :
    AdmissiblePoint newtonUnivariateRootFunction :=
  ⟨t, fderiv_det_ne_zero_of_deriv_ne_zero (deriv_newtonUnivariateRootFunction_ne_zero t)⟩

/-- The scalar Newton update for `newtonUnivariateRootFunction`, obtained from the owner Newton
step. -/
def newtonUnivariateRootStep (t : ℝ) : ℝ :=
  step newtonUnivariateRootFunction (newtonUnivariateRootAdmissiblePoint t)

/- Every Newton step for `newtonUnivariateRootFunction` stays in the canonical admissible
domain. This is internal bridge data needed to specialize `NewtonSystem.orbit` to the scalar
example. -/
private theorem newtonUnivariateRootStepPreservesAdmissibility :
    StepPreservesAdmissibility newtonUnivariateRootFunction := by
  intro t
  exact fderiv_det_ne_zero_of_deriv_ne_zero
    (deriv_newtonUnivariateRootFunction_ne_zero (step newtonUnivariateRootFunction t))

/-- The canonical Newton orbit for `newtonUnivariateRootFunction`, viewed as an ordinary scalar
iterate sequence. -/
def newtonUnivariateRootOrbit (t0 : ℝ) : ℕ → ℝ :=
  orbit newtonUnivariateRootFunction
    (newtonUnivariateRootAdmissiblePoint t0)
    newtonUnivariateRootStepPreservesAdmissibility

/-- The canonical Newton orbit for this scalar example agrees with ordinary iteration of the
scalar Newton update. -/
theorem newtonUnivariateRootIterates_eq_iterate (t0 : ℝ) (k : ℕ) :
    (newtonUnivariateRootOrbit t0) k = (newtonUnivariateRootStep^[k]) t0 := by
  induction k with
  | zero =>
      rfl
  | succ k hk =>
      have hpoint :
          orbitPoint newtonUnivariateRootFunction (newtonUnivariateRootAdmissiblePoint t0)
              newtonUnivariateRootStepPreservesAdmissibility k =
            newtonUnivariateRootAdmissiblePoint ((newtonUnivariateRootOrbit t0) k) := by
        apply Subtype.ext
        rfl
      rw [Function.iterate_succ_apply']
      rw [newtonUnivariateRootOrbit, orbit_succ newtonUnivariateRootFunction
        (newtonUnivariateRootAdmissiblePoint t0)
        newtonUnivariateRootStepPreservesAdmissibility k, hpoint, hk]
      rfl

/-- Newton's method for `newtonUnivariateRootFunction` reduces to the cubic map `t ↦ -t^3`. -/
-- Proof sketch: expand the scalar Newton update with `NewtonSystem.step_scalar_def`, substitute
-- the derivative formula from
-- `deriv_newtonUnivariateRootFunction`, and simplify the resulting quotient.
theorem newtonUnivariateRootStep_eq_neg_cube (t : ℝ) :
    newtonUnivariateRootStep t = -(t ^ (3 : ℕ)) := by
  -- Expand the Newton update into the textbook scalar formula.
  rw [newtonUnivariateRootStep,
    step_scalar_def newtonUnivariateRootFunction t (deriv_newtonUnivariateRootFunction_ne_zero t),
    newtonUnivariateRootFunction, deriv_newtonUnivariateRootFunction]
  let s : ℝ := Real.sqrt (1 + t ^ (2 : ℕ))
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact (Real.sqrt_ne_zero (show 0 ≤ 1 + t ^ (2 : ℕ) by positivity)).2 (by nlinarith)
  have hs_sq : s ^ (2 : ℕ) = 1 + t ^ (2 : ℕ) := by
    dsimp [s]
    simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ 1 + t ^ (2 : ℕ) by positivity))
  -- Clearing the nonzero square-root denominator reduces the step to a polynomial identity.
  have hmain : t - (t / s) / (1 / s ^ (3 : ℕ)) = -(t ^ (3 : ℕ)) := by
    field_simp [hs0]
    rw [hs_sq]
    ring
  simpa [s] using hmain

/-- Helper for Example 1.7.3: taking absolute values turns the Newton step into the cubic map on
magnitudes. -/
lemma abs_newtonUnivariateRootStep_eq_abs_cube (t : ℝ) :
    |newtonUnivariateRootStep t| = |t| ^ (3 : ℕ) := by
  -- The sign disappears under absolute value, leaving a pure cubic growth law.
  rw [newtonUnivariateRootStep_eq_neg_cube, abs_neg, abs_pow]

/-- Helper for Example 1.7.3: the subsequence `3^k` tends to `+∞`. -/
lemma three_pow_tendsto_atTop :
    Filter.Tendsto (fun k : ℕ ↦ 3 ^ k) Filter.atTop Filter.atTop := by
  -- Compare `3^k` to the identity sequence using the standard lower bound `k < 3^k`.
  refine Filter.tendsto_atTop.mpr ?_
  intro n
  filter_upwards [Filter.eventually_ge_atTop n] with k hk
  exact le_trans hk (Nat.lt_pow_self (show 1 < 3 by decide)).le

/-- Example 1.7.3: for the Newton iteration associated to `φ(t) = t / √(1 + t²)`, the iterates
started from `t₀` satisfy `|t_k| = |t₀|^(3^k)`. Consequently the method converges cubically to
`0` on `|t₀| < 1`, is two-periodic at `t₀ = ±1`, and diverges in magnitude on `|t₀| > 1`. -/
-- Proof sketch: use `newtonUnivariateRootStep_eq_neg_cube` to rewrite the recursion as
-- `t_{k+1} = -t_k^3`, then take absolute values and iterate the identity `|t_{k+1}| = |t_k|^3`.
theorem abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow (t0 : ℝ) (k : ℕ) :
    |(newtonUnivariateRootOrbit t0) k| = |t0| ^ (3 ^ k) := by
  induction k with
  | zero =>
      -- The zeroth iterate is the starting point, and `3^0 = 1`.
      rw [newtonUnivariateRootIterates_eq_iterate]
      simp
  | succ k hk =>
      -- One Newton step raises the current magnitude to the third power.
      rw [newtonUnivariateRootIterates_eq_iterate, Function.iterate_succ_apply',
        abs_newtonUnivariateRootStep_eq_abs_cube]
      rw [show |(newtonUnivariateRootStep^[k]) t0| = |t0| ^ (3 ^ k) by
        simpa [newtonUnivariateRootIterates_eq_iterate] using hk]
      calc
        (|t0| ^ (3 ^ k)) ^ (3 : ℕ) = |t0| ^ (3 ^ k * 3) := by rw [pow_mul]
        _ = |t0| ^ (3 ^ Nat.succ k) := by rw [Nat.pow_succ]

/-- If `|t₀| < 1`, the Newton iterates for `t / √(1 + t²)` converge to `0`. -/
-- Proof sketch: combine
-- `abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow` with the fact that
-- `|t₀|^(3^k) → 0` for every real number of absolute value strictly less than `1`.
theorem newtonUnivariateRootIterates_tendsto_zero_of_abs_lt_one (t0 : ℝ)
    (ht0 : |t0| < 1) :
    Filter.Tendsto (newtonUnivariateRootOrbit t0) Filter.atTop (nhds 0) := by
  -- Move to absolute values and then use the explicit formula `|t_k| = |t0|^(3^k)`.
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hpow : Filter.Tendsto (fun n : ℕ ↦ |t0| ^ n) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg t0) ht0
  convert hpow.comp three_pow_tendsto_atTop using 1
  ext k
  simp [Function.comp, abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow]

/-- If `|t₀| = 1`, then `t₀` is a periodic point of period `2` for the scalar Newton map attached
to `t / √(1 + t²)`. -/
-- Proof sketch: from `newtonUnivariateRootStep_eq_neg_cube` and `|t₀| = 1`, every iterate has
-- absolute value `1`, and the update reduces to multiplication by `-1`, yielding period `2`.
theorem newtonUnivariateRootStep_isPeriodicPt_of_abs_eq_one (t0 : ℝ)
    (ht0 : |t0| = 1) :
    Function.IsPeriodicPt newtonUnivariateRootStep 2 t0 := by
  -- Route correction: the `|t0| = 1` regime is best handled by the exact classification
  -- `t0 = 1 ∨ t0 = -1`, then computing two explicit Newton steps.
  have hcases : t0 = 1 ∨ t0 = -1 := by
    rwa [← abs_one, abs_eq_abs] at ht0
  rcases hcases with rfl | rfl
  · rw [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply', Function.iterate_one]
    norm_num [newtonUnivariateRootStep_eq_neg_cube]
  · rw [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply', Function.iterate_one]
    norm_num [newtonUnivariateRootStep_eq_neg_cube]

/-- Consequently, if `|t₀| = 1`, the Newton iterate sequence repeats with period `2`. -/
theorem newtonUnivariateRootIterates_two_periodic_of_abs_eq_one (t0 : ℝ)
    (ht0 : |t0| = 1) (k : ℕ) :
    (newtonUnivariateRootOrbit t0) (k + 2) = (newtonUnivariateRootOrbit t0) k := by
  have hk := (newtonUnivariateRootStep_isPeriodicPt_of_abs_eq_one t0 ht0).apply_iterate k
  rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Function.iterate_add_apply] at hk
  rw [newtonUnivariateRootIterates_eq_iterate, newtonUnivariateRootIterates_eq_iterate]
  simpa [Nat.add_comm] using hk

/-- If `|t₀| > 1`, the absolute values of the Newton iterates for `t / √(1 + t²)` tend to
`+∞`, so the method diverges in magnitude. -/
-- Proof sketch: use
-- `abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow`; when `|t₀| > 1`, the powers
-- `|t₀|^(3^k)` grow without bound.
theorem abs_newtonUnivariateRootIterates_tendsto_atTop_of_one_lt_abs (t0 : ℝ)
    (ht0 : 1 < |t0|) :
    Filter.Tendsto (fun k ↦ |(newtonUnivariateRootOrbit t0) k|)
      Filter.atTop Filter.atTop := by
  -- The explicit magnitude formula reduces divergence to the standard `r^n → +∞` fact for `r > 1`.
  have hpow : Filter.Tendsto (fun n : ℕ ↦ |t0| ^ n) Filter.atTop Filter.atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt ht0
  convert hpow.comp three_pow_tendsto_atTop using 1
  ext k
  simp [Function.comp, abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow]

end
