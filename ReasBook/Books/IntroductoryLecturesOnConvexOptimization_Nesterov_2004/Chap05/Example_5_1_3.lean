/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

/- Example 5.1.3 lives in the scalar self-concordance domain.

Sampled owner declarations:
* `IsSelfConcordantOnWith`, the chapter owner for self-concordance with constant `Mf`;
* `IsStandardSelfConcordantOn`, the canonical chapter owner for the case `Mf = 1`;
* `IsSelfConcordantBarrierOnWith`, the later barrier refinement extending the standard owner;
* `Real.deriv_log`, the mathlib scalar logarithm derivative owner used in proofs.

Best owner abstraction:
* source-facing: the logarithmic barrier on `(0, ∞)`;
* core/canonical: `IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ))`;
* bridge/view: `IsSelfConcordantBarrierOnWith`, which adds the barrier parameter inequality.

The scalar derivative identities for `x ↦ -log x` are proof-level derived API here, not the
mathematical owner of the example, so the file keeps only the canonical self-concordance
statement. -/

/-- Helper for Example 5.1.3: a `C²` scalar field has a differentiable gradient at the point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ ℝ →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    -- A `C²` scalar field has a differentiable first derivative.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule applies directly.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Example 5.1.3: the derivative of the directional slice of `x ↦ -log x` is the
expected affine-inverse expression. -/
private theorem negLog_directionalSlice_deriv (x u t : ℝ) :
    deriv (directionalSlice (fun y : ℝ ↦ -Real.log y) x u) t = -u * (u * t + x)⁻¹ := by
  -- Differentiate the shifted-and-scaled logarithm, then carry the outer minus sign.
  change deriv (-fun s : ℝ ↦ Real.log (x + s * u)) t = -u * (u * t + x)⁻¹
  calc
    deriv (-fun s : ℝ ↦ Real.log (x + s * u)) t
        = -deriv (fun s : ℝ ↦ Real.log (x + s * u)) t := by
            simpa using (deriv.neg (f := fun s : ℝ ↦ Real.log (x + s * u)) (x := t))
    _ = -deriv (fun s : ℝ ↦ Real.log (u * s + x)) t := by
          exact congrArg (fun h : ℝ → ℝ ↦ -deriv h t) (by
            funext s
            ring)
    _ = -(u * deriv (fun s : ℝ ↦ Real.log (s + x)) (u * t)) := by
          congr 1
          simpa [Function.comp] using
            deriv_comp_mul_left u (fun s : ℝ ↦ Real.log (s + x)) t
    _ = -(u * (u * t + x)⁻¹) := by rw [deriv_comp_add_const, Real.deriv_log]
    _ = -u * (u * t + x)⁻¹ := by ring

/-- Helper for Example 5.1.3: the Hessian quadratic form of `x ↦ -log x` at a positive point is
`u^2 / x^2`. -/
theorem negLog_hessian_quadratic_form_eq {x u : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    inner ℝ u (hessian (fun y : ℝ ↦ -Real.log y) x u) = u ^ (2 : ℕ) / x ^ (2 : ℕ) := by
  have hx0 : 0 < x := hx
  have hcont : ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) x := by
    -- Positive points lie away from the singularity of `log`, so the barrier is `C²` there.
    simpa using (Real.contDiffAt_log.2 hx0.ne').neg
  have hdiff : DifferentiableAt ℝ (fun y : ℝ ↦ -Real.log y) x :=
    hcont.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ fun y : ℝ ↦ -Real.log y) x :=
    differentiableAt_gradient_of_contDiffAt_two hcont
  have hsecond :
      secondDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u = u ^ (2 : ℕ) / x ^ (2 : ℕ) := by
    -- Compute the second derivative of the scalar slice by differentiating the affine-inverse
    -- formula once more and evaluating at `t = 0`.
    calc
      secondDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u
          = deriv (deriv (directionalSlice (fun y : ℝ ↦ -Real.log y) x u)) 0 := by
              simp [secondDirectionalDerivative, iteratedDeriv_succ]
      _ = deriv (fun t : ℝ ↦ -u * (u * t + x)⁻¹) 0 := by
            congr 1
            ext t
            rw [negLog_directionalSlice_deriv]
      _ = (-u) * deriv (fun t : ℝ ↦ (u * t + x)⁻¹) 0 := by
            rw [deriv_const_mul_field]
      _ = (-u) * (u * deriv (fun t : ℝ ↦ (t + x)⁻¹) (u * 0)) := by
            have hmul :
                deriv (fun t : ℝ ↦ (u * t + x)⁻¹) 0 =
                  u * deriv (fun t : ℝ ↦ (t + x)⁻¹) (u * 0) := by
              simpa [Function.comp] using
                deriv_comp_mul_left u (fun t : ℝ ↦ (t + x)⁻¹) 0
            rw [hmul]
      _ = (-u) * (u * deriv Inv.inv x) := by
            rw [deriv_comp_add_const]
            simp
      _ = (-u) * (u * (-(x ^ (2 : ℕ))⁻¹)) := by rw [deriv_inv]
      _ = u ^ (2 : ℕ) / x ^ (2 : ℕ) := by
            field_simp [hx0.ne']
  -- Bridge the scalar second derivative back to the Chapter 5 Hessian surface.
  calc
    inner ℝ u (hessian (fun y : ℝ ↦ -Real.log y) x u)
        = secondDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u := by
            symm
            exact secondDirectionalDerivative_eq_hessian_quadratic_form hcont
    _ = u ^ (2 : ℕ) / x ^ (2 : ℕ) := hsecond

/-- Helper for Example 5.1.3: the Hessian local norm of `x ↦ -log x` at a positive point is
`|u| / x`. -/
theorem negLog_hessianLocalNorm_eq_abs_div {x u : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ‖u‖[(fun y : ℝ ↦ -Real.log y); x] = |u| / x := by
  have hx0 : 0 < x := hx
  -- Rewrite the local norm through the Hessian quadratic form and collapse `sqrt((u/x)^2)`.
  rw [hessianLocalNorm_def, negLog_hessian_quadratic_form_eq hx, ← div_pow, Real.sqrt_sq_eq_abs,
    abs_div, abs_of_pos hx0]

/-- Helper for Example 5.1.3: the third directional derivative of `x ↦ -log x` at a positive
point is `-2 * u^3 / x^3`. -/
theorem negLog_thirdDirectionalDerivative_eq {x u : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    thirdDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u = -2 * u ^ (3 : ℕ) / x ^ (3 : ℕ) := by
  have hx0 : 0 < x := hx
  have hinv :
      iteratedDeriv 2 (fun t : ℝ ↦ (u * t + x)⁻¹) 0 = 2 * u ^ (2 : ℕ) * x ^ (-3 : ℤ) := by
    -- The affine-inverse slice is handled by mathlib's closed formula for iterated derivatives.
    rw [iteratedDeriv_eq_iterate]
    simpa [pow_two] using congrArg (fun f : ℝ → ℝ ↦ f 0) (iter_deriv_inv_linear 2 u x)
  -- Differentiate the slice once to an affine inverse, then invoke the closed inverse formula.
  calc
    thirdDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u
        = iteratedDeriv 2 (deriv (directionalSlice (fun y : ℝ ↦ -Real.log y) x u)) 0 := by
            simp [thirdDirectionalDerivative, iteratedDeriv_succ']
    _ = iteratedDeriv 2 (fun t : ℝ ↦ -u * (u * t + x)⁻¹) 0 := by
          congr 1
          ext t
          rw [negLog_directionalSlice_deriv]
    _ = -u * iteratedDeriv 2 (fun t : ℝ ↦ (u * t + x)⁻¹) 0 := by
          simp
    _ = -u * (2 * u ^ (2 : ℕ) * x ^ (-3 : ℤ)) := by rw [hinv]
    _ = -2 * u ^ (3 : ℕ) / x ^ (3 : ℕ) := by
          rw [zpow_neg]
          field_simp [hx0.ne']

-- Proof sketch: verify the standard self-concordance conditions for `x ↦ -Real.log x` on
-- `(0, ∞)` using the canonical scalar logarithm derivative identities.
/-- Example 5.1.3: the univariate logarithmic barrier `x ↦ -log x` on `(0, ∞)` is standard
self-concordant. -/
instance negLog_isStandardSelfConcordantOn :
    IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) := by
  refine
    { isOpen_domain := isOpen_Ioi
      contDiffOn := ?_
      convexOn := ?_
      third_deriv_bound := ?_ }
  · intro x hx
    -- Positive points avoid the logarithmic singularity, so the barrier is `C³` on the domain.
    have hx0 : 0 < x := hx
    simpa using (Real.contDiffAt_log.2 hx0.ne').neg.contDiffWithinAt
  · -- Route correction: use the already-computed positive Hessian quadratic form instead of a
    -- concavity-to-convexity coercion that does not elaborate reliably here.
    have hC2 : ContDiffOn ℝ 2 (fun x : ℝ ↦ -Real.log x) (Set.Ioi (0 : ℝ)) := by
      intro x hx
      have hx0 : 0 < x := hx
      simpa using (Real.contDiffAt_log.2 hx0.ne').neg.contDiffWithinAt
    apply (convexOn_iff_hessian_quadratic_form_nonneg isOpen_Ioi (convex_Ioi (0 : ℝ)) hC2).2
    intro x hx u
    rw [real_inner_comm, negLog_hessian_quadratic_form_eq hx]
    positivity
  · intro x hx u
    have hx0 : 0 < x := hx
    -- Rewrite both sides by the explicit scalar formulas and close the estimate by equality.
    rw [negLog_thirdDirectionalDerivative_eq hx, negLog_hessianLocalNorm_eq_abs_div hx]
    have habs :
        |(-2 : ℝ) * u ^ (3 : ℕ) / x ^ (3 : ℕ)| = 2 * (|u| / x) ^ (3 : ℕ) := by
      have hx3 : 0 < x ^ (3 : ℕ) := by positivity
      calc
        |(-2 : ℝ) * u ^ (3 : ℕ) / x ^ (3 : ℕ)|
            = |(-2 : ℝ) * u ^ (3 : ℕ)| / |x ^ (3 : ℕ)| := by rw [abs_div]
        _ = 2 * (|u| ^ (3 : ℕ) / x ^ (3 : ℕ)) := by
              rw [abs_mul, abs_pow, abs_of_pos hx3, mul_div_assoc]
              norm_num
        _ = 2 * (|u| / x) ^ (3 : ℕ) := by
              congr 1
              rw [← div_pow]
    simpa [mul_assoc] using habs.le
