/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_1

open scoped ConstrainedArgmin CubicRegularizationModelNotation Gradient

noncomputable section

universe u

section CubicRegularizationModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped CubicRegularizationResidual

/- Lemma 4.1.5 lies in the chapter cubic-regularization model-value domain on complete real
inner-product spaces.

Sampled owner declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`
* `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y` in
  `Definition_4_1_3`
* `cubicRegularizationProblem`, `Φ[f; M](x)`, and `f̄[f; M](x)` in `Definition_4_1_3`
* `HessianLipschitzOn.secondOrderTaylorModel_error_le` in `Lemma_4_1_1`

Source/core/bridge triage:
* source-facing: the feasible-comparison and descent consequences of Lemma 4.1.5
* core/canonical: the whole-space owner `Φ[f; M](x)` and its real-valued surface `f̄[f; M](x)`
* bridge/view: realizing `f̄[f; M](x)` at the current minimizing trial point `trialPoint` from
  `IsMinOn (m[f; M](x)) Set.univ trialPoint`

Primitive data:
* the objective `f`
* the regularization parameter `M`
* the current minimizing trial point `trialPoint`
* the owner hypotheses `IsMinOn (m[f; M](x)) Set.univ trialPoint` and
  `HessianLipschitzOn L 𝓕 f`

Derived API:
* the pointwise residual `r[trialPoint] x`, which specializes to the textbook `r_M(x)` after
  choosing the minimizing trial point `trialPoint = T_M(x)`
* the pointwise feasible-comparison upper bound for `f̄[f; M](x)`
* the source-facing minimum corollary of that pointwise comparison
* the residual-cube decrease estimate
* the local upper bound `f y ≤ m_x^M(y)` on feasible points when `M ≥ L`
* objective control of a minimizing trial point once that trial point is known to lie in `𝓕`

The previous local wrapper `cubicRegularizedModelValue` duplicated the canonical owner
`Φ[f; M](x)`; this file now states the source-facing lemmas directly on that owner and leaves
realization at a chosen minimizing trial point to
`cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`. -/

variable {trialPoint : E}

/-- Helper for Lemma 4.1.5: restricting the cubic model to the affine line
`t ↦ x + t • (trialPoint - x)` preserves local minimality at the minimizing parameter `t = 1`. -/
private theorem cubic_model_line_isLocalMin_at_one
    {f : E → ℝ} {M : ℝ} {x : E}
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint) :
    IsLocalMin
      (fun t : ℝ ↦ (m[f; M](x)) (x + t • (trialPoint - x)))
      1 := by
  have hlocal : IsLocalMin (m[f; M](x)) trialPoint :=
    hstep.isLocalMin (by simp)
  have hlocal1 :
      IsLocalMin (m[f; M](x)) (x + (1 : ℝ) • (trialPoint - x)) := by
    -- The affine slice hits the minimizing trial point exactly at the parameter `1`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlocal
  have hline :
      ContinuousAt (fun t : ℝ ↦ x + t • (trialPoint - x)) 1 := by
    -- The affine line through `x` and `trialPoint` is smooth, hence continuous at `1`.
    simpa [one_smul] using
      (HasDerivAt.const_add x
        ((hasDerivAt_id (1 : ℝ)).smul_const (trialPoint - x))).continuousAt
  -- Compose ambient local minimality with the affine line parametrization.
  change IsLocalMin
    ((m[f; M](x)) ∘ fun t : ℝ ↦ x + t • (trialPoint - x))
    1
  exact hlocal1.comp_continuous (g := fun t : ℝ ↦ x + t • (trialPoint - x)) (b := 1) hline

/-- Helper for Lemma 4.1.5: comparing the minimizing trial point with its reflection across `x`
shows that the gradient pairing with the trial displacement is nonpositive. -/
private theorem cubic_model_gradient_pairing_nonpos_of_reflection
    {f : E → ℝ} {M : ℝ} {x : E}
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint) :
    inner ℝ (∇ f x) (trialPoint - x) ≤ 0 := by
  let d : E := trialPoint - x
  have hmin :
      m[f; M](x; trialPoint) ≤ (m[f; M](x)) (x - d) :=
    hstep (by simp)
  have htrial :
      m[f; M](x; trialPoint) =
        f x + inner ℝ (∇ f x) d +
          (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
          (M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Expand the model at the minimizing trial point in terms of the displacement `d`.
    simp [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply, d]
  have hreflect :
      (m[f; M](x)) (x - d) =
        f x - inner ℝ (∇ f x) d +
          (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
          (M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- At the reflected point, the linear term changes sign while the quadratic and cubic terms
    -- stay unchanged.
    have hreflect : x - d = x + (-1 : ℝ) • d := by
      simp [sub_eq_add_neg]
    rw [hreflect, cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
    simp
    ring
  rw [htrial, hreflect] at hmin
  linarith

/-- Helper for Lemma 4.1.5: the scalar line slice through
`t ↦ x + t • (trialPoint - x)` satisfies the textbook stationarity identity at the minimizing
parameter `t = 1`. -/
private theorem cubic_model_directional_stationarity_at_trialPoint
    {f : E → ℝ} {M : ℝ} {x : E}
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint) :
    inner ℝ (∇ f x) (trialPoint - x) +
      inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
      (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) = 0 := by
  let d : E := trialPoint - x
  have hlineMin :
      IsLocalMin (fun t : ℝ ↦ (m[f; M](x)) (x + t • d)) 1 := by
    -- Recenter the source optimality condition on the scalar parameter `t = 1`.
    simpa [d] using cubic_model_line_isLocalMin_at_one (trialPoint := trialPoint) hstep
  have hmodel :
      HasDerivAt
        (fun t : ℝ ↦ (m[f; M](x)) (x + t • d))
        (inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d +
          (M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ))
        1 := by
    have hslice :
        (fun t : ℝ ↦ (m[f; M](x)) (x + t • d)) =
          fun t : ℝ ↦
            f x +
              inner ℝ (∇ f x) d * t +
              ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ) +
              (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ) := by
      -- Expanding the model on the affine line produces a scalar cubic polynomial with an
      -- absolute-value cubic penalty.
      funext t
      rw [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
      have hdisp : x + t • d - x = t • d := by
        simp [sub_eq_add_neg, add_assoc]
      rw [hdisp, norm_smul, mul_pow]
      simp [inner_smul_right, inner_smul_left, mul_assoc]
      ring
    rw [hslice]
    have hlin :
        HasDerivAt (fun t : ℝ ↦ inner ℝ (∇ f x) d * t) (inner ℝ (∇ f x) d) 1 := by
      -- The linear Taylor term differentiates to the gradient pairing.
      simpa using (HasDerivAt.const_mul (inner ℝ (∇ f x) d) (hasDerivAt_id (1 : ℝ)))
    have hquad :
        HasDerivAt
          (fun t : ℝ ↦ ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ))
          (inner ℝ (hessian f x d) d)
          1 := by
      -- The quadratic Taylor term differentiates to the Hessian quadratic form at `t = 1`.
      have hquadBase :
          HasDerivAt
            (fun t : ℝ ↦ ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ))
            ((((inner ℝ (hessian f x d) d) / 2 : ℝ) * (2 * 1)) : ℝ)
            1 := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
          (HasDerivAt.const_mul (((inner ℝ (hessian f x d) d) / 2 : ℝ))
            ((hasDerivAt_id (1 : ℝ)).pow 2))
      convert hquadBase using 1
      ring
    have habsCube :
        HasDerivAt (fun t : ℝ ↦ |t| ^ (3 : ℕ)) (3 : ℝ) 1 := by
      -- Near the positive point `1`, the cubic penalty behaves like the ordinary cubic.
      convert
        (hasDerivAt_abs_rpow (1 : ℝ) (by norm_num) :
          HasDerivAt (fun t : ℝ ↦ |t| ^ (3 : ℝ)) _ 1) using 1
      · ext t
        rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
      · norm_num
    have hcubic :
        HasDerivAt
          (fun t : ℝ ↦ (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ))
          ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ))
          1 := by
      -- Differentiate the absolute-value cubic penalty and simplify the scalar coefficient.
      have hbase :
          HasDerivAt
            (fun t : ℝ ↦ (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ))
            ((((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * 3)
            1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (HasDerivAt.const_mul (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) habsCube)
      convert hbase using 1
      ring
    -- Summing the derivatives of the constant, linear, quadratic, and cubic pieces gives the
    -- scalar stationarity identity along the line slice.
    simpa [add_assoc, add_left_comm, add_comm] using
      (HasDerivAt.const_add (f x) (hlin.add hquad |>.add hcubic))
  exact hlineMin.hasDerivAt_eq_zero hmodel

-- Proof sketch: use the second-order Taylor remainder estimate from Lemma 4.1.1 to bound the
-- cubic model at each feasible `y`, then apply global minimality of `trialPoint` for the cubic
-- model.
/-- Lemma 4.1.5 (1), pointwise form: for `x ∈ 𝓕` and every feasible `y`, the cubic model value
`\bar f_M(x)` is bounded above by the comparison quantity
`f(y) + ((L + M) / 6) ‖y - x‖³`. -/
theorem cubicRegularizationValue_le_feasibleComparison_of_mem
    {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    (hy : y ∈ 𝓕) :
    f̄[f; M](x) ≤
      f y + (((L : ℝ) + M) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
  have hvalue :
      f̄[f; M](x) = m[f; M](x; trialPoint) :=
    cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn hstep
  have hmin :
      m[f; M](x; trialPoint) ≤ m[f; M](x; y) :=
    hstep (by simp)
  have hmodel_le :
      m[f; M](x; y) ≤
        f y + (((L : ℝ) + M) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
    -- The minimizing model value at `y` is controlled by the lower side of the Taylor remainder.
    rw [cubicRegularizationQuadraticApproximation_apply]
    have herror := hf.secondOrderTaylorModel_error_le x y hx hy
    linarith [(abs_le.mp herror).1]
  -- Realize `f̄[f; M](x)` at `trialPoint`, then compare it with the feasible point `y`.
  calc
    f̄[f; M](x) = m[f; M](x; trialPoint) := hvalue
    _ ≤ m[f; M](x; y) := hmin
    _ ≤ f y + (((L : ℝ) + M) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := hmodel_le

-- Lemma 4.1.5 (1) in the textbook minimum language is the immediate corollary of the stronger
-- pointwise feasible-comparison theorem above.
/-- Lemma 4.1.5 (1): for `x ∈ 𝓕`, the cubic model value `\bar f_M(x)` is bounded above by the
minimum of the feasible comparison quantity `f(y) + ((L + M) / 6) ‖y - x‖³`. -/
theorem cubicRegularizationValue_le_feasibleComparisonMinimum
    {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x yMin : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    (hyMin :
      yMin ∈ argmin[𝓕]
        (fun y ↦ f y + (((L : ℝ) + M) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ))) :
    f̄[f; M](x) ≤
      f yMin + (((L : ℝ) + M) / 6 : ℝ) * ‖yMin - x‖ ^ (3 : ℕ) :=
  cubicRegularizationValue_le_feasibleComparison_of_mem hf hstep hx
    (mem_constrainedArgmin_iff.mp hyMin).1

-- Proof sketch: write `\bar f_M(x)` as the cubic model value at `T_M(x)`, use the first-order
-- optimality relation for the global cubic minimizer together with the nonnegativity of the
-- descent term `⟪∇ f(x), x - T_M(x)⟫`, and simplify the remaining terms to obtain the explicit
-- `(M / 12) r_M(x)^3` lower bound.
/-- Lemma 4.1.5 (2): the gap `f(x) - \bar f_M(x)` dominates
`(M / 12) * r[trialPoint] x ^ 3`; when `trialPoint = T_M(x)`, this is the textbook bound
`(M / 12) r_M(x)^3`. -/
theorem objective_sub_cubicRegularizationValue_ge_residual_cube
    {f : E → ℝ} {M : ℝ} {x : E}
    (hM : 0 ≤ M)
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint) :
    f x - f̄[f; M](x) ≥
      (M / 12 : ℝ) * r[trialPoint] x ^ (3 : ℕ) := by
  let d : E := trialPoint - x
  have hcoeff_nonneg : 0 ≤ (M / 12 : ℝ) := by
    linarith
  have hvalue :
      f̄[f; M](x) = m[f; M](x; trialPoint) :=
    cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn hstep
  have hpair_nonpos :
      inner ℝ (∇ f x) d ≤ 0 := by
    -- Comparing the minimizer with its reflected point supplies the sign of the linear term.
    simpa [d] using
      cubic_model_gradient_pairing_nonpos_of_reflection (trialPoint := trialPoint) hstep
  have hstationary :
      inner ℝ (∇ f x) (trialPoint - x) +
        inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
        (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) = 0 :=
    cubic_model_directional_stationarity_at_trialPoint (trialPoint := trialPoint) hstep
  have hrewrite :
      f x - f̄[f; M](x) =
        -inner ℝ (∇ f x) (trialPoint - x) -
          (1 / 2 : ℝ) * inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) -
          (M / 6 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    -- Realizing `f̄[f; M](x)` at `trialPoint` leaves only the explicit model terms.
    rw [hvalue, cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
    ring
  have hgap :
      f x - f̄[f; M](x) =
        -(1 / 2 : ℝ) * inner ℝ (∇ f x) d +
          (M / 12 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Eliminate the Hessian quadratic term using the stationarity identity.
    rw [hrewrite]
    simp [d]
    have hstationary' :
        inner ℝ (∇ f x) (trialPoint - x) +
          inner ℝ ((hessian f x) trialPoint - (hessian f x) x) (trialPoint - x) +
          (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) = 0 := by
      simpa [map_sub] using hstationary
    linarith
  have hmain :
      f x - f̄[f; M](x) ≥
        (M / 12 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    rw [hgap]
    have hlin_nonneg : 0 ≤ -(1 / 2 : ℝ) * inner ℝ (∇ f x) d := by
      nlinarith
    nlinarith [hcoeff_nonneg]
  -- Rewrite the residual owner back to the norm `‖x - trialPoint‖`.
  simpa [d, cubicRegularizationResidual_eq_norm_sub, norm_sub_rev] using hmain

-- Proof sketch: apply the local Taylor upper bound from
-- `HessianLipschitzOn.secondOrderTaylorModel_error_le` at the feasible pair `x, y ∈ 𝓕`, then
-- absorb the cubic remainder using `M ≥ L` to compare the objective directly with the cubic
-- model at `y`.
/-- Lemma 4.1.5 (3): if `x, y ∈ 𝓕` and `M ≥ L`, then the objective value at `y` is bounded above
by the cubic model centered at `x`. -/
theorem objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz
    {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hx : x ∈ 𝓕)
    (hy : y ∈ 𝓕)
    (hLM : (L : ℝ) ≤ M) :
    f y ≤ m[f; M](x; y) := by
  have hupper :
      f y ≤ secondOrderTaylorModelAt f x y + ((L : ℝ) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
    -- The upper side of the Taylor remainder controls the objective by the quadratic model.
    have herror := hf.secondOrderTaylorModel_error_le x y hx hy
    linarith [(abs_le.mp herror).2]
  have hcubic :
      ((L : ℝ) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) ≤
        (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
    -- The larger regularization parameter `M` absorbs the Hessian-Lipschitz cubic remainder.
    have hpow_nonneg : 0 ≤ ‖y - x‖ ^ (3 : ℕ) := by
      positivity
    have hcoeff : ((L : ℝ) / 6 : ℝ) ≤ (M / 6 : ℝ) := by
      linarith
    exact mul_le_mul_of_nonneg_right hcoeff hpow_nonneg
  -- Combine the Taylor upper bound with the coefficient comparison and fold back to `m[f; M](x; y)`.
  calc
    f y ≤ secondOrderTaylorModelAt f x y + ((L : ℝ) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := hupper
    _ ≤ secondOrderTaylorModelAt f x y + (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
      gcongr
    _ = m[f; M](x; y) := by rw [cubicRegularizationQuadraticApproximation_apply]

-- Proof sketch: first apply
-- `objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz` at the
-- feasible minimizing trial point `trialPoint`, then rewrite the cubic model value there as the
-- canonical owner `f̄[f; M](x)` using
-- `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn hstep`.
/-- Lemma 4.1.5 (4): if `M ≥ L` and a minimizing cubic trial point lies in `𝓕`, then its
objective value is bounded above by the model value `\bar f_M(x)`. -/
theorem objective_cubicTrialPoint_le_cubicRegularizationValue_of_le_hessianLipschitz
    {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    (htrialPoint : trialPoint ∈ 𝓕)
    (hLM : (L : ℝ) ≤ M) :
    f trialPoint ≤ f̄[f; M](x) := by
  have htrial : f trialPoint ≤ m[f; M](x; trialPoint) :=
    objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz
      hf hx htrialPoint hLM
  simpa [cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn hstep] using htrial

end CubicRegularizationModel
