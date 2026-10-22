/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

/- Primary domain: regularization-based scheme-III gradient-norm bounds for smooth convex
unconstrained minimization on a real finite-dimensional inner-product space.

Owner declarations sampled before refining this file:
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean`, the chapter owner of the centered
  quadratic regularization;
* `ConstantStepSchemeIII` in `Proposition_2_12`, the source-facing owner of method `(2.2.22)`;
* `constantStepSchemeIII_objective_gap_le_exponential_rate` in `Proposition_2_12`, the owner
  exponential objective-gap estimate for that scheme on a strongly convex smooth objective;
* `regularized_minimizer_norm_le_of_norm_le` in `Proposition_2_14`, the owner radius control for
  the regularized minimizer.

Best owner abstraction:
* source-facing: Theorem 2.27 for the original smooth-convex objective `f`;
* core/canonical: the regularized scheme-III trajectory
  `scheme : ConstantStepSchemeIII (quadraticallyRegularizedObjective f δ x0) ((L : ℝ) + δ)
    (q[δ, (L : ℝ) + δ]) x0`,
  with `δ = ε / (2 * R0)`;
* bridge/view: the derivation from `hf` of the regularized strongly convex smooth problem, then
  the passage from the regularized scheme-III objective-gap estimate to the original
  gradient-norm target.

Primitive data:
* the original objective `f`, target `ε`, radius `R0`, initial point `x0`, and minimizer `xStar`;
* the smooth-convex owner hypothesis on `f`;
* the source-facing scheme-III trajectory on the regularized objective.

Derived API:
* the regularized strongly convex smooth objective built from `hf`;
* the regularized minimizer radius control from
  `regularized_minimizer_norm_le_of_norm_le`;
* the owner scheme-III objective-gap rate from
  `constantStepSchemeIII_objective_gap_le_exponential_rate`;
* the conversion from the auxiliary regularized estimate to the original gradient-norm target.

The broader optimal-method formulation is a bridge/view reformulation of the same auxiliary
analysis, not the source-facing owner of `(2.2.22)`, so it is not kept as the main public theorem
in this file. -/

section

variable {L : NNReal} {R0 ε : ℝ} {f : E → ℝ}

local notation "δ" => ε / (2 * R0)

namespace ConvexC1SeminormSmooth

/- The source theorem is stated on `ℝⁿ`, and the chapter owner hypothesis `f ∈ 𝓕[L, p]¹¹`
already packages that finite-dimensional smooth-convex setting intrinsically. The regularization
bridge below therefore stays on the source-facing owner layer without reintroducing coordinates. -/
/-- Helper for Theorem 2.27: the quadratically regularized objective has the expected gradient
`∇ f x + δ • (x - x₀)` whenever `f` has gradient `∇ f x` at `x`. -/
lemma hasGradientAt_quadraticallyRegularizedObjective
    {γ : ℝ} {x0 x : E}
    (hf_x : HasGradientAt f (∇ f x) x) :
    HasGradientAt (quadraticallyRegularizedObjective f γ x0)
      (∇ f x + γ • (x - x0)) x := by
  -- Differentiate the quadratic penalty and then add it to the gradient of `f`.
  let penalty : E → ℝ := fun y ↦ (γ / 2) * ‖y - x0‖ ^ (2 : ℕ)
  have hpenalty :
      HasGradientAt penalty (γ • (x - x0)) x := by
    have hsub : HasFDerivAt (fun y : E ↦ y - x0) (.id ℝ E) x := by
      simpa using
        (hasFDerivAt_sub_const x0 :
          HasFDerivAt (fun y : E ↦ y - x0) (.id ℝ E) x)
    have hnormSq :
        HasFDerivAt (fun y : E ↦ ‖y - x0‖ ^ (2 : ℕ))
          (2 • innerSL ℝ (x - x0)) x := by
      simpa using hsub.norm_sq
    have hsmul :
        HasFDerivAt (fun y : E ↦ (γ / 2) * ‖y - x0‖ ^ (2 : ℕ))
          ((γ / 2) • (2 • innerSL ℝ (x - x0))) x := by
      simpa [smul_eq_mul] using hnormSq.const_smul (γ / 2)
    have hlin :
        ((γ / 2) • (2 • innerSL ℝ (x - x0))) =
          InnerProductSpace.toDual ℝ E (γ • (x - x0)) := by
      ext y
      simp [InnerProductSpace.toDual_apply_apply, two_smul]
      ring
    have hsmul' :
        HasFDerivAt penalty
          (InnerProductSpace.toDual ℝ E (γ • (x - x0))) x := by
      exact hlin ▸ hsmul
    simpa [penalty] using hsmul'.hasGradientAt
  simpa [penalty, quadraticallyRegularizedObjective_apply] using
    (hf_x.hasFDerivAt.add hpenalty.hasFDerivAt).hasGradientAt

/-- Helper for Theorem 2.27: the ambient gradient of the regularized objective is the sum of the
original gradient and the centered quadratic correction. -/
lemma gradient_quadraticallyRegularizedObjective_eq
    (hf : f ∈ 𝓕[L, p]¹¹) {γ : ℝ} (x0 x : E) :
    ∇ (quadraticallyRegularizedObjective f γ x0) x = ∇ f x + γ • (x - x0) := by
  -- Identify the gradient through the explicit `HasGradientAt` formula.
  exact (hasGradientAt_quadraticallyRegularizedObjective (hf.hasGradientAt x)).gradient

/-- Helper for Theorem 2.27: adding the centered quadratic regularization makes the smooth convex
objective `f` into a `δ`-strongly convex `((L : ℝ) + δ)`-smooth objective. -/
lemma regularizedObjective_isStrongConvexSmooth
    (hf : f ∈ 𝓕[L, p]¹¹) (x0 : E) (hδ_pos : 0 < δ) :
    IsStrongConvexSmoothObjective δ ((L : ℝ) + δ)
      (quadraticallyRegularizedObjective f δ x0) := by
  refine ⟨hδ_pos, ?_, ?_, ?_⟩
  · -- The quadratic penalty is `C¹`, so the sum stays `C¹`.
    have hquad :
        ContDiff ℝ 1 (fun x : E ↦ ‖x - x0‖ ^ (2 : ℕ)) := by
      simpa using (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    have hpenalty :
        ContDiff ℝ 1 (fun x : E ↦ (δ / 2) * ‖x - x0‖ ^ (2 : ℕ)) := by
      simpa [smul_eq_mul] using hquad.const_smul (δ / 2)
    simpa [quadraticallyRegularizedObjective_apply] using hf.contDiff.add hpenalty
  · -- Strong convexity comes from the quadratic term and convexity of `f`.
    have hsum :
        f + quadraticallyRegularizedObjective (fun _ : E ↦ 0) δ x0 =
          quadraticallyRegularizedObjective f δ x0 := by
      funext x
      simp [quadraticallyRegularizedObjective_apply]
    rw [← hsum]
    exact
      (quadraticallyRegularizedObjective_zero_strongConvexOn x0 δ).add_convexOn hf.convexOn
  · intro x y
    -- Rewrite the regularized gradients and bound the quadratic correction directly.
    rw [gradient_quadraticallyRegularizedObjective_eq hf x0 x,
      gradient_quadraticallyRegularizedObjective_eq hf x0 y]
    have hδ_nonneg : 0 ≤ δ := hδ_pos.le
    have hbase :
        ‖δ • (x - y)‖ = δ * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ_nonneg]
    have hgrad :
        ‖∇ f x - ∇ f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa [Seminorm.dualNorm_normSeminorm_eq_norm] using hf.dualNorm_gradient_sub_le x y
    have hshift :
        (∇ f x - ∇ f y) + (δ • (x - x0) - δ • (y - x0)) =
          (∇ f x - ∇ f y) + δ • (x - y) := by
      congr 1
      calc
        δ • (x - x0) - δ • (y - x0)
            = (δ • x - δ • x0) - (δ • y - δ • x0) := by
                rw [smul_sub, smul_sub]
        _ = δ • x - δ • y := by
              abel_nf
        _ = δ • (x - y) := by
              rw [smul_sub]
    calc
      ‖(∇ f x + δ • (x - x0)) - (∇ f y + δ • (y - x0))‖
          = ‖(∇ f x - ∇ f y) + (δ • (x - x0) - δ • (y - x0))‖ := by
              congr 1
              abel_nf
      _ = ‖(∇ f x - ∇ f y) + δ • (x - y)‖ := by rw [hshift]
      _ ≤ ‖∇ f x - ∇ f y‖ + ‖δ • (x - y)‖ := norm_add_le _ _
      _ = ‖∇ f x - ∇ f y‖ + δ * ‖x - y‖ := by rw [hbase]
      _ ≤ (L : ℝ) * ‖x - y‖ + δ * ‖x - y‖ := by
        nlinarith [hgrad]
      _ = ((L : ℝ) + δ) * ‖x - y‖ := by ring

/-- Helper for Theorem 2.27: a minimizer of the regularized objective already has original
gradient norm at most `ε / 2`. -/
lemma regularized_minimizer_gradient_norm_le_half_target
    (hf : f ∈ 𝓕[L, p]¹¹)
    (x0 xStar xδStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hR : ‖x0 - xStar‖ ≤ R0)
    (hδ_pos : 0 < δ)
    (hxδStar : IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xδStar) :
    ‖∇ f xδStar‖ ≤ ε / 2 := by
  have hR0_nonneg : 0 ≤ R0 := le_trans (norm_nonneg _) hR
  have hR0_ne : R0 ≠ 0 := by
    intro hR0
    simp [hR0] at hδ_pos
  have hradius :
      ‖xδStar - x0‖ ≤ R0 :=
    regularized_minimizer_norm_le_of_norm_le
      f hf.convexOn xStar hxStar x0 xδStar hδ_pos hxδStar hR
  have hstationary :
      ∇ f xδStar = (-δ) • (xδStar - x0) := by
    have hreg :=
      gradient_add_quadratic_regularization_eq_zero_of_isMinOn
        f
        δ
        x0
        xδStar
        (hf.contDiff.differentiable_one xδStar)
        hxδStar
    simpa [smul_neg] using eq_neg_of_add_eq_zero_left hreg
  have hδR0 : δ * R0 = ε / 2 := by
    change (ε / (2 * R0)) * R0 = ε / 2
    field_simp [hR0_ne]
  -- Convert the stationarity identity into the target norm bound.
  calc
    ‖∇ f xδStar‖ = δ * ‖xδStar - x0‖ := by
      have hδ_nonneg : 0 ≤ δ := hδ_pos.le
      rw [hstationary, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hδ_nonneg]
    _ ≤ δ * R0 := by gcongr
    _ = ε / 2 := hδR0

/-- Helper for Theorem 2.27: the scheme-III exponential objective-gap rate on the regularized
objective implies a squared-distance bound to its minimizer. -/
lemma regularized_iterate_sqdist_le_of_exponential_rate
    (hf : f ∈ 𝓕[L, p]¹¹)
    (x0 xδStar : E)
    (scheme :
      ConstantStepSchemeIII
        (quadraticallyRegularizedObjective f δ x0)
        ((L : ℝ) + δ) (q[δ, (L : ℝ) + δ]) x0)
    (hδ_pos : 0 < δ)
    (T : ℕ)
    (hxδStar : IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xδStar) :
    ‖scheme T - xδStar‖ ^ 2 ≤
      (((L : ℝ) + 2 * δ) / δ) * ‖x0 - xδStar‖ ^ 2 *
        Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ])) := by
  let g := quadraticallyRegularizedObjective f δ x0
  have hregularized : IsStrongConvexSmoothObjective δ ((L : ℝ) + δ) g :=
    regularizedObjective_isStrongConvexSmooth hf x0 hδ_pos
  have hgap :=
    constantStepSchemeIII_objective_gap_le_exponential_rate
      hregularized hxδStar scheme T
  have hgrowth :=
    hregularized.strongConvexOn.quadratic_growth_of_isMinOn hxδStar (scheme T)
  -- Compare the lower quadratic-growth estimate with the upper objective-gap estimate.
  change g (scheme T) - g xδStar ≤
    ((((L : ℝ) + δ) + δ) / 2) * ‖x0 - xδStar‖ ^ (2 : ℕ) *
      Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ])) at hgap
  change g (scheme T) ≥
    g xδStar + (δ / 2) * ‖scheme T - xδStar‖ ^ (2 : ℕ) at hgrowth
  have haux :
      (δ / 2) * ‖scheme T - xδStar‖ ^ (2 : ℕ) ≤
        ((((L : ℝ) + δ) + δ) / 2) * ‖x0 - xδStar‖ ^ (2 : ℕ) *
          Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ])) := by
    linarith
  have hδhalf_pos : 0 < δ / 2 := by positivity
  have hdiv :
      ‖scheme T - xδStar‖ ^ (2 : ℕ) ≤
        (((((L : ℝ) + δ) + δ) / 2) * ‖x0 - xδStar‖ ^ (2 : ℕ) *
          Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ]))) / (δ / 2) := by
    rw [le_div_iff₀ hδhalf_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using haux
  have hrewrite :
      (((((L : ℝ) + δ) + δ) / 2) * ‖x0 - xδStar‖ ^ (2 : ℕ) *
          Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ]))) / (δ / 2) =
        (((L : ℝ) + 2 * δ) / δ) * ‖x0 - xδStar‖ ^ 2 *
          Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ])) := by
    field_simp [hδ_pos.ne']
    ring_nf
  exact hrewrite ▸ hdiv

/-- Helper for Theorem 2.27: the original gradient at the scheme iterate differs from the
regularized minimizer gradient by at most `ε / 2`. -/
lemma regularized_gradient_difference_le_half_target
    (hf : f ∈ 𝓕[L, p]¹¹)
    (x0 xStar xδStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hR : ‖x0 - xStar‖ ≤ R0)
    (scheme :
      ConstantStepSchemeIII
        (quadraticallyRegularizedObjective f δ x0)
        ((L : ℝ) + δ) (q[δ, (L : ℝ) + δ]) x0)
    (T : ℕ)
    (hT :
      3 * Real.sqrt (1 + 2 * (L : ℝ) * R0 / ε) *
        Real.log (1 + 2 * (L : ℝ) * R0 / ε) ≤ (T : ℝ))
    (hδ_pos : 0 < δ)
    (hxδStar : IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xδStar) :
    ‖∇ f (scheme T) - ∇ f xδStar‖ ≤ ε / 2 := by
  let b : ℝ := 2 * (L : ℝ) * R0 / ε
  have hL_nonneg : 0 ≤ (L : ℝ) := NNReal.coe_nonneg L
  have hR0_nonneg : 0 ≤ R0 := le_trans (norm_nonneg _) hR
  have hR0_ne : R0 ≠ 0 := by
    intro hR0
    simp [hR0] at hδ_pos
  have hR0_pos : 0 < R0 := lt_of_le_of_ne hR0_nonneg hR0_ne.symm
  have hε_pos : 0 < ε := by
    have hδR0 : ε = 2 * δ * R0 := by
      change ε = 2 * (ε / (2 * R0)) * R0
      field_simp [hR0_ne]
    nlinarith [hδ_pos, hR0_pos, hδR0]
  have hε_ne : ε ≠ 0 := hε_pos.ne'
  have hb_nonneg : 0 ≤ b := by
    positivity
  have hb_one_pos : 0 < 1 + b := by
    positivity
  have hradius :
      ‖x0 - xδStar‖ ≤ R0 := by
    simpa [norm_sub_rev] using
      (regularized_minimizer_norm_le_of_norm_le
        f hf.convexOn xStar hxStar x0 xδStar hδ_pos hxδStar hR)
  have hsq_radius :
      ‖x0 - xδStar‖ ^ 2 ≤ R0 ^ 2 := by
    simpa [pow_two] using
      (sq_le_sq₀ (norm_nonneg _) hR0_nonneg).2 hradius
  have hsq_dist :=
    regularized_iterate_sqdist_le_of_exponential_rate
      hf x0 xδStar scheme hδ_pos T hxδStar
  have hcoef :
      (((L : ℝ) + 2 * δ) / δ) = b + 2 := by
    unfold b
    field_simp [hR0_ne, hε_ne]
  have hq :
      q[δ, (L : ℝ) + δ] = 1 / (1 + b) := by
    unfold b
    field_simp [hR0_ne, hε_ne]
    ring
  have hsqrt_q :
      Real.sqrt (q[δ, (L : ℝ) + δ]) = 1 / Real.sqrt (1 + b) := by
    have hq_nonneg : 0 ≤ q[δ, (L : ℝ) + δ] := scheme.qf_mem_Ioc.1.le
    have hsqrt_mul :
        Real.sqrt (q[δ, (L : ℝ) + δ]) * Real.sqrt (1 + b) = 1 := by
      calc
        Real.sqrt (q[δ, (L : ℝ) + δ]) * Real.sqrt (1 + b)
            = Real.sqrt (q[δ, (L : ℝ) + δ] * (1 + b)) := by
                symm
                rw [Real.sqrt_mul hq_nonneg]
        _ = 1 := by
          rw [hq]
          field_simp [hb_one_pos.ne']
          rw [Real.sqrt_one]
    apply (eq_div_iff (Real.sqrt_pos.2 hb_one_pos).ne').2
    simpa [mul_comm] using hsqrt_mul
  have hT_scaled :
      3 * Real.log (1 + b) ≤ (T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ]) := by
    have hsqrt_pos : 0 < Real.sqrt (1 + b) := Real.sqrt_pos.2 hb_one_pos
    calc
      3 * Real.log (1 + b)
          = (3 * Real.sqrt (1 + b) * Real.log (1 + b)) * (1 / Real.sqrt (1 + b)) := by
              field_simp [hsqrt_pos.ne']
      _ ≤ (T : ℝ) * (1 / Real.sqrt (1 + b)) := by
        gcongr
      _ = (T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ]) := by
        rw [hsqrt_q]
  have hexp_bound :
      Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ])) ≤ 1 / (1 + b) ^ (3 : ℕ) := by
    have hneg :
        -(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ]) ≤ -3 * Real.log (1 + b) := by
      linarith
    calc
      Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ]))
          ≤ Real.exp (-3 * Real.log (1 + b)) := by
              exact Real.exp_le_exp.mpr hneg
      _ = 1 / (1 + b) ^ (3 : ℕ) := by
        have hexp :
            Real.exp (-3 * Real.log (1 + b)) =
              Real.exp (-(3 * Real.log (1 + b))) := by
          congr 1
          ring
        rw [hexp, Real.exp_neg]
        rw [show (3 : ℝ) * Real.log (1 + b) = (3 : ℕ) * Real.log (1 + b) by norm_num,
          Real.exp_nat_mul, Real.exp_log hb_one_pos]
        simp [one_div]
  have hdist_bound :
      ‖scheme T - xδStar‖ ^ 2 ≤ R0 ^ 2 * ((b + 2) * (1 / (1 + b) ^ (3 : ℕ))) := by
    have htemp :
        (((L : ℝ) + 2 * δ) / δ) * ‖x0 - xδStar‖ ^ 2 *
            Real.exp (-(T : ℝ) * Real.sqrt (q[δ, (L : ℝ) + δ])) ≤
          (((L : ℝ) + 2 * δ) / δ) * R0 ^ 2 * (1 / (1 + b) ^ (3 : ℕ)) := by
      have hcoef_nonneg : 0 ≤ (((L : ℝ) + 2 * δ) / δ) := by
        positivity
      have hleft :
          (((L : ℝ) + 2 * δ) / δ) * ‖x0 - xδStar‖ ^ 2 ≤
            (((L : ℝ) + 2 * δ) / δ) * R0 ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq_radius hcoef_nonneg
      exact mul_le_mul hleft hexp_bound (by positivity) (by positivity)
    have hsq_dist' := hsq_dist
    rw [hcoef] at hsq_dist'
    have htemp' := htemp
    rw [hcoef] at htemp'
    exact le_trans
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hsq_dist')
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using htemp')
  have hLip :
      ‖∇ f (scheme T) - ∇ f xδStar‖ ≤ (L : ℝ) * ‖scheme T - xδStar‖ :=
    by
      simpa [Seminorm.dualNorm_normSeminorm_eq_norm] using
        hf.dualNorm_gradient_sub_le (scheme T) xδStar
  have hgrad_sq :
      ‖∇ f (scheme T) - ∇ f xδStar‖ ^ 2 ≤
        ((L : ℝ) * ‖scheme T - xδStar‖) ^ 2 := by
    exact
      (sq_le_sq₀
        (norm_nonneg _)
        (mul_nonneg hL_nonneg (norm_nonneg _))).2
        hLip
  have hb_poly : b ^ (2 : ℕ) * (b + 2) ≤ (1 + b) ^ (3 : ℕ) := by
    nlinarith [sq_nonneg b, sq_nonneg (b + 1)]
  have hratio :
      b ^ (2 : ℕ) * (b + 2) * (1 / (1 + b) ^ (3 : ℕ)) ≤ 1 := by
    have hden_pos : 0 < (1 + b) ^ (3 : ℕ) := by positivity
    field_simp [hden_pos.ne']
    simpa [mul_comm, mul_left_comm, mul_assoc] using hb_poly
  have hnum :
      ((L : ℝ) * ‖scheme T - xδStar‖) ^ 2 ≤ (ε / 2) ^ 2 := by
    have hrewrite :
        ((L : ℝ) * ‖scheme T - xδStar‖) ^ 2 ≤
          ((L : ℝ) ^ (2 : ℕ)) *
            (R0 ^ (2 : ℕ) * ((b + 2) * (1 / (1 + b) ^ (3 : ℕ)))) := by
      have hLsq :
          ((L : ℝ) * ‖scheme T - xδStar‖) ^ 2 =
            (L : ℝ) ^ (2 : ℕ) * ‖scheme T - xδStar‖ ^ (2 : ℕ) := by
        ring_nf
      rw [hLsq]
      gcongr
    have hrewrite_num :
        (L : ℝ) ^ (2 : ℕ) * (R0 ^ (2 : ℕ) * ((b + 2) * (1 / (1 + b) ^ (3 : ℕ)))) =
          ((ε / 2) ^ (2 : ℕ)) * (b ^ (2 : ℕ) * (b + 2) * (1 / (1 + b) ^ (3 : ℕ))) := by
      unfold b
      field_simp [hε_ne]
    calc
      ((L : ℝ) * ‖scheme T - xδStar‖) ^ 2
          ≤ (L : ℝ) ^ (2 : ℕ) * (R0 ^ (2 : ℕ) * ((b + 2) * (1 / (1 + b) ^ (3 : ℕ)))) :=
        by
          have hdist_bound' :=
            mul_le_mul_of_nonneg_left hdist_bound (sq_nonneg (L : ℝ))
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hdist_bound'
      _ = ((ε / 2) ^ (2 : ℕ)) * (b ^ (2 : ℕ) * (b + 2) * (1 / (1 + b) ^ (3 : ℕ))) :=
        hrewrite_num
      _ ≤ ((ε / 2) ^ (2 : ℕ)) * 1 := by
        nlinarith [hratio, sq_nonneg (ε / 2)]
      _ = (ε / 2) ^ 2 := by ring
  -- Pass back from the squared inequality to the norm inequality.
  exact
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 <|
      le_trans hgrad_sq hnum

/-- Theorem 2.27: let `f : E → ℝ` be convex and `C¹` with `L`-Lipschitz gradient. If `xStar`
minimizes `f`, if `‖x₀ - xStar‖ ≤ R₀`, and if method `(2.2.22)` is applied from `x₀` to the
regularized objective `f₈(x) = f(x) + (ε / (4 R₀)) ‖x - x₀‖²`, then any iterate count at least
`3 √(1 + 2 L R₀ / ε) log (1 + 2 L R₀ / ε)` yields a point whose original gradient norm is at
most `ε`. Here `δ = ε / (2 R₀)`, and the regularized problem has reciprocal condition number
`q[δ, (L : ℝ) + δ]`, so the source-facing method parameter is fixed by the regularization rather
than chosen via an auxiliary admissible `α₀`; the owner scheme assumption already forces `δ > 0`,
and with `hR : ‖x₀ - xStar‖ ≤ R₀` this yields the textbook side conditions `R₀ > 0` and
`ε > 0` internally instead of keeping them as primitive public hypotheses. -/
-- Proof sketch: set `δ = ε / (2 R₀)` and view the auxiliary objective `f₈` as strongly convex
-- smooth with parameters `μ = δ` and `L = original_L + δ`. Apply
-- `constantStepSchemeIII_objective_gap_le_exponential_rate` to the regularized problem and let
-- `xδStar` be a minimizer of `f₈`. The radius control
-- `regularized_minimizer_norm_le_of_norm_le` keeps `xδStar` in the closed ball of radius `R₀`
-- around `x₀`, while
-- `gradient_add_quadratic_regularization_eq_zero_of_isMinOn` converts the first-order condition
-- for `xδStar` into the needed bound on `‖∇ f (scheme T)‖`. The assumed lower bound on `T`
-- simplifies the resulting exponential estimate to the stated target `ε`.
theorem constantStepSchemeIII_regularizedObjective_gradient_norm_le_target
    (hf : f ∈ 𝓕[L, p]¹¹)
    (x0 xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hR : ‖x0 - xStar‖ ≤ R0)
    (scheme :
      ConstantStepSchemeIII
        (quadraticallyRegularizedObjective f δ x0)
        ((L : ℝ) + δ) (q[δ, (L : ℝ) + δ]) x0)
    (T : ℕ)
    (hT :
      3 * Real.sqrt (1 + 2 * (L : ℝ) * R0 / ε) *
        Real.log (1 + 2 * (L : ℝ) * R0 / ε) ≤ (T : ℝ)) :
    ‖∇ f (scheme T)‖ ≤ ε := by
  have hδ_pos : 0 < δ := by
    -- The scheme stores `q[δ, (L : ℝ) + δ] > 0`, and its smoothness parameter is positive.
    have hLδ_pos : 0 < (L : ℝ) + δ := scheme.L_pos
    have hq_pos : 0 < q[δ, (L : ℝ) + δ] := scheme.qf_mem_Ioc.1
    change 0 < δ / ((L : ℝ) + δ) at hq_pos
    exact (div_pos_iff_of_pos_right hLδ_pos).mp hq_pos
  have hregularized :
      IsStrongConvexSmoothObjective δ ((L : ℝ) + δ)
        (quadraticallyRegularizedObjective f δ x0) :=
    regularizedObjective_isStrongConvexSmooth hf x0 hδ_pos
  -- Choose the unique minimizer of the regularized problem as the comparison point.
  have hexists :
      ∃! xδStar : E,
        xδStar ∈ Set.univ ∧
          IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xδStar := by
    have hstrong_with :
        StrongConvexOnWith (normSeminorm ℝ E) δ Set.univ
          (quadraticallyRegularizedObjective f δ x0) := by
      exact strongConvexOnWith_normSeminorm_iff.mpr
        ⟨hδ_pos, hregularized.strongConvexOn⟩
    exact
      hstrong_with.existsUnique_isMinOn_of_isClosed
        hregularized.contDiff.continuous.continuousOn
        Set.univ_nonempty
        isClosed_univ
  obtain ⟨xδStar, hxδStar, -⟩ := hexists
  have hminδ :
      IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xδStar :=
    hxδStar.2
  have hstationary_half :
      ‖∇ f xδStar‖ ≤ ε / 2 :=
    regularized_minimizer_gradient_norm_le_half_target
      hf x0 xStar xδStar hxStar hR hδ_pos hminδ
  have htransport_half :
      ‖∇ f (scheme T) - ∇ f xδStar‖ ≤ ε / 2 :=
    regularized_gradient_difference_le_half_target
      hf x0 xStar xδStar hxStar hR scheme T hT hδ_pos hminδ
  -- Split the target by the triangle inequality at the regularized minimizer.
  calc
    ‖∇ f (scheme T)‖
        = ‖(∇ f (scheme T) - ∇ f xδStar) + ∇ f xδStar‖ := by
            congr 1
            abel_nf
    _ ≤ ‖∇ f (scheme T) - ∇ f xδStar‖ + ‖∇ f xδStar‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := by ring

end ConvexC1SeminormSmooth

end
