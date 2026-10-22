/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import TR_LALM_theory.Definition_2_2.KKT
public import TR_LALM_theory.Proposition_4_1.Step

public section

open Filter
open scoped ContDiff InnerProductSpace NNReal

namespace LALM.Correction

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {rho beta : NNRealˣ}
variable {xStar : EuclideanSpace ℝ (Fin n)}
variable {multiplierStar : EuclideanSpace ℝ (Fin m)}
variable {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
  EuclideanSpace ℝ (Fin n)}

/-- Helper for legacy appendix remark C.2: one is at most two as an extended natural number. -/
private lemma one_le_two_enat : (1 : ℕ∞ω) ≤ 2 := by
  norm_num

/-- Helper for legacy appendix remark C.2: taking one derivative from class two leaves class one. -/
private lemma one_add_one_le_two_enat : (1 : ℕ∞ω) + 1 ≤ 2 := by
  norm_num

/-- Helper for legacy appendix remark C.2: taking one derivative from class one leaves class zero. -/
private lemma zero_add_one_le_one_enat : (0 : ℕ∞ω) + 1 ≤ 1 := by
  norm_num

/-- Helper for legacy appendix remark C.2: two is nonzero as an extended natural number. -/
private lemma two_ne_zero_enat : (2 : ℕ∞ω) ≠ 0 := by
  norm_num

/-- Helper for legacy appendix remark C.2: the natural number one is strictly less than two. -/
private lemma one_lt_two_nat : (1 : ℕ) < 2 := by
  norm_num

/-- Helper for legacy appendix remark C.2: the natural number two is nonzero. -/
private lemma two_ne_zero_nat : (2 : ℕ) ≠ 0 := by
  norm_num

/-- Helper for legacy appendix remark C.2: a minimizer of the proximal step model is controlled by
the model gradient at the zero step. -/
lemma minimizerNorm_le_inv_mul_stepModelGradientZeroNorm
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin n))
    (h_rho : 0 ≤ rho) (h_beta : 0 < beta)
    (h_minimizes : IsMinOn (LALM.stepModel f c rho beta x multiplier) Set.univ q) :
    ‖q‖ ≤ beta⁻¹ * ‖LALM.stepModelGradient f c rho beta x multiplier 0‖ := by
  -- Stationarity at the minimizer turns the gradient-pairing identity into a
  -- coercive estimate for the proximal quadratic term.
  have h_zero := LALM.stepModelGradient_eq_zero_of_minimizes
    f c rho beta x multiplier q h_minimizes
  have h_pairing := LALM.stepModelGradientPairing
    f c rho beta x multiplier q 0
  have h_coercive :
      beta * ‖q‖ ^ 2 ≤
        ‖LALM.stepModelGradient f c rho beta x multiplier 0‖ * ‖q‖ := by
    calc
      beta * ‖q‖ ^ 2 ≤
          rho * ‖fderiv ℝ c x (q - 0)‖ ^ 2 + beta * ‖q - 0‖ ^ 2 := by
        simp only [sub_zero]
        nlinarith [mul_nonneg h_rho (sq_nonneg ‖fderiv ℝ c x q‖)]
      _ = ⟪LALM.stepModelGradient f c rho beta x multiplier q -
            LALM.stepModelGradient f c rho beta x multiplier 0, q - 0⟫_ℝ :=
        h_pairing.symm
      _ ≤ ‖LALM.stepModelGradient f c rho beta x multiplier 0‖ * ‖q‖ := by
        rw [h_zero, zero_sub, sub_zero]
        simpa only [norm_neg] using
          real_inner_le_norm (-LALM.stepModelGradient f c rho beta x multiplier 0) q
  -- Cancel the step norm when it is nonzero; the zero case is immediate.
  by_cases hq : ‖q‖ = 0
  · rw [hq]
    exact mul_nonneg (inv_nonneg.mpr h_beta.le) (norm_nonneg _)
  · rw [le_inv_mul_iff₀ h_beta]
    have hq_pos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) (Ne.symm hq)
    nlinarith [h_coercive]

/-- Helper for legacy appendix remark C.2: taking adjoints preserves the differentiability class
of a family of real continuous linear maps. -/
lemma contDiff_constraintGradient_of_fderiv {k : ℕ∞ω}
    (h_cderiv : ContDiff ℝ k (fderiv ℝ c)) :
    ContDiff ℝ k (EqualityConstrained.constraintGradient c) := by
  have h_adjoint : IsBoundedLinearMap ℝ
      (ContinuousLinearMap.adjoint :
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) →
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    refine (⟨?_, ?_⟩ : IsLinearMap ℝ _).with_bound 1 ?_
    · intro A B
      exact map_add ContinuousLinearMap.adjoint A B
    · intro r A
      simp only [map_smul]
    · intro A
      simpa only [LinearIsometryEquiv.norm_map, one_mul] using
        (le_refl (‖A‖ : ℝ))
  simpa only [EqualityConstrained.constraintGradient_def, Function.comp_def] using
    h_adjoint.contDiff.comp h_cderiv

/-- Helper for legacy appendix remark C.2: at the zero step, the model gradient is the gradient
of the objective plus the adjoint linearized-constraint contribution. -/
lemma stepModelGradient_zero_eq
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) :
    LALM.stepModelGradient f c rho beta x multiplier 0 =
      gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • c x) := by
  have h_affine : HasFDerivAt
      (fun q ↦ c x + fderiv ℝ c x q) (fderiv ℝ c x) 0 := by
    fun_prop
  have h_objective : HasFDerivAt
      (fun q ↦ ⟪gradient f x, q⟫_ℝ) (innerSL ℝ (gradient f x)) 0 := by
    simpa only [coe_innerSL_apply] using (innerSL ℝ (gradient f x)).hasFDerivAt
  have h_multiplier : HasFDerivAt
      (fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ)
      (innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) 0 := by
    simpa only [Function.comp_def, innerSL_apply_apply,
      EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
      (innerSL ℝ multiplier).hasFDerivAt.comp 0 h_affine
  have h_penalty : HasFDerivAt
      (fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2)
      ((rho / 2) • 2 • innerSL ℝ
        (EqualityConstrained.constraintGradient c x (c x))) 0 := by
    simpa only [map_zero, add_zero, EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
      h_affine.norm_sq.const_mul (rho / 2)
  have h_proximal : HasFDerivAt (fun q ↦ (beta / 2) * ‖q‖ ^ 2)
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) 0 := by
    simpa only [id_eq, ContinuousLinearMap.comp_id, map_zero, smul_zero] using
      (hasFDerivAt_id (0 : EuclideanSpace ℝ (Fin n))).norm_sq.const_mul (beta / 2)
  have h_sum := ((h_objective.add h_multiplier).add h_penalty).add h_proximal
  have h_functions : LALM.stepModel f c rho beta x multiplier =ᶠ[nhds 0]
      ((((fun q ↦ ⟪gradient f x, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (beta / 2) * ‖q‖ ^ 2) := by
    filter_upwards with q
    exact LALM.stepModel_def f c rho beta x multiplier q
  have h_derivativeEq :
      (((innerSL ℝ (gradient f x) +
          innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) +
          (rho / 2) • 2 • innerSL ℝ
            (EqualityConstrained.constraintGradient c x (c x))) + 0) =
        innerSL ℝ (gradient f x + EqualityConstrained.constraintGradient c x
          (multiplier + rho • c x)) := by
    ext v
    simp only [map_add, map_smul, innerSL_apply_apply, add_apply, smul_apply,
      zero_apply]
    ring
  have h_explicit : HasFDerivAt (LALM.stepModel f c rho beta x multiplier)
      (innerSL ℝ (gradient f x + EqualityConstrained.constraintGradient c x
        (multiplier + rho • c x))) 0 :=
    (h_sum.congr_of_eventuallyEq h_functions).congr_fderiv h_derivativeEq
  exact innerSL_inj.mp
    ((LALM.hasFDerivAt_stepModel f c rho beta x multiplier 0).unique h_explicit)

/-- Helper for legacy appendix remark C.2: the zero-step model gradient is first order in the
distance from a KKT pair. -/
lemma stepModelGradientZero_isBigO
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    (h_kkt : KKT.IsPair f c xStar multiplierStar) :
    (fun y ↦ LALM.stepModelGradient f c (rho : ℝ) (beta : ℝ) y.1 y.2 0) =O[
        nhds (xStar, multiplierStar)]
      (fun y ↦ ‖y - (xStar, multiplierStar)‖) := by
  -- The objective gradient and constraint-gradient operator inherit one
  -- derivative from the two derivatives of `f` and `c`.
  have h_fderiv : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right one_add_one_le_two_enat
  have h_cderiv : ContDiff ℝ 1 (fderiv ℝ c) :=
    hc.fderiv_right one_add_one_le_two_enat
  have h_gradient : ContDiff ℝ 1 (gradient f) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.contDiff.comp
      h_fderiv
  have h_constraintGradient :
      ContDiff ℝ 1 (EqualityConstrained.constraintGradient c) :=
    contDiff_constraintGradient_of_fderiv h_cderiv
  have h_modelGradientExplicit : ContDiff ℝ 1
      (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        gradient f y.1 + EqualityConstrained.constraintGradient c y.1
          (y.2 + (rho : ℝ) • c y.1)) := by
    exact (h_gradient.comp contDiff_fst).add
      ((h_constraintGradient.comp contDiff_fst).clm_apply
        (contDiff_snd.add (ContDiff.const_smul (rho : ℝ)
          ((hc.of_le one_le_two_enat).comp contDiff_fst))))
  -- At the reference pair, KKT stationarity and feasibility make this smooth
  -- model-gradient map vanish.
  obtain ⟨h_stationarity, h_feasibility⟩ :=
    (KKT.isPair_iff f c xStar multiplierStar).mp h_kkt
  have h_vanish :
      LALM.stepModelGradient f c (rho : ℝ) (beta : ℝ)
        xStar multiplierStar 0 = 0 := by
    rw [stepModelGradient_zero_eq, h_feasibility, smul_zero, add_zero]
    simpa only [KKT.stationarity_def] using h_stationarity
  -- Differentiability gives the first-order Big-O estimate; normalize its
  -- right side to the scalar distance used by the statement.
  have h_linear := (h_modelGradientExplicit.differentiable_one
    (xStar, multiplierStar)).isBigO_sub.norm_right
  refine h_linear.congr_left fun y ↦ ?_
  rw [← stepModelGradient_zero_eq f c (rho : ℝ) (beta : ℝ) y.1 y.2,
    ← stepModelGradient_zero_eq f c (rho : ℝ) (beta : ℝ) xStar multiplierStar,
    h_vanish, sub_zero]

/-- Helper for legacy appendix remark C.2: a `C²` constraint map has a quadratic linearization
residual along any base points converging to a fixed point and steps converging to zero. -/
lemma residualComp_isBigO_sq
    {alpha : Type*} {l : Filter alpha}
    {x q : alpha → EuclideanSpace ℝ (Fin n)}
    (hc : ContDiff ℝ 2 c)
    (h_x : Tendsto x l (nhds xStar)) (h_q : Tendsto q l (nhds 0)) :
    (fun a ↦ residual c (x a) (q a)) =O[l] (fun a ↦ ‖q a‖ ^ 2) := by
  -- A first derivative of `c` is locally Lipschitz because `c` is `C²`.
  have h_cderiv : ContDiff ℝ 1 (fderiv ℝ c) :=
    hc.fderiv_right one_add_one_le_two_enat
  obtain ⟨K, s, h_s, h_lipschitz⟩ :=
    h_cderiv.contDiffAt.exists_lipschitzOnWith
  obtain ⟨epsilon, h_epsilon, h_ball⟩ := Metric.mem_nhds_iff.mp h_s
  have h_trial : Tendsto (fun a ↦ trialPoint (x a) (q a)) l (nhds xStar) := by
    simpa only [trialPoint_def, add_zero] using h_x.add h_q
  have h_x_ball : ∀ᶠ a in l, x a ∈ Metric.ball xStar epsilon :=
    h_x (Metric.ball_mem_nhds xStar h_epsilon)
  have h_trial_ball :
      ∀ᶠ a in l, trialPoint (x a) (q a) ∈ Metric.ball xStar epsilon :=
    h_trial (Metric.ball_mem_nhds xStar h_epsilon)
  have h_differentiable : Differentiable ℝ c :=
    hc.differentiable two_ne_zero_enat
  -- Eventually both endpoints lie in one convex ball on which the Taylor
  -- remainder estimate uses the locally Lipschitz derivative.
  apply Asymptotics.IsBigO.of_bound ((K : ℝ) / 2)
  filter_upwards [h_x_ball, h_trial_ball] with a hxa htriala
  have h_segment : segment ℝ (x a) (trialPoint (x a) (q a)) ⊆ s :=
    ((convex_ball xStar epsilon).segment_subset hxa htriala).trans h_ball
  have h_remainder := LALM.norm_sub_sub_fderiv_le c K s
    (x a) (trialPoint (x a) (q a)) (fun z _ ↦ h_differentiable z)
    h_lipschitz h_segment
  simpa only [residual_def, trialPoint_def, add_sub_cancel_left,
    Real.norm_of_nonneg (sq_nonneg ‖q a‖)] using h_remainder

/-- Helper for legacy appendix remark C.2: injectivity at a limit point gives a uniform positive
lower bound for nearby constraint-gradient operators. -/
lemma constraintGradient_lowerBound_eventually
    {alpha : Type*} {l : Filter alpha}
    {x : alpha → EuclideanSpace ℝ (Fin n)}
    (hc : ContDiff ℝ 1 c)
    (h_injective : Function.Injective
      (EqualityConstrained.constraintGradient c xStar))
    (h_x : Tendsto x l (nhds xStar)) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ᶠ a in l,
      ∀ u : EuclideanSpace ℝ (Fin m),
        kappa * ‖u‖ ≤ ‖EqualityConstrained.constraintGradient c (x a) u‖ := by
  -- Finite dimensionality turns injectivity into a quantitative lower bound
  -- at the reference point.
  obtain ⟨K, -, h_antilipschitz⟩ :=
    (EqualityConstrained.constraintGradient c xStar).toLinearMap.injective_iff_antilipschitz.mp
      h_injective
  obtain ⟨kappa, h_kappa, h_lower⟩ :=
    antilipschitzWith_iff_exists_mul_le_norm.mp ⟨K, h_antilipschitz⟩
  have h_cderiv : ContDiff ℝ 0 (fderiv ℝ c) :=
    hc.fderiv_right zero_add_one_le_one_enat
  have h_constraintGradient :
      Continuous (EqualityConstrained.constraintGradient c) :=
    (contDiff_constraintGradient_of_fderiv h_cderiv).continuous
  have h_operatorTendsto : Tendsto
      (fun a ↦ EqualityConstrained.constraintGradient c (x a)) l
      (nhds (EqualityConstrained.constraintGradient c xStar)) :=
    h_constraintGradient.continuousAt.tendsto.comp h_x
  have h_close : ∀ᶠ a in l,
      ‖EqualityConstrained.constraintGradient c (x a) -
        EqualityConstrained.constraintGradient c xStar‖ < kappa / 2 :=
    h_operatorTendsto (eventually_norm_sub_lt _ (half_pos h_kappa))
  refine ⟨kappa / 2, half_pos h_kappa, ?_⟩
  filter_upwards [h_close] with a ha
  intro u
  -- Operator-norm continuity preserves half of the reference lower bound.
  have h_difference :
      ‖(EqualityConstrained.constraintGradient c xStar -
          EqualityConstrained.constraintGradient c (x a)) u‖ ≤
        (kappa / 2) * ‖u‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c xStar -
          EqualityConstrained.constraintGradient c (x a)) u‖ ≤
          ‖EqualityConstrained.constraintGradient c xStar -
            EqualityConstrained.constraintGradient c (x a)‖ * ‖u‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (kappa / 2) * ‖u‖ := by
        apply mul_le_mul_of_nonneg_right
        · simpa only [norm_sub_rev] using ha.le
        · exact norm_nonneg u
  have h_triangle :
      ‖EqualityConstrained.constraintGradient c xStar u‖ ≤
        ‖EqualityConstrained.constraintGradient c (x a) u‖ +
          ‖(EqualityConstrained.constraintGradient c xStar -
            EqualityConstrained.constraintGradient c (x a)) u‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c xStar u‖ =
          ‖EqualityConstrained.constraintGradient c (x a) u +
            (EqualityConstrained.constraintGradient c xStar -
              EqualityConstrained.constraintGradient c (x a)) u‖ := by
        congr 1
        simp only [sub_apply]
        abel
      _ ≤ _ := norm_add_le _ _
  calc
    (kappa / 2) * ‖u‖ = kappa * ‖u‖ - (kappa / 2) * ‖u‖ := by ring
    _ ≤ ‖EqualityConstrained.constraintGradient c xStar u‖ -
        ‖(EqualityConstrained.constraintGradient c xStar -
          EqualityConstrained.constraintGradient c (x a)) u‖ :=
      sub_le_sub (h_lower u) h_difference
    _ ≤ ‖EqualityConstrained.constraintGradient c (x a) u‖ :=
      sub_le_iff_le_add.mpr h_triangle

/-- Helper for legacy appendix remark C.2: injectivity of the constraint gradient makes the
chosen Gram inverse a right inverse. -/
lemma comp_gramInverse_of_injective
    (z : EuclideanSpace ℝ (Fin n))
    (h_injective : Function.Injective
      (EqualityConstrained.constraintGradient c z))
    (u : EuclideanSpace ℝ (Fin m)) :
    gram c z (gramInverse c z u) = u := by
  -- The Gram map is injective, hence surjective in finite dimension, and its
  -- chosen left inverse is consequently also a right inverse.
  have h_gramInjective : Function.Injective (gram c z) := by
    rw [gram_def, ← ContinuousLinearMap.adjoint_toLinearMap]
    simpa only [LinearMap.coe_comp, Function.comp_apply] using
      (LinearMap.adjoint_comp_self_injective_iff
        (EqualityConstrained.constraintGradient c z).toLinearMap).mpr h_injective
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.mp h_gramInjective u
  rw [← hv]
  exact congrArg (gram c z) (LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr h_gramInjective) v)

/-- Helper for legacy appendix remark C.2: stable LICQ makes the correction asymptotically no
larger than the nonlinear constraint residual. -/
lemma stepComp_isBigO_residual_of_licq
    {alpha : Type*} {l : Filter alpha}
    {x q : alpha → EuclideanSpace ℝ (Fin n)}
    (hc : ContDiff ℝ 1 c)
    (h_injective : Function.Injective
      (EqualityConstrained.constraintGradient c xStar))
    (h_x : Tendsto x l (nhds xStar)) (h_q : Tendsto q l (nhds 0)) :
    (fun a ↦ step c (x a) (q a)) =O[l]
      (fun a ↦ residual c (x a) (q a)) := by
  -- Move the uniform LICQ lower bound to the trial points where the Gram
  -- correction is evaluated.
  have h_trial : Tendsto (fun a ↦ trialPoint (x a) (q a)) l (nhds xStar) := by
    simpa only [trialPoint_def, add_zero] using h_x.add h_q
  obtain ⟨kappa, h_kappa, h_lower⟩ :=
    constraintGradient_lowerBound_eventually hc h_injective h_trial
  apply Asymptotics.IsBigO.of_bound kappa⁻¹
  filter_upwards [h_lower] with a ha
  let z := trialPoint (x a) (q a)
  let v := gramInverse c z (residual c (x a) (q a))
  have h_gradientInjective : Function.Injective
      (EqualityConstrained.constraintGradient c z) := by
    intro u w huw
    have h_zero : EqualityConstrained.constraintGradient c z (u - w) = 0 := by
      rw [map_sub, huw, sub_self]
    have h_bound := ha (u - w)
    rw [h_zero, norm_zero] at h_bound
    have h_normZero : ‖u - w‖ = 0 := by
      nlinarith [norm_nonneg (u - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h_normZero)
  have h_gram := comp_gramInverse_of_injective z h_gradientInjective
    (residual c (x a) (q a))
  have h_normSq :
      ‖EqualityConstrained.constraintGradient c z v‖ ^ 2 =
        ⟪v, residual c (x a) (q a)⟫_ℝ := by
    calc
      ‖EqualityConstrained.constraintGradient c z v‖ ^ 2 =
          ⟪ContinuousLinearMap.adjoint
              (EqualityConstrained.constraintGradient c z)
                (EqualityConstrained.constraintGradient c z v), v⟫_ℝ := by
        simpa only [ContinuousLinearMap.comp_apply, RCLike.re_to_real] using
          ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left
            (EqualityConstrained.constraintGradient c z) v
      _ = ⟪gram c z v, v⟫_ℝ := by
        rw [gram_def]
        rfl
      _ = ⟪residual c (x a) (q a), v⟫_ℝ := by rw [h_gram]
      _ = ⟪v, residual c (x a) (q a)⟫_ℝ := real_inner_comm _ _
  have h_scaled :
      kappa * ‖EqualityConstrained.constraintGradient c z v‖ ^ 2 ≤
        ‖EqualityConstrained.constraintGradient c z v‖ *
          ‖residual c (x a) (q a)‖ := by
    calc
      kappa * ‖EqualityConstrained.constraintGradient c z v‖ ^ 2 =
          kappa * ⟪v, residual c (x a) (q a)⟫_ℝ := by rw [h_normSq]
      _ ≤ kappa * (‖v‖ * ‖residual c (x a) (q a)‖) := by
        gcongr
        exact real_inner_le_norm _ _
      _ = (kappa * ‖v‖) * ‖residual c (x a) (q a)‖ := by ring
      _ ≤ ‖EqualityConstrained.constraintGradient c z v‖ *
          ‖residual c (x a) (q a)‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact ha v
        · exact norm_nonneg _
  have h_gradientBound :
      ‖EqualityConstrained.constraintGradient c z v‖ ≤
        kappa⁻¹ * ‖residual c (x a) (q a)‖ := by
    by_cases h_zero : ‖EqualityConstrained.constraintGradient c z v‖ = 0
    · rw [h_zero]
      positivity
    · rw [le_inv_mul_iff₀ h_kappa]
      have h_positive : 0 < ‖EqualityConstrained.constraintGradient c z v‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero)
      nlinarith [h_scaled]
  -- The correction is the negative constraint-gradient image just bounded.
  rw [step_def]
  simpa only [z, v, norm_neg] using h_gradientBound

/-- The uncorrected primal-multiplier update determined by a base-step map. -/
@[expose]
def baseUpdate
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (rho : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
  fun y ↦ (trialPoint y.1 (p y), y.2 + rho • c (trialPoint y.1 (p y)))

/-- The base update applies the trial-point and classical multiplier formulas. -/
@[simp]
theorem baseUpdate_apply
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (rho : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    baseUpdate c rho p y =
      (trialPoint y.1 (p y), y.2 + rho • c (trialPoint y.1 (p y))) := rfl

/-- The corrected primal-multiplier update determined by a base-step map. -/
@[expose]
noncomputable def correctedUpdate
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (rho : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
  fun y ↦ (nextPoint c y.1 (p y), nextMultiplier c rho y.1 y.2 (p y))

/-- The corrected update applies the corrected point and multiplier formulas. -/
@[simp]
theorem correctedUpdate_apply
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (rho : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    correctedUpdate c rho p y =
      (nextPoint c y.1 (p y), nextMultiplier c rho y.1 y.2 (p y)) := rfl

/-- Helper for legacy appendix remark C.2: pointwise subtraction of the corrected and base
updates exposes the primal correction and the corresponding constraint increment. -/
lemma correctedUpdate_sub_baseUpdate_apply
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (rho : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    (correctedUpdate c rho p - baseUpdate c rho p) y =
      (step c y.1 (p y),
        rho • (c (nextPoint c y.1 (p y)) - c (trialPoint y.1 (p y)))) := by
  -- Evaluate both update records before simplifying their two components.
  apply Prod.ext
  · change nextPoint c y.1 (p y) - trialPoint y.1 (p y) = step c y.1 (p y)
    rw [nextPoint_def]
    exact add_sub_cancel_left _ _
  · change nextMultiplier c rho y.1 y.2 (p y) -
      (y.2 + rho • c (trialPoint y.1 (p y))) =
        rho • (c (nextPoint c y.1 (p y)) - c (trialPoint y.1 (p y)))
    rw [nextMultiplier_def]
    module

section

variable (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
variable (h_kkt : KKT.IsPair f c xStar multiplierStar)
variable (h_licq : ∀ᶠ x in nhds xStar,
  Function.Injective (EqualityConstrained.constraintGradient c x))
variable (h_minimizes : ∀ᶠ y in nhds (xStar, multiplierStar),
  IsMinOn (LALM.stepModel f c rho beta y.1 y.2) Set.univ (p y))

include hf hc h_kkt h_minimizes in
/-- Helper for legacy appendix remark C.2: a locally chosen minimizer of the base LALM step model is
first order in the distance from a KKT pair. -/
theorem baseStep_isBigO :
    p =O[nhds (xStar, multiplierStar)]
      (fun y ↦ ‖y - (xStar, multiplierStar)‖) := by
  -- Apply the minimizer coercivity estimate throughout the eventual
  -- minimization neighborhood.
  have h_rho : (0 : ℝ) ≤ rho := by positivity
  have h_beta : (0 : ℝ) < beta :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 beta.ne_zero)
  have h_minimizerBound :
      p =O[nhds (xStar, multiplierStar)]
        (fun y ↦ LALM.stepModelGradient f c (rho : ℝ) (beta : ℝ) y.1 y.2 0) := by
    apply Asymptotics.IsBigO.of_bound (beta : ℝ)⁻¹
    filter_upwards [h_minimizes] with y hy
    exact minimizerNorm_le_inv_mul_stepModelGradientZeroNorm
      f c rho beta y.1 y.2 (p y) h_rho h_beta hy
  -- Smooth KKT vanishing controls the zero-step gradient by the state error.
  exact h_minimizerBound.trans (stepModelGradientZero_isBigO hf hc h_kkt)

include hc h_licq in
/-- Helper for legacy appendix remark C.2: the feasibility correction associated with the base step is
quadratic in the norm of that step, provided that the base step tends to zero. -/
theorem step_isBigO_sq
    (h_step : Tendsto p (nhds (xStar, multiplierStar)) (nhds 0)) :
    (fun y ↦ step c y.1 (p y)) =O[nhds (xStar, multiplierStar)]
      (fun y ↦ ‖p y‖ ^ 2) := by
  -- LICQ at the reference point follows from the eventual neighborhood
  -- hypothesis, and the first projection converges to the primal reference.
  have h_injective : Function.Injective
      (EqualityConstrained.constraintGradient c xStar) :=
    mem_of_mem_nhds h_licq
  have h_fst : Tendsto
      (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦ y.1)
      (nhds (xStar, multiplierStar)) (nhds xStar) := continuousAt_fst
  have h_correctionToResidual := stepComp_isBigO_residual_of_licq
    (hc.of_le one_le_two_enat) h_injective h_fst h_step
  -- Compose the stable-LICQ estimate with the quadratic Taylor remainder.
  exact h_correctionToResidual.trans
    (residualComp_isBigO_sq hc h_fst h_step)

include hf hc h_kkt h_licq h_minimizes in
/-- Under the full hypotheses of legacy appendix remark C.2, the first-order base-step estimate
supplies the convergence assumption for the quadratic correction estimate. -/
theorem step_isBigO_sq_of_minimizes :
    (fun y ↦ step c y.1 (p y)) =O[nhds (xStar, multiplierStar)]
      (fun y ↦ ‖p y‖ ^ 2) := by
  -- The first-order base-step estimate forces the selected step to vanish at
  -- the KKT pair.
  have h_distanceTendsto : Tendsto
      (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        ‖y - (xStar, multiplierStar)‖)
      (nhds (xStar, multiplierStar)) (nhds 0) := by
    have h_const : ContinuousAt
        (fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
          (xStar, multiplierStar)) (xStar, multiplierStar) := continuousAt_const
    have h_subTendsto : Tendsto
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
          y - (xStar, multiplierStar))
        (nhds (xStar, multiplierStar))
        (nhds ((xStar, multiplierStar) - (xStar, multiplierStar))) :=
      (continuousAt_id : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦ y)
        (xStar, multiplierStar)).sub h_const
    simpa only [sub_self, norm_zero] using h_subTendsto.norm
  have h_stepTendsto : Tendsto p (nhds (xStar, multiplierStar)) (nhds 0) :=
    (baseStep_isBigO hf hc h_kkt h_minimizes).trans_tendsto h_distanceTendsto
  -- Feed that convergence into the primitive quadratic-correction theorem.
  exact step_isBigO_sq hc h_licq h_stepTendsto

include hf hc h_kkt h_licq h_minimizes in
/-- Helper for legacy appendix remark C.2: the corrected and base primal-multiplier updates differ by a
term quadratic in the distance from the KKT pair. -/
theorem correctedUpdate_sub_baseUpdate_isBigO_sq :
    (correctedUpdate c rho p - baseUpdate c rho p) =O[nhds (xStar, multiplierStar)]
      (fun y ↦ ‖y - (xStar, multiplierStar)‖ ^ 2) := by
  -- Square the first-order base-step bound, then compose it with the
  -- quadratic correction estimate.
  have h_base := baseStep_isBigO hf hc h_kkt h_minimizes
  have h_correction := step_isBigO_sq_of_minimizes
    hf hc h_kkt h_licq h_minimizes
  have h_correctionDistance :
      (fun y ↦ step c y.1 (p y)) =O[nhds (xStar, multiplierStar)]
        (fun y ↦ ‖y - (xStar, multiplierStar)‖ ^ 2) :=
    h_correction.trans (h_base.norm_left.pow 2)
  have h_distanceTendsto : Tendsto
      (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        ‖y - (xStar, multiplierStar)‖)
      (nhds (xStar, multiplierStar)) (nhds 0) := by
    have h_const : ContinuousAt
        (fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
          (xStar, multiplierStar)) (xStar, multiplierStar) := continuousAt_const
    have h_subTendsto : Tendsto
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
          y - (xStar, multiplierStar))
        (nhds (xStar, multiplierStar))
        (nhds ((xStar, multiplierStar) - (xStar, multiplierStar))) :=
      (continuousAt_id : ContinuousAt
        (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦ y)
        (xStar, multiplierStar)).sub h_const
    simpa only [sub_self, norm_zero] using h_subTendsto.norm
  have h_distanceSqTendsto : Tendsto
      (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        ‖y - (xStar, multiplierStar)‖ ^ 2)
      (nhds (xStar, multiplierStar)) (nhds 0) := by
    simpa only [zero_pow two_ne_zero_nat] using h_distanceTendsto.pow 2
  have h_correctionTendsto : Tendsto
      (fun y ↦ step c y.1 (p y)) (nhds (xStar, multiplierStar)) (nhds 0) :=
    h_correctionDistance.trans_tendsto h_distanceSqTendsto
  have h_stepTendsto : Tendsto p (nhds (xStar, multiplierStar)) (nhds 0) :=
    h_base.trans_tendsto h_distanceTendsto
  have h_trialTendsto : Tendsto
      (fun y ↦ trialPoint y.1 (p y)) (nhds (xStar, multiplierStar)) (nhds xStar) := by
    simpa only [trialPoint_def, add_zero] using
      (continuous_fst.tendsto (xStar, multiplierStar)).add h_stepTendsto
  have h_nextTendsto : Tendsto
      (fun y ↦ nextPoint c y.1 (p y)) (nhds (xStar, multiplierStar)) (nhds xStar) := by
    simpa only [nextPoint_def, add_zero] using h_trialTendsto.add h_correctionTendsto
  -- Strict differentiability of `c` controls its increment between the trial
  -- and corrected points by the primal correction.
  have h_pointPairTendsto : Tendsto
      (fun y ↦ (nextPoint c y.1 (p y), trialPoint y.1 (p y)))
      (nhds (xStar, multiplierStar)) (nhds (xStar, xStar)) :=
    h_nextTendsto.prodMk_nhds h_trialTendsto
  have h_constraintDifferenceRaw :=
    (hc.contDiffAt.hasStrictFDerivAt two_ne_zero_enat).isBigO_sub.comp_tendsto
      h_pointPairTendsto
  have h_constraintDifference :
      (fun y ↦ c (nextPoint c y.1 (p y)) - c (trialPoint y.1 (p y))) =O[
        nhds (xStar, multiplierStar)]
        (fun y ↦ step c y.1 (p y)) := by
    refine h_constraintDifferenceRaw.congr ?_ ?_
    · intro y
      rfl
    · intro y
      simp only [Function.comp_apply, nextPoint_def, add_sub_cancel_left]
  have h_multiplierDistance :
      (fun y ↦ (rho : ℝ) •
        (c (nextPoint c y.1 (p y)) - c (trialPoint y.1 (p y)))) =O[
          nhds (xStar, multiplierStar)]
        (fun y ↦ ‖y - (xStar, multiplierStar)‖ ^ 2) := by
    refine ((h_constraintDifference.trans h_correctionDistance).const_smul_left
      (rho : ℝ)).congr_left ?_
    intro y
    rfl
  -- Assemble the two components through the stable pointwise update interface.
  have h_product := h_correctionDistance.prod_left h_multiplierDistance
  exact h_product.congr_left fun y ↦
    (correctedUpdate_sub_baseUpdate_apply c rho p y).symm

include hf hc h_kkt h_licq h_minimizes in
/-- legacy appendix remark C.2: the corrected update and base update have the same Fréchet
derivative at the KKT pair. Thus the correction does not generically change the
common local linear convergence factor, though derivative-degenerate cases may differ. -/
theorem fderiv_correctedUpdate_eq_baseUpdate :
    fderiv ℝ (correctedUpdate c rho p) (xStar, multiplierStar) =
      fderiv ℝ (baseUpdate c rho p) (xStar, multiplierStar) := by
  -- The quadratic update difference has zero Fréchet derivative at the KKT
  -- pair, independently of whether either update is itself differentiable.
  have h_differenceDerivative : HasFDerivAt
      (correctedUpdate c rho p - baseUpdate c rho p)
      (0 : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      (xStar, multiplierStar) :=
    (correctedUpdate_sub_baseUpdate_isBigO_sq
      hf hc h_kkt h_licq h_minimizes).hasFDerivAt one_lt_two_nat
  by_cases h_baseDifferentiable :
      DifferentiableAt ℝ (baseUpdate c rho p) (xStar, multiplierStar)
  · -- Adding the differentiable base update back to the zero-derivative
    -- difference identifies the derivative of the corrected update.
    have h_sum := h_differenceDerivative.add h_baseDifferentiable.hasFDerivAt
    have h_functionPointwise : ∀ y,
        correctedUpdate c rho p y =
          ((correctedUpdate c rho p - baseUpdate c rho p) + baseUpdate c rho p) y := by
      intro y
      simp
    have h_functionEq : correctedUpdate c rho p =ᶠ[nhds (xStar, multiplierStar)]
        (correctedUpdate c rho p - baseUpdate c rho p) + baseUpdate c rho p :=
      Filter.Eventually.of_forall h_functionPointwise
    have h_correctedDerivative : HasFDerivAt (correctedUpdate c rho p)
        (fderiv ℝ (baseUpdate c rho p) (xStar, multiplierStar))
        (xStar, multiplierStar) := by
      simpa only [zero_add] using h_sum.congr_of_eventuallyEq h_functionEq
    exact h_correctedDerivative.fderiv
  · -- If the corrected update were differentiable, subtracting the already
    -- differentiable difference would make the base update differentiable.
    have h_correctedNotDifferentiable :
        ¬DifferentiableAt ℝ (correctedUpdate c rho p) (xStar, multiplierStar) := by
      intro h_correctedDifferentiable
      have h_sub := h_correctedDifferentiable.sub h_differenceDerivative.differentiableAt
      have h_functionPointwise : ∀ y,
          baseUpdate c rho p y =
            (correctedUpdate c rho p -
              (correctedUpdate c rho p - baseUpdate c rho p)) y := by
        intro y
        simp
      have h_functionEq : baseUpdate c rho p =ᶠ[nhds (xStar, multiplierStar)]
          correctedUpdate c rho p -
            (correctedUpdate c rho p - baseUpdate c rho p) :=
        Filter.Eventually.of_forall h_functionPointwise
      exact h_baseDifferentiable (h_sub.congr_of_eventuallyEq h_functionEq)
    rw [fderiv_zero_of_not_differentiableAt h_correctedNotDifferentiable,
      fderiv_zero_of_not_differentiableAt h_baseDifferentiable]

end

end LALM.Correction
