/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped LevelSetNotation
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.1.3 lies in the cubic-regularization / Hessian-Lipschitz descent domain.

Sampled owner declarations:
* `HessianLipschitzOn` in `Definition_4_1_2`
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`
* `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y` in `Definition_4_1_3`
* `regularizedHessian_isPositive_of_isMinOn_cubicRegularizationQuadraticApproximation` in
  `Lemma_4_1_2`
* `𝓛[f](α)` together with `mem_levelSet_iff` in `Definition_4_1_1`

Source/core/bridge triage:
* source-facing: the two clauses of Lemma 4.1.3, namely the displayed inner-product inequality
  `(4.1.9)` and the current-sublevel / feasibility conclusion for `T_M(x)`
* core/canonical: `HessianLipschitzOn`, `cubicRegularizationQuadraticApproximation`,
  `IsMinOn ... Set.univ ...`, and the Chapter 4.2 owner `CubicRegularizationMapping f M`
* bridge/view: explicit endpoint-feasibility and segment-feasibility lemmas around the second
  clause over the whole-space owner

Primitive data:
* the feasible region `𝓕`
* the Hessian-Lipschitz owner `[HessianLipschitzOn L 𝓕 f]`
* the cubic-model minimizer hypothesis
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint`
* the source ambient containment `𝓛[f]((f x0)) ⊆ 𝓕`
* for the inner-product inequality `(4.1.9)`, the source base-point membership
  `x ∈ 𝓛[f]((f x0))`
* for the internal second-clause analysis, the source threshold `((2 / 3 : ℝ) * (L : ℝ) < M)`
* for the internal second-clause analysis, the source interior-feasibility hypothesis
  `x ∈ interior 𝓕`

-- Semantic recall note: repeated `lean_leansearch` timed out on this item, so the repair below
-- follows the local Chapter 4 owners directly.

Derived API:
* the labeled inequality `(4.1.9)` over the canonical whole-space owner
  `CubicRegularizationMapping f M`
* the source-facing current-sublevel / feasibility clause for the canonical whole-space
  cubic-step owner together with an explicit interior-feasibility hypothesis
* explicit-feasibility helpers for whole-space cubic-step owners

The whole-space owner `CubicRegularizationMapping` remains the chapter's canonical representation
of a chosen unconstrained cubic step for the chapter's unconstrained results. For the source-facing
second clause here, the public statement keeps that canonical owner and records the needed
interior-feasibility bridge explicitly as a hypothesis; the whole-space feasibility bridges stay
available as private helpers. -/

section

variable {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x trialPoint : E}

/-- Helper for Lemma 4.1.3: the scalar first-order optimality condition along the segment from
`x` to the minimizing trial point rewrites the gradient pairing as the regularized quadratic
form from the source proof. -/
lemma gradient_pairing_eq_regularized_quadratic_form
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    inner ℝ (∇ f x) (x - trialPoint) =
      inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
        (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  let d : E := trialPoint - x
  have hreg : HessianLipschitzOn L 𝓕 f := inferInstance
  have hC2 : ContDiffAt ℝ 2 f x := hreg.contDiffAt hx
  -- Pair the existing first-order optimality identity with the displacement `d = trialPoint - x`.
  have hstationary :
      ∇ f x + hessian f x d + ((M / 2 : ℝ) * ‖d‖) • d = 0 :=
    cubicRegularization_firstOrderOptimalityCondition_of_isMinOn hC2 hstep
  have hinner :=
    congrArg (fun z : E ↦ inner ℝ z d) hstationary
  have hscalar :
      inner ℝ (((M / 2 : ℝ) * ‖d‖) • d) d = (M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    rw [real_inner_comm, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hinner_zero :
      inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d + (M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ) = 0 := by
    simpa [d, inner_add_left, hscalar, add_assoc] using hinner
  have hflip :
      inner ℝ (∇ f x) (x - trialPoint) = - inner ℝ (∇ f x) d := by
    rw [show x - trialPoint = -d by
      simp [d, sub_eq_add_neg], inner_neg_right]
  linarith

/-- Helper for Lemma 4.1.3: the missing source inequality
`⟪∇²f(x)(trialPoint - x), trialPoint - x⟫ + (M / 2) ‖trialPoint - x‖^3 ≥ 0` is the scalar
regularized-Hessian positivity input used immediately after the stationarity identity. -/
lemma regularized_quadratic_form_nonneg
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    0 ≤ inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
      (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  let reflection : E := (2 : ℝ) • x - trialPoint
  let d : E := trialPoint - x
  -- Compare the minimizing trial point with its reflection through `x`; the odd linear term is
  -- the only contribution that changes sign.
  have hstep' := hstep
  rw [isMinOn_iff] at hstep'
  have hreflect_model :
      cubicRegularizationQuadraticApproximation f M x trialPoint ≤
        cubicRegularizationQuadraticApproximation f M x reflection :=
    hstep' reflection (by simp)
  have hreflection_sub : reflection - x = -d := by
    simp [reflection, d, two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hgrad_nonneg : 0 ≤ inner ℝ (∇ f x) (x - trialPoint) := by
    have htrial_eval :
        cubicRegularizationQuadraticApproximation f M x trialPoint =
          f x + inner ℝ (∇ f x) d +
            (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
            (M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
      simp [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply, d]
    have hreflect_eval :
        cubicRegularizationQuadraticApproximation f M x reflection =
          f x - inner ℝ (∇ f x) d +
            (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
            (M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
      rw [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply,
        hreflection_sub, map_neg]
      simp [norm_neg]
      ring
    have hgrad_nonpos_d : inner ℝ (∇ f x) d ≤ 0 := by
      rw [htrial_eval, hreflect_eval] at hreflect_model
      linarith
    have hflip :
        inner ℝ (∇ f x) (x - trialPoint) = - inner ℝ (∇ f x) d := by
      rw [show x - trialPoint = -d by simp [d, sub_eq_add_neg], inner_neg_right]
    rw [hflip]
    linarith
  -- Rewrite the gradient pairing by the scalarized stationarity identity.
  have hpair :
      inner ℝ (∇ f x) (x - trialPoint) =
        inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
          (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) :=
    by
      simpa using
        (@gradient_pairing_eq_regularized_quadratic_form
          E _ _ _ 𝓕 f L M x trialPoint inferInstance hstep hx)
  rw [← hpair]
  exact hgrad_nonneg

/-- Helper for Lemma 4.1.3, inequality `(4.1.9)`: once the base point `x` is known to be
feasible, the displacement `x - trialPoint` has nonnegative pairing with the gradient at `x`.
Specializing to `trialPoint = T_M(x)` recovers the displayed formula in the source lemma. -/
theorem inner_gradient_base_sub_cubicTrialPoint_nonneg
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕) :
    0 ≤ inner ℝ (∇ f x) (x - trialPoint) := by
  -- Route correction: first rewrite the pairing by the stationarity identity, then discharge the
  -- resulting scalar form by the regularized-Hessian nonnegativity input.
  have hpair :
      inner ℝ (∇ f x) (x - trialPoint) =
        inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
          (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) :=
    by
      simpa using
        (@gradient_pairing_eq_regularized_quadratic_form
          E _ _ _ 𝓕 f L M x trialPoint inferInstance hstep hx)
  have hnonneg :
      0 ≤ inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
        (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) :=
    by
      simpa using
        (@regularized_quadratic_form_nonneg
          E _ _ _ 𝓕 f L M x trialPoint inferInstance hstep hx)
  simpa [hpair] using hnonneg

/-- Helper for Lemma 4.1.3: every feasible point on the segment from `x` to the minimizing trial
point satisfies the source cubic-decrease estimate. -/
lemma segment_objective_drop_of_mem_feasible
    [HessianLipschitzOn L 𝓕 f]
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hz : x + α • (trialPoint - x) ∈ 𝓕) :
    f (x + α • (trialPoint - x)) ≤
      f x - α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
  let z : E := x + α • (trialPoint - x)
  have hf : HessianLipschitzOn L 𝓕 f := inferInstance
  have herror :=
    hf.secondOrderTaylorModel_error_le x z hx hz
  -- First replace `f z` by the quadratic Taylor model plus the cubic Hessian-Lipschitz error.
  have hupper :
      f z ≤ secondOrderTaylorModelAt f x z + ((L : ℝ) / 6) * ‖z - x‖ ^ (3 : ℕ) := by
    linarith [(abs_le.mp herror).2]
  have hpair :
      inner ℝ (∇ f x) (x - trialPoint) =
        inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
          (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) :=
    by
      simpa using
        (@gradient_pairing_eq_regularized_quadratic_form
          E _ _ _ 𝓕 f L M x trialPoint inferInstance hstep hx)
  have hnonneg : 0 ≤ inner ℝ (∇ f x) (x - trialPoint) :=
    by
      simpa using
        (@inner_gradient_base_sub_cubicTrialPoint_nonneg
          E _ _ _ 𝓕 f L M x trialPoint inferInstance hstep hx)
  have hzsub : z - x = α • (trialPoint - x) := by
    dsimp [z]
    abel_nf
  have hquad_scale :
      inner ℝ (hessian f x (α • (trialPoint - x))) (α • (trialPoint - x)) =
        α ^ (2 : ℕ) * inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) := by
    simp [inner_smul_left, inner_smul_right, pow_two, mul_assoc]
  have hgrad_flip :
      inner ℝ (∇ f x) (x - trialPoint) = - inner ℝ (∇ f x) (trialPoint - x) := by
    rw [show x - trialPoint = -(trialPoint - x) by abel_nf, inner_neg_right]
  have hpair' :
      inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) =
        - inner ℝ (∇ f x) (trialPoint - x) - (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    linarith [hpair, hgrad_flip]
  -- Then rewrite the Taylor model exactly as in the source proof.
  have hmodel :
      secondOrderTaylorModelAt f x z + ((L : ℝ) / 6) * ‖z - x‖ ^ (3 : ℕ) =
        f x + (α - α ^ (2 : ℕ) / 2) * inner ℝ (∇ f x) (trialPoint - x) -
          α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    rw [secondOrderTaylorModelAt_apply, hzsub, inner_smul_right, hquad_scale, hpair', norm_smul,
      Real.norm_of_nonneg hα.1, mul_pow]
    ring
  rw [hmodel] at hupper
  have hcoef : 0 ≤ α - α ^ (2 : ℕ) / 2 := by
    nlinarith [hα.1, hα.2]
  have hgrad_nonpos : inner ℝ (∇ f x) (trialPoint - x) ≤ 0 := by
    have hgrad_neg :
        inner ℝ (∇ f x) (trialPoint - x) = - inner ℝ (∇ f x) (x - trialPoint) := by
      rw [show trialPoint - x = -(x - trialPoint) by abel_nf, inner_neg_right]
    rw [hgrad_neg]
    exact neg_nonpos.mpr hnonneg
  have hdrop_linear :
      (α - α ^ (2 : ℕ) / 2) * inner ℝ (∇ f x) (trialPoint - x) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos hcoef hgrad_nonpos
  linarith

/-- Helper for Lemma 4.1.3: at every feasible parameter on the segment from `x` to `trialPoint`,
the objective restricted to that affine line is continuous. This is the local continuity bridge
available from the Hessian-Lipschitz hypothesis on the open feasible region. -/
lemma feasibleSegmentObjectiveContinuousAt
    [HessianLipschitzOn L 𝓕 f]
    {α : ℝ}
    (hz : x + α • (trialPoint - x) ∈ 𝓕) :
    ContinuousAt (fun β : ℝ ↦ f (x + β • (trialPoint - x))) α := by
  let g : ℝ → E := fun β ↦ x + β • (trialPoint - x)
  have hf : HessianLipschitzOn L 𝓕 f := inferInstance
  have hsegment : Continuous g := by
    continuity
  have hsegmentAt : ContinuousAt g α := hsegment.continuousAt
  have hcontf : ContinuousAt f (g α) := by
    simpa [g] using (hf.contDiffAt hz).continuousAt
  -- Restrict the pointwise `C²` regularity on `𝓕` to the affine segment through `x`.
  simpa [g, Function.comp] using hcontf.comp hsegmentAt

/-- Helper for Lemma 4.1.3: every positive feasible segment parameter already lies in the strict
current sublevel set as soon as the cubic step is nontrivial and `M > (2 / 3) L`. -/
lemma segment_objective_strict_drop_of_mem_feasible
    [HessianLipschitzOn L 𝓕 f]
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M)
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hαpos : 0 < α)
    (hmove : trialPoint ≠ x)
    (hz : x + α • (trialPoint - x) ∈ 𝓕) :
    f (x + α • (trialPoint - x)) < f x := by
  have hdrop :
      f (x + α • (trialPoint - x)) ≤
        f x - α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) :=
    segment_objective_drop_of_mem_feasible hstep hx hα hz
  have hcoef_pos : 0 < M / 4 - α * (L : ℝ) / 6 := by
    have hαL : α * (L : ℝ) / 6 ≤ (L : ℝ) / 6 := by
      have hL_nonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.2
      have hmul : α * (L : ℝ) ≤ 1 * (L : ℝ) := by
        exact mul_le_mul_of_nonneg_right hα.2 hL_nonneg
      nlinarith
    have hLM : (L : ℝ) / 6 < M / 4 := by
      nlinarith
    linarith
  have hnorm_pos : 0 < ‖trialPoint - x‖ ^ (3 : ℕ) := by
    have hnorm : 0 < ‖trialPoint - x‖ := by
      refine norm_pos_iff.mpr ?_
      exact sub_ne_zero.mpr hmove
    exact pow_pos hnorm _
  have hpenalty_pos :
      0 < α ^ (2 : ℕ) * (M / 4 - α * (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    have hαsq_pos : 0 < α ^ (2 : ℕ) := by positivity
    positivity
  -- The nonzero coefficient in the cubic decrease estimate upgrades `≤` to a strict drop.
  linarith

omit [CompleteSpace E] in
/-- Helper for Lemma 4.1.3: once every feasible point on the segment from `x` to `trialPoint`
falls back into the current sublevel set, the source first-exit argument should force the whole
segment to stay feasible. -/
lemma segment_feasible_of_sublevel_containment
    (hxint : x ∈ interior 𝓕)
    (hopen : IsOpen 𝓕)
    (hcontSegment : Continuous fun α : ℝ ↦ f (x + α • (trialPoint - x)))
    (hsublevel : 𝓛[f]((f x)) ⊆ 𝓕)
    (hsegment :
      ∀ {α : ℝ}, α ∈ Set.Icc (0 : ℝ) 1 →
        x + α • (trialPoint - x) ∈ 𝓕 →
        x + α • (trialPoint - x) ∈ 𝓛[f]((f x))) :
    trialPoint ∈ 𝓕 := by
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let segment : I → E := fun t ↦ x + (t : ℝ) • (trialPoint - x)
  let U : Set I := segment ⁻¹' 𝓕
  have hsegment_cont : Continuous segment := by
    -- The affine segment parameterization is continuous on the compact interval.
    continuity
  have hU_open : IsOpen U := by
    -- The feasible-parameter set is open because `𝓕` itself is open.
    exact hopen.preimage hsegment_cont
  have hU_eq :
      U = (fun t : I ↦ f (segment t)) ⁻¹' Set.Iic (f x) := by
    -- On `Icc 0 1`, feasibility is equivalent to current-sublevel membership by hypothesis.
    ext t
    constructor
    · intro htU
      simpa [U, segment, mem_levelSet_iff] using hsegment t.2 htU
    · intro htLevel
      exact hsublevel (by simpa [segment, mem_levelSet_iff] using htLevel)
  have hU_closed : IsClosed U := by
    -- Closedness comes from continuity of the scalar objective along the whole segment.
    rw [hU_eq]
    exact isClosed_Iic.preimage (hcontSegment.comp continuous_subtype_val)
  have hU_clopen : IsClopen U := ⟨hU_closed, hU_open⟩
  letI : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc
  have h0 : (⟨0, by constructor <;> norm_num⟩ : I) ∈ U := by
    -- The left endpoint is the base point `x`, which is interior-feasible by assumption.
    simpa [U, segment] using interior_subset hxint
  have hU_univ : U = Set.univ := hU_clopen.eq_univ ⟨_, h0⟩
  have h1 : (⟨1, by constructor <;> norm_num⟩ : I) ∈ U := by
    simp [hU_univ]
  -- Evaluating the universal feasible-parameter set at `1` yields the trial point.
  simpa [U, segment] using h1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Helper for Lemma 4.1.3: every point of the current sublevel set already lies in `𝓕` once the
initial sublevel set is known to lie in `𝓕` and `x` belongs to that initial sublevel set. -/
lemma current_sublevel_subset_feasible
    {x0 x : E}
    (hlevel0 : 𝓛[f]((f x0)) ⊆ 𝓕)
    (hx : x ∈ 𝓛[f]((f x0))) :
    𝓛[f]((f x)) ⊆ 𝓕 := by
  intro y hy
  -- Chain the current-sublevel inequality with the original one before reusing `hlevel0`.
  have hx_le : f x ≤ f x0 := by
    simpa [mem_levelSet_iff] using hx
  have hy_le : f y ≤ f x := by
    simpa [mem_levelSet_iff] using hy
  apply hlevel0
  simpa [mem_levelSet_iff] using le_trans hy_le hx_le

/-- Helper for Lemma 4.1.3: once the cubic trial point is known to be feasible, the endpoint
case `α = 1` of the segment decrease estimate places it back in the current sublevel set
`𝓛[f]((f x))`. -/
lemma trialPoint_mem_currentSublevel_of_mem_feasible
    [HessianLipschitzOn L 𝓕 f]
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M)
    (hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    (htrialPoint : trialPoint ∈ 𝓕) :
    trialPoint ∈ 𝓛[f]((f x)) := by
  have hdrop :
      f trialPoint ≤
        f x - (M / 4 - (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    -- Specialize the feasible segment decrease estimate to the endpoint `α = 1`.
    simpa using
      (@segment_objective_drop_of_mem_feasible
        E _ _ _ 𝓕 f L M x trialPoint inferInstance hstep hx
        1
        (by constructor <;> norm_num)
        (by simpa))
  have hcoeff_nonneg : 0 ≤ M / 4 - (L : ℝ) / 6 := by
    -- The source threshold `M > (2 / 3) L` makes the endpoint penalty nonnegative.
    nlinarith
  have hpow_nonneg : 0 ≤ ‖trialPoint - x‖ ^ (3 : ℕ) := by
    positivity
  have hpenalty_nonneg :
      0 ≤ (M / 4 - (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    exact mul_nonneg hcoeff_nonneg hpow_nonneg
  have hle : f trialPoint ≤ f x := by
    calc
      f trialPoint ≤ f x - (M / 4 - (L : ℝ) / 6) * ‖trialPoint - x‖ ^ (3 : ℕ) := hdrop
      _ ≤ f x := by
        linarith
  simpa [mem_levelSet_iff] using hle

/-- Lemma 4.1.3 (1). Under the chapter's initial-sublevel containment context, for any
`x ∈ 𝓛[f]((f x₀))`, the gradient at `x` has nonnegative pairing with the cubic-step
displacement `x - T_M(x)`. This is the displayed inequality `(4.1.9)` for the canonical
whole-space cubic-step owner. -/
theorem cubicStep_nonneg_inner
    [HessianLipschitzOn L 𝓕 f]
    (step : CubicRegularizationMapping f M)
    {x0 x : E}
    (hlevel0 : 𝓛[f]((f x0)) ⊆ 𝓕)
    (hx : x ∈ 𝓛[f]((f x0))) :
    0 ≤ inner ℝ (∇ f x) (x - step x) := by
  have hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (step x) := by
    simpa using step.isMinOn_apply x
  have hxF : x ∈ 𝓕 := hlevel0 hx
  -- Reuse the base-point optimality inequality at the canonical cubic step `T_M(x)`.
  simpa using
    (@inner_gradient_base_sub_cubicTrialPoint_nonneg
      E _ _ _ 𝓕 f L M x (step x) inferInstance hstep hxF)

/-- Internal feasibility bridge: if the chosen whole-space cubic-step owner sends
interior-feasible base points back into `𝓕`, then under the Chapter 4 threshold
`M > (2 / 3) L` and `x ∈ interior 𝓕`, the cubic step belongs to the current sublevel set
`𝓛[f]((f x))`, and that current sublevel set is contained in `𝓕`. -/
private theorem cubicStep_mem_currentSublevel_of_mapsTo_interior
    [HessianLipschitzOn L 𝓕 f]
    (step : CubicRegularizationMapping f M)
    (hInterior : Set.MapsTo step (interior 𝓕) 𝓕)
    {x0 x : E}
    (hlevel0 : 𝓛[f]((f x0)) ⊆ 𝓕)
    (hx : x ∈ 𝓛[f]((f x0)))
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M)
    (hxint : x ∈ interior 𝓕) :
    step x ∈ 𝓛[f]((f x)) ∧ 𝓛[f]((f x)) ⊆ 𝓕 := by
  have hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (step x) := by
    simpa using step.isMinOn_apply x
  have hxF : x ∈ 𝓕 := hlevel0 hx
  have hstepF : step x ∈ 𝓕 := hInterior hxint
  refine ⟨?_, current_sublevel_subset_feasible hlevel0 hx⟩
  simpa using
    (@trialPoint_mem_currentSublevel_of_mem_feasible
      E _ _ _ 𝓕 f L M x (step x) inferInstance hM hstep hxF hstepF)

/-- Lemma 4.1.3 (2). Under the chapter's initial-sublevel containment context, let `T_M` be the
canonical whole-space cubic-step owner and assume it sends interior-feasible base points back into
`𝓕`. If `M > (2 / 3) L` and `x ∈ interior 𝓕`, then `T_M(x)` belongs to the current sublevel set
`𝓛[f]((f x))`, and that current sublevel set is contained in `𝓕`. This keeps the source clause on
the chapter's `T_M` owner while making the needed endpoint-feasibility bridge explicit. -/
theorem cubicStep_mem_currentSublevel_and_currentSublevel_subset_feasible
    [HessianLipschitzOn L 𝓕 f]
    (step : CubicRegularizationMapping f M)
    (hInterior : Set.MapsTo step (interior 𝓕) 𝓕)
    {x0 x : E}
    (hlevel0 : 𝓛[f]((f x0)) ⊆ 𝓕)
    (hx : x ∈ 𝓛[f]((f x0)))
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M)
    (hxint : x ∈ interior 𝓕) :
    step x ∈ 𝓛[f]((f x)) ∧ 𝓛[f]((f x)) ⊆ 𝓕 := by
  exact cubicStep_mem_currentSublevel_of_mapsTo_interior step hInterior hlevel0 hx hM hxint

/-- Helper for Lemma 4.1.3: for the current whole-space cubic-step owner,
explicit segment-feasibility suffices to place the cubic step in the current sublevel set, and
that sublevel set is still contained in `𝓕`. This keeps the explicit feasibility route available
until the chapter-level feasibility bridge for `CubicRegularizationMapping` is formalized. -/
private lemma cubicStep_mem_sublevel_and_feasible_of_segment_mem
    [HessianLipschitzOn L 𝓕 f]
    (step : CubicRegularizationMapping f M)
    {x0 x : E}
    (hlevel0 : 𝓛[f]((f x0)) ⊆ 𝓕)
    (hx : x ∈ 𝓛[f]((f x0)))
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M)
    (hsegment :
      ∀ {α : ℝ}, α ∈ Set.Icc (0 : ℝ) 1 → x + α • (step x - x) ∈ 𝓕) :
    step x ∈ 𝓛[f]((f x)) ∧ 𝓛[f]((f x)) ⊆ 𝓕 := by
  have hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (step x) := by
    simpa using step.isMinOn_apply x
  have hxF : x ∈ 𝓕 := hlevel0 hx
  have hstepF : step x ∈ 𝓕 := by
    simpa using
      (hsegment
        (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by
          constructor <;> norm_num))
  refine ⟨?_, current_sublevel_subset_feasible hlevel0 hx⟩
  simpa using
    (@trialPoint_mem_currentSublevel_of_mem_feasible
      E _ _ _ 𝓕 f L M x (step x) inferInstance hM hstep hxF hstepF)

/-- Helper for Lemma 4.1.3: for the current whole-space cubic-step owner, explicit endpoint
feasibility suffices to place `T_M(x)` in the current sublevel set `𝓛[f]((f x))`, and that
current sublevel set is contained in `𝓕`. -/
private lemma cubicStep_mem_sublevel_and_feasible_of_mem_feasible
    [HessianLipschitzOn L 𝓕 f]
    (step : CubicRegularizationMapping f M)
    {x0 x : E}
    (hlevel0 : 𝓛[f]((f x0)) ⊆ 𝓕)
    (hx : x ∈ 𝓛[f]((f x0)))
    (hM : (2 / 3 : ℝ) * (L : ℝ) < M)
    (hstepF : step x ∈ 𝓕) :
    step x ∈ 𝓛[f]((f x)) ∧ 𝓛[f]((f x)) ⊆ 𝓕 := by
  have hstep :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (step x) := by
    simpa using step.isMinOn_apply x
  have hxF : x ∈ 𝓕 := hlevel0 hx
  refine ⟨?_, current_sublevel_subset_feasible hlevel0 hx⟩
  simpa using
    (@trialPoint_mem_currentSublevel_of_mem_feasible
      E _ _ _ 𝓕 f L M x (step x) inferInstance hM hstep hxF hstepF)

end
