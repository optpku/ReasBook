/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped CubicRegularizationResidual Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The threshold constant `\tilde ω = L₀^4 / (324 (L + L₀)^6 τ_f^3)` appearing in the
two-phase rate estimate for gradient-dominated cubic regularization. -/
abbrev gradientDominatedCubicThreshold (L L0 τf : ℝ) : ℝ :=
  L0 ^ (4 : ℕ) / (324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ))

/-- Expanding `gradientDominatedCubicThreshold L L0 τf` recovers the textbook formula for
`\tilde ω`. -/
@[simp] theorem gradientDominatedCubicThreshold_def (L L0 τf : ℝ) :
    gradientDominatedCubicThreshold L L0 τf =
      L0 ^ (4 : ℕ) / (324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ)) :=
  rfl

section GradientDominatedCubicRegularization

variable {f : E → ℝ} {stepMap : ℝ → E → E} {L0 L τf : ℝ} {x0 : E}

variable
  (method :
    CubicRegularizationMethod
      f
      stepMap
      L0 L x0)

variable (xStar : E)
variable
  (hgradientDominated :
    GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
variable
  (hresidual_lower :
    ∀ k : ℕ,
      r[method.acceptedTrialPoint k] (method k) ≥
        Real.sqrt
          (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))

local notation "ω̃" => gradientDominatedCubicThreshold L L0 τf
local notation "Δ" => fun k : ℕ ↦ f (method k) - f xStar
local notation "σ" =>
  Real.rpow ω̃ (1 / 4 : ℝ) /
    (Real.rpow ω̃ (1 / 4 : ℝ) + Real.rpow (Δ 0) (1 / 4 : ℝ))
local notation "δ" => fun k : ℕ ↦ Δ k / ω̃

/- Theorem 4.1.7 lies in the Chapter 4 cubic-regularization / degree-two
gradient-domination rate domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner for the iterate
  sequence, regularization schedule, and accepted-step relation;
* `GradientDominatedOn` and `GradientDominatedOn.UsesConstant` in `Definition_4_1_9`, the chapter
  owner and witness predicate for minimizer/constant data;
* `CubicRegularizationMethod.objective_sub_succ_ge_gradient_norm_rpow_threeHalves` in
  `Lemma_4_1_8`, the owner-level one-step descent estimate derived from the canonical cubic-step
  hypotheses;
* `StrongConvexOn.gradientDominatedOn_two` in `Proposition_4_1_4`, together with
  `GradientDominatedOn.exists_usesConstant_of_mem_argmin` in `Definition_4_1_9`, the canonical
  upstream route from strong convexity to the `UsesConstant` witness needed here;
* `gradientDominated_cubicRegularization_log_gap_le_geometric` in `Theorem_4_1_6`, the adjacent
  owner-level cubic regularization rate theorem already stated on a general real inner-product
  space.

Best owner abstraction:
* source-facing: the two-phase cubic-regularization rate estimates under degree-two gradient
  domination;
* core/canonical: `CubicRegularizationMethod` together with
  `GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf`;
* bridge/view: the scalar textbook threshold `gradientDominatedCubicThreshold`, together with the
  local first-phase scalar `σ`.

Primitive data:
* the objective `f`;
* the cubic-regularization method `method`;
* the minimizer `xStar` and domination constant `τf`;
* the owner witness `GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf`;
* the minimizing-step and residual-lower-bound hypotheses that feed the canonical one-step drop
  theorem from `Lemma_4_1_8`.

Derived API:
* the threshold `\tilde ω`;
* the local first-phase exponential contraction constant `σ`;
* the first- and second-phase objective-gap bounds below.

This keeps the theorem source-facing, lowers the ambient space from the textbook `ℝⁿ` model to
the intrinsic real inner-product-space owner layer already used elsewhere in the chapter, reuses
the chapter algorithm owner instead of a bare iterate sequence, and treats the one-step decrease
estimate as derived API through `Lemma_4_1_8` rather than as primitive public data.
-/

/-- Helper for Theorem 4.1.7: the threshold `\tilde ω` is positive under the standing cubic
regularization and gradient-domination hypotheses. -/
lemma threshold_pos (hL0_pos : 0 < L0) (hL0_le_L : L0 ≤ L) (hτf_pos : 0 < τf) : 0 < ω̃ := by
  -- Expand the threshold and discharge positivity from `L₀ > 0` and `τf > 0`.
  rw [gradientDominatedCubicThreshold_def]
  have hsum_pos : 0 < L + L0 := by
    linarith
  have hden_pos : 0 < 324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ) := by
    positivity
  exact div_pos (pow_pos hL0_pos _) hden_pos

/-- Helper for Theorem 4.1.7: every trajectory gap `Δ k = f(x_k) - f(x^*)` is nonnegative because
`xStar` is a global minimizer. -/
lemma gap_nonneg
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (k : ℕ) : 0 ≤ Δ k := by
  -- Convert the `argmin` witness for `xStar` into the pointwise lower bound `f xStar ≤ f (x_k)`.
  rcases (mem_constrainedArgmin_iff.mp hgd.mem_argmin) with ⟨_, hxStar_min⟩
  exact sub_nonneg.mpr (hxStar_min (by simp))

/-- Helper for Theorem 4.1.7: taking the quarter power of `\tilde ω` recovers the one-step
descent coefficient divided by `τ_f^(3/4)`. -/
lemma threshold_rpow_one_quarter_eq_descent_constant
    (hL0_pos : 0 < L0) (hL0_le_L : L0 ≤ L) (hτf_pos : 0 < τf) :
    Real.rpow ω̃ (1 / 4 : ℝ) =
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) /
        Real.rpow τf (3 / 4 : ℝ) := by
  -- Expand the threshold and take the quarter root factor by factor.
  rw [gradientDominatedCubicThreshold_def]
  have hsum_pos : 0 < L + L0 := by
    linarith
  have hL0_root :
      Real.rpow (L0 ^ (4 : ℕ)) (1 / 4 : ℝ) = L0 := by
    calc
      Real.rpow (L0 ^ (4 : ℕ)) (1 / 4 : ℝ)
          = Real.rpow L0 ((4 : ℝ) * (1 / 4 : ℝ)) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul hL0_pos.le (4 : ℝ) (1 / 4 : ℝ)).symm
      _ = L0 := by
            norm_num [Real.rpow_one]
  have h81 :
      Real.rpow (81 : ℝ) (1 / 4 : ℝ) = 3 := by
    calc
      Real.rpow (81 : ℝ) (1 / 4 : ℝ)
          = Real.rpow ((3 : ℝ) ^ (4 : ℕ)) (1 / 4 : ℝ) := by norm_num
      _ = Real.rpow (3 : ℝ) ((4 : ℝ) * (1 / 4 : ℝ)) := by
            simpa [Real.rpow_natCast] using
              (Real.rpow_mul (by positivity : 0 ≤ (3 : ℝ)) (4 : ℝ) (1 / 4 : ℝ)).symm
      _ = 3 := by
            norm_num [Real.rpow_one]
  have h4 :
      Real.rpow (4 : ℝ) (1 / 4 : ℝ) = Real.sqrt 2 := by
    calc
      Real.rpow (4 : ℝ) (1 / 4 : ℝ)
          = Real.rpow ((2 : ℝ) ^ (2 : ℕ)) (1 / 4 : ℝ) := by norm_num
      _ = Real.rpow (2 : ℝ) ((2 : ℝ) * (1 / 4 : ℝ)) := by
            simpa [Real.rpow_natCast] using
              (Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ)) (2 : ℝ) (1 / 4 : ℝ)).symm
      _ = Real.sqrt 2 := by
            rw [show (2 : ℝ) * (1 / 4 : ℝ) = (1 / 2 : ℝ) by norm_num]
            simp [Real.sqrt_eq_rpow]
  have h324 :
      Real.rpow (324 : ℝ) (1 / 4 : ℝ) = 3 * Real.sqrt 2 := by
    calc
      Real.rpow (324 : ℝ) (1 / 4 : ℝ)
          = Real.rpow ((81 : ℝ) * 4) (1 / 4 : ℝ) := by norm_num
      _ = Real.rpow (81 : ℝ) (1 / 4 : ℝ) * Real.rpow (4 : ℝ) (1 / 4 : ℝ) := by
            simpa using
              (Real.mul_rpow
                (x := (81 : ℝ)) (y := (4 : ℝ)) (z := (1 / 4 : ℝ))
                (by positivity : 0 ≤ (81 : ℝ))
                (by positivity : 0 ≤ (4 : ℝ)))
      _ = 3 * Real.sqrt 2 := by
            rw [h81, h4]
  have hLsum :
      Real.rpow ((L + L0) ^ (6 : ℕ)) (1 / 4 : ℝ) =
        Real.rpow (L + L0) (3 / 2 : ℝ) := by
    calc
      Real.rpow ((L + L0) ^ (6 : ℕ)) (1 / 4 : ℝ)
          = Real.rpow (L + L0) ((6 : ℝ) * (1 / 4 : ℝ)) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul hsum_pos.le (6 : ℝ) (1 / 4 : ℝ)).symm
      _ = Real.rpow (L + L0) (3 / 2 : ℝ) := by
            congr 1
            norm_num
  have hτ :
      Real.rpow (τf ^ (3 : ℕ)) (1 / 4 : ℝ) = Real.rpow τf (3 / 4 : ℝ) := by
    calc
      Real.rpow (τf ^ (3 : ℕ)) (1 / 4 : ℝ)
          = Real.rpow τf ((3 : ℝ) * (1 / 4 : ℝ)) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul hτf_pos.le (3 : ℝ) (1 / 4 : ℝ)).symm
      _ = Real.rpow τf (3 / 4 : ℝ) := by
            congr 1
            norm_num
  have hden_split :
      Real.rpow (324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ)) (1 / 4 : ℝ) =
        Real.rpow (324 : ℝ) (1 / 4 : ℝ) *
          Real.rpow ((L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ)) (1 / 4 : ℝ) := by
    simpa [mul_assoc] using
      (Real.mul_rpow
        (x := (324 : ℝ))
        (y := (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ))
        (z := (1 / 4 : ℝ))
        (by positivity : 0 ≤ (324 : ℝ))
        (by positivity : 0 ≤ (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ)))
  have hden_tail_split :
      Real.rpow ((L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ)) (1 / 4 : ℝ) =
        Real.rpow ((L + L0) ^ (6 : ℕ)) (1 / 4 : ℝ) *
          Real.rpow (τf ^ (3 : ℕ)) (1 / 4 : ℝ) := by
    simpa using
      (Real.mul_rpow
        (x := (L + L0) ^ (6 : ℕ))
        (y := τf ^ (3 : ℕ))
        (z := (1 / 4 : ℝ))
        (by positivity : 0 ≤ (L + L0) ^ (6 : ℕ))
        (by positivity : 0 ≤ τf ^ (3 : ℕ)))
  calc
    Real.rpow (L0 ^ (4 : ℕ) / (324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ))) (1 / 4 : ℝ)
        = Real.rpow (L0 ^ (4 : ℕ)) (1 / 4 : ℝ) /
            Real.rpow (324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ)) (1 / 4 : ℝ) := by
              simpa using
                (Real.div_rpow
                  (by positivity : 0 ≤ L0 ^ (4 : ℕ))
                  (by positivity : 0 ≤ 324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ))
                  (1 / 4 : ℝ))
    _ = Real.rpow (L0 ^ (4 : ℕ)) (1 / 4 : ℝ) /
          (Real.rpow (324 : ℝ) (1 / 4 : ℝ) *
            Real.rpow ((L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ)) (1 / 4 : ℝ)) := by
            rw [hden_split]
    _ = Real.rpow (L0 ^ (4 : ℕ)) (1 / 4 : ℝ) /
          (Real.rpow (324 : ℝ) (1 / 4 : ℝ) *
            (Real.rpow ((L + L0) ^ (6 : ℕ)) (1 / 4 : ℝ) *
              Real.rpow (τf ^ (3 : ℕ)) (1 / 4 : ℝ))) := by
            rw [hden_tail_split]
    _ = (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) /
          Real.rpow τf (3 / 4 : ℝ) := by
            rw [hL0_root, h324, hLsum, hτ]
            ring

/-- Helper for Theorem 4.1.7: the degree-two gradient-domination bound at `x_{k+1}` converts the
next gap term `\tilde ω^{1/4} Δ_{k+1}^{3/4}` into the cubic descent coefficient times
`‖∇ f(x_{k+1})‖^{3/2}`. -/
lemma threshold_gap_term_le_gradient_term
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (k : ℕ) :
    Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ) ≤
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) *
        Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
  -- Apply the degree-two domination bound at `x_{k+1}` and raise it to the `3 / 4` power.
  have hτf_pos : 0 < τf := hgd.pos
  have hΔ_nonneg : 0 ≤ Δ (k + 1) :=
    gap_nonneg (method := method) (xStar := xStar) hgd (k + 1)
  have hω_pos : 0 < ω̃ :=
    threshold_pos (L := L) (L0 := L0) method.L0_pos method.L0_le_L hτf_pos
  have hg_nonneg : 0 ≤ ‖∇ f (method (k + 1))‖ := by
    positivity
  have hbound :
      Δ (k + 1) ≤ τf * Real.rpow ‖∇ f (method (k + 1))‖ (2 : ℝ) := by
    simpa [gradientWithin, gradient, fderivWithin_univ, Real.rpow_natCast] using
      (GradientDominatedOn.UsesConstant.bound
        (p := 2) (𝓕 := Set.univ) (f := f) (xStar := xStar) (τf := τf)
        hgd (x := method (k + 1)) (by simp))
  have hpow :
      Real.rpow (Δ (k + 1)) (3 / 4 : ℝ) ≤
        Real.rpow τf (3 / 4 : ℝ) *
          Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
    calc
      Real.rpow (Δ (k + 1)) (3 / 4 : ℝ)
          ≤ Real.rpow (τf * Real.rpow ‖∇ f (method (k + 1))‖ (2 : ℝ)) (3 / 4 : ℝ) := by
              exact Real.rpow_le_rpow hΔ_nonneg hbound (by positivity : 0 ≤ (3 / 4 : ℝ))
      _ = Real.rpow τf (3 / 4 : ℝ) *
            Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
            calc
              Real.rpow (τf * Real.rpow ‖∇ f (method (k + 1))‖ (2 : ℝ)) (3 / 4 : ℝ)
                  = Real.rpow τf (3 / 4 : ℝ) *
                      Real.rpow (Real.rpow ‖∇ f (method (k + 1))‖ (2 : ℝ)) (3 / 4 : ℝ) := by
                          simpa using
                            (Real.mul_rpow
                              (x := τf)
                              (y := Real.rpow ‖∇ f (method (k + 1))‖ (2 : ℝ))
                              (z := (3 / 4 : ℝ))
                              hτf_pos.le
                              (Real.rpow_nonneg hg_nonneg (2 : ℝ)))
              _ = Real.rpow τf (3 / 4 : ℝ) *
                    Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
                      congr 1
                      calc
                        Real.rpow (Real.rpow ‖∇ f (method (k + 1))‖ (2 : ℝ)) (3 / 4 : ℝ)
                            = Real.rpow ‖∇ f (method (k + 1))‖ ((2 : ℝ) * (3 / 4 : ℝ)) := by
                                symm
                                exact Real.rpow_mul hg_nonneg (2 : ℝ) (3 / 4 : ℝ)
                        _ = Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
                              congr 1
                              norm_num
  rw [threshold_rpow_one_quarter_eq_descent_constant
    (L := L) (L0 := L0) (τf := τf) method.L0_pos method.L0_le_L hτf_pos]
  have hτpow_pos : 0 < Real.rpow τf (3 / 4 : ℝ) := by
    exact Real.rpow_pos_of_pos hτf_pos _
  have hcoeff_nonneg :
      0 ≤
        ((L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) /
          Real.rpow τf (3 / 4 : ℝ)) := by
    have hsum_pos : 0 < L + L0 := by
      linarith [method.L0_pos, method.L0_le_L]
    have hsqrt2_pos : 0 < Real.sqrt 2 := by
      positivity
    have hLsum_rpow_pos : 0 < Real.rpow (L + L0) (3 / 2 : ℝ) := by
      exact Real.rpow_pos_of_pos hsum_pos _
    have hden_pos : 0 < 3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ) := by
      exact mul_pos (mul_pos (by positivity) hsqrt2_pos) hLsum_rpow_pos
    exact (div_pos (div_pos method.L0_pos hden_pos) hτpow_pos).le
  have hcancel :
      ((L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) /
          Real.rpow τf (3 / 4 : ℝ)) *
        (Real.rpow τf (3 / 4 : ℝ) *
          Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ)) =
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) *
        Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
    field_simp [hτpow_pos.ne']
  calc
    ((L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) /
        Real.rpow τf (3 / 4 : ℝ)) *
      Real.rpow (Δ (k + 1)) (3 / 4 : ℝ)
        ≤ ((L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) /
            Real.rpow τf (3 / 4 : ℝ)) *
          (Real.rpow τf (3 / 4 : ℝ) *
            Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hpow hcoeff_nonneg
    _ = (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) *
          Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := hcancel

/-- Helper for Theorem 4.1.7: combining the cubic one-step decrease with degree-two gradient
domination yields the scalar recurrence
`Δ_k - Δ_{k+1} ≥ \tilde ω^(1/4) Δ_{k+1}^{3/4}`. -/
lemma gap_step_recurrence
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) :
    Δ k - Δ (k + 1) ≥
      Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ) := by
  -- First bridge the next gap term to the owner-level descent coefficient, then apply the
  -- one-step cubic decrease estimate from Lemma 4.1.8.
  have hbridge :=
    threshold_gap_term_le_gradient_term
      (method := method) (xStar := xStar) hgd k
  have hdrop :=
    method.objective_sub_succ_ge_gradient_norm_rpow_threeHalves k (hres k)
  have hdrop' :
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) *
          Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) ≤
        Δ k - Δ (k + 1) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdrop
  exact le_trans hbridge hdrop'

/-- Helper for Theorem 4.1.7: every normalized gap `δ k = Δ k / \tilde ω` is nonnegative. -/
lemma normalized_gap_nonneg
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (k : ℕ) : 0 ≤ δ k :=
  div_nonneg (gap_nonneg (method := method) (xStar := xStar) hgd k)
    (threshold_pos method.L0_pos method.L0_le_L hgd.pos).le

/-- Helper for Theorem 4.1.7: dividing the one-step gap recurrence by `\tilde ω` gives the
textbook normalized inequality
`δ_k - δ_{k+1} ≥ δ_{k+1}^{3/4}`. -/
lemma normalized_gap_step_recurrence
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) :
    δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 4 : ℝ) := by
  -- Divide the unnormalized recurrence by the positive threshold and normalize the right-hand
  -- side with `δ_{k+1} = Δ_{k+1} / \tilde ω`.
  have hω_pos : 0 < ω̃ :=
    threshold_pos (L := L) (L0 := L0) method.L0_pos method.L0_le_L hgd.pos
  have hstep :
      Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ) ≤
        Δ k - Δ (k + 1) := by
    simpa using
      (gap_step_recurrence
        (method := method) (xStar := xStar) hgd hres k)
  have hrewrite :
      Δ k / ω̃ - Δ (k + 1) / ω̃ = (Δ k - Δ (k + 1)) / ω̃ := by
    field_simp [hω_pos.ne']
  have hΔ_nonneg : 0 ≤ Δ (k + 1) :=
    gap_nonneg (method := method) (xStar := xStar) hgd (k + 1)
  have hω_split :
      Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow ω̃ (3 / 4 : ℝ) = ω̃ := by
    calc
      Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow ω̃ (3 / 4 : ℝ)
          = Real.rpow ω̃ ((1 / 4 : ℝ) + (3 / 4 : ℝ)) := by
              symm
              exact Real.rpow_add hω_pos (1 / 4 : ℝ) (3 / 4 : ℝ)
      _ = ω̃ := by
            norm_num [Real.rpow_one]
  have hleft :
      (Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ)) / ω̃ =
        Real.rpow (δ (k + 1)) (3 / 4 : ℝ) := by
    have hωroot_pos : 0 < Real.rpow ω̃ (1 / 4 : ℝ) := by
      exact Real.rpow_pos_of_pos hω_pos _
    have hωthree_pos : 0 < Real.rpow ω̃ (3 / 4 : ℝ) := by
      exact Real.rpow_pos_of_pos hω_pos _
    calc
      (Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ)) / ω̃
          = (Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ)) /
              (Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow ω̃ (3 / 4 : ℝ)) := by
              rw [hω_split]
      _ = Real.rpow (Δ (k + 1)) (3 / 4 : ℝ) / Real.rpow ω̃ (3 / 4 : ℝ) := by
              field_simp [hωroot_pos.ne', hωthree_pos.ne']
      _ = Real.rpow (Δ (k + 1) / ω̃) (3 / 4 : ℝ) := by
            symm
            exact Real.div_rpow hΔ_nonneg hω_pos.le (3 / 4 : ℝ)
      _ = Real.rpow (δ (k + 1)) (3 / 4 : ℝ) := by
            rfl
  have hdiv :
      (Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ)) / ω̃ ≤
        (Δ k - Δ (k + 1)) / ω̃ := by
    exact div_le_div_of_nonneg_right hstep hω_pos.le
  have hnormalized :
      Real.rpow (δ (k + 1)) (3 / 4 : ℝ) ≤ δ k - δ (k + 1) := by
    calc
      Real.rpow (δ (k + 1)) (3 / 4 : ℝ)
          = (Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ)) / ω̃ := by
              symm
              exact hleft
      _ ≤ (Δ k - Δ (k + 1)) / ω̃ := hdiv
      _ = δ k - δ (k + 1) := hrewrite.symm
  exact hnormalized

/-- Helper for Theorem 4.1.7: the normalized gaps are nonincreasing from one iteration to the
next. -/
lemma normalized_gap_antitone_step
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) : δ (k + 1) ≤ δ k := by
  -- The normalized recurrence subtracts a nonnegative `3 / 4`-power term from `δ k`.
  have hstep :=
    normalized_gap_step_recurrence
      (method := method) (xStar := xStar) hgd hres k
  have hpow_nonneg : 0 ≤ Real.rpow (δ (k + 1)) (3 / 4 : ℝ) := by
    exact Real.rpow_nonneg
      (normalized_gap_nonneg (method := method) (xStar := xStar) hgd (k + 1))
      _
  linarith

/-- Helper for Theorem 4.1.7: every normalized gap is bounded above by the initial normalized
gap. -/
lemma normalized_gap_le_initial
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) : δ k ≤ δ 0 := by
  -- Iterate the one-step antitonicity from the initial index up to `k`.
  induction k with
  | zero =>
      exact le_rfl
  | succ k ih =>
      exact le_trans
        (normalized_gap_antitone_step
          (method := method) (xStar := xStar) hgd hres k)
        ih

/-- Helper for Theorem 4.1.7: the first-phase constant `σ` is exactly
`1 / (1 + δ₀^(1/4))` in terms of the normalized initial gap. -/
lemma sigma_eq_inv_one_add_initial_normalized_gap_rpow_one_quarter
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf) :
    σ = 1 / (1 + Real.rpow (δ 0) (1 / 4 : ℝ)) := by
  -- Rewrite the initial gap as `\tilde ω * δ₀` and factor the common quarter root of
  -- `\tilde ω` from the denominator.
  have hω_pos : 0 < ω̃ :=
    threshold_pos (L := L) (L0 := L0) method.L0_pos method.L0_le_L hgd.pos
  have hδ0_nonneg : 0 ≤ δ 0 :=
    normalized_gap_nonneg (method := method) (xStar := xStar) hgd 0
  have hscale {a ω : ℝ} (hω : 0 < ω) : a = ω * (a / ω) := by
    field_simp [hω.ne']
  have hΔ0 :
      Δ 0 = ω̃ * δ 0 := by
    simpa using hscale (a := Δ 0) (ω := ω̃) hω_pos
  have hΔ0_rpow :
      Real.rpow (Δ 0) (1 / 4 : ℝ) =
        Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (δ 0) (1 / 4 : ℝ) := by
    calc
      Real.rpow (Δ 0) (1 / 4 : ℝ)
          = Real.rpow (ω̃ * δ 0) (1 / 4 : ℝ) := by rw [hΔ0]
      _ = Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (δ 0) (1 / 4 : ℝ) := by
            simpa using
              (Real.mul_rpow
                (x := ω̃) (y := δ 0) (z := (1 / 4 : ℝ))
                hω_pos.le hδ0_nonneg)
  have hωroot_pos : 0 < Real.rpow ω̃ (1 / 4 : ℝ) := by
    exact Real.rpow_pos_of_pos hω_pos _
  have hfactor :
      Real.rpow ω̃ (1 / 4 : ℝ) +
          Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (δ 0) (1 / 4 : ℝ) =
        Real.rpow ω̃ (1 / 4 : ℝ) * (1 + Real.rpow (δ 0) (1 / 4 : ℝ)) := by
    ring
  calc
    σ = Real.rpow ω̃ (1 / 4 : ℝ) /
          (Real.rpow ω̃ (1 / 4 : ℝ) * (1 + Real.rpow (δ 0) (1 / 4 : ℝ))) := by
            rw [hΔ0_rpow, hfactor]
    _ = 1 / (1 + Real.rpow (δ 0) (1 / 4 : ℝ)) := by
          field_simp [hωroot_pos.ne']

/-- Helper for Theorem 4.1.7: a scalar recurrence of the form
`a - b ≥ b^(3/4)` yields one-step exponential contraction once `b` is bounded by an initial
scale `a0`. -/
lemma large_phase_scalar_contraction_of_step
    {a b a0 : ℝ}
    (hb_nonneg : 0 ≤ b)
    (hb_le_a0 : b ≤ a0)
    (hstep : a - b ≥ Real.rpow b (3 / 4 : ℝ)) :
    b ≤ Real.exp (-(1 / (1 + Real.rpow a0 (1 / 4 : ℝ)))) * a := by
  -- Split off the trivial zero-gap case before dividing by the quarter root of the scale.
  by_cases hb_zero : b = 0
  · subst hb_zero
    have ha_nonneg : 0 ≤ a := by
      simpa using hstep
    exact mul_nonneg (show 0 ≤ Real.exp (-(1 / (1 + Real.rpow a0 (1 / 4 : ℝ)))) by positivity) ha_nonneg
  have hb_pos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb_zero)
  have ha0_pos : 0 < a0 := lt_of_lt_of_le hb_pos hb_le_a0
  have hquarter_le :
      Real.rpow b (1 / 4 : ℝ) ≤ Real.rpow a0 (1 / 4 : ℝ) := by
    exact Real.rpow_le_rpow hb_nonneg hb_le_a0 (by positivity : 0 ≤ (1 / 4 : ℝ))
  have hsplit :
      b = Real.rpow b (3 / 4 : ℝ) * Real.rpow b (1 / 4 : ℝ) := by
    calc
      b = Real.rpow b (1 : ℝ) := by simpa using (Real.rpow_one b).symm
      _ = Real.rpow b ((3 / 4 : ℝ) + (1 / 4 : ℝ)) := by norm_num
      _ = Real.rpow b (3 / 4 : ℝ) * Real.rpow b (1 / 4 : ℝ) := by
            exact Real.rpow_add hb_pos _ _
  have hdivide :
      b / Real.rpow a0 (1 / 4 : ℝ) ≤ Real.rpow b (3 / 4 : ℝ) := by
    refine (div_le_iff₀ (Real.rpow_pos_of_pos ha0_pos _)).2 ?_
    calc
      b = Real.rpow b (3 / 4 : ℝ) * Real.rpow b (1 / 4 : ℝ) := hsplit
      _ ≤ Real.rpow b (3 / 4 : ℝ) * Real.rpow a0 (1 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hquarter_le (Real.rpow_nonneg hb_nonneg _)
  have hstep' : a - b ≥ b / Real.rpow a0 (1 / 4 : ℝ) := le_trans hdivide hstep
  have ha_nonneg : 0 ≤ a := by
    have hpow_nonneg : 0 ≤ Real.rpow b (3 / 4 : ℝ) := Real.rpow_nonneg hb_nonneg _
    linarith
  let t : ℝ := Real.rpow a0 (1 / 4 : ℝ)
  have ht_pos : 0 < t := by
    dsimp [t]
    exact Real.rpow_pos_of_pos ha0_pos _
  have hfactor :
      b ≤ a / (1 + 1 / t) := by
    refine (le_div_iff₀ (by positivity : 0 < 1 + 1 / t)).2 ?_
    have hsum : b + b / t ≤ a := by
      dsimp [t] at hstep' ⊢
      linarith
    calc
      b * (1 + 1 / t) = b + b / t := by ring
      _ ≤ a := hsum
  have hfactor' :
      b ≤ (1 - 1 / (1 + t)) * a := by
    rw [show a / (1 + 1 / t) = (1 - 1 / (1 + t)) * a by
      field_simp [ht_pos.ne']
      ring] at hfactor
    exact hfactor
  calc
    b ≤ (1 - 1 / (1 + t)) * a := hfactor'
    _ ≤ Real.exp (-(1 / (1 + t))) * a := by
          exact mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg (1 / (1 + t))) ha_nonneg
    _ = Real.exp (-(1 / (1 + Real.rpow a0 (1 / 4 : ℝ)))) * a := by
          simp [t]

/-- Helper for Theorem 4.1.7: while the normalized gap is at least `1`, one step contracts it by
the exponential factor `exp(-σ)`. -/
lemma normalized_gap_large_phase_step
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) (hk : 1 ≤ δ k) :
    δ (k + 1) ≤ Real.exp (-σ) * δ k := by
  -- Rewrite `σ` in normalized form and apply the standalone scalar contraction lemma.
  rw [sigma_eq_inv_one_add_initial_normalized_gap_rpow_one_quarter
    (method := method) (xStar := xStar) hgd]
  exact large_phase_scalar_contraction_of_step
    (hb_nonneg := normalized_gap_nonneg (method := method) (xStar := xStar) hgd (k + 1))
    (hb_le_a0 := normalized_gap_le_initial (method := method) (xStar := xStar) hgd hres (k + 1))
    (hstep := normalized_gap_step_recurrence (method := method) (xStar := xStar) hgd hres k)

/-- Helper for Theorem 4.1.7: if the normalized gap at index `k` is at least `1`, then iterating
the large-phase contraction yields the exponential bound `δ_k ≤ δ₀ e^{-kσ}`. -/
lemma normalized_gap_le_exponential_until_threshold
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) (hk : 1 ≤ δ k) :
    δ k ≤ δ 0 * Real.exp (-(k : ℝ) * σ) := by
  -- Iterate the one-step large-phase contraction; antitonicity keeps all previous indices in the
  -- same large-gap regime.
  induction k with
  | zero =>
      simpa using le_rfl
  | succ k ih =>
      have hk_prev : 1 ≤ δ k := by
        have hmono :=
          normalized_gap_antitone_step
            (method := method) (xStar := xStar) hgd hres k
        linarith
      have hstep :=
        normalized_gap_large_phase_step
          (method := method) (xStar := xStar) hgd hres k hk_prev
      have hprev := ih hk_prev
      calc
        δ (k + 1) ≤ Real.exp (-σ) * δ k := hstep
        _ ≤ Real.exp (-σ) * (δ 0 * Real.exp (-(k : ℝ) * σ)) := by
              exact mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = δ 0 * Real.exp (-((k + 1 : ℕ) : ℝ) * σ) := by
              calc
                Real.exp (-σ) * (δ 0 * Real.exp (-(k : ℝ) * σ))
                    = δ 0 * (Real.exp (-σ) * Real.exp (-(k : ℝ) * σ)) := by ring
                _ = δ 0 * Real.exp (-σ + -(k : ℝ) * σ) := by rw [← Real.exp_add]
                _ = δ 0 * Real.exp (-((k + 1 : ℕ) : ℝ) * σ) := by
                      congr 1
                      norm_num [Nat.cast_add]
                      ring

/-- Helper for Theorem 4.1.7: the normalized recurrence implies the one-step
`4 / 3`-power estimate `δ_{k+1} ≤ δ_k^(4/3)`. -/
lemma normalized_gap_small_phase_step
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) :
    δ (k + 1) ≤ Real.rpow (δ k) (4 / 3 : ℝ) := by
  -- Drop the nonnegative `δ_{k+1}` term, then invert the `3 / 4` power.
  have hstep :=
    normalized_gap_step_recurrence
      (method := method) (xStar := xStar) hgd hres k
  have hnext_nonneg : 0 ≤ δ (k + 1) :=
    normalized_gap_nonneg (method := method) (xStar := xStar) hgd (k + 1)
  have hk_nonneg : 0 ≤ δ k :=
    normalized_gap_nonneg (method := method) (xStar := xStar) hgd k
  have hpow : Real.rpow (δ (k + 1)) (3 / 4 : ℝ) ≤ δ k := by
    linarith
  have hinv :=
    (Real.le_rpow_inv_iff_of_pos hnext_nonneg hk_nonneg
      (by norm_num : 0 < (3 / 4 : ℝ))).2 hpow
  simpa using hinv

include hgradientDominated hresidual_lower

/-- Theorem 4.1.7 (1): every iterate whose suboptimality gap is still at least `\tilde ω`
satisfies the exponential bound
`f(x_k) - f(x^*) ≤ (f(x₀) - f(x^*)) e^{-kσ}`, where
`σ = \tilde ω^{1/4} / (\tilde ω^{1/4} + (f(x₀) - f(x^*))^{1/4})`. -/
-- Proof sketch: first apply
-- `method.objective_sub_succ_ge_gradient_norm_rpow_threeHalves` to the method
-- owner and `hresidual_lower` to obtain the canonical one-step decrease estimate.
-- Combine that estimate
-- with the gradient-domination bound at `x_{k+1}` to obtain
-- `Δ_k - Δ_{k+1} ≥ \tilde ω^{1/4} Δ_{k+1}^{3/4}` for `Δ_k = f(x_k) - f(x^*)`. While
-- `Δ_k ≥ \tilde ω`, this yields a uniform multiplicative contraction. The same one-step
-- decrease estimate makes the gaps nonincreasing, so the hypothesis at index `k` already forces
-- the initial gap to lie above `\tilde ω`; iterating the contraction then gives the stated
-- exponential decay up to the threshold `\tilde ω`.

theorem gradientDominated_cubicRegularization_gap_le_exponential_until_threshold
    (k : ℕ)
    (hk : ω̃ ≤ Δ k) :
    Δ k ≤ Δ 0 * Real.exp (-(k : ℝ) * σ) := by
  -- Route correction: after `include`, the helper layer already proves the normalized large-gap
  -- estimate, so this proof only rewrites `ω̃ ≤ Δ k` as `1 ≤ δ k` and scales back by `ω̃`.
  have hω_pos : 0 < ω̃ :=
    threshold_pos (L := L) (L0 := L0) method.L0_pos method.L0_le_L hgradientDominated.pos
  have hscale {a ω : ℝ} (hω : 0 < ω) : a = ω * (a / ω) := by
    field_simp [hω.ne']
  have hδk : 1 ≤ δ k := by
    exact (le_div_iff₀ hω_pos).2 (by simpa using hk)
  have hnormalized :=
    normalized_gap_le_exponential_until_threshold
      (method := method) (xStar := xStar) hgradientDominated hresidual_lower k hδk
  have hΔk :
      Δ k = ω̃ * δ k := by
    simpa using hscale (a := Δ k) (ω := ω̃) hω_pos
  have hΔ0 :
      Δ 0 = ω̃ * δ 0 := by
    simpa using hscale (a := Δ 0) (ω := ω̃) hω_pos
  calc
    Δ k = ω̃ * δ k := hΔk
    _ ≤ ω̃ * (δ 0 * Real.exp (-(k : ℝ) * σ)) := by
          exact mul_le_mul_of_nonneg_left hnormalized hω_pos.le
    _ = (ω̃ * δ 0) * Real.exp (-(k : ℝ) * σ) := by
          ring
    _ = Δ 0 * Real.exp (-(k : ℝ) * σ) := by
          rw [← hΔ0]

/-- Theorem 4.1.7 (2): if the suboptimality gap drops below `\tilde ω` at some index `k₀`, then
every later iterate satisfies the superlinear recurrence
`f(x_{k+1}) - f(x^*) ≤ \tilde ω ((f(x_k) - f(x^*)) / \tilde ω)^{4/3}`. -/
-- Proof sketch: the one-step cubic-regularization decrease estimate from `Lemma_4_1_8`, together
-- with the model-value upper bound built into `CubicRegularizationMethod`, makes the objective
-- gaps along the trajectory nonincreasing. Hence `f(x_{k₀}) - f(x^*) < \tilde ω` already implies
-- `f(x_k) - f(x^*) < \tilde ω` for every later `k ≥ k₀`. The scalar recurrence obtained by
-- combining `Lemma_4_1_8` with degree-two gradient domination then
-- implies `Δ_{k+1}^{3/4} ≤ Δ_k / \tilde ω`, and raising both sides to the power `4 / 3`
-- yields the displayed superlinear estimate.
theorem gradientDominated_cubicRegularization_gap_le_four_thirds_after_threshold
    (k0 : ℕ)
    (hk0 : Δ k0 < ω̃)
    (k : ℕ)
    (hk : k0 ≤ k) :
    Δ (k + 1) ≤ ω̃ * Real.rpow (Δ k / ω̃) (4 / 3 : ℝ) := by
  -- The small-phase bound is already proved on normalized gaps; only the scaling by `\tilde ω`
  -- remains.
  have _ : Δ k0 < ω̃ := hk0
  have _ : k0 ≤ k := hk
  have hω_pos : 0 < ω̃ :=
    threshold_pos (L := L) (L0 := L0) method.L0_pos method.L0_le_L hgradientDominated.pos
  have hscale {a ω : ℝ} (hω : 0 < ω) : a = ω * (a / ω) := by
    field_simp [hω.ne']
  have hnormalized :=
    normalized_gap_small_phase_step
      (method := method) (xStar := xStar) hgradientDominated hresidual_lower k
  have hΔsucc :
      Δ (k + 1) = ω̃ * δ (k + 1) := by
    simpa using hscale (a := Δ (k + 1)) (ω := ω̃) hω_pos
  calc
    Δ (k + 1) = ω̃ * δ (k + 1) := hΔsucc
    _ ≤ ω̃ * Real.rpow (δ k) (4 / 3 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hnormalized hω_pos.le
    _ = ω̃ * Real.rpow (Δ k / ω̃) (4 / 3 : ℝ) := by
          rfl

omit hgradientDominated hresidual_lower

end GradientDominatedCubicRegularization
