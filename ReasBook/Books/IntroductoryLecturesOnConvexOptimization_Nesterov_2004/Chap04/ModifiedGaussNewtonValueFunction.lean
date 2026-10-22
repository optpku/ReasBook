/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_12

noncomputable section

open Set
open SetConstrainedMinimizationProblem
open scoped ConvexAnalysis
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁]

/-- The canonical modified Gauss--Newton optimal value `f_M(x)`, represented directly by the
Chapter 1 whole-space owner in `EReal`. -/
def modifiedGaussNewtonOptimalValueAt
    (ψ : E₁ → E₁ → ℝ) (x : E₁) : ℝ → EReal :=
  fun M ↦ (unconstrained (quadraticallyRegularizedObjective (ψ x) M x)).optimalValue

/-- Expanding `modifiedGaussNewtonOptimalValueAt ψ x` gives the Chapter 1 range-form infimum of
the regularized model values at parameter `M`. -/
-- Proof sketch: unfold `modifiedGaussNewtonOptimalValueAt` and apply the Chapter 1 owner lemma
-- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image`, then rewrite the whole-space
-- image over `Set.univ` as a range.
theorem modifiedGaussNewtonOptimalValueAt_eq_sInf_range
    (ψ : E₁ → E₁ → ℝ) (x : E₁) (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt ψ x M =
      sInf (Set.range fun y : E₁ ↦ (quadraticallyRegularizedObjective (ψ x) M x y : EReal)) :=
by
  -- Expand the Chapter 1 owner and rewrite the whole-space image as a range.
  simpa [modifiedGaussNewtonOptimalValueAt, Set.image_univ] using
    (unconstrained (quadraticallyRegularizedObjective (ψ x) M x)).optimalValue_eq_sInf_image

-- Proof sketch: package the quadratic-regularized local model as the canonical whole-space owner
-- `unconstrained (quadraticallyRegularizedObjective (ψ x) M x)`,
-- apply the Chapter 1 equality
-- `optimalValue_eq_of_isMinOn` at the minimizing point `step x`, and rewrite the objective value
-- as `step.modelValue x`.
/-- Evaluating a chosen modified Gauss--Newton minimizer at `x` realizes the canonical owner
value `f_M(x)` as the minimum of the quadratic-regularized local model. -/
theorem modifiedGaussNewtonOptimalValueAt_eq_modelValue
    {ψ : E₁ → E₁ → ℝ} {𝓕 : Set E₁} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ 𝓕 M) (x : 𝓕) :
    modifiedGaussNewtonOptimalValueAt ψ x M = step.modelValue x := by
  let problem := unconstrained (quadraticallyRegularizedObjective (ψ x) M x)
  -- The chosen step attains the whole-space minimum for the canonical owner problem.
  have hmin : IsMinOn problem problem.feasibleSet (step x) := by
    simpa [problem] using step.isMinOn_apply x
  have hvalue : problem.optimalValue = (problem (step x) : EReal) :=
    problem.optimalValue_eq_of_isMinOn (x := step x) (by simp [problem]) hmin
  -- Rewriting the owner objective at the minimizer gives the model value.
  simpa [problem, modifiedGaussNewtonOptimalValueAt, ModifiedGaussNewtonStep.modelValue] using
    hvalue

/-- In the whole-space case `𝓕 = Set.univ`, the canonical owner value at `x` is the whole-space
model value of any chosen modified Gauss--Newton minimizer. -/
-- Proof sketch: specialize
-- `modifiedGaussNewtonOptimalValueAt_eq_modelValue` to the subtype point `⟨x, Set.mem_univ x⟩`
-- and rewrite `modelValue` using the whole-space notation `f[step](x)`.
theorem modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv
    {ψ : E₁ → E₁ → ℝ} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    modifiedGaussNewtonOptimalValueAt ψ x M = f[step](x) := by
  -- Specialize the attained-minimum bridge to the canonical whole-space point.
  simpa [ModifiedGaussNewtonStep.modelValueAtUniv] using
    modifiedGaussNewtonOptimalValueAt_eq_modelValue step ⟨x, Set.mem_univ x⟩

/-- Any chosen whole-space modified Gauss--Newton minimizer makes the canonical owner value
finite at the corresponding regularization parameter `M`. -/
-- Proof sketch: use
-- `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv` to exhibit
-- `modifiedGaussNewtonOptimalValueAt ψ x M` as the `EReal` coercion of the real number
-- `f[step](x)`.
theorem modifiedGaussNewtonOptimalValueAt_mem_dom_of_step
    {ψ : E₁ → E₁ → ℝ} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    M ∈ dom (modifiedGaussNewtonOptimalValueAt ψ x) := by
  -- The attained whole-space value is a finite real number, hence the owner lies in its domain.
  have hvalue :
      modifiedGaussNewtonOptimalValueAt ψ x M = (f[step](x) : EReal) :=
    modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv step x
  -- Route correction: rewrite the owner value to the attained real model value and close
  -- finiteness directly by the `EReal` coercion API.
  rw [mem_extendedRealEffectiveDomain_iff, hvalue]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- On the finite-value domain of the canonical owner, its Chapter 3 real-part bridge agrees with
the source-facing model value `f_M(x)` of any chosen whole-space minimizing step. -/
-- Proof sketch: coerce both sides to `EReal`, rewrite the left side with
-- `coe_extendedRealRealPart` using `modifiedGaussNewtonOptimalValueAt_mem_dom_of_step`, and then
-- apply `modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv`.
theorem extendedRealRealPart_modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv
    {ψ : E₁ → E₁ → ℝ} {M : ℝ} (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M = f[step](x) :=
by
  have hdom : M ∈ dom (modifiedGaussNewtonOptimalValueAt ψ x) :=
    modifiedGaussNewtonOptimalValueAt_mem_dom_of_step step x
  -- Coercing the real part back to `EReal` recovers the attained owner value.
  have hcoe :
      ((extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M : ℝ) : EReal) =
        (f[step](x) : EReal) := by
    rw [coe_extendedRealRealPart hdom, modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv step x]
  exact (EReal.coe_eq_coe_iff).1 hcoe

/-- In the positive-regularization regime, the source-facing modified Gauss--Newton value is the
finite real part of the canonical whole-space owner value. -/
def modifiedGaussNewtonOptimalValue
    (ψ : E₁ → E₁ → ℝ) (x : E₁) :
    NNRealˣ → ℝ :=
  fun M ↦ extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) (M : ℝ)

/-- Helper for Proposition 4.4.6: for fixed base point `x` and trial point `y`, the
quadratically regularized slice is affine in the regularization parameter `M`. -/
theorem quadraticallyRegularizedObjective_affine_in_regularization
    (ψ : E₁ → E₁ → ℝ) (x y : E₁) (M₁ M₂ a b : ℝ) (hab : a + b = 1) :
    a * quadraticallyRegularizedObjective (ψ x) M₁ x y +
      b * quadraticallyRegularizedObjective (ψ x) M₂ x y =
    quadraticallyRegularizedObjective (ψ x) (a * M₁ + b * M₂) x y := by
  -- Expand the quadratic model at the three parameters and collect the `M`-dependence.
  rw [quadraticallyRegularizedObjective_apply, quadraticallyRegularizedObjective_apply,
    quadraticallyRegularizedObjective_apply]
  -- Collect the affine dependence on `M` and collapse the coefficient with `a + b = 1`.
  calc
    a * (ψ x y + M₁ / 2 * ‖y - x‖ ^ 2) + b * (ψ x y + M₂ / 2 * ‖y - x‖ ^ 2) =
        (a + b) * ψ x y + ((a * M₁ + b * M₂) / 2) * ‖y - x‖ ^ 2 := by
          ring
    _ = ψ x y + ((a * M₁ + b * M₂) / 2) * ‖y - x‖ ^ 2 := by
          rw [hab]
          ring

/-- A positive-parameter minimizing step identifies the source-facing owner
`modifiedGaussNewtonOptimalValue ψ x M` with the textbook whole-space model value `f_M(x)`. -/
@[simp] theorem modifiedGaussNewtonOptimalValue_eq_modelValueAtUniv
    {ψ : E₁ → E₁ → ℝ} (x : E₁)
    (M : NNRealˣ) (step : ModifiedGaussNewtonStep ψ Set.univ (M : ℝ)) :
    modifiedGaussNewtonOptimalValue ψ x M = f[step](x) := by
  simpa [modifiedGaussNewtonOptimalValue] using
    extendedRealRealPart_modifiedGaussNewtonOptimalValueAt_eq_modelValueAtUniv step x

/-- Helper for Proposition 4.4.6: the canonical owner value at `x` is bounded above by the
regularized local model evaluated at any chosen trial point `y`. -/
theorem modifiedGaussNewtonOptimalValueAt_le_trialValue
    (ψ : E₁ → E₁ → ℝ) (x y : E₁) (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt ψ x M ≤
      (quadraticallyRegularizedObjective (ψ x) M x y : EReal) := by
  let problem := unconstrained (quadraticallyRegularizedObjective (ψ x) M x)
  -- Compare the owner optimal value with the objective at the feasible trial point `y`.
  have hopt : problem.optimalValue ≤ (problem y : EReal) :=
    problem.optimalValue_le_of_mem_feasibleSet (by simp [problem])
  simpa [problem, modifiedGaussNewtonOptimalValueAt] using hopt

-- Proof sketch: for fixed `x` and `y`, the map
-- `M ↦ ψ(x; y) + (M / 2) ‖y - x‖²` is affine, hence concave, in `M`. The canonical owner
-- `modifiedGaussNewtonOptimalValueAt ψ x` is the pointwise infimum of these affine functions in
-- `EReal`; once this canonical owner is known to be finite on `(0, ∞)`, the Chapter 3 real-part
-- bridge gives the source-facing real-valued function `M ↦ f_M(x)` as the positive-parameter
-- owner `modifiedGaussNewtonOptimalValue ψ x`, and chosen minimizing steps identify that owner
-- with the textbook quantity `f[step M](x)` through the bridge above.
/-- Internal bridge: if the canonical modified Gauss--Newton optimal value is finite on `(0, ∞)`,
then its Chapter 3 finite real part is concave in the regularization parameter `M` on that
interval. -/
theorem modifiedGaussNewtonOptimalValueAt_concaveInRegularization
    {ψ : E₁ → E₁ → ℝ} {x : E₁}
    (hfinite :
      Ioi (0 : ℝ) ⊆ dom (modifiedGaussNewtonOptimalValueAt ψ x)) :
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)) :=
by
  refine ⟨convex_Ioi (0 : ℝ), ?_⟩
  intro M₁ hM₁ M₂ hM₂ a b ha hb hab
  let M := a * M₁ + b * M₂
  have hM₁' : 0 < M₁ := hM₁
  have hM₂' : 0 < M₂ := hM₂
  have hM : M ∈ Ioi (0 : ℝ) := by
    -- Positivity of the mixed parameter keeps the owner inside its finite-value domain.
    dsimp [M]
    by_cases ha_zero : a = 0
    · have hb_one : b = 1 := by nlinarith [hab, ha_zero]
      simpa [ha_zero, hb_one] using hM₂'
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
      have hleft : 0 < a * M₁ := mul_pos ha_pos hM₁'
      have hright : 0 ≤ b * M₂ := mul_nonneg hb (le_of_lt hM₂')
      have hsum : 0 < a * M₁ + b * M₂ := add_pos_of_pos_of_nonneg hleft hright
      simpa using hsum
  have hdom₁ : M₁ ∈ dom (modifiedGaussNewtonOptimalValueAt ψ x) := hfinite hM₁
  have hdom₂ : M₂ ∈ dom (modifiedGaussNewtonOptimalValueAt ψ x) := hfinite hM₂
  have hdomM : M ∈ dom (modifiedGaussNewtonOptimalValueAt ψ x) := hfinite hM
  -- It suffices to show that the weighted endpoint value is a lower bound for every trial slice
  -- at the mixed parameter, then close the owner inequality with `le_sInf`.
  refine (le_extendedRealRealPart_iff hdomM).2 ?_
  rw [modifiedGaussNewtonOptimalValueAt_eq_sInf_range]
  refine le_sInf ?_
  rintro z ⟨y, rfl⟩
  have htrial₁E :
      modifiedGaussNewtonOptimalValueAt ψ x M₁ ≤
        (quadraticallyRegularizedObjective (ψ x) M₁ x y : EReal) :=
    modifiedGaussNewtonOptimalValueAt_le_trialValue ψ x y M₁
  have htrial₂E :
      modifiedGaussNewtonOptimalValueAt ψ x M₂ ≤
        (quadraticallyRegularizedObjective (ψ x) M₂ x y : EReal) :=
    modifiedGaussNewtonOptimalValueAt_le_trialValue ψ x y M₂
  have htrial₁ :
      extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M₁ ≤
        quadraticallyRegularizedObjective (ψ x) M₁ x y :=
    (extendedRealRealPart_le_iff hdom₁).2 htrial₁E
  have htrial₂ :
      extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M₂ ≤
        quadraticallyRegularizedObjective (ψ x) M₂ x y :=
    (extendedRealRealPart_le_iff hdom₂).2 htrial₂E
  have hweighted :
      a * extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M₁ +
          b * extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M₂ ≤
        a * quadraticallyRegularizedObjective (ψ x) M₁ x y +
          b * quadraticallyRegularizedObjective (ψ x) M₂ x y := by
    -- Combine the two endpoint bounds with the nonnegative coefficients `a` and `b`.
    exact add_le_add
      (mul_le_mul_of_nonneg_left htrial₁ ha)
      (mul_le_mul_of_nonneg_left htrial₂ hb)
  have hslice :
      a * extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M₁ +
          b * extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M₂ ≤
        quadraticallyRegularizedObjective (ψ x) M x y := by
    -- The trial slice is affine in `M`, so the weighted endpoint slice is exactly the mixed one.
    calc
      a * extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M₁ +
          b * extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x) M₂ ≤
        a * quadraticallyRegularizedObjective (ψ x) M₁ x y +
          b * quadraticallyRegularizedObjective (ψ x) M₂ x y := hweighted
      _ = quadraticallyRegularizedObjective (ψ x) M x y := by
        rw [quadraticallyRegularizedObjective_affine_in_regularization
          (ψ := ψ) (x := x) (y := y) (M₁ := M₁) (M₂ := M₂) (a := a) (b := b) hab]
  exact (EReal.coe_le_coe_iff).2 hslice

end
