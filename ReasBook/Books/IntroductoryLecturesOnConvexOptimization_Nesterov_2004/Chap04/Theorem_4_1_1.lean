/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Gradient
open scoped CubicRegularizationResidual

noncomputable section

universe u

/- Theorem 4.1.1 lies in the cubic-regularization iteration-complexity domain.

Sampled owner declarations:
* `HessianLipschitzOn` in `Definition_4_1_2`;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`;
* `CubicRegularizationMethod.acceptedTrialPoint` in `Algorithm_4_1_5`;
* `cubicRegularizationResidual` in `Lemma_4_1_5`;
* `cubicRegularizationLocalOptimalityMeasure` in `Definition_4_1_4`.

Source/core/bridge triage:
* source-facing: Theorem 4.1.1 for the residual-cube rate and the stationarity sequence
  `μ_L(xᵢ)` along a cubic-regularization method;
* core/canonical: `HessianLipschitzOn` for the chapter smoothness owner, together with
  `CubicRegularizationMethod` and the generic step-map residual owner
  `cubicRegularizationResidual` from `Lemma_4_1_5`;
* bridge/view: the owner-level minimizing-step theorem `method.stepMap_isMinOn i` together with
  the bridge estimate `cubicRegularizationLocalOptimalityMeasure_le_norm_sub_of_isMinOn` from
  `Lemma_4_1_6`, transported to the trajectory via `method.acceptedTrialPoint_eq_succ`.

Primitive data:
* a cubic-regularization method `method` with step map `stepMap`,
* a lower bound `fStar` for the objective,
* the canonical local-optimality bridge data needed to apply
  `cubicRegularizationLocalOptimalityMeasure_le_norm_sub_of_isMinOn` along the trajectory.

Derived API:
* the residual-cube decrease estimate along the cubic-regularization trajectory, derived from
  `method.objective_step_le_value`, `method.stepMap_isMinOn`,
  `objective_sub_cubicRegularizationValue_ge_residual_cube`, and
  `method.regularization_pos`,
* summability of the residual cubes,
* convergence `μ_L(x_k) → 0`,
* the explicit `k^{-1/3}` bound for the finite minimum of `μ_L(x_i)`.
-/

section CubicRegularizationResidualRate

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable
  {f : E → ℝ}
  {stepMap : ℝ → E → E}
  {L0 L : ℝ}
  {x0 : E}
  {fStar : ℝ}

variable
  (method :
    CubicRegularizationMethod
      f
      stepMap
      L0 L x0)

local notation:max "r[" M "](" x ")" => r[stepMap M x] x

namespace CubicRegularizationMethod

/-- Along a cubic-regularization method, the textbook decrease estimate
`f(xᵢ) - f(xᵢ₊₁) ≥ (Mᵢ / 12) r_{Mᵢ}(xᵢ)^3` is derived from the accepted-step owner data; it is not
extra primitive input. -/
theorem objective_sub_succ_ge_residual_cube
    (method : CubicRegularizationMethod f stepMap L0 L x0)
    (i : ℕ) :
    f (method i) - f (method (i + 1)) ≥
      (method.regularization i / 12) * r[method.regularization i](method i) ^ (3 : ℕ) := by
  let modelValue :=
    EReal.toReal
      (SetConstrainedMinimizationProblem.optimalValue
        (cubicRegularizationProblem f (method.regularization i) (method i)))
  -- The accepted step is no larger than the cubic-model value at the current iterate.
  have hmodel :
      f (method i) - modelValue ≥
        (method.regularization i / 12) * r[method.regularization i](method i) ^ (3 : ℕ) :=
    objective_sub_cubicRegularizationValue_ge_residual_cube
      (f := f)
      (M := method.regularization i)
      (x := method i)
      (trialPoint := stepMap (method.regularization i) (method i))
      (method.regularization_pos i).le (method.stepMap_isMinOn i)
  have haccept :
      f (method (i + 1)) ≤ modelValue := by
    simpa [modelValue, method.x_succ i] using method.objective_step_le_value i
  -- Replacing the model value by the accepted objective preserves the same lower bound.
  have hdrop : f (method i) - modelValue ≤ f (method i) - f (method (i + 1)) := by
    simpa [modelValue] using sub_le_sub_left haccept (f (method i))
  exact le_trans hmodel hdrop

end CubicRegularizationMethod

-- Proof sketch: telescope the finite sum of decreases
-- `∑_{i=0}^{k-1} (f(xᵢ) - f(xᵢ₊₁)) = f(x₀) - f(x_k)`, bound `f(x_k)` below by `f*`, and use
-- `L₀ ≤ Mᵢ` from the method owner to obtain
-- `(L₀ / 12) * ∑_{i=0}^{k-1} r_{Mᵢ}(xᵢ)^3 ≤ f(x₀) - f*`. Since the residuals are norms, the
-- cubic residual series is nonnegative termwise, hence summable with the same bound on its total
-- sum.
/-- Auxiliary summability lemma: any cubic-regularization trajectory satisfying the textbook
decrease estimate has summable residual cubes with the expected `tsum` bound. The public
Theorem 4.1.1 (1) below applies this to the owner-derived decrease estimate. -/
theorem cubicRegularization_residual_cube_summable_and_tsum_le_of_decrease
    (hf_lower : ∀ z : E, fStar ≤ f z)
    (hdecrease :
      ∀ i : ℕ,
        f (method i) - f (method (i + 1)) ≥
          (method.regularization i / 12) * r[method.regularization i](method i) ^ (3 : ℕ)) :
    Summable (fun i ↦ r[method.regularization i](method i) ^ (3 : ℕ)) ∧
      (∑' i, r[method.regularization i](method i) ^ (3 : ℕ)) ≤
        (12 / L0) * (f (method 0) - fStar) := by
  let a : ℕ → ℝ := fun i ↦ r[method.regularization i](method i) ^ (3 : ℕ)
  have ha_nonneg : ∀ i : ℕ, 0 ≤ a i := by
    intro i
    dsimp [a]
    positivity
  have hsum_range_le :
      ∀ n : ℕ, ∑ i ∈ Finset.range n, a i ≤ (12 / L0) * (f (method 0) - fStar) := by
    intro n
    have hpointwise :
        ∀ i ∈ Finset.range n, a i ≤ (12 / L0) * (f (method i) - f (method (i + 1))) := by
      intro i hi
      have hratio :
          L0 / 12 ≤ method.regularization i / 12 := by
        nlinarith [method.L0_le_regularization i]
      have hscaled :
          (L0 / 12) * a i ≤
            (method.regularization i / 12) * a i := by
        exact mul_le_mul_of_nonneg_right hratio (ha_nonneg i)
      have hstep :
          (L0 / 12) * a i ≤ f (method i) - f (method (i + 1)) :=
        hscaled.trans (hdecrease i)
      have hfactor_pos : 0 < 12 / L0 := by
        exact div_pos (by norm_num) method.L0_pos
      calc
        a i = (12 / L0) * ((L0 / 12) * a i) := by
          field_simp [method.L0_pos.ne']
        _ ≤ (12 / L0) * (f (method i) - f (method (i + 1))) := by
          exact mul_le_mul_of_nonneg_left hstep hfactor_pos.le
    have htel :
        ∑ i ∈ Finset.range n, (f (method i) - f (method (i + 1))) =
          f (method 0) - f (method n) := by
      simpa using (Finset.sum_range_sub' (fun i ↦ f (method i)) n)
    have hterminal :
        f (method 0) - f (method n) ≤ f (method 0) - fStar := by
      simpa using sub_le_sub_left (hf_lower (method n)) (f (method 0))
    have hfactor_nonneg : 0 ≤ 12 / L0 := by
      exact le_of_lt (div_pos (by norm_num) method.L0_pos)
    calc
      ∑ i ∈ Finset.range n, a i
          ≤ ∑ i ∈ Finset.range n, (12 / L0) * (f (method i) - f (method (i + 1))) :=
        Finset.sum_le_sum hpointwise
      _ = (12 / L0) * ∑ i ∈ Finset.range n, (f (method i) - f (method (i + 1))) := by
        rw [Finset.mul_sum]
      _ = (12 / L0) * (f (method 0) - f (method n)) := by
        rw [htel]
      _ ≤ (12 / L0) * (f (method 0) - fStar) := by
        exact mul_le_mul_of_nonneg_left hterminal hfactor_nonneg
  -- Bounded nonnegative partial sums give both summability and the same bound on the total sum.
  exact
    ⟨summable_of_sum_range_le ha_nonneg hsum_range_le,
      Real.tsum_le_of_sum_range_le ha_nonneg hsum_range_le⟩

/-- Theorem 4.1.1 (1): for a cubic-regularization method, the textbook decrease estimate is
derived from the owner data, so a lower bound `f* ≤ f` suffices to conclude that
`∑_{i=0}^∞ r_{Mᵢ}(xᵢ)^3` is summable and bounded by `(12 / L₀) (f(x₀) - f*)`. -/
theorem cubicRegularization_residual_cube_summable_and_tsum_le
    (hf_lower : ∀ z : E, fStar ≤ f z) :
    Summable (fun i ↦ r[method.regularization i](method i) ^ (3 : ℕ)) ∧
      (∑' i, r[method.regularization i](method i) ^ (3 : ℕ)) ≤
        (12 / L0) * (f (method 0) - fStar) := by
  -- The public statement is the auxiliary telescoping lemma applied to the owner-derived decrease.
  exact
    cubicRegularization_residual_cube_summable_and_tsum_le_of_decrease
      (method := method) hf_lower
      (fun i ↦ method.objective_sub_succ_ge_residual_cube i)

end CubicRegularizationResidualRate

section CubicRegularizationStationarityRate

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

variable {f : E → ℝ} {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal} {x0 : E} {fStar : ℝ}

variable
  (method :
    CubicRegularizationMethod
      f
      stepMap
      L0 (L : ℝ) x0)

local notation:max "r[" M "](" x ")" =>
  r[stepMap M x] x
local notation:max "μ[" M "](" x ")" =>
  cubicRegularizationLocalOptimalityMeasure f (L : ℝ) M x

variable {𝓕 : Set E}

/-- If `0 < M ≤ 2L`, then the source-facing stationarity measure `μ_L(x)` is controlled by the
owner-level measure `μ_M(x)` up to the factor `4 / 3`. -/
theorem cubicRegularizationLocalOptimalityMeasure_at_L_le_four_thirds_mul
    {x : E} {M : ℝ}
    (hM : 0 < M)
    (hM_le : M ≤ 2 * (L : ℝ)) :
    μ[(L : ℝ)](x) ≤ (4 / 3 : ℝ) * μ[M](x) := by
  have hL_nonneg : 0 ≤ (L : ℝ) := by
    exact_mod_cast L.2
  have hL_pos : 0 < (L : ℝ) := by
    nlinarith
  have hμ_nonneg : 0 ≤ μ[M](x) := by
    exact le_trans (Real.sqrt_nonneg _) <|
      sqrt_scaledGradientNorm_le_cubicRegularizationLocalOptimalityMeasure
        f (L : ℝ) M x
  rw [cubicRegularizationLocalOptimalityMeasure_eq_max]
  refine max_le ?_ ?_
  · -- Compare the gradient component coefficients before invoking the `μ[M]` upper bound.
    have hratio_nonneg : 0 ≤ (((L : ℝ) + M) / (2 * (L : ℝ))) := by
      positivity
    have hinner_nonneg : 0 ≤ (2 / ((L : ℝ) + M)) * ‖∇ f x‖ := by
      positivity
    have hratio_le : ((L : ℝ) + M) / (2 * (L : ℝ)) ≤ (16 / 9 : ℝ) := by
      rw [div_le_iff₀ (show 0 < 2 * (L : ℝ) by positivity)]
      nlinarith
    have hsqrt_ratio :
        Real.sqrt (((L : ℝ) + M) / (2 * (L : ℝ))) ≤ (4 / 3 : ℝ) := by
      rw [← Real.sqrt_sq (show 0 ≤ (4 / 3 : ℝ) by norm_num)]
      have hsq : ((L : ℝ) + M) / (2 * (L : ℝ)) ≤ ((4 / 3 : ℝ) ^ (2 : ℕ)) := by
        nlinarith [hratio_le]
      exact Real.sqrt_le_sqrt hsq
    calc
      Real.sqrt ((2 / ((L : ℝ) + (L : ℝ))) * ‖∇ f x‖)
          = Real.sqrt
              ((((L : ℝ) + M) / (2 * (L : ℝ))) *
                ((2 / ((L : ℝ) + M)) * ‖∇ f x‖)) := by
            field_simp [hL_pos.ne', add_comm, add_left_comm, add_assoc]
            ring
      _ = Real.sqrt (((L : ℝ) + M) / (2 * (L : ℝ))) *
            Real.sqrt ((2 / ((L : ℝ) + M)) * ‖∇ f x‖) := by
            rw [Real.sqrt_mul hratio_nonneg]
      _ ≤ (4 / 3 : ℝ) * Real.sqrt ((2 / ((L : ℝ) + M)) * ‖∇ f x‖) := by
            exact mul_le_mul_of_nonneg_right hsqrt_ratio (Real.sqrt_nonneg _)
      _ ≤ (4 / 3 : ℝ) * μ[M](x) := by
            exact mul_le_mul_of_nonneg_left
              (sqrt_scaledGradientNorm_le_cubicRegularizationLocalOptimalityMeasure
                f (L : ℝ) M x)
              (by norm_num)
  · -- The spectral component differs only by a scalar ratio bounded by `4 / 3`.
    have hratio_nonneg : 0 ≤ (2 * (L : ℝ) + M) / (3 * (L : ℝ)) := by
      positivity
    have hratio_le : (2 * (L : ℝ) + M) / (3 * (L : ℝ)) ≤ (4 / 3 : ℝ) := by
      rw [div_le_iff₀ (show 0 < 3 * (L : ℝ) by positivity)]
      nlinarith
    calc
      -(2 / (2 * (L : ℝ) + (L : ℝ))) * λ_min(∇²f x)
          = ((2 * (L : ℝ) + M) / (3 * (L : ℝ))) *
              (-(2 / (2 * (L : ℝ) + M)) * λ_min(∇²f x)) := by
            field_simp [hL_pos.ne', add_comm, add_left_comm, add_assoc]
            ring
      _ ≤ ((2 * (L : ℝ) + M) / (3 * (L : ℝ))) * μ[M](x) := by
            exact mul_le_mul_of_nonneg_left
              (scaledNegLeastHessianEigenvalue_le_cubicRegularizationLocalOptimalityMeasure
                f (L : ℝ) M x)
              hratio_nonneg
      _ ≤ (4 / 3 : ℝ) * μ[M](x) := by
            exact mul_le_mul_of_nonneg_right hratio_le hμ_nonneg

/-- Helper for Theorem 4.1.1: a `HessianLipschitzOn` owner gives the local Loewner transport
bound `∇²f(x) - L‖y - x‖ I ≤ ∇²f(y) ≤ ∇²f(x) + L‖y - x‖ I`. -/
theorem HessianLipschitzOn.hessian_loewner_bounds
    {x y : E} (hf : HessianLipschitzOn L 𝓕 f)
    (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    let s : ℝ := (L : ℝ) * ‖y - x‖
    hessian f x - s • (1 : E →L[ℝ] E) ≤ hessian f y ∧
      hessian f y ≤ hessian f x + s • (1 : E →L[ℝ] E) := by
  let Δ : E →L[ℝ] E := hessian f y - hessian f x
  let s : ℝ := (L : ℝ) * ‖y - x‖
  -- The Hessian difference is self-adjoint because both endpoint Hessians are self-adjoint.
  have hΔ_symm : Δ.IsSymmetric := by
    dsimp [Δ]
    exact
      ((hessian_isSelfAdjoint_of_contDiffAt f y (hf.contDiffAt hy)).isSymmetric).sub
        ((hessian_isSelfAdjoint_of_contDiffAt f x (hf.contDiffAt hx)).isSymmetric)
  have hΔ_norm : ‖Δ‖ ≤ s := by
    dsimp [Δ, s]
    simpa [norm_sub_rev, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hf.norm_sub_le hy hx
  -- Convert the operator-norm bound into quadratic-form bounds along every direction.
  have hquad_bound (u : E) :
      |inner ℝ (Δ u) u| ≤ s * ‖u‖ ^ (2 : ℕ) := by
    calc
      |inner ℝ (Δ u) u| ≤ ‖Δ u‖ * ‖u‖ := by
        simpa [real_inner_comm] using abs_real_inner_le_norm (Δ u) u
      _ ≤ (‖Δ‖ * ‖u‖) * ‖u‖ := by
        gcongr
        exact Δ.le_opNorm u
      _ = ‖Δ‖ * ‖u‖ ^ (2 : ℕ) := by
        ring
      _ ≤ s * ‖u‖ ^ (2 : ℕ) := by
        gcongr
  have hsI_symm : (s • (1 : E →L[ℝ] E)).IsSymmetric := by
    intro u v
    simp [real_inner_smul_left, real_inner_smul_right]
  have hupper_nonneg : 0 ≤ s • (1 : E →L[ℝ] E) - Δ := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
    constructor
    · exact hsI_symm.sub hΔ_symm
    · intro u
      have hu : inner ℝ (Δ u) u ≤ s * ‖u‖ ^ (2 : ℕ) := (abs_le.mp (hquad_bound u)).2
      have hrewrite :
          inner ℝ ((s • (1 : E →L[ℝ] E) - Δ) u) u =
            s * ‖u‖ ^ (2 : ℕ) - inner ℝ (Δ u) u := by
        simp [real_inner_smul_left, inner_sub_left]
      rw [hrewrite]
      linarith
  have hlower_nonneg : 0 ≤ s • (1 : E →L[ℝ] E) + Δ := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
    constructor
    · exact hsI_symm.add hΔ_symm
    · intro u
      have hu : -(s * ‖u‖ ^ (2 : ℕ)) ≤ inner ℝ (Δ u) u := (abs_le.mp (hquad_bound u)).1
      have hrewrite :
          inner ℝ ((s • (1 : E →L[ℝ] E) + Δ) u) u =
            s * ‖u‖ ^ (2 : ℕ) + inner ℝ (Δ u) u := by
        simp [real_inner_smul_left, inner_add_left]
      rw [hrewrite]
      linarith
  constructor
  · -- The lower Loewner bound is the positivity of `s I + Δ` rewritten in order form.
    rw [ContinuousLinearMap.le_def]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp <| by
      dsimp [Δ, s] at hlower_nonneg ⊢
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlower_nonneg
  · -- The upper Loewner bound is the positivity of `s I - Δ` rewritten in order form.
    rw [ContinuousLinearMap.le_def]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp <| by
      dsimp [Δ, s] at hupper_nonneg ⊢
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hupper_nonneg

/-- Helper for Theorem 4.1.1: on a nontrivial finite-dimensional real inner-product space,
positivity of `A + c I` forces every spectral value of a self-adjoint operator `A` to be at least
`-c`. -/
theorem neg_le_sInf_spectrum_of_nonnegative_shift
    [Nontrivial E]
    {A : E →L[ℝ] E} {c : ℝ}
    (hA_self : IsSelfAdjoint A)
    (hshift : 0 ≤ A + c • (1 : E →L[ℝ] E)) :
    -c ≤ sInf (spectrum ℝ A) := by
  let μ : ℝ :=
    ⨅ x : { x : E // x ≠ 0 },
      inner ℝ ((A : E →ₗ[ℝ] E) (x : E)) (x : E) / ‖(x : E)‖ ^ (2 : ℕ)
  -- A self-adjoint operator in finite dimension has a Rayleigh-minimizing eigenvalue.
  have hμ : Module.End.HasEigenvalue (A : E →ₗ[ℝ] E) μ := by
    simpa [μ] using hA_self.isSymmetric.hasEigenvalue_iInf_of_finiteDimensional
  have hs_nonempty : (spectrum ℝ A).Nonempty := by
    exact ⟨μ, by simpa [ContinuousLinearMap.spectrum_eq] using hμ.mem_spectrum⟩
  refine le_csInf hs_nonempty ?_
  intro x hx
  have hxlin : x ∈ spectrum ℝ (A : E →ₗ[ℝ] E) := by
    simpa [ContinuousLinearMap.spectrum_eq] using hx
  obtain ⟨v, hv_mem, hv_ne⟩ :=
    (Module.End.HasEigenvalue.of_mem_spectrum hxlin).exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hv_mem
  have hshift_pos : (A + c • (1 : E →L[ℝ] E)).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp hshift
  -- Evaluate the shifted positivity inequality on an eigenvector for `x`.
  have hinner_nonneg : 0 ≤ inner ℝ ((A + c • (1 : E →L[ℝ] E)) v) v :=
    hshift_pos.inner_nonneg_left v
  have hv_norm_sq_pos : 0 < ‖v‖ ^ (2 : ℕ) := by
    positivity
  have hAv : A v = x • v := hv_mem
  have hrewrite :
      inner ℝ ((A + c • (1 : E →L[ℝ] E)) v) v =
        (x + c) * ‖v‖ ^ (2 : ℕ) := by
    calc
      inner ℝ ((A + c • (1 : E →L[ℝ] E)) v) v
          = inner ℝ (A v) v + inner ℝ ((c • (1 : E →L[ℝ] E)) v) v := by
              simp [inner_add_left]
      _ = inner ℝ (x • v) v + inner ℝ (c • v) v := by
            simp [hAv]
      _ = x * ‖v‖ ^ (2 : ℕ) + c * ‖v‖ ^ (2 : ℕ) := by
            simp [inner_smul_left, inner_self_eq_norm_sq_to_K]
      _ = (x + c) * ‖v‖ ^ (2 : ℕ) := by
            ring
  rw [hrewrite] at hinner_nonneg
  have hx_add_nonneg : 0 ≤ x + c := by
    exact nonneg_of_mul_nonneg_left hinner_nonneg hv_norm_sq_pos
  linarith

/-- Along a cubic-regularization method in a Hessian-Lipschitz region, the least-Hessian-
eigenvalue lower bound used in Lemma 4.1.6 is derived owner data. It follows from the accepted
cubic-model minimizer together with the regularized-Hessian positivity theorem, so later
stationarity results do not keep it as a primitive public hypothesis. -/
theorem cubicRegularization_hessianLeastEigenvalue_lower_bound
    [HessianLipschitzOn L 𝓕 f]
    (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    (i : ℕ) :
    -(((method.regularization i / 2) + (L : ℝ)) * r[method.regularization i](method i)) ≤
      λ_min(∇²f(method (i + 1))) := by
  -- Route correction: use the source-faithful operator route, not a negative-curvature witness.
  by_cases hE : Subsingleton E
  · letI : Subsingleton E := hE
    have hhess0 : hessian f (method (i + 1)) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have hcoeff_nonneg :
        0 ≤ ((method.regularization i / 2) + (L : ℝ)) * r[method.regularization i](method i) := by
      have hr_nonneg : 0 ≤ r[method.regularization i](method i) := by
        simpa [cubicRegularizationResidual] using
          norm_nonneg (method i - stepMap (method.regularization i) (method i))
      nlinarith [method.regularization_pos i, show 0 ≤ (L : ℝ) by exact_mod_cast L.2, hr_nonneg]
    -- In the trivial space the Hessian vanishes, so the claim reduces to a scalar nonpositivity.
    rw [show λ_min(∇²f(method (i + 1))) = 0 by simp [hessianLeastEigenvalue, hhess0]]
    linarith
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let hf : HessianLipschitzOn L 𝓕 f := inferInstance
    let x := method i
    let y := method (i + 1)
    let r : ℝ := r[method.regularization i](method i)
    let s : ℝ := (L : ℝ) * r
    have hy_eq : y = stepMap (method.regularization i) x := by
      dsimp [x, y]
      rw [method.x_succ i, method.step_apply_eq_stepMap i (method i)]
    have hy_mem : y ∈ 𝓕 := by
      dsimp [y]
      exact hmem (i + 1)
    -- Start from the regularized-Hessian positivity at the accepted cubic minimizer.
    have hreg_pos :
        (hessian f x + ((method.regularization i / 2) * r) • (1 : E →L[ℝ] E)).IsPositive := by
      dsimp [x, r]
      simpa [hy_eq] using
        regularizedHessian_isPositive_of_isMinOn_cubicRegularizationQuadraticApproximation
          (method.regularization_pos i).le
          (hf.contDiffAt (hmem i))
          (method.stepMap_isMinOn i)
    have hreg_nonneg :
        0 ≤ hessian f x + ((method.regularization i / 2) * r) • (1 : E →L[ℝ] E) :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hreg_pos
    -- Transport the Hessian lower bound from `x_i` to `x_{i+1}` through the local Loewner estimate.
    have hloew_lower :
        hessian f (method i) - ((L : ℝ) * r[method.regularization i](method i)) • (1 : E →L[ℝ] E) ≤
          hessian f (method (i + 1)) := by
      simpa [y, hy_eq, cubicRegularizationResidual, method.x_succ i, norm_sub_rev] using
        (hf.hessian_loewner_bounds (hmem i) hy_mem).1
    have hdelta_nonneg :
        0 ≤ (hessian f y + s • (1 : E →L[ℝ] E)) - hessian f x := by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      dsimp [x, y, r, s] at hloew_lower ⊢
      simpa [ContinuousLinearMap.le_def, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hloew_lower
    have hdelta_pos :
        ((hessian f y + s • (1 : E →L[ℝ] E)) - hessian f x).IsPositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp hdelta_nonneg
    have hshift_pos :
        (hessian f x + ((method.regularization i / 2) * r) • (1 : E →L[ℝ] E) +
            ((hessian f y + s • (1 : E →L[ℝ] E)) - hessian f x)).IsPositive :=
      hreg_pos.add hdelta_pos
    have hshift_nonneg :
        0 ≤ hessian f y + ((((method.regularization i / 2) * r) + s) • (1 : E →L[ℝ] E)) := by
      exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr <| by
        simpa [sub_eq_add_neg, add_smul, add_assoc, add_left_comm, add_comm] using hshift_pos
    -- Convert positivity of the shifted Hessian into the displayed lower bound on `λ_min`.
    have hy_self : IsSelfAdjoint (hessian f y) :=
      hessian_isSelfAdjoint_of_contDiffAt f y (hf.contDiffAt hy_mem)
    have hspec :
        -((((method.regularization i / 2) * r) + s)) ≤ λ_min(∇²f y) := by
      simpa [hessianLeastEigenvalue] using
        neg_le_sInf_spectrum_of_nonnegative_shift (E := E) hy_self hshift_nonneg
    have hscalar :
        (((method.regularization i / 2) + (L : ℝ)) * r) =
          (((method.regularization i / 2) * r) + s) := by
      dsimp [s]
      ring
    have htarget :
        -(((method.regularization i / 2) + (L : ℝ)) * r) ≤ λ_min(∇²f y) := by
      nlinarith [hspec, hscalar]
    simpa [y] using htarget

/-- Along a cubic-regularization method, the canonical owner-level bridge
`μ_{Mᵢ}(xᵢ₊₁) ≤ ‖xᵢ₊₁ - xᵢ‖` from `Lemma_4_1_6`, together with the internally derived
least-Hessian-eigenvalue lower bound and `Mᵢ ≤ 2L`, yields the source-facing comparison
`μ_L(xᵢ₊₁) ≤ (4 / 3) r_{Mᵢ}(xᵢ)`. -/
theorem cubicRegularization_localOptimalityMeasure_succ_le_four_thirds_mul_residual
    [HessianLipschitzOn L 𝓕 f]
    (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    (i : ℕ) :
    μ[(L : ℝ)](method (i + 1)) ≤ (4 / 3 : ℝ) * r[method.regularization i](method i) := by
  let hf : HessianLipschitzOn L 𝓕 f := inferInstance
  -- First apply the owner-level bridge at the accepted cubic minimizer.
  have hy_mem : stepMap (method.regularization i) (method i) ∈ 𝓕 := by
    simpa [method.x_succ i, method.step_apply_eq_stepMap i (method i)] using hmem (i + 1)
  have hlambda :
      -((method.regularization i / 2 + (L : ℝ)) * ‖method i - stepMap (method.regularization i) (method i)‖) ≤
        λ_min(∇²f(stepMap (method.regularization i) (method i))) := by
    simpa [cubicRegularizationResidual, method.x_succ i, method.step_apply_eq_stepMap i (method i),
      norm_sub_rev] using
      (cubicRegularization_hessianLeastEigenvalue_lower_bound
        (method := method) (𝓕 := 𝓕) hmem i)
  have hμM_raw :
      μ[method.regularization i](stepMap (method.regularization i) (method i)) ≤
        ‖stepMap (method.regularization i) (method i) - method i‖ :=
    cubicRegularizationLocalOptimalityMeasure_le_norm_sub_of_isMinOn
      (f := f)
      (L := L)
      (𝓕 := 𝓕)
      (M := method.regularization i)
      (x := method i)
      (y := stepMap (method.regularization i) (method i))
      hf
      (method.regularization_pos i)
      (method.stepMap_isMinOn i)
      (hmem i)
      hy_mem
      (by simpa [norm_sub_rev] using hlambda)
  have hμM :
      μ[method.regularization i](method (i + 1)) ≤ r[method.regularization i](method i) := by
    simpa [cubicRegularizationResidual, method.x_succ i, method.step_apply_eq_stepMap i (method i),
      norm_sub_rev]
      using hμM_raw
  have hL_le : method.regularization i ≤ 2 * (L : ℝ) :=
    method.regularization_le_two_mul_L i
  -- Then transport from `μ[M_i]` to `μ[L]` using the parameter comparison lemma.
  calc
    μ[(L : ℝ)](method (i + 1))
        ≤ (4 / 3 : ℝ) * μ[method.regularization i](method (i + 1)) :=
          cubicRegularizationLocalOptimalityMeasure_at_L_le_four_thirds_mul
            (f := f)
            (L := L)
            (x := method (i + 1))
            (M := method.regularization i)
            (method.regularization_pos i)
            hL_le
    _ ≤ (4 / 3 : ℝ) * r[method.regularization i](method i) := by
          exact mul_le_mul_of_nonneg_left hμM (by norm_num)

-- Proof sketch: first use the owner-level decrease theorem
-- `method.objective_sub_succ_ge_residual_cube i` to obtain
-- `f(xᵢ) - f(xᵢ₊₁) ≥ (Mᵢ / 12) r_{Mᵢ}(xᵢ)^3`. Then apply
-- `cubicRegularization_residual_cube_summable_and_tsum_le` to get summability of
-- `r_{Mᵢ}(xᵢ)^3`, hence `r_{Mᵢ}(xᵢ) → 0` because the residuals are norms. Use
-- `cubicRegularization_localOptimalityMeasure_succ_le_four_thirds_mul_residual` to derive the
-- source-facing estimate `μ_L(xᵢ₊₁) ≤ (4 / 3) r_{Mᵢ}(xᵢ)`, then conclude by the squeeze theorem
-- and the nonnegativity built into `cubicRegularizationLocalOptimalityMeasure` that
-- `μ_L(xᵢ) → 0`.
/-- Theorem 4.1.1 (2): under the cubic-regularization method owner and the canonical
`HessianLipschitzOn` bridge data from `Lemma_4_1_6`, the stationarity sequence `μ_L(xᵢ)`
converges to `0`; both the residual-cube decrease estimate and the spectral lower bound needed by
the local-optimality bridge are derived from the owner data rather than assumed separately. -/
theorem cubicRegularization_localOptimalityMeasure_tendsto_zero
    [HessianLipschitzOn L 𝓕 f]
    (hf_lower : ∀ z : E, fStar ≤ f z)
    (hmem : ∀ i : ℕ, method i ∈ 𝓕) :
    Tendsto (fun i ↦ μ[(L : ℝ)](method i)) atTop (nhds 0) := by
  have hres :=
    cubicRegularization_residual_cube_summable_and_tsum_le
      (method := method) (fStar := fStar) hf_lower
  have hres_nonneg : ∀ i : ℕ, 0 ≤ r[method.regularization i](method i) := by
    intro i
    simpa [cubicRegularizationResidual] using
      norm_nonneg (method i - stepMap (method.regularization i) (method i))
  -- Summability of the residual cubes implies that the residuals themselves converge to zero.
  have hres_tendsto : Tendsto (fun i ↦ r[method.regularization i](method i)) atTop (nhds 0) := by
    let g : ℕ → ℝ := fun i ↦ (r[method.regularization i](method i) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)
    have hg_tendsto0pow : Tendsto g atTop (nhds ((0 : ℝ) ^ (1 / 3 : ℝ))) := by
      have hpow_tendsto :
          Tendsto (fun i ↦ r[method.regularization i](method i) ^ (3 : ℕ)) atTop (nhds 0) :=
        hres.1.tendsto_atTop_zero
      simpa [g] using
        hpow_tendsto.rpow tendsto_const_nhds (Or.inr (by norm_num : 0 < (1 / 3 : ℝ)))
    have hg_tendsto : Tendsto g atTop (nhds 0) := by
      simpa using hg_tendsto0pow
    have hg_eq : g = fun i ↦ r[method.regularization i](method i) := by
      have hroot (x : ℝ) (hx : 0 ≤ x) :
          Real.rpow (Real.rpow x (3 : ℝ)) (1 / 3 : ℝ) = x := by
        change (x ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = x
        rw [← Real.rpow_mul hx]
        norm_num [Real.rpow_one]
      funext i
      simpa [g, Real.rpow_natCast] using hroot (r[method.regularization i](method i)) (hres_nonneg i)
    simpa [hg_eq] using hg_tendsto
  -- The one-step stationarity estimate is squeezed between `0` and a vanishing multiple of the residual.
  have hsucc_tendsto : Tendsto (fun i ↦ μ[(L : ℝ)](method (i + 1))) atTop (nhds 0) := by
    have hbound :
        ∀ i : ℕ, μ[(L : ℝ)](method (i + 1)) ≤ (4 / 3 : ℝ) * r[method.regularization i](method i) := by
      intro i
      exact cubicRegularization_localOptimalityMeasure_succ_le_four_thirds_mul_residual
        (method := method) (𝓕 := 𝓕) hmem i
    have hμ_nonneg : ∀ i : ℕ, 0 ≤ μ[(L : ℝ)](method (i + 1)) := by
      intro i
      exact le_trans (Real.sqrt_nonneg _) <|
        sqrt_scaledGradientNorm_le_cubicRegularizationLocalOptimalityMeasure
          f (L : ℝ) (L : ℝ) (method (i + 1))
    have hscaled_tendsto :
        Tendsto (fun i ↦ (4 / 3 : ℝ) * r[method.regularization i](method i)) atTop (nhds 0) := by
      simpa using hres_tendsto.const_mul (4 / 3 : ℝ)
    exact squeeze_zero hμ_nonneg hbound hscaled_tendsto
  -- Shifting the index back by one recovers the original stationarity sequence.
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hsucc_tendsto

-- Proof sketch: let
-- `m_k = min_{1 ≤ i ≤ k} μ_L(xᵢ) =
--   (Finset.Icc 1 k).inf' (Finset.nonempty_Icc.2 hk) (fun i ↦ μ_L(xᵢ))`.
-- For each `i = 1, ..., k`, apply
-- `cubicRegularization_localOptimalityMeasure_succ_le_four_thirds_mul_residual` at `i - 1` to
-- get `r_{M_{i-1}}(x_{i-1}) ≥ (3 / 4) m_k`, so
-- `k * (27 / 64) * m_k^3 ≤ ∑_{j=0}^{k-1} r_{Mⱼ}(xⱼ)^3`. Then apply
-- `cubicRegularization_residual_cube_summable_and_tsum_le` to bound the right-hand side by
-- `(12 / L₀) (f(x₀) - f*)` and solve the resulting scalar inequality for `m_k`.
/-- Theorem 4.1.1 (3): under the same cubic-regularization method and Hessian-Lipschitz bridge
data, every finite minimum `min_{1 ≤ i ≤ k} μ_L(xᵢ)` admits the explicit `k^{-1/3}` estimate
once the residual comparison from `Lemma_4_1_6` has been transported to the trajectory. The
needed residual-cube decrease estimate and spectral lower bound are both derived from the owner
data rather than assumed separately. -/
theorem cubicRegularization_minimum_localOptimalityMeasure_le_explicit_bound
    [HessianLipschitzOn L 𝓕 f]
    (hf_lower : ∀ z : E, fStar ≤ f z)
    (hmem : ∀ i : ℕ, method i ∈ 𝓕)
    {k : ℕ} (hk : 1 ≤ k) :
    (Finset.Icc 1 k).inf' (Finset.nonempty_Icc.2 hk)
        (fun i ↦ μ[(L : ℝ)](method i)) ≤
      (8 / 3 : ℝ) *
        Real.rpow
          ((3 * (f (method 0) - fStar)) / (2 * (k : ℝ) * L0))
          (1 / 3 : ℝ) := by
  let m_k : ℝ :=
    (Finset.Icc 1 k).inf' (Finset.nonempty_Icc.2 hk) (fun i ↦ μ[(L : ℝ)](method i))
  have hμ_nonneg : ∀ i : ℕ, 0 ≤ μ[(L : ℝ)](method i) := by
    intro i
    exact le_trans (Real.sqrt_nonneg _) <|
      sqrt_scaledGradientNorm_le_cubicRegularizationLocalOptimalityMeasure
        f (L : ℝ) (L : ℝ) (method i)
  have hm_nonneg : 0 ≤ m_k := by
    refine Finset.le_inf' (s := Finset.Icc 1 k)
      (H := Finset.nonempty_Icc.2 hk)
      (f := fun i : ℕ ↦ μ[(L : ℝ)](method i)) ?_
    intro i hi
    exact hμ_nonneg i
  -- Every residual on the first `k` steps dominates `(3 / 4) * m_k`.
  have hmk_le (j : ℕ) (hj : j ∈ Finset.range k) : m_k ≤ μ[(L : ℝ)](method (j + 1)) := by
    have hjIcc : j + 1 ∈ Finset.Icc 1 k := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.succ_le_succ (Nat.zero_le j), Nat.succ_le_of_lt (Finset.mem_range.mp hj)⟩
    exact Finset.inf'_le (fun i ↦ μ[(L : ℝ)](method i)) hjIcc
  have hres_lower (j : ℕ) (hj : j ∈ Finset.range k) :
      ((3 / 4 : ℝ) * m_k) ^ (3 : ℕ) ≤ r[method.regularization j](method j) ^ (3 : ℕ) := by
    have hstep :=
      cubicRegularization_localOptimalityMeasure_succ_le_four_thirds_mul_residual
        (method := method) (𝓕 := 𝓕) hmem j
    have hbase : (3 / 4 : ℝ) * m_k ≤ r[method.regularization j](method j) := by
      nlinarith [hmk_le j hj, hstep]
    have hbase_nonneg : 0 ≤ (3 / 4 : ℝ) * m_k := by
      positivity
    exact pow_le_pow_left₀ hbase_nonneg hbase 3
  have hsum_lower :
      (k : ℝ) * (((3 / 4 : ℝ) * m_k) ^ (3 : ℕ)) ≤
        ∑ j ∈ Finset.range k, r[method.regularization j](method j) ^ (3 : ℕ) := by
    calc
      (k : ℝ) * (((3 / 4 : ℝ) * m_k) ^ (3 : ℕ))
          = ∑ j ∈ Finset.range k, (((3 / 4 : ℝ) * m_k) ^ (3 : ℕ)) := by
              simp
      _ ≤ ∑ j ∈ Finset.range k, r[method.regularization j](method j) ^ (3 : ℕ) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact hres_lower j hj
  -- Re-run the textbook telescoping argument on the first `k` iterations.
  have hsum_upper :
      ∑ j ∈ Finset.range k, r[method.regularization j](method j) ^ (3 : ℕ) ≤
        (12 / L0) * (f (method 0) - fStar) := by
    have hpointwise :
        ∀ j ∈ Finset.range k,
          r[method.regularization j](method j) ^ (3 : ℕ) ≤
            (12 / L0) * (f (method j) - f (method (j + 1))) := by
      intro j hj
      have hratio : L0 / 12 ≤ method.regularization j / 12 := by
        nlinarith [method.L0_le_regularization j]
      have hscaled :
          (L0 / 12) * (r[method.regularization j](method j) ^ (3 : ℕ)) ≤
            (method.regularization j / 12) * (r[method.regularization j](method j) ^ (3 : ℕ)) := by
        have hres_nonneg : 0 ≤ r[method.regularization j](method j) := by
          simpa [cubicRegularizationResidual] using
            norm_nonneg (method j - stepMap (method.regularization j) (method j))
        have hr_cube_nonneg :
            0 ≤ r[method.regularization j](method j) ^ (3 : ℕ) := by
          exact pow_nonneg hres_nonneg _
        exact mul_le_mul_of_nonneg_right hratio hr_cube_nonneg
      have hstep := method.objective_sub_succ_ge_residual_cube j
      have hmain :
          (L0 / 12) * (r[method.regularization j](method j) ^ (3 : ℕ)) ≤
            f (method j) - f (method (j + 1)) :=
        hscaled.trans hstep
      have hfactor_pos : 0 < 12 / L0 := by
        exact div_pos (by norm_num) method.L0_pos
      calc
        r[method.regularization j](method j) ^ (3 : ℕ)
            = (12 / L0) *
                ((L0 / 12) * (r[method.regularization j](method j) ^ (3 : ℕ))) := by
                  field_simp [method.L0_pos.ne']
        _ ≤ (12 / L0) * (f (method j) - f (method (j + 1))) := by
              exact mul_le_mul_of_nonneg_left hmain hfactor_pos.le
    have htel :
        ∑ j ∈ Finset.range k, (f (method j) - f (method (j + 1))) =
          f (method 0) - f (method k) := by
      simpa using (Finset.sum_range_sub' (fun j ↦ f (method j)) k)
    have hterminal : f (method 0) - f (method k) ≤ f (method 0) - fStar := by
      simpa using sub_le_sub_left (hf_lower (method k)) (f (method 0))
    have hfactor_nonneg : 0 ≤ 12 / L0 := by
      exact le_of_lt (div_pos (by norm_num) method.L0_pos)
    calc
      ∑ j ∈ Finset.range k, r[method.regularization j](method j) ^ (3 : ℕ)
          ≤ ∑ j ∈ Finset.range k, (12 / L0) * (f (method j) - f (method (j + 1))) :=
            Finset.sum_le_sum hpointwise
      _ = (12 / L0) * ∑ j ∈ Finset.range k, (f (method j) - f (method (j + 1))) := by
            rw [Finset.mul_sum]
      _ = (12 / L0) * (f (method 0) - f (method k)) := by
            rw [htel]
      _ ≤ (12 / L0) * (f (method 0) - fStar) := by
            exact mul_le_mul_of_nonneg_left hterminal hfactor_nonneg
  have hA_nonneg : 0 ≤ f (method 0) - fStar := by
    nlinarith [hf_lower (method 0)]
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk
  -- Solve the resulting scalar cubic inequality for the window minimum `m_k`.
  have hbound :
      m_k ≤ (8 / 3 : ℝ) *
        Real.rpow ((3 * (f (method 0) - fStar)) / (2 * (k : ℝ) * L0)) (1 / 3 : ℝ) := by
    let B : ℝ := (3 * (f (method 0) - fStar)) / (2 * (k : ℝ) * L0)
    have hB_nonneg : 0 ≤ B := by
      have hden_pos : 0 < 2 * (k : ℝ) * L0 := by
        nlinarith [hk_pos, method.L0_pos]
      dsimp [B]
      exact div_nonneg (by nlinarith [hf_lower (method 0)]) hden_pos.le
    have hrhs_nonneg : 0 ≤ (8 / 3 : ℝ) * Real.rpow B (1 / 3 : ℝ) := by
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg hB_nonneg _)
    apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hrhs_nonneg
    have hrhs_cube :
        (((8 / 3 : ℝ) * Real.rpow B (1 / 3 : ℝ)) ^ (3 : ℕ)) = (512 / 27 : ℝ) * B := by
      rw [mul_pow]
      have hpow : (Real.rpow B (1 / 3 : ℝ)) ^ (3 : ℕ) = B := by
        change (B ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = B
        rw [← Real.rpow_natCast, ← Real.rpow_mul hB_nonneg]
        norm_num [Real.rpow_one]
      rw [hpow]
      norm_num
    rw [hrhs_cube]
    have hcube :
        m_k ^ (3 : ℕ) ≤
          ((768 / L0) * (f (method 0) - fStar)) / ((27 : ℝ) * (k : ℝ)) := by
      have hineq' :
          (27 : ℝ) * (k : ℝ) * m_k ^ (3 : ℕ) ≤
            (768 / L0) * (f (method 0) - fStar) := by
        have hsum_le := le_trans hsum_lower hsum_upper
        have hsum_le' := mul_le_mul_of_nonneg_left hsum_le (show 0 ≤ (64 : ℝ) by norm_num)
        ring_nf at hsum_le'
        convert hsum_le' using 1 <;> ring_nf
      have hk27_pos : 0 < (27 : ℝ) * (k : ℝ) := by
        positivity
      exact (le_div_iff₀ hk27_pos).2 <| by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hineq'
    have htarget :
        ((768 / L0) * (f (method 0) - fStar)) / ((27 : ℝ) * (k : ℝ)) =
          (512 / 27 : ℝ) * B := by
      dsimp [B]
      field_simp [method.L0_pos.ne', hk_pos.ne']
      ring
    exact htarget ▸ hcube
  simpa [m_k] using hbound

end CubicRegularizationStationarityRate

end
