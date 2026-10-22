/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: smooth-convex optimal-method estimating-sequence bounds on a real Hilbert
space.

Owner declarations sampled before refining this file:
* `OptimalMethodRecurrence` in `Algorithm_2_2` owns the recurrence-side data `αₖ`, `γₖ`, `vₖ`,
  together with the canonical weight `λₖ = method.weight k`;
* `GeneralOptimalMethodScheme` in `Algorithm_2_2` is the chapter owner once the step-`(c)`
  descent inequality is added; this is the minimal owner that supports the iterate-versus-
  estimating-sequence control needed for the public norm bounds below;
* the intrinsic smooth-convex owner layer
  `ConvexOn ℝ Set.univ f`, `∀ x, HasGradientAt f (∇ f x) x`, and `LipschitzWith L (∇ f)` is the
  chapter's canonical Hilbert-space abstraction, used directly in `Theorem_2_16`;
* `ConvexC1SeminormSmooth.gradient_lipschitz` in `Theorem_2_5` is only the finite-dimensional
  bridge from the Chapter 2 wrapper `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` to that intrinsic owner
  layer.

Best owner abstraction:
* source-facing: the textbook weighted gradient average `gₖ`, canonically attached to the owner
  recurrence and used in the source bounds for `k ≥ 1`;
* core/canonical: the recurrence owner `method : OptimalMethodRecurrence ...` for `gₖ` itself,
  and the scheme owner `method : GeneralOptimalMethodScheme ...` for the norm bounds, together
  with the intrinsic whole-space smooth-convex hypotheses `ConvexOn ℝ Set.univ f`,
  `∀ x, HasGradientAt f (∇ f x) x`, and `LipschitzWith L (∇ f)`;
* bridge/view: the owner curvature/center expression for `gₖ` and the normalization identity for
  its finite-sum coefficients.

Primitive data:
* whole-space convexity of `f`;
* ambient gradient witnesses `HasGradientAt f (∇ f x) x`;
* the global Lipschitz bound for `∇ f`;
* a minimizer `xStar` with `hxStar : IsMinOn f Set.univ xStar`;
* the owner recurrence `method`.

Derived API:
* `method.gradientAverage k`, with source-facing notation `g_[method; k]`, given by the textbook
  weighted finite sum; the source bounds only use it for `k ≥ 1`;
* `gradientAverage_normalization`, the textbook normalization identity for the finite-sum
  coefficients of `gₖ`;
* `gradientAverage_eq_weight_mul_initial_curvature`, the bridge from the source-facing weighted
  sum to the owner center/weight expression;
* the center and gradient-average norm bounds from Theorem 2.22, which use the scheme-level
  iterate control and therefore live on `GeneralOptimalMethodScheme`. -/

namespace OptimalMethodRecurrence

variable {L : ℝ} {f : E → ℝ} {x0 : E} {gamma0 : ℝ}

section

variable (method : OptimalMethodRecurrence f (L : ℝ) 0 x0 gamma0)

/-- Helper for Theorem 2.22: the scalar recurrence `estimatingWeight method.alpha` is exactly the
owner weight sequence `method.weight`. -/
theorem estimatingWeight_eq_weight
    (k : ℕ) :
    estimatingWeight method.alpha k = method.weight k := by
  -- Both sides satisfy the same recursion `λ₀ = 1`, `λₖ₊₁ = (1 - αₖ) λₖ`.
  induction k with
  | zero =>
      simp [estimatingWeight]
  | succ k ih =>
      rw [estimatingWeight, method.weight_succ, ih]

/-- Helper for Theorem 2.22: every owner weight stays at most `1`. -/
theorem weight_le_one
    (k : ℕ) :
    method.weight k ≤ 1 := by
  -- The owner weight starts at `1` and each successor multiplies by a factor in `(0, 1)`.
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [method.weight_succ]
      have hfactor_nonneg : 0 ≤ 1 - method.alpha k := by
        linarith [(method.alpha_mem_Ioo k).2]
      have hfactor_le_one : 1 - method.alpha k ≤ 1 := by
        linarith [(method.alpha_mem_Ioo k).1]
      have hweight_nonneg : 0 ≤ method.weight k := (method.weight_pos k).le
      nlinarith

/-- Helper for Theorem 2.22: every positive-stage owner weight is strictly below `1`. -/
theorem weight_lt_one_of_one_le
    {k : ℕ} (hk : 1 ≤ k) :
    method.weight k < 1 := by
  -- Once `k ≥ 1`, the last update contributes a factor `1 - α_{k-1}` strictly smaller than `1`.
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨j, rfl⟩
  rw [method.weight_succ]
  have hfactor_nonneg : 0 ≤ 1 - method.alpha j := by
    linarith [(method.alpha_mem_Ioo j).2]
  have hfactor_lt_one : 1 - method.alpha j < 1 := by
    linarith [(method.alpha_mem_Ioo j).1]
  have hweight_nonneg : 0 ≤ method.weight j := (method.weight_pos j).le
  have hweight_le_one : method.weight j ≤ 1 := method.weight_le_one j
  nlinarith

/-- The weighted gradient average `gₖ` from Theorem 2.22. For `k ≥ 1` this is the textbook
weighted finite sum, while `g₀` is fixed to `0` explicitly so the owner remains total without
using division-by-zero conventions. The exported source-facing notation is `g_[method; k]`. -/
def gradientAverage
    : ℕ → E
  | 0 => 0
  | k + 1 => method.weightedAverage (fun i ↦ ∇ f (method.y i)) (k + 1)

namespace OptimalMethodGradientAverage

scoped notation:max "g_[" method ";" k "]" =>
  OptimalMethodRecurrence.gradientAverage method k

end OptimalMethodGradientAverage

open scoped OptimalMethodRecurrence.OptimalMethodGradientAverage

@[simp] theorem gradientAverage_zero :
    g_[method; 0] = 0 :=
  rfl

@[simp] theorem gradientAverage_succ
    (k : ℕ) :
    g_[method; k + 1] =
      method.weightedAverage (fun i ↦ ∇ f (method.y i)) (k + 1) :=
  rfl

/-- Helper for Theorem 2.22: in the smooth-convex specialization `μ = 0`, the owner center update
has the source form `v_{k+1} = v_k - (α_k / γ_{k+1}) ∇ f(y_k)`. -/
theorem v_succ_eq_sub_weighted_gradient
    (k : ℕ) :
    method.v (k + 1) =
      method.v k - (method.alpha k / method.gamma (k + 1)) • ∇ f (method.y k) := by
  -- Route correction: freeze the `μ = 0` one-step update once so the telescoping proof does not
  -- repeatedly normalize the same scalar/module expression.
  have hgamma_next :
      method.gamma (k + 1) = method.weight (k + 1) * gamma0 := by
    simpa using method.gamma_sub_mu_eq_weight_mul_initial_gap (k + 1)
  have hgamma_next_ne : method.gamma (k + 1) ≠ 0 := by
    rw [hgamma_next]
    exact mul_ne_zero (method.weight_pos (k + 1)).ne' method.gamma0_pos.ne'
  calc
    method.v (k + 1)
        = (1 / method.gamma (k + 1)) •
            (((1 - method.alpha k) * method.gamma k) • method.v k -
              method.alpha k • ∇ f (method.y k)) := by
              simpa using method.v_succ k
    _ = (1 / method.gamma (k + 1)) •
          (method.gamma (k + 1) • method.v k -
            method.alpha k • ∇ f (method.y k)) := by
          rw [method.gamma_succ k]
          ring_nf
    _ = (1 / method.gamma (k + 1)) • (method.gamma (k + 1) • method.v k) -
          (1 / method.gamma (k + 1)) •
            (method.alpha k • ∇ f (method.y k)) := by
          rw [smul_sub]
    _ = method.v k - (method.alpha k / method.gamma (k + 1)) •
          ∇ f (method.y k) := by
          rw [smul_smul, one_div, inv_mul_cancel₀ hgamma_next_ne, one_smul]
          rw [smul_smul]
          congr 1
          field_simp [hgamma_next_ne]

/-- Helper for Theorem 2.22: the weighted gradient sum is the initial-curvature multiple of the
center displacement `x₀ - vₖ`. -/
theorem weighted_gradient_sum_eq_initial_curvature_sub_center
    (k : ℕ) :
    Finset.sum (Finset.range k) (fun i ↦
      (method.alpha i / method.weight (i + 1)) • ∇ f (method.y i)) =
      gamma0 • (method 0 - method.v k) := by
  -- Telescope the finite sum against the one-step center update from
  -- `v_succ_eq_sub_weighted_gradient`.
  induction k with
  | zero =>
      simp [method.x_zero, method.v_zero]
  | succ k ih =>
      have hgamma_next :
          method.gamma (k + 1) = method.weight (k + 1) * gamma0 := by
        simpa using method.gamma_sub_mu_eq_weight_mul_initial_gap (k + 1)
      rw [Finset.sum_range_succ, ih]
      calc
        gamma0 • (method 0 - method.v k) +
            (method.alpha k / method.weight (k + 1)) • ∇ f (method.y k)
            =
              gamma0 • (method 0 - method.v k) +
                gamma0 •
                  ((method.alpha k / method.gamma (k + 1)) •
                    ∇ f (method.y k)) := by
                rw [smul_smul]
                congr 1
                rw [hgamma_next, div_eq_mul_inv, div_eq_mul_inv]
                field_simp [method.gamma0_pos.ne']
        _ = gamma0 •
              ((method 0 - method.v k) +
                (method.alpha k / method.gamma (k + 1)) •
                  ∇ f (method.y k)) := by
              simp [smul_add]
        _ = gamma0 •
              (method 0 -
                (method.v k - (method.alpha k / method.gamma (k + 1)) •
                  ∇ f (method.y k))) := by
              congr 1
              abel
        _ = gamma0 • (method 0 - method.v (k + 1)) := by
              rw [method.v_succ_eq_sub_weighted_gradient]

/-- The coefficients in the source formula for `gₖ` normalize to the textbook scalar
`(1 - λₖ) / λₖ`. -/
-- Proof sketch: rewrite `αᵢ / λᵢ₊₁` as `1 / λᵢ₊₁ - 1 / λᵢ` using
-- `λᵢ₊₁ = (1 - αᵢ) λᵢ`, then telescope the finite sum.
theorem gradientAverage_normalization
    (k : ℕ) :
    ∑ i ∈ Finset.range k, method.alpha i / method.weight (i + 1) =
      (1 - method.weight k) / method.weight k := by
  -- The source coefficients telescope after one-step normalization by the owner weight.
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hterm :
          method.alpha k / method.weight (k + 1) =
            1 / method.weight (k + 1) - 1 / method.weight k := by
        rw [method.weight_succ]
        field_simp
          [(method.weight_pos k).ne', sub_ne_zero.mpr (method.alpha_mem_Ioo k).2.ne']
        ring
      rw [Finset.sum_range_succ, ih, hterm, method.weight_succ]
      field_simp
        [(method.weight_pos k).ne', sub_ne_zero.mpr (method.alpha_mem_Ioo k).2.ne']
      ring

/-- In the smooth-convex specialization `μ = 0`, the source-defined gradient average can equally
be written using the owner center `vₖ` and weight `λₖ` for every positive stage `k`. -/
-- Proof sketch: use the owner recurrences for `vₖ`, `γₖ`, and `λₖ` to identify
-- `γ₀ λₖ (method 0 - vₖ)` with
-- `λₖ ∑_{i < k} (αᵢ / λᵢ₊₁) ∇ f(yᵢ)`, then use `k ≥ 1` to divide by `1 - λₖ`.
theorem gradientAverage_eq_weight_mul_initial_curvature
    (k : ℕ) (hk : 1 ≤ k) :
    g_[method; k] =
      (method.weight k * gamma0 / (1 - method.weight k)) • (method 0 - method.v k) := by
  -- For positive stages, `gₖ` is the weighted finite average, so only the telescoped vector sum
  -- remains to be substituted.
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨j, rfl⟩
  rw [gradientAverage_succ, OptimalMethodRecurrence.weightedAverage]
  rw [method.weighted_gradient_sum_eq_initial_curvature_sub_center]
  rw [smul_smul]
  congr 1
  ring

end

end OptimalMethodRecurrence

open scoped OptimalMethodRecurrence.OptimalMethodGradientAverage

namespace GeneralOptimalMethodScheme

variable {L : NNReal} {f : E → ℝ} {x0 : E} {gamma0 : ℝ}

-- The source-facing owner of `gₖ` remains `OptimalMethodRecurrence.gradientAverage`. The scheme
-- statements below reuse that owner through the underlying recurrence view of `method`.
local notation:max "g_[" method ";" k "]" =>
  OptimalMethodRecurrence.gradientAverage
    (GeneralOptimalMethodScheme.toOptimalMethodRecurrence method) k

section SmoothObjective

variable (hconv : ConvexOn ℝ Set.univ f)
variable (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
variable (hgrad_lipschitz : LipschitzWith L (∇ f))
variable (xStar : E)
variable (hxStar : IsMinOn f Set.univ xStar)

section SmoothConvex

variable {x0 : E} {gamma0 : ℝ}
variable (method : GeneralOptimalMethodScheme f (L : ℝ) 0 x0 gamma0)

/-- Helper for Theorem 2.22: the source curvature sequence `γ_k` coincides with the owner
curvature sequence of the optimal-method scheme. -/
theorem estimating_curvature_eq_method_gamma
    (k : ℕ) :
    estimatingSequenceCurvature 0 gamma0 method.alpha k = method.gamma k := by
  -- The source and owner curvatures satisfy the same initial value and successor recurrence.
  induction k with
  | zero =>
      simpa using method.gamma_zero.symm
  | succ k ih =>
      rw [estimatingSequenceCurvature_succ, ih]
      simpa using (method.gamma_succ k).symm

/-- Helper for Theorem 2.22: the source center recursion `v_k` coincides with the owner center
sequence of the optimal-method scheme. -/
theorem estimating_center_eq_method_v
    (k : ℕ) :
    estimatingSequenceCenter f method.alpha method.y 0 gamma0 (method 0) k = method.v k := by
  -- After identifying the curvatures, the source center recursion is exactly `method.v_succ`.
  induction k with
  | zero =>
      simpa [method.x_zero] using method.v_zero.symm
  | succ k ih =>
      rw [estimatingSequenceCenter_succ, ih]
      simpa [method.estimating_curvature_eq_method_gamma k,
        method.estimating_curvature_eq_method_gamma (k + 1)] using
        (method.v_succ k).symm

/-- Helper for Theorem 2.22: the owner interpolation point satisfies the source identity
`y_k = α_k v_k + (1 - α_k) x_k` in the smooth-convex case `μ = 0`. -/
theorem y_eq_alpha_smul_v_add_one_sub_smul_x
    (k : ℕ) :
    method.y k = method.alpha k • method.v k + (1 - method.alpha k) • method k := by
  -- Rewrite the owner interpolation formula by canceling the current curvature `γ_k`.
  have hgamma_eq : method.gamma k = method.weight k * gamma0 := by
    simpa using method.gamma_sub_mu_eq_weight_mul_initial_gap k
  have hgamma_ne : method.gamma k ≠ 0 := by
    rw [hgamma_eq]
    exact mul_ne_zero (method.weight_pos k).ne' method.gamma0_pos.ne'
  calc
    method.y k
        = (1 / method.gamma k) •
            ((method.alpha k * method.gamma k) • method.v k +
              method.gamma (k + 1) • method k) := by
              simpa using method.y_eq k
    _ = (1 / method.gamma k) •
          ((method.alpha k * method.gamma k) • method.v k +
            ((1 - method.alpha k) * method.gamma k) • method k) := by
            rw [method.gamma_succ k]
            ring_nf
    _ = method.alpha k • method.v k + (1 - method.alpha k) • method k := by
        have hcoef1 : (1 / method.gamma k) * (method.alpha k * method.gamma k) = method.alpha k := by
          field_simp [hgamma_ne]
        have hcoef2 :
            (1 / method.gamma k) * ((1 - method.alpha k) * method.gamma k) =
              1 - method.alpha k := by
          field_simp [hgamma_ne]
        rw [smul_add, smul_smul, smul_smul, hcoef1, hcoef2]

/-- Helper for Theorem 2.22: the successor formula for `φ_k^*` simplifies to the exact
smooth-convex descent form used in the source induction. -/
theorem estimating_value_succ_eq_descent_form
    (k : ℕ) :
    estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) (k + 1) =
      (1 - method.alpha k) *
          estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) k +
        method.alpha k * f (method.y k) -
        (1 / (2 * (L : ℝ))) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
        method.alpha k * inner ℝ (∇ f (method.y k)) (method.v k - method.y k) := by
  -- Package the raw recursion by rewriting the owner curvature and center once, then simplify
  -- the two scalar coefficients using the `μ = 0` recurrences.
  calc
    estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) (k + 1)
        = (1 - method.alpha k) *
            estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) k +
          method.alpha k * f (method.y k) -
          (method.alpha k ^ (2 : ℕ) / (2 * method.gamma (k + 1))) *
            ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
          (method.alpha k * (1 - method.alpha k) * method.gamma k / method.gamma (k + 1)) *
            inner ℝ (∇ f (method.y k)) (method.v k - method.y k) := by
          simpa [method.estimating_curvature_eq_method_gamma k,
            method.estimating_curvature_eq_method_gamma (k + 1),
            method.estimating_center_eq_method_v k] using
            estimatingSequenceValue_succ
              f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) k
    _ = (1 - method.alpha k) *
            estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) k +
          method.alpha k * f (method.y k) -
          (1 / (2 * (L : ℝ))) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) +
          method.alpha k * inner ℝ (∇ f (method.y k)) (method.v k - method.y k) := by
          have halpha_ne : method.alpha k ≠ 0 := (method.alpha_pos k).ne'
          have hgamma_next :
              method.gamma (k + 1) = (1 - method.alpha k) * method.gamma k := by
            simpa using method.gamma_succ k
          have hgamma_eq : method.gamma k = method.weight k * gamma0 := by
            simpa using method.gamma_sub_mu_eq_weight_mul_initial_gap k
          have hgamma_ne : method.gamma k ≠ 0 := by
            rw [hgamma_eq]
            exact mul_ne_zero (method.weight_pos k).ne' method.gamma0_pos.ne'
          have hfactor_ne : 1 - method.alpha k ≠ 0 := by
            exact sub_ne_zero.mpr (method.alpha_mem_Ioo k).2.ne'
          have hquadratic :
              method.alpha k ^ (2 : ℕ) / (2 * method.gamma (k + 1)) =
                1 / (2 * (L : ℝ)) := by
            rw [method.gamma_succ_eq_L_mul_sq]
            field_simp [method.L_pos.ne', halpha_ne]
          have hlinear :
              method.alpha k * (1 - method.alpha k) * method.gamma k / method.gamma (k + 1) =
                method.alpha k := by
            rw [hgamma_next]
            field_simp [hgamma_ne, hfactor_ne]
          rw [hquadratic, hlinear]

include hconv hgrad

/-- Helper for Theorem 2.22: the source minimum values dominate the actual objective values along
the optimal-method trajectory. -/
theorem estimating_value_ge_objective
    (k : ℕ) :
    f (method k) ≤
      estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) k := by
  -- Follow the source induction: compare the descent step with the tangent-plane lower bound at
  -- `y_k`, then use the affine identity for `y_k` to cancel the linear terms exactly.
  induction k with
  | zero =>
      simp [estimatingSequenceValue]
  | succ k ih =>
      have hfactor_nonneg : 0 ≤ 1 - method.alpha k := by
        linarith [(method.alpha_mem_Ioo k).2]
      have hih :
          (1 - method.alpha k) * f (method k) ≤
            (1 - method.alpha k) *
              estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0
                (method 0) k := by
        exact mul_le_mul_of_nonneg_left ih hfactor_nonneg
      have htangent :
          f (method.y k) + inner ℝ (∇ f (method.y k)) (method k - method.y k) ≤
            f (method k) := by
        have hlower :=
          ConvexOn.lower_tangent_plane_of_hasGradientWithinAt hconv
            (method.y k) (by simp) (∇ f (method.y k))
            ((hasGradientWithinAt_univ).2 (hgrad (method.y k))) (method k) (by simp)
        linarith
      have htangent_scaled :
          (1 - method.alpha k) *
              (f (method.y k) + inner ℝ (∇ f (method.y k)) (method k - method.y k)) ≤
            (1 - method.alpha k) * f (method k) := by
        exact mul_le_mul_of_nonneg_left htangent hfactor_nonneg
      have hdom :
          (1 - method.alpha k) *
              (f (method.y k) + inner ℝ (∇ f (method.y k)) (method k - method.y k)) ≤
            (1 - method.alpha k) *
              estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0
                (method 0) k := by
        exact le_trans htangent_scaled hih
      have hcancel_vec :
          (1 - method.alpha k) • (method k - method.y k) +
            method.alpha k • (method.v k - method.y k) = 0 := by
        rw [method.y_eq_alpha_smul_v_add_one_sub_smul_x k]
        module
      have hcancel_inner :
          (1 - method.alpha k) * inner ℝ (∇ f (method.y k)) (method k - method.y k) +
            method.alpha k * inner ℝ (∇ f (method.y k)) (method.v k - method.y k) = 0 := by
        have hinner :=
          congrArg (fun z ↦ inner ℝ (∇ f (method.y k)) z) hcancel_vec
        simpa [inner_add_right, inner_smul_right] using hinner
      have hstep_model :
          f (method.y k) ≤
            (1 - method.alpha k) *
                estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0
                  (method 0) k +
              method.alpha k * f (method.y k) +
              method.alpha k * inner ℝ (∇ f (method.y k)) (method.v k - method.y k) := by
        have hdom' :
            (1 - method.alpha k) * f (method.y k) +
                (1 - method.alpha k) * inner ℝ (∇ f (method.y k)) (method k - method.y k) ≤
              (1 - method.alpha k) *
                estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0
                  (method 0) k := by
          simpa [mul_add] using hdom
        have hsum :=
          add_le_add_right hdom'
            (method.alpha k * f (method.y k) +
              method.alpha k * inner ℝ (∇ f (method.y k)) (method.v k - method.y k))
        have hone :
            (1 - method.alpha k) * f (method.y k) + method.alpha k * f (method.y k) =
              f (method.y k) := by
          ring
        linarith
      calc
        f (method (k + 1))
            ≤ f (method.y k) - (1 / (2 * (L : ℝ))) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) :=
              method.x_succ_le k
        _ ≤ ((1 - method.alpha k) *
                estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0
                  (method 0) k +
              method.alpha k * f (method.y k) +
              method.alpha k * inner ℝ (∇ f (method.y k)) (method.v k - method.y k)) -
              (1 / (2 * (L : ℝ))) * ‖∇ f (method.y k)‖ ^ (2 : ℕ) := by
              gcongr
        _ = estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0
              (method 0) (k + 1) := by
              rw [method.estimating_value_succ_eq_descent_form]
              ring

omit hconv
include hgrad hgrad_lipschitz

/-- Helper for Theorem 2.22: the smoothness assumptions imply `C¹` regularity. -/
theorem contDiff_one_of_hasGradientAt_lipschitz :
    ContDiff ℝ 1 f := by
  -- Rewrite the derivative through the Riesz map so the Lipschitz gradient yields continuity of
  -- `fderiv`.
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (hgrad x).differentiableAt, ?_⟩
  have hEq : fderiv ℝ f = fun x ↦ InnerProductSpace.toDual ℝ E (∇ f x) := by
    funext x
    simpa using (hgrad x).hasFDerivAt.fderiv
  have hcont : Continuous (fun x ↦ InnerProductSpace.toDual ℝ E (∇ f x)) :=
    (InnerProductSpace.toDual ℝ E).continuous.comp hgrad_lipschitz.continuous
  simpa [hEq] using hcont

include xStar hxStar

/-- Helper for Theorem 2.22: the initial objective gap is bounded by the smooth quadratic upper
model at a minimizer. -/
theorem smooth_gap_le_initial_distance_sq :
    f (method 0) - f xStar ≤
      ((L : ℝ) / 2) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
  -- Evaluate the smooth Taylor upper bound at the minimizer and remove the vanishing linear
  -- term `⟨∇ f xStar, method 0 - xStar⟩`.
  have hfC1 : ContDiff ℝ 1 f :=
    contDiff_one_of_hasGradientAt_lipschitz hgrad hgrad_lipschitz
  have hgrad_zero : ∇ f xStar = 0 :=
    isMinOn_gradient_eq_zero hxStar
  calc
    f (method 0) - f xStar
        ≤ firstOrderTaylorModelAt f xStar (method 0) - f xStar +
            ((L : ℝ) / 2) * ‖method 0 - xStar‖ ^ (2 : ℕ) := by
          have hupper :=
            taylor_upper_bound_of_contDiffOne_withLipschitzGradient
              hfC1 hgrad_lipschitz xStar (method 0)
          simpa [firstOrderTaylorModelAt_apply, hgrad_zero, add_comm, add_left_comm, add_assoc]
            using sub_le_sub_right hupper (f xStar)
    _ = ((L : ℝ) / 2) * ‖method 0 - xStar‖ ^ (2 : ℕ) := by
          simp [hgrad_zero]
    _ = ((L : ℝ) / 2) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
          rw [norm_sub_rev]

include hconv

/-- Theorem 2.22 (1): for the smooth convex optimal-method scheme, every
estimating-sequence center `vₖ` stays within `sqrt (1 + L / γ₀) ‖x* - x₀‖` of a minimizer `x*`,
written on the owner surface as `‖xStar - method 0‖`. -/
-- Proof sketch: evaluate the estimating-sequence upper bound at a minimizer `xStar`, compare the
-- resulting quadratic model with the initial quadratic model of curvature `gamma0`, and use the
-- smooth convex inequality `f (method 0) - f xStar ≤ (L / 2) ‖xStar - method 0‖²`.
theorem center_norm_le
    (k : ℕ) :
    ‖method.v k - xStar‖ ≤
      Real.sqrt (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖ := by
  -- Evaluate the estimating-sequence upper model at the minimizer `xStar`, compare it with the
  -- centered quadratic formula for `φ_k`, and cancel the common weight `λ_k`.
  have hgamma_nonzero : ∀ j, estimatingSequenceCurvature 0 gamma0 method.alpha (j + 1) ≠ 0 := by
    intro j
    have hgamma_eq : method.gamma (j + 1) = method.weight (j + 1) * gamma0 := by
      simpa using method.gamma_sub_mu_eq_weight_mul_initial_gap (j + 1)
    rw [method.estimating_curvature_eq_method_gamma (j + 1), hgamma_eq]
    exact mul_ne_zero (method.weight_pos (j + 1)).ne' method.gamma0_pos.ne'
  have hstrong : StrongConvexOn Set.univ 0 f := by
    rcases hconv with ⟨hconv_set, hineq⟩
    refine ⟨hconv_set, ?_⟩
    intro x hx y hy a b ha hb hab
    simpa using hineq hx hy ha hb hab
  have halpha_mem_Icc : ∀ j, method.alpha j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    exact Set.mem_Icc_of_Ioo (method.alpha_mem_Ioo j)
  have hmodel_upper :=
    strongConvexEstimatingFunction_upper_bound_apply
      (E := E) (f := f)
      (φ₀ := quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
      (y := method.y) (α := method.alpha)
      hstrong (fun j ↦ hgrad (method.y j)) halpha_mem_Icc k xStar
  have hphi_eval :
      strongConvexEstimatingFunction 0 f
          (quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
          method.y method.alpha k xStar =
        estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) k +
          (method.gamma k / 2) * ‖xStar - method.v k‖ ^ (2 : ℕ) := by
    simpa [method.estimating_curvature_eq_method_gamma k, method.estimating_center_eq_method_v k]
      using
        estimatingSequence_eq_canonicalQuadratic_apply
          f method.alpha method.y 0 (f (method 0)) gamma0 (method 0) hgamma_nonzero k xStar
  have hvalue_ge :
      f xStar ≤ estimatingSequenceValue f method.alpha method.y 0 (f (method 0)) gamma0
        (method 0) k := by
    exact le_trans (isMinOn_univ_iff.mp hxStar (method k))
      (method.estimating_value_ge_objective hconv hgrad k)
  have hquad_le_gap :
      (method.gamma k / 2) * ‖xStar - method.v k‖ ^ (2 : ℕ) ≤
        strongConvexEstimatingFunction 0 f
            (quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
            method.y method.alpha k xStar -
          f xStar := by
    rw [hphi_eval]
    linarith
  have hmodel_gap :
      strongConvexEstimatingFunction 0 f
          (quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
          method.y method.alpha k xStar -
        f xStar ≤
      method.weight k *
        (f (method 0) - f xStar + (gamma0 / 2) * ‖xStar - method 0‖ ^ (2 : ℕ)) := by
    have hphi0 :
        quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0) xStar =
          f (method 0) + (gamma0 / 2) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
      rw [quadraticallyRegularizedObjective_apply]
    have hline :
        strongConvexEstimatingFunction 0 f
            (quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0))
            method.y method.alpha k xStar ≤
          (1 - estimatingWeight method.alpha k) * f xStar +
            estimatingWeight method.alpha k *
              quadraticallyRegularizedObjective (fun _ ↦ f (method 0)) gamma0 (method 0) xStar := by
      simpa [AffineMap.lineMap_apply_module] using hmodel_upper
    rw [method.toOptimalMethodRecurrence.estimatingWeight_eq_weight] at hline
    rw [hphi0] at hline
    linarith
  have hgamma_eq : method.gamma k = method.weight k * gamma0 := by
    simpa using method.gamma_sub_mu_eq_weight_mul_initial_gap k
  have hweight_cancel :
      (gamma0 / 2) * ‖xStar - method.v k‖ ^ (2 : ℕ) ≤
        f (method 0) - f xStar + (gamma0 / 2) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
    have hcombined := le_trans hquad_le_gap hmodel_gap
    rw [hgamma_eq] at hcombined
    have hrewrite :
        (method.weight k * gamma0 / 2) * ‖xStar - method.v k‖ ^ (2 : ℕ) =
          method.weight k * ((gamma0 / 2) * ‖xStar - method.v k‖ ^ (2 : ℕ)) := by
      ring
    rw [hrewrite] at hcombined
    nlinarith [hcombined, method.weight_pos k]
  have hsmooth := method.smooth_gap_le_initial_distance_sq hgrad hgrad_lipschitz xStar hxStar
  have hsq :
      ‖xStar - method.v k‖ ^ (2 : ℕ) ≤
        (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
    have hineq :
        (gamma0 / 2) * ‖xStar - method.v k‖ ^ (2 : ℕ) ≤
          ((L : ℝ) / 2) * ‖xStar - method 0‖ ^ (2 : ℕ) +
            (gamma0 / 2) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
      linarith
    have hscaled :
        gamma0 * ‖xStar - method.v k‖ ^ (2 : ℕ) ≤
          (gamma0 + (L : ℝ)) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
      nlinarith [hineq]
    have hscaled' :
        ‖xStar - method.v k‖ ^ (2 : ℕ) ≤
          ((gamma0 + (L : ℝ)) / gamma0) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
      have hmul :=
      mul_le_mul_of_nonneg_right hscaled (one_div_nonneg.mpr method.gamma0_pos.le)
      have hgamma0_ne : gamma0 ≠ 0 := method.gamma0_pos.ne'
      simpa [div_eq_mul_inv, hgamma0_ne, add_mul, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm] using hmul
    have hcoeff : ((gamma0 + (L : ℝ)) / gamma0) = 1 + (L : ℝ) / gamma0 := by
      field_simp [method.gamma0_pos.ne']
    simpa [hcoeff] using hscaled'
  have htarget_sq :
      ‖xStar - method.v k‖ ^ (2 : ℕ) ≤
        (Real.sqrt (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖) ^ (2 : ℕ) := by
    have hfactor_nonneg : 0 ≤ 1 + (L : ℝ) / gamma0 := by
      have hdiv_nonneg : 0 ≤ (L : ℝ) / gamma0 := by
        exact div_nonneg (show 0 ≤ (L : ℝ) by exact_mod_cast L.2) method.gamma0_pos.le
      linarith
    have hsqrt_sq :
        (Real.sqrt (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖) ^ (2 : ℕ) =
          (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
      calc
        (Real.sqrt (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖) ^ (2 : ℕ)
            = (Real.sqrt (1 + (L : ℝ) / gamma0)) ^ (2 : ℕ) *
                ‖xStar - method 0‖ ^ (2 : ℕ) := by
                ring
        _ = (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖ ^ (2 : ℕ) := by
              rw [Real.sq_sqrt hfactor_nonneg]
    rwa [hsqrt_sq]
  have htarget_nonneg :
      0 ≤ Real.sqrt (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖ := by
    positivity
  have hleft_nonneg : 0 ≤ ‖xStar - method.v k‖ := norm_nonneg _
  have hnorm :
      ‖xStar - method.v k‖ ≤ Real.sqrt (1 + (L : ℝ) / gamma0) * ‖xStar - method 0‖ := by
    nlinarith [htarget_sq, htarget_nonneg, hleft_nonneg]
  simpa [norm_sub_rev] using hnorm

/-- Theorem 2.22 (2): for every positive stage `k`, the weighted gradient average `gₖ` satisfies
the displayed norm bound in terms of `λₖ`, `γ₀`, and the initial distance to a minimizer. -/
-- Proof sketch: use the explicit formula
-- `g_[method; k] = (γ₀ λₖ / (1 - λₖ)) (method 0 - vₖ)`, equivalently
-- `method.v k = method 0 - ((1 - λₖ) / (λₖ γ₀)) g_[method; k]`, and combine the triangle
-- inequality with
-- `center_norm_le`.
theorem gradientAverage_norm_le
    (k : ℕ) (hk : 1 ≤ k) :
    ‖g_[method; k]‖ ≤
      (method.weight k * gamma0 /
        (1 - method.weight k)) *
        (1 + Real.sqrt (1 + (L : ℝ) / gamma0)) *
        ‖xStar - method 0‖ := by
  -- Rewrite `gₖ` through `method 0 - v_k`, then apply the triangle inequality and the center
  -- bound from the first part of the theorem.
  have hcoeff_nonneg : 0 ≤ method.weight k * gamma0 / (1 - method.weight k) := by
    have hdenom_pos : 0 < 1 - method.weight k := by
      linarith [method.toOptimalMethodRecurrence.weight_lt_one_of_one_le hk]
    have hnum_nonneg : 0 ≤ method.weight k * gamma0 := by
      exact mul_nonneg (method.weight_pos k).le method.gamma0_pos.le
    exact div_nonneg hnum_nonneg hdenom_pos.le
  have hdist :
      ‖method 0 - method.v k‖ ≤
        (1 + Real.sqrt (1 + (L : ℝ) / gamma0)) * ‖xStar - method 0‖ := by
    have hcenter := method.center_norm_le hconv hgrad hgrad_lipschitz xStar hxStar k
    have htriangle :
        ‖method 0 - method.v k‖ ≤ ‖method 0 - xStar‖ + ‖xStar - method.v k‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (method 0 - xStar) (xStar - method.v k)
    have hsum :
        ‖method 0 - xStar‖ + ‖xStar - method.v k‖ ≤
          (1 + Real.sqrt (1 + (L : ℝ) / gamma0)) * ‖xStar - method 0‖ := by
      rw [norm_sub_rev] at hcenter
      rw [norm_sub_rev]
      nlinarith
    exact le_trans htriangle hsum
  calc
    ‖g_[method; k]‖
        =
          ‖((method.weight k * gamma0 / (1 - method.weight k)) •
            (method 0 - method.v k))‖ := by
            rw [method.toOptimalMethodRecurrence.gradientAverage_eq_weight_mul_initial_curvature
              k hk]
    _ = ‖method.weight k * gamma0 / (1 - method.weight k)‖ * ‖method 0 - method.v k‖ := by
          rw [norm_smul]
    _ = |method.weight k * gamma0 / (1 - method.weight k)| * ‖method 0 - method.v k‖ := by
          rw [Real.norm_eq_abs]
    _ = (method.weight k * gamma0 / (1 - method.weight k)) * ‖method 0 - method.v k‖ := by
          rw [abs_of_nonneg hcoeff_nonneg]
    _ ≤ (method.weight k * gamma0 / (1 - method.weight k)) *
          ((1 + Real.sqrt (1 + (L : ℝ) / gamma0)) * ‖xStar - method 0‖) := by
          exact mul_le_mul_of_nonneg_left hdist hcoeff_nonneg
    _ = (method.weight k * gamma0 / (1 - method.weight k)) *
          (1 + Real.sqrt (1 + (L : ℝ) / gamma0)) * ‖xStar - method 0‖ := by
          ring

end SmoothConvex

section Gamma0EqThreeMul

variable {x0 : E}
variable (method : GeneralOptimalMethodScheme f (L : ℝ) 0 x0 (3 * (L : ℝ)))

omit hconv hgrad hgrad_lipschitz xStar hxStar

/-- Helper for Theorem 2.22: the smooth-convex square-root factor simplifies to
`(3 + 2 √3) / 3` when `γ₀ = 3L`. -/
theorem sqrt_factor_eq_three_plus_two_sqrt_three :
    (3 * (L : ℝ)) * (1 + Real.sqrt (1 + (L : ℝ) / (3 * (L : ℝ)))) =
      (3 + 2 * Real.sqrt 3) * (L : ℝ) := by
  -- Simplify the ratio `L / (3L)` to `1 / 3`, then rationalize `√(4 / 3)`.
  by_cases hL : (L : ℝ) = 0
  · simp [hL]
  · have hdiv : (L : ℝ) / (3 * (L : ℝ)) = 1 / 3 := by
      field_simp [hL]
    have hsqrt :
        Real.sqrt (1 + (L : ℝ) / (3 * (L : ℝ))) = 2 * Real.sqrt 3 / 3 := by
      rw [hdiv]
      norm_num
      field_simp [show (Real.sqrt 3) ≠ 0 by positivity]
      rw [sq, Real.mul_self_sqrt (by positivity)]
    calc
      (3 * (L : ℝ)) * (1 + Real.sqrt (1 + (L : ℝ) / (3 * (L : ℝ))))
          = (3 * (L : ℝ)) * (1 + 2 * Real.sqrt 3 / 3) := by
              rw [hsqrt]
      _ = (3 + 2 * Real.sqrt 3) * (L : ℝ) := by
            ring

include hconv hgrad hgrad_lipschitz xStar hxStar

/-- Theorem 2.22 (3): when `γ₀ = 3L`, the weighted gradient average `gₖ` satisfies the explicit
`O((k + 1)⁻²)` norm bound from the textbook. -/
-- Proof sketch: combine `gradientAverage_norm_le` with the owner weight-factor estimate
-- `weight_ratio_le_of_gamma0_eq_three_mul`, then simplify the remaining
-- scalar factor at `γ₀ = 3L`.
theorem gradientAverage_norm_le_of_gamma0_eq_three_mul
    (k : ℕ) (hk : 1 ≤ k) :
    ‖g_[method; k]‖ ≤
      (4 * (3 + 2 * Real.sqrt 3) * (L : ℝ) * ‖xStar - method 0‖) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) := by
  -- Isolate the owner weight ratio `λₖ / (1 - λₖ)`, bound it by the chapter estimate, and use the
  -- closed-form simplification of the square-root factor at `γ₀ = 3L`.
  have hbase :=
    method.gradientAverage_norm_le hconv hgrad hgrad_lipschitz xStar hxStar k hk
  have hratio := method.toOptimalMethodRecurrence.weight_ratio_le_of_gamma0_eq_three_mul hk
  have hfactor_nonneg :
      0 ≤ (3 + 2 * Real.sqrt 3) * (L : ℝ) * ‖xStar - method 0‖ := by
    positivity
  calc
    ‖g_[method; k]‖
        ≤ (method.weight k * (3 * (L : ℝ)) / (1 - method.weight k)) *
            (1 + Real.sqrt (1 + (L : ℝ) / (3 * (L : ℝ)))) *
            ‖xStar - method 0‖ := hbase
    _ = (method.weight k / (1 - method.weight k)) *
          ((3 * (L : ℝ)) * (1 + Real.sqrt (1 + (L : ℝ) / (3 * (L : ℝ))))) *
          ‖xStar - method 0‖ := by
          ring
    _ = (method.weight k / (1 - method.weight k)) *
          ((3 + 2 * Real.sqrt 3) * (L : ℝ)) *
          ‖xStar - method 0‖ := by
          rw [sqrt_factor_eq_three_plus_two_sqrt_three (L := L)]
    _ ≤ (4 / (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4)) *
          (((3 + 2 * Real.sqrt 3) * (L : ℝ)) * ‖xStar - method 0‖) := by
          have hmul := mul_le_mul_of_nonneg_right hratio hfactor_nonneg
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = (4 * (3 + 2 * Real.sqrt 3) * (L : ℝ) * ‖xStar - method 0‖) /
          (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) := by
          field_simp

end Gamma0EqThreeMul

end SmoothObjective

end GeneralOptimalMethodScheme
