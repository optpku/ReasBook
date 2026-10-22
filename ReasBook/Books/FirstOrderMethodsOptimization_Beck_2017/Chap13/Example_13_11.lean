/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_18
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Proposition_10_59
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_6
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Example_13_10

noncomputable section

open InnerProductSpace (toDualMap)
open Matrix
open Metric
open scoped Gradient RealInnerProductSpace

-- Chapter 7 owns the global `Λ[...]` parser. Use the Chapter 10 meaning only in this file.
local notation "Λ[" a "]" => primalCounterparts a

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "B" => closedBall (0 : E) 1
variable (A : Matrix (Fin n) (Fin n) ℝ)
local notation "qA" => quadratic_affine_function_on_lp (2 : ENNReal) (-A) 0 0

private theorem qA_apply (x : E) :
    qA x = -((1 / 2 : ℝ) * ⟪A.toEuclideanLin x, x⟫) := by
  simpa using quadratic_affine_function_on_lp_two_apply_eq (-A) (0 : E) x

/-- Helper for Example 13.11: on the effective domain of the unit-ball indicator, the composite
objective reduces to the real quadratic owner `qA`. -/
private theorem qA_composite_model_objective_eq_coe_real_of_mem_effective_domain
    {x : E} (hx : x ∈ effective_domain (extendedIndicator B)) :
    composite_model_objective (Function.toEReal qA) (extendedIndicator B) x =
      ((qA x : ℝ) : EReal) := by
  have hxB : x ∈ B := by
    simpa [effective_domain_extendedIndicator] using hx
  rw [composite_model_objective_apply]
  simp [Function.toEReal, extendedIndicator, hxB]

/-- Helper for Example 13.11: every point on a unit-ball oracle segment with parameter in `[0, 1]`
stays in the effective domain of the unit-ball indicator. -/
private theorem qA_trial_mem_effective_domain_of_mem_Icc
    {x p : E} (hx : x ∈ effective_domain (extendedIndicator B))
    (hp : p ∈ effective_domain (extendedIndicator B))
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    x + α • (p - x) ∈ effective_domain (extendedIndicator B) := by
  have hindicator_convex : is_convex_function (extendedIndicator B) := by
    exact extendedIndicator_isConvexFunction_of_convex B (convex_closedBall (0 : E) 1)
  have hcombo :
      α • p + (1 - α) • x ∈ effective_domain (extendedIndicator B) :=
    combo_mem_effective_domain_of_is_convex_function hindicator_convex hp hx hα
  have hrewrite : x + α • (p - x) = α • p + (1 - α) • x := by
    rw [smul_sub]
    calc
      x + (α • p - α • x) = α • p + (x - α • x) := by
        abel
      _ = α • p + (1 - α) • x := by
        rw [sub_smul, one_smul]
  rw [hrewrite]
  exact hcombo

/- This item is `source-facing`: it specializes the Chapter 13 generalized conditional-gradient
trajectory to the quadratic maximization problem on the Euclidean unit ball.

Domain sampling in the Euclidean quadratic / conditional-gradient domain gives the owner layers:

- `is_generalized_conditional_gradient_trajectory` for the iterate/search-point/stepsize data;
- `uses_generalized_conditional_gradient_exact_line_search_rule` for the exact line-search
  condition on the composite objective;
- `is_stationary_point_on` for the Chapter 3 constrained stationarity predicate on the ball;
- `Matrix.toEuclideanLin` for the canonical action of a real matrix on `ℝ^n`;
- the Chapter 5/6 quadratic owner `qA = quadratic_affine_function_on_lp (2 : ENNReal) (-A) 0 0`;
- the bridge theorem `quadratic_affine_function_on_lp_two_apply_eq`, which rewrites that owner to
  the intrinsic Euclidean quadratic `x ↦ -((1 / 2 : ℝ) * ⟪A.toEuclideanLin x, x⟫)`.

Primitive data here are just the matrix `A`, the trajectory data `(xᵏ, pᵏ, tₖ)`, and the closed
ball constraint. The canonical quadratic owner therefore belongs in the theorem statement, while
the intrinsic Euclidean formula is recovered by `qA_apply` as a thin local bridge for later proof
rewrites. -/

/-- Helper for Example 13.11: the quadratic owner `qA` has gradient `x ↦ -A x`. -/
lemma qA_hasGradientAt
    (hA : A.PosSemidef) (x : E) :
    HasGradientAt qA (-A.toEuclideanLin x) x := by
  let T : E →L[ℝ] E := A.toEuclideanLin.toContinuousLinearMap
  have hsymm : (T : E →ₗ[ℝ] E).IsSymmetric :=
    by
      change A.toEuclideanLin.IsSymmetric
      exact (Matrix.isSymmetric_toEuclideanLin_iff).2 hA.1
  -- Route correction: differentiate the symmetric Rayleigh form directly, then scale by `-1/2`
  -- to match the source objective `qA`.
  have hinner :
      HasFDerivAt (fun y : E ↦ ⟪T y, y⟫) (2 • innerSL ℝ (T x)) x := by
    simpa [hsymm.coe_reApplyInnerSelf_apply] using
      (hsymm.hasStrictFDerivAt_reApplyInnerSelf x).hasFDerivAt
  have hscaled :
      HasFDerivAt (fun y : E ↦ -((1 / 2 : ℝ) * ⟪T y, y⟫))
        ((-(1 / 2 : ℝ)) • (2 • innerSL ℝ (T x))) x := by
    simpa using hinner.const_mul (-(1 / 2 : ℝ))
  have hfrechet :
      ((-(1 / 2 : ℝ)) • (2 • innerSL ℝ (T x))) =
        (InnerProductSpace.toDual ℝ E) (-T x) := by
    ext y
    simp [real_inner_comm]
  rw [hfrechet] at hscaled
  -- Rewrite the Chapter 5 quadratic owner back to the intrinsic Euclidean formula.
  have hquad :
      HasGradientAt (fun y : E ↦ -((1 / 2 : ℝ) * ⟪A.toEuclideanLin y, y⟫))
        (-A.toEuclideanLin x) x := by
    simpa [T] using hscaled.hasGradientAt
  convert hquad using 1
  funext y
  rw [qA_apply]

/-- Helper for Example 13.11: if `x` is feasible but not stationary on the unit ball, then
`A x ≠ 0`. -/
lemma matrix_image_ne_zero_of_not_stationary_on_ball
    (hA : A.PosSemidef) {x : E} (hx : x ∈ B)
    (hns : ¬ is_stationary_point_on qA B x) :
    A.toEuclideanLin x ≠ 0 := by
  intro hzero
  apply hns
  -- A zero matrix image gives zero gradient, so the variational inequality is trivially true.
  rw [is_stationary_point_on_iff_forall_inner_nonneg]
  refine ⟨(qA_hasGradientAt A hA x).differentiableAt, hx, ?_⟩
  intro y hy
  rw [(qA_hasGradientAt A hA x).gradient, hzero]
  simp

/-- Helper for Example 13.11: the Chapter 13 linear minimization oracle on the unit ball is the
normalized matrix image. -/
lemma argmin_eq_normalized_matrix_image
    (hA : A.PosSemidef) {x p : E} (hx : x ∈ B)
    (hp : p ∈ generalized_conditional_gradient_argmin qA (extendedIndicator B) x)
    (hns : ¬ is_stationary_point_on qA B x) :
    p = ‖A.toEuclideanLin x‖⁻¹ • A.toEuclideanLin x := by
  have hAx_ne :
      A.toEuclideanLin x ≠ 0 :=
    matrix_image_ne_zero_of_not_stationary_on_ball A hA hx hns
  -- Reuse the Chapter 13 unit-ball oracle bridge from Example 13.10, then specialize the
  -- negative-gradient owner using `qA_hasGradientAt`.
  have hp_counterpart : p ∈ Λ[toDualMap ℝ E (A.toEuclideanLin x)] := by
    have hp_neg_grad : p ∈ Λ[toDualMap ℝ E (-∇ qA x)] := by
      exact
        mem_unit_ball_generalized_conditional_gradient_argmin_iff_mem_primalCounterparts.mp hp
    simpa [(qA_hasGradientAt A hA x).gradient] using hp_neg_grad
  have hp_singleton :
      p ∈ ({‖A.toEuclideanLin x‖⁻¹ • A.toEuclideanLin x} : Set E) := by
    rwa [primalCounterparts_toDualMap_eq_singleton_normalized hAx_ne] at hp_counterpart
  simpa [Set.mem_singleton_iff] using hp_singleton

/-- Helper for Example 13.11: along any segment starting at `x`, the quadratic objective expands
into its initial value plus a linear term and a nonpositive curvature correction. -/
lemma quadratic_segment_eq_initial_add_linear_curvature
    (hA : A.PosSemidef) (x p : E) (s : ℝ) :
    qA (x + s • (p - x)) =
      qA x + s * ⟪∇ qA x, p - x⟫ -
        (1 / 2 : ℝ) * s ^ (2 : ℕ) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
  let d : E := p - x
  let T : E →ₗ[ℝ] E := A.toEuclideanLin
  have hsymm : (T : E →ₗ[ℝ] E).IsSymmetric :=
    by
      change A.toEuclideanLin.IsSymmetric
      exact (Matrix.isSymmetric_toEuclideanLin_iff).2 hA.1
  have hcross : ⟪T d, x⟫ = ⟪T x, d⟫ := by
    -- Symmetry turns the two mixed terms in the quadratic expansion into the same scalar.
    calc
      ⟪T d, x⟫ = ⟪d, T x⟫ := hsymm d x
      _ = ⟪T x, d⟫ := by simp [real_inner_comm]
  have hgrad : ∇ qA x = -T x := by
    rw [(qA_hasGradientAt A hA x).gradient]
  have hraw :
      qA (x + s • d) =
        qA x - s * ⟪T x, d⟫ - (1 / 2 : ℝ) * s ^ (2 : ℕ) * ⟪T d, d⟫ := by
    -- Expand the quadratic along the segment and combine the mixed terms using `hcross`.
    rw [qA_apply, qA_apply, LinearMap.map_add, LinearMap.map_smul, inner_add_left,
      inner_add_right, inner_add_right, inner_smul_left, inner_smul_right, hcross]
    rw [inner_smul_left, inner_smul_right]
    simp [T]
    ring_nf
  -- Replace the explicit linear term by the gradient from `qA_hasGradientAt`.
  calc
    qA (x + s • (p - x)) =
        qA x - s * ⟪T x, d⟫ - (1 / 2 : ℝ) * s ^ (2 : ℕ) * ⟪T d, d⟫ := by
      simpa [d] using hraw
    _ = qA x + s * ⟪∇ qA x, p - x⟫ -
          (1 / 2 : ℝ) * s ^ (2 : ℕ) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
      rw [hgrad]
      simp [d, T, inner_neg_left, sub_eq_add_neg]

/-- Helper for Example 13.11: on `[0,1]`, the secant-gap curvature term from the quadratic
segment expansion is nonnegative. -/
lemma secant_gap_nonneg_of_posSemidef
    (hA : A.PosSemidef) (x p : E) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (1 / 2 : ℝ) * s * (1 - s) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
  have hs_nonneg : 0 ≤ s * (1 - s) := by
    -- The scalar secant factor is nonnegative exactly on the unit interval.
    nlinarith [hs.1, hs.2]
  have hcurv : 0 ≤ ⟪A.toEuclideanLin (p - x), p - x⟫ := by
    -- Positive semidefiniteness controls the segment curvature in every direction.
    have hpositive : (A.toEuclideanLin).IsPositive :=
      (Matrix.isPositive_toEuclideanLin_iff).2 hA
    simpa [real_inner_comm] using hpositive.inner_nonneg_right (p - x)
  nlinarith

/-- Helper for Example 13.11: the quadratic restriction to a unit-ball oracle segment lies above
the secant through its endpoints. -/
lemma quadratic_segment_ge_endpoint_combo
    (hA : A.PosSemidef) (x p : E) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 - s) * qA x + s * qA p ≤ qA (x + s • (p - x)) := by
  have hseg :=
    quadratic_segment_eq_initial_add_linear_curvature A hA x p s
  have hp_endpoint : x + (1 : ℝ) • (p - x) = p := by
    simp
  have hend :
      qA p =
        qA x + ⟪∇ qA x, p - x⟫ -
          (1 / 2 : ℝ) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
    -- Evaluate the segment expansion at the endpoint `s = 1`.
    simpa [hp_endpoint] using
      (quadratic_segment_eq_initial_add_linear_curvature A hA x p (1 : ℝ))
  have hgap :
      0 ≤ (1 / 2 : ℝ) * s * (1 - s) * ⟪A.toEuclideanLin (p - x), p - x⟫ :=
    secant_gap_nonneg_of_posSemidef A hA x p hs
  have hrewrite :
      qA (x + s • (p - x)) - ((1 - s) * qA x + s * qA p) =
        (1 / 2 : ℝ) * s * (1 - s) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
    let c : ℝ := ⟪A.toEuclideanLin (p - x), p - x⟫
    rw [hseg, hend]
    simp
    ring
  have hnonneg :
      0 ≤ qA (x + s • (p - x)) - ((1 - s) * qA x + s * qA p) := by
    rw [hrewrite]
    exact hgap
  -- Compare the value at `s` with the secant interpolation of the endpoint formulas.
  exact sub_nonneg.mp hnonneg

/-- Helper for Example 13.11: if the oracle direction has strictly negative linearized slope,
then the endpoint `p` strictly improves the quadratic objective over `x`. -/
lemma quadratic_endpoint_lt_initial_of_inner_lt_zero
    (hA : A.PosSemidef) {x p : E}
    (hinner_lt : ⟪∇ qA x, p - x⟫ < 0) :
    qA p < qA x := by
  let d : E := p - x
  have hcurv : 0 ≤ ⟪A.toEuclideanLin d, d⟫ := by
    -- Positive semidefiniteness controls the curvature correction at the endpoint.
    have hpositive : (A.toEuclideanLin).IsPositive :=
      (Matrix.isPositive_toEuclideanLin_iff).2 hA
    simpa [d, real_inner_comm] using hpositive.inner_nonneg_right d
  have hend :
      qA p =
        qA x + ⟪∇ qA x, p - x⟫ -
          (1 / 2 : ℝ) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
    -- The endpoint `p` is the segment value at `s = 1`.
    have hp_endpoint : x + (1 : ℝ) • (p - x) = p := by
      simp
    simpa [hp_endpoint] using
      (quadratic_segment_eq_initial_add_linear_curvature A hA x p (1 : ℝ))
  -- The strictly negative linear term dominates because the curvature correction is nonpositive.
  linarith [hend, hinner_lt, hcurv]

/-- Helper for Example 13.11: a minimizer on `[0,1]` whose value is bounded below by the secant
through the endpoints must equal the right endpoint when that endpoint is strictly lower than the
left endpoint. -/
lemma eq_right_endpoint_of_min_le_right_of_secant
    {φ : ℝ → ℝ} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hmin_right : φ τ ≤ φ 1)
    (hsecant : (1 - τ) * φ 0 + τ * φ 1 ≤ φ τ)
    (hend : φ 1 < φ 0) :
    τ = 1 := by
  -- The secant lower bound is strict unless `τ = 1`, so a minimizer no larger than `φ 1` must
  -- sit at the right endpoint.
  by_contra hne
  have hlt : τ < 1 := lt_of_le_of_ne hτ.2 hne
  have hstrict :
      φ 1 < (1 - τ) * φ 0 + τ * φ 1 := by
    nlinarith
  linarith

/-- Helper for Example 13.11: exact line search on a feasible unit-ball segment compares the
quadratic value at the chosen stepsize with the right endpoint in real form. -/
lemma exact_line_search_real_compare_endpoint_on_feasible_segment
    {x p : E} {τ : ℝ}
    (hx : x ∈ B) (hp : p ∈ B)
    (ht : τ ∈ conditional_gradient_exact_line_search_stepsizes
      (composite_model_objective (Function.toEReal qA) (extendedIndicator B)) x p) :
    qA (x + τ • (p - x)) ≤ qA p := by
  have hx_dom : x ∈ effective_domain (extendedIndicator B) := by
    simpa [effective_domain_extendedIndicator] using hx
  have hp_dom : p ∈ effective_domain (extendedIndicator B) := by
    simpa [effective_domain_extendedIndicator] using hp
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 :=
    (mem_conditional_gradient_exact_line_search_stepsizes_iff.mp ht).1
  have htrial_dom :
      x + τ • (p - x) ∈ effective_domain (extendedIndicator B) :=
    qA_trial_mem_effective_domain_of_mem_Icc hx_dom hp_dom hτ
  have hcompare :
      composite_model_objective (Function.toEReal qA) (extendedIndicator B)
          (x + τ • (p - x)) ≤
        composite_model_objective (Function.toEReal qA) (extendedIndicator B) p := by
    -- Route correction: normalize the exact-line-search owner before stripping the indicator and
    -- `EReal` coercions, so the later rewrites only touch feasible points.
    rw [mem_conditional_gradient_exact_line_search_stepsizes_iff, isMinOn_iff] at ht
    rcases ht with ⟨_, hmin⟩
    simpa using hmin 1 (by constructor <;> norm_num)
  have hcompare_coe :
      (((qA (x + τ • (p - x)) : ℝ) : EReal)) ≤ (((qA p : ℝ) : EReal)) := by
    -- Feasibility turns the composite objective back into the real quadratic owner.
    rw [qA_composite_model_objective_eq_coe_real_of_mem_effective_domain A htrial_dom,
      qA_composite_model_objective_eq_coe_real_of_mem_effective_domain A hp_dom] at hcompare
    exact hcompare
  exact EReal.coe_le_coe_iff.mp hcompare_coe

/-- Helper for Example 13.11: a strict endpoint improvement forces the exact line search stepsize
to be the right endpoint of the unit interval. -/
lemma exact_line_search_stepsize_eq_one_of_endpoint_improvement
    (hA : A.PosSemidef) {x p : E} {τ : ℝ}
    (hx : x ∈ B) (hp : p ∈ B)
    (ht : τ ∈ conditional_gradient_exact_line_search_stepsizes
      (composite_model_objective (Function.toEReal qA) (extendedIndicator B)) x p)
    (hend : qA p < qA x) :
    τ = 1 := by
  let φ : ℝ → ℝ := fun s ↦ qA (x + s • (p - x))
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 :=
    (mem_conditional_gradient_exact_line_search_stepsizes_iff.mp ht).1
  have hmin_right : φ τ ≤ φ 1 := by
    -- The previous helper removes the indicator layer and compares the chosen step to the
    -- endpoint `s = 1`.
    simpa [φ] using
      exact_line_search_real_compare_endpoint_on_feasible_segment A hx hp ht
  have hsecant : (1 - τ) * φ 0 + τ * φ 1 ≤ φ τ := by
    -- Positive semidefiniteness makes the quadratic restriction lie above its endpoint secant.
    simpa [φ] using quadratic_segment_ge_endpoint_combo A hA x p hτ
  have hendφ : φ 1 < φ 0 := by
    simpa [φ] using hend
  exact eq_right_endpoint_of_min_le_right_of_secant hτ hmin_right hsecant hendφ

-- Proof sketch: use the generalized conditional-gradient update rule
-- `x^(k+1) = x^k + t_k (p^k - x^k)` from Algorithm 13.2 together with the exact line-search
-- condition on the quadratic-on-ball composite objective. For a positive-semidefinite matrix, the
-- one-dimensional restriction is concave, so its minimum on `[0, 1]` is attained at an endpoint.
-- Nonstationarity on the ball rules out `t_k = 0`, forcing `t_k = 1`; the linear minimization
-- oracle on the Euclidean unit ball then gives
-- `p^k = ‖A x^k‖⁻¹ • A x^k`, and substituting into the update yields the power-method step.
/-- Example 13.11: for the quadratic maximization problem on the Euclidean unit ball with
`A ∈ 𝕊_+^n`, if `(xᵏ, pᵏ, tₖ)` is a generalized conditional-gradient trajectory for the quadratic
term `x ↦ -(1 / 2) ⟪x, A x⟫` and the closed-ball indicator, if each `tₖ` is chosen by exact line
search, and if `xᵏ` is not a constrained stationary point on the unit ball, then the next iterate
is exactly the normalized matrix image
`xᵏ⁺¹ = (1 / ‖A xᵏ‖) • A xᵏ`, i.e. the standard power-method update. -/
theorem generalized_conditional_gradient_step_eq_power_method_of_not_stationary
    (hA : A.PosSemidef)
    {x p : ℕ → E} {t : ℕ → Set.Icc (0 : ℝ) 1}
    (htraj :
      is_generalized_conditional_gradient_trajectory
        qA (extendedIndicator B) x p t)
    (hline :
      uses_generalized_conditional_gradient_exact_line_search_rule
        qA (extendedIndicator B) x p t)
    (k : ℕ)
    (hk : ¬ is_stationary_point_on qA B (x k)) :
    x (k + 1) = ‖A.toEuclideanLin (x k)‖⁻¹ • A.toEuclideanLin (x k) := by
  -- First propagate feasibility of the closed ball along the whole trajectory.
  have hxBall : ∀ j : ℕ, x j ∈ B := by
    intro j
    induction j with
    | zero =>
        exact is_conditional_gradient_trajectory_zero
          (f := Function.toEReal qA) htraj
    | succ j hj =>
        rcases is_conditional_gradient_trajectory_step
            (f := Function.toEReal qA) htraj j with ⟨hpjBall, _, hstep⟩
        have hxj_dom : x j ∈ effective_domain (extendedIndicator B) := by
          simpa [effective_domain_extendedIndicator] using hj
        have hpj_dom : p j ∈ effective_domain (extendedIndicator B) := by
          simpa [effective_domain_extendedIndicator] using hpjBall
        have hnext_dom :
            x j + (t j : ℝ) • (p j - x j) ∈ effective_domain (extendedIndicator B) :=
          qA_trial_mem_effective_domain_of_mem_Icc hxj_dom hpj_dom (t j).2
        simpa [effective_domain_extendedIndicator, hstep] using hnext_dom
  have hxkBall : x k ∈ B := hxBall k
  have hpkArgmin :
      p k ∈ generalized_conditional_gradient_argmin qA (extendedIndicator B) (x k) :=
    htraj.argmin_mem k
  rcases is_conditional_gradient_trajectory_step
      (f := Function.toEReal qA) htraj k with ⟨hpkBall, hpkMinRaw, hstep⟩
  have hgrad : ∇ qA (x k) = -A.toEuclideanLin (x k) :=
    (qA_hasGradientAt A hA (x k)).gradient
  have hgradRaw :
      ∇ (fun y ↦ (Function.toEReal qA y).toReal) (x k) = -A.toEuclideanLin (x k) := by
    change ∇ qA (x k) = -A.toEuclideanLin (x k)
    exact hgrad
  have hpkMin :
      IsMinOn (fun q ↦ inner ℝ q (-A.toEuclideanLin (x k))) B (p k) := by
    rw [hgradRaw] at hpkMinRaw
    exact hpkMinRaw
  have hpkMin' := hpkMin
  rw [isMinOn_iff] at hpkMin'
  -- Nonstationarity upgrades the oracle inequality to strict negativity of the linearized slope.
  have hinner_nonpos : ⟪∇ qA (x k), p k - x k⟫ ≤ 0 := by
    have hcompare :
        inner ℝ (p k) (-A.toEuclideanLin (x k)) ≤
          inner ℝ (x k) (-A.toEuclideanLin (x k)) :=
      hpkMin' (x k) hxkBall
    rw [hgrad]
    simpa [inner_sub_right, real_inner_comm] using sub_nonpos.mpr hcompare
  have hinner_lt : ⟪∇ qA (x k), p k - x k⟫ < 0 := by
    refine lt_of_le_of_ne hinner_nonpos ?_
    intro hzero
    apply hk
    rw [is_stationary_point_on_iff_forall_inner_nonneg]
    refine ⟨(qA_hasGradientAt A hA (x k)).differentiableAt, hxkBall, ?_⟩
    intro y hy
    have hcompare :
        inner ℝ (p k) (-A.toEuclideanLin (x k)) ≤
          inner ℝ y (-A.toEuclideanLin (x k)) :=
      hpkMin' y hy
    have hy_nonneg : 0 ≤ ⟪-A.toEuclideanLin (x k), y - p k⟫ := by
      simpa [inner_sub_right, real_inner_comm] using sub_nonneg.mpr hcompare
    have hdecomp : y - x k = (y - p k) + (p k - x k) := by
      abel
    calc
      ⟪∇ qA (x k), y - x k⟫
          = ⟪-A.toEuclideanLin (x k), y - x k⟫ := by rw [hgrad]
      _ = ⟪-A.toEuclideanLin (x k), y - p k⟫ +
            ⟪-A.toEuclideanLin (x k), p k - x k⟫ := by
              rw [hdecomp, inner_add_right]
      _ = ⟪-A.toEuclideanLin (x k), y - p k⟫ := by rw [hgrad] at hzero; rw [hzero, add_zero]
      _ ≥ 0 := hy_nonneg
  -- Exact line search must choose the endpoint `t_k = 1` because the oracle endpoint is better.
  have hendpoint_lt : qA (p k) < qA (x k) :=
    quadratic_endpoint_lt_initial_of_inner_lt_zero A hA hinner_lt
  have htk_eq : (t k : ℝ) = 1 :=
    exact_line_search_stepsize_eq_one_of_endpoint_improvement
      A hA hxkBall hpkBall (hline k) hendpoint_lt
  have hpk_eq :
      p k = ‖A.toEuclideanLin (x k)‖⁻¹ • A.toEuclideanLin (x k) :=
    argmin_eq_normalized_matrix_image A hA hxkBall hpkArgmin hk
  -- Substitute the endpoint stepsize and the oracle normalization into the trajectory update.
  calc
    x (k + 1) = x k + (t k : ℝ) • (p k - x k) := hstep
    _ = x k + (1 : ℝ) • (p k - x k) := by rw [htk_eq]
    _ = p k := by simp
    _ = ‖A.toEuclideanLin (x k)‖⁻¹ • A.toEuclideanLin (x k) := hpk_eq

end
