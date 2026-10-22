/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace SmoothInterpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A global minimizer of a strongly convex function enjoys the full quadratic
error bound, including when the function itself is not differentiable. -/
theorem strong_minimum_bound {H : E → ℝ} {m : ℝ}
    (hH : StrongConvexOn univ m H) {s : E} (hs : ∀ t, H s ≤ H t) (t : E) :
    H s + m / 2 * ‖t - s‖ ^ 2 ≤ H t := by
  have hstep (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
      m / 2 * ‖t - s‖ ^ 2 ≤ H t - H s + a * (m / 2 * ‖t - s‖ ^ 2) := by
    have hc := hH.2 (mem_univ t) (mem_univ s) ha.le (by linarith : 0 ≤ 1-a)
      (by ring : a + (1-a) = 1)
    have hb := hs (a • t + (1-a) • s)
    simp only [smul_eq_mul] at hc
    nlinarith
  have he : ∀ᶠ a : ℝ in 𝓝[>] 0,
      m / 2 * ‖t - s‖ ^ 2 ≤ H t - H s + a * (m / 2 * ‖t - s‖ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with a ha ha1
    exact hstep a ha ha1
  have hb := ge_of_tendsto (Continuous.tendsto
    (by fun_prop : Continuous (fun a : ℝ ↦ H t - H s + a * (m / 2 * ‖t - s‖ ^ 2))) 0 |>.mono_left nhdsWithin_le_nhds :
    Tendsto (fun a : ℝ ↦ H t - H s + a * (m / 2 * ‖t - s‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (H t - H s + 0 * (m / 2 * ‖t - s‖ ^ 2)))) he
  linarith

/-- The hypotheses used by the finite quadratic conjugate construction. -/
structure QuadraticCore (H : E → ℝ) (m : ℝ) : Prop where
  positive : 0 < m
  continuous : Continuous H
  stronglyConvex : StrongConvexOn univ m H
  zero : H 0 = 0
  lower : ∀ s, m / 2 * ‖s‖ ^ 2 ≤ H s

namespace QuadraticCore

variable {H : E → ℝ} {m : ℝ} (hH : QuadraticCore H m)

include hH

/-- Subtracting a linear functional preserves the strong-convexity modulus. -/
theorem tilt_stronglyConvex (x : E) :
    StrongConvexOn univ m (fun s ↦ H s - ⟪x, s⟫) := by
  refine ⟨convex_univ, ?_⟩
  intro s hs t ht a b ha hb hab
  have hc := hH.stronglyConvex.2 hs ht ha hb hab
  simp only [inner_add_right, inner_smul_right, smul_eq_mul] at *
  linarith

variable [FiniteDimensional ℝ E]

/-- Quadratic coercivity ensures the supremum defining the conjugate is
attained at every dual argument. -/
theorem exists_minimizer (x : E) :
    ∃ s, ∀ t, H s - ⟪x, s⟫ ≤ H t - ⟪x, t⟫ := by
  have hc : Continuous (fun s ↦ H s - ⟪x, s⟫) :=
    hH.continuous.sub (continuous_const.inner continuous_id)
  apply hc.exists_forall_le' 0
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
    (eventually_ge_atTop (2 * ‖x‖ / m))] with s hs
  have hm : 0 < m := hH.positive
  have hs' : 2 * ‖x‖ ≤ ‖s‖ * m := (div_le_iff₀ hm).mp hs
  have hi : ⟪x, s⟫ ≤ ‖x‖ * ‖s‖ := real_inner_le_norm _ _
  have hl := hH.lower s
  simp only [hH.zero, inner_zero_right, sub_zero]
  nlinarith [mul_le_mul_of_nonneg_right hs' (norm_nonneg s)]

/-- The unique maximizing vector for the conjugate. -/
noncomputable def gradient (x : E) : E := (hH.exists_minimizer x).choose

theorem gradient_minimizes (x t : E) :
    H (hH.gradient x) - ⟪x, hH.gradient x⟫ ≤ H t - ⟪x, t⟫ :=
  (hH.exists_minimizer x).choose_spec t

/-- The conjugate is defined by its attained supremum, hence is real valued. -/
noncomputable def conjugate (x : E) : ℝ := ⟪x, hH.gradient x⟫ - H (hH.gradient x)

/-- Strong convexity quantitatively separates the maximizer from all competitors. -/
theorem gradient_bound (x t : E) :
    H (hH.gradient x) - ⟪x, hH.gradient x⟫ + m / 2 * ‖t - hH.gradient x‖ ^ 2
      ≤ H t - ⟪x, t⟫ :=
  strong_minimum_bound (hH.tilt_stronglyConvex x) (hH.gradient_minimizes x) t

/-- Strong monotonicity of the inverse subgradient map. -/
theorem gradient_monotone (x y : E) :
    m * ‖hH.gradient x - hH.gradient y‖ ^ 2 ≤
      ⟪x - y, hH.gradient x - hH.gradient y⟫ := by
  have hx := hH.gradient_bound x (hH.gradient y)
  have hy := hH.gradient_bound y (hH.gradient x)
  rw [norm_sub_rev (hH.gradient y)] at hx
  simp only [inner_sub_left, inner_sub_right]
  linarith

/-- Quantitative Lipschitz bound for the inverse subgradient map. -/
theorem gradient_norm_sub (x y : E) :
    ‖hH.gradient x - hH.gradient y‖ ≤ m⁻¹ * ‖x - y‖ := by
  rw [inv_mul_eq_div, le_div_iff₀ hH.positive]
  have hb := hH.gradient_monotone x y
  have hi := real_inner_le_norm (x-y) (hH.gradient x-hH.gradient y)
  by_cases hz : ‖hH.gradient x - hH.gradient y‖ = 0
  · simp [hz]
  · have hp : 0 < ‖hH.gradient x - hH.gradient y‖ := lt_of_le_of_ne
      (norm_nonneg _) (Ne.symm hz)
    nlinarith

/-- The uniform Lipschitz constant of the conjugate gradient. -/
noncomputable def constant : NNReal := ⟨m⁻¹, inv_nonneg.mpr hH.positive.le⟩

theorem gradient_lipschitz : LipschitzWith hH.constant hH.gradient := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖hH.gradient x-hH.gradient y‖ ≤ m⁻¹ * ‖x-y‖
  exact hH.gradient_norm_sub x y

/-- Every affine term lies below the attained conjugate value. -/
theorem le_conjugate (x t : E) : ⟪x, t⟫ - H t ≤ hH.conjugate x := by
  have hb := hH.gradient_minimizes x t
  dsimp [conjugate]
  linarith

/-- The conjugate's first-order remainder has a uniform quadratic bound. -/
theorem remainder (x y : E) :
    0 ≤ hH.conjugate y - hH.conjugate x - ⟪hH.gradient x, y-x⟫ ∧
    hH.conjugate y - hH.conjugate x - ⟪hH.gradient x, y-x⟫ ≤
      m⁻¹ * ‖y-x‖ ^ 2 := by
  have hx := hH.le_conjugate y (hH.gradient x)
  have hy := hH.le_conjugate x (hH.gradient y)
  have hi := real_inner_le_norm (hH.gradient y-hH.gradient x) (y-x)
  have hl := mul_le_mul_of_nonneg_right (hH.gradient_norm_sub y x) (norm_nonneg (y-x))
  simp only [inner_sub_left, inner_sub_right, real_inner_comm] at hi ⊢
  dsimp [conjugate] at hx hy ⊢
  constructor <;> nlinarith

/-- A quadratic remainder proves differentiability of the conjugate. -/
theorem hasFDerivAt_conjugate (x : E) :
    HasFDerivAt hH.conjugate (innerSL ℝ (hH.gradient x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hm : 0 < m := hH.positive
  filter_upwards [Metric.ball_mem_nhds (0 : E) (mul_pos hε hm)] with t ht
  have ht' : ‖t‖ < ε * m := by simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hb := hH.remainder x (x+t)
  simp only [add_sub_cancel_left] at hb
  change ‖hH.conjugate (x+t) - hH.conjugate x - ⟪hH.gradient x, t⟫‖ ≤ ε * ‖t‖
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  calc
    _ ≤ m⁻¹ * ‖t‖ ^ 2 := hb.2
    _ ≤ ε * ‖t‖ := by
      have ht'' : m⁻¹ * ‖t‖ ≤ ε := by
        rw [inv_mul_eq_div, div_le_iff₀ hm]
        exact ht'.le
      nlinarith [mul_le_mul_of_nonneg_right ht'' (norm_nonneg t)]

/-- Continuity of the derivative gives global continuously differentiable regularity. -/
theorem contDiff_conjugate : ContDiff ℝ 1 hH.conjugate := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ innerSL ℝ (hH.gradient x), ?_, hH.hasFDerivAt_conjugate⟩
  exact (innerSL ℝ).continuous.comp hH.gradient_lipschitz.continuous

/-- The derivative has the same Lipschitz constant as its Riesz representative. -/
theorem fderiv_lipschitz : LipschitzWith hH.constant (fderiv ℝ hH.conjugate) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [(hH.hasFDerivAt_conjugate x).fderiv, (hH.hasFDerivAt_conjugate y).fderiv,
    dist_eq_norm, ← map_sub, innerSL_apply_norm]
  rw [dist_eq_norm]
  change ‖hH.gradient x-hH.gradient y‖ ≤ m⁻¹ * ‖x-y‖
  exact hH.gradient_norm_sub x y

/-- The attained conjugate is convex. -/
theorem convexOn_conjugate : ConvexOn ℝ univ hH.conjugate := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let s := hH.gradient (a • x + b • y)
  have hx' := mul_le_mul_of_nonneg_left (hH.le_conjugate x s) ha
  have hy' := mul_le_mul_of_nonneg_left (hH.le_conjugate y s) hb
  change ⟪a • x+b • y, s⟫ - H s ≤ a • hH.conjugate x + b • hH.conjugate y
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  have hh := congrArg (fun r : ℝ ↦ r * H s) hab
  nlinarith only [hx', hy', hh]

/-- A supplied subgradient pair identifies the unique conjugate maximizer. -/
theorem gradient_eq_of_subgradient {x p : E}
    (hp : ∀ t, H p + ⟪x, t-p⟫ ≤ H t) : hH.gradient x = p := by
  have hb := hH.gradient_bound x p
  have hp' := hp (hH.gradient x)
  simp only [inner_sub_right] at hp'
  have hn : ‖p - hH.gradient x‖ ^ 2 = 0 := by
    have hm := hH.positive
    nlinarith [sq_nonneg ‖p - hH.gradient x‖]
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))).symm

/-- Conjugacy preserves exactly the prescribed value at a subgradient pair. -/
theorem conjugate_eq_of_subgradient {x p : E}
    (hp : ∀ t, H p + ⟪x, t-p⟫ ≤ H t) :
    hH.conjugate x = ⟪x, p⟫ - H p := by
  rw [conjugate, hH.gradient_eq_of_subgradient hp]

theorem gradient_zero : hH.gradient 0 = 0 := by
  apply hH.gradient_eq_of_subgradient
  intro t
  simp only [hH.zero, inner_zero_left, zero_add]
  exact (mul_nonneg (div_nonneg hH.positive.le (by norm_num)) (sq_nonneg _)).trans (hH.lower t)

theorem conjugate_zero : hH.conjugate 0 = 0 := by
  simp only [conjugate, hH.gradient_zero, inner_zero_left, hH.zero, sub_self]

theorem conjugate_nonneg (x : E) : 0 ≤ hH.conjugate x := by
  simpa only [hH.zero, inner_zero_right, sub_self] using hH.le_conjugate x 0

end QuadraticCore

end SmoothInterpolation
