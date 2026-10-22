/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 8.37: a finite `EReal` supremum on a ball forces each point of that
ball into the effective domain and bounds its real value by the real supremum. -/
private lemma mem_effectiveDomain_and_toReal_le_sSup_image_ball
    (f : H → Set.Ioi (⊥ : EReal))
    {x₀ : H} {ρ : ℝ} {u : H}
    (hsup : sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤)
    (hu : u ∈ Metric.ball x₀ ρ) :
    u ∈ effectiveDomain f ∧
      (f u : EReal).toReal ≤
        (sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ)).toReal := by
  -- Image membership places `f u` below the `EReal` supremum of the ball image.
  have hfu_le :
      (f u : EReal) ≤ sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) := by
    exact le_sSup (Set.mem_image_of_mem (fun y ↦ (f y : EReal)) hu)
  have hu_dom : u ∈ effectiveDomain f := by
    -- A value below a finite supremum is itself finite.
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfu_le hsup
  have hfu_bot : (f u : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f u : EReal) from (f u).2)
  have hsup_ne_top :
      sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) ≠ ⊤ := ne_of_lt hsup
  refine ⟨hu_dom, ?_⟩
  -- `toReal` preserves the comparison against the finite supremum.
  simpa using EReal.toReal_le_toReal hfu_le hfu_bot hsup_ne_top

/-- Helper for Proposition 8.37: the finite weighted sum of two effective-domain values is the cast
of the corresponding real weighted sum of their `toReal` values. -/
private lemma weighted_value_sum_eq_coe_two_points
    (f : H → Set.Ioi (⊥ : EReal))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (α : ℝ) :
    (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) =
      ((α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal : ℝ) : EReal) := by
  -- Effective-domain membership lets us rewrite both endpoint values as real casts.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  rw [← EReal.coe_toReal hx_top hx_bot,
    show (1 - α : EReal) = ((1 - α : ℝ) : EReal) by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub],
    ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  simp

/-- Helper for Proposition 8.37: Jensen's inequality on the effective domain becomes the analogous
real inequality after applying `toReal`. -/
private lemma toReal_le_of_convexOn_ineq
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal).toReal ≤
      α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal := by
  -- Start from the stored `EReal` Jensen inequality on the effective domain.
  have hineq :
      (f (α • x + (1 - α) • y) : EReal) ≤
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) :=
    hconv.ineq hx hy hα0 hα1
  have hsum_lt_top :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) < ⊤ := by
    rw [weighted_value_sum_eq_coe_two_points f hx hy α]
    exact EReal.coe_lt_top _
  have hleft_bot :
      (f (α • x + (1 - α) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (α • x + (1 - α) • y) : EReal) from
      (f (α • x + (1 - α) • y)).2)
  have hsum_ne_top :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ :=
    ne_of_lt hsum_lt_top
  have htoReal :=
    EReal.toReal_le_toReal hineq hleft_bot hsum_ne_top
  -- Rewrite the finite right-hand side back to an ordinary real convex combination.
  rw [weighted_value_sum_eq_coe_two_points f hx hy α] at htoReal
  simpa using htoReal

-- Proof sketch: write each point of the smaller ball as a convex combination of the center and a
-- point of the larger ball, use convexity to bound `f x - f x₀`, repeat with the roles reversed,
-- and use the finite supremum on the larger ball to control both inequalities.
/-- Proposition 8.37 (1): if a convex `]-∞,+∞]`-valued function has finite supremum on
`Metric.ball x₀ ρ`, then on the smaller ball `Metric.ball x₀ (α * ρ)` its finite real values differ
from the value at `x₀` by at most `α` times the gap between that supremum and `f x₀`. -/
theorem oscillation_bound_on_smaller_ball
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H} {ρ : ℝ} (hρ : 0 < ρ)
    (hx₀ : x₀ ∈ effectiveDomain f)
    (hsup : sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {x : H} (hx : x ∈ Metric.ball x₀ (α * ρ)) (hx_dom : x ∈ effectiveDomain f) :
    |((f x : EReal).toReal - (f x₀ : EReal).toReal)| ≤
      α * ((sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ)).toReal -
        (f x₀ : EReal).toReal) := by
  let η : EReal := sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x₀ ρ)
  let u : H := x₀ + α⁻¹ • (x - x₀)
  let v : H := x₀ + α⁻¹ • (x₀ - x)
  let γ : ℝ := 1 / (1 + α)
  have hx₀_ball : x₀ ∈ Metric.ball x₀ ρ := Metric.mem_ball_self hρ
  have hx_norm : ‖x - x₀‖ < α * ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hu_ball : u ∈ Metric.ball x₀ ρ := by
    -- The rescaled point `u` lies on the ray from `x₀` through `x` at radius `ρ`.
    rw [Metric.mem_ball, dist_eq_norm]
    have hu_sub : u - x₀ = α⁻¹ • (x - x₀) := by
      dsimp [u]
      abel_nf
    rw [hu_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hα0.le)]
    have hscale :
        α⁻¹ * ‖x - x₀‖ < α⁻¹ * (α * ρ) :=
      mul_lt_mul_of_pos_left hx_norm (inv_pos.mpr hα0)
    calc
      α⁻¹ * ‖x - x₀‖ < α⁻¹ * (α * ρ) := hscale
      _ = ρ := by
        field_simp [hα0.ne']
  have hv_ball : v ∈ Metric.ball x₀ ρ := by
    -- The reflected rescaled point `v` lies on the opposite ray at the same radius.
    rw [Metric.mem_ball, dist_eq_norm]
    have hv_sub : v - x₀ = α⁻¹ • (x₀ - x) := by
      dsimp [v]
      abel_nf
    rw [hv_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hα0.le)]
    have hscale :
        α⁻¹ * ‖x₀ - x‖ < α⁻¹ * (α * ρ) := by
      simpa [norm_sub_rev] using mul_lt_mul_of_pos_left hx_norm (inv_pos.mpr hα0)
    calc
      α⁻¹ * ‖x₀ - x‖ < α⁻¹ * (α * ρ) := hscale
      _ = ρ := by
        field_simp [hα0.ne']
  rcases mem_effectiveDomain_and_toReal_le_sSup_image_ball f hsup hu_ball with ⟨hu_dom, hu_le⟩
  rcases mem_effectiveDomain_and_toReal_le_sSup_image_ball f hsup hv_ball with ⟨hv_dom, hv_le⟩
  have hu_le' : (f u : EReal).toReal ≤ η.toReal := by
    simpa [η] using hu_le
  have hv_le' : (f v : EReal).toReal ≤ η.toReal := by
    simpa [η] using hv_le
  have hu_eq : x = α • u + (1 - α) • x₀ := by
    -- This is the textbook decomposition of `x` toward the boundary point `u`.
    have hu_eq' : α • u + (1 - α) • x₀ = x := by
      dsimp [u]
      rw [smul_add, smul_smul]
      have hαinv : α * α⁻¹ = 1 := by
        field_simp [hα0.ne']
      rw [hαinv, one_smul]
      module
    exact hu_eq'.symm
  have hγ0 : 0 < γ := by
    dsimp [γ]
    positivity
  have hγ1 : γ < 1 := by
    have hγ_mul : γ * (1 + α) = 1 := by
      have h1α_ne : 1 + α ≠ 0 := by linarith
      dsimp [γ]
      field_simp [h1α_ne]
    nlinarith [hγ0, hγ_mul, hα0]
  have h1_sub_γ : 1 - γ = α / (1 + α) := by
    dsimp [γ]
    field_simp [hα0.ne']
    ring
  have hx₀_eq : x₀ = γ • x + (1 - γ) • v := by
    -- This is the reflected decomposition used to bound `f x₀ - f x`.
    have hcoeff : (α / (1 + α)) * α⁻¹ = 1 / (1 + α) := by
      field_simp [hα0.ne']
    have hsum : α / (1 + α) + 1 / (1 + α) = 1 := by
      field_simp [hα0.ne']
      ring
    have hx₀_eq' : γ • x + (1 - γ) • v = x₀ := by
      rw [h1_sub_γ]
      dsimp [γ, v]
      rw [smul_add, smul_smul, hcoeff, smul_sub]
      calc
        (1 / (1 + α)) • x + ((α / (1 + α)) • x₀ + ((1 / (1 + α)) • x₀ - (1 / (1 + α)) • x))
            = ((α / (1 + α) + 1 / (1 + α)) • x₀) +
                ((1 / (1 + α) - 1 / (1 + α)) • x) := by
                  module
        _ = x₀ := by
            rw [hsum]
            simp
    exact hx₀_eq'.symm
  have hforward :
      (f x : EReal).toReal - (f x₀ : EReal).toReal ≤
        α * (η.toReal - (f x₀ : EReal).toReal) := by
    -- Convexity at `x = α • u + (1 - α) • x₀` gives the forward gap estimate.
    have hconv_real :
        (f x : EReal).toReal ≤
          α * (f u : EReal).toReal + (1 - α) * (f x₀ : EReal).toReal := by
      simpa [hu_eq] using toReal_le_of_convexOn_ineq f hconv hu_dom hx₀ hα0 hα1
    nlinarith [hconv_real, hu_le']
  have hbackward :
      (f x₀ : EReal).toReal - (f x : EReal).toReal ≤
        α * (η.toReal - (f x₀ : EReal).toReal) := by
    -- Apply the same convexity estimate to the reflected decomposition of `x₀`.
    have hconv_real :
        (f x₀ : EReal).toReal ≤
          γ * (f x : EReal).toReal + (1 - γ) * (f v : EReal).toReal := by
      simpa [hx₀_eq] using toReal_le_of_convexOn_ineq f hconv hx_dom hv_dom hγ0 hγ1
    have hbackward_upper :
        (f x₀ : EReal).toReal ≤ γ * (f x : EReal).toReal + (1 - γ) * η.toReal := by
      nlinarith [hconv_real, hv_le']
    rw [show γ = 1 / (1 + α) by rfl, h1_sub_γ] at hbackward_upper
    have h1α_pos : 0 < 1 + α := by
      linarith
    have hmul :
        (1 + α) * (f x₀ : EReal).toReal ≤ (f x : EReal).toReal + α * η.toReal := by
      calc
        (1 + α) * (f x₀ : EReal).toReal
            ≤ (1 + α) * (1 / (1 + α) * (f x : EReal).toReal + α / (1 + α) * η.toReal) := by
                exact mul_le_mul_of_nonneg_left hbackward_upper (le_of_lt h1α_pos)
        _ = (f x : EReal).toReal + α * η.toReal := by
            field_simp [h1α_pos.ne']
    nlinarith [hmul]
  -- Combine the two signed bounds into the required absolute-value estimate.
  refine abs_le.mpr ?_
  constructor
  · linarith
  · exact hforward

/-- Helper for Proposition 8.37: two real values taken on the doubled ball differ by at most the
diameter of the doubled-ball image. -/
private lemma point_gap_le_diam_of_mem_real_image_ball
    (f : H → Set.Ioi (⊥ : EReal))
    {x₀ : H} {ρ : ℝ}
    (hbounded : Bornology.IsBounded
      (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ))
    {u v : H} (hu : u ∈ Metric.ball x₀ (2 * ρ)) (hv : v ∈ Metric.ball x₀ (2 * ρ)) :
    (f u : EReal).toReal - (f v : EReal).toReal ≤
      Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) := by
  let s : Set ℝ := (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ)
  have hu_image : (f u : EReal).toReal ∈ s := by
    exact Set.mem_image_of_mem (fun z ↦ (f z : EReal).toReal) hu
  have hv_image : (f v : EReal).toReal ∈ s := by
    exact Set.mem_image_of_mem (fun z ↦ (f z : EReal).toReal) hv
  have hdist :
      dist (f u : EReal).toReal (f v : EReal).toReal ≤ Metric.diam s :=
    Metric.dist_le_diam_of_mem hbounded hu_image hv_image
  -- The diameter controls the real distance, hence each signed gap.
  calc
    (f u : EReal).toReal - (f v : EReal).toReal
        ≤ dist (f u : EReal).toReal (f v : EReal).toReal := by
          simpa [Real.dist_eq] using
            (le_abs_self ((f u : EReal).toReal - (f v : EReal).toReal))
    _ ≤ Metric.diam s := hdist
    _ = Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) := by
          rfl

/-- Helper for Proposition 8.37: the textbook extrapolation point gives the one-sided Lipschitz
estimate on the smaller ball. -/
private lemma forward_gap_le_lipschitz_rhs
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H} {ρ : ℝ} (hρ : 0 < ρ)
    (hball_dom : Metric.ball x₀ (2 * ρ) ⊆ effectiveDomain f)
    (hbounded : Bornology.IsBounded
      (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ))
    {x y : H} (hx : x ∈ Metric.ball x₀ ρ) (hy : y ∈ Metric.ball x₀ ρ)
    (hy_dom : y ∈ effectiveDomain f) (hxy : x ≠ y) :
    (f x : EReal).toReal - (f y : EReal).toReal ≤
      (Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) / ρ) *
        ‖x - y‖ := by
  let d : ℝ := ‖x - y‖
  let α : ℝ := d / (d + ρ)
  let z : H := x + ((1 / α) - 1) • (x - y)
  have hd_pos : 0 < d := by
    dsimp [d]
    simpa [norm_pos_iff] using sub_ne_zero.mpr hxy
  have hd_nonneg : 0 ≤ d := le_of_lt hd_pos
  have hα0 : 0 < α := by
    dsimp [α]
    positivity
  have hα1 : α < 1 := by
    -- The extrapolation coefficient lies strictly between `0` and `1`.
    dsimp [α]
    have hsum_pos : 0 < d + ρ := by
      linarith
    refine (div_lt_one hsum_pos).2 ?_
    linarith
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hα_ne : α ≠ 0 := ne_of_gt hα0
  have hαmul : α * ((1 / α) - 1) = 1 - α := by
    field_simp [hα_ne]
  have hcoeff_mul : ((1 / α) - 1) * d = ρ := by
    dsimp [α]
    field_simp [hd_ne, hρ.ne']
    ring
  have hα_le : α ≤ d / ρ := by
    -- The textbook coefficient is dominated by the normalized displacement.
    dsimp [α]
    exact div_le_div_of_nonneg_left hd_nonneg hρ (by linarith)
  have hcoeff_nonneg : 0 ≤ (1 / α) - 1 := by
    by_contra hneg
    have hmul_nonpos : ((1 / α) - 1) * d ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hneg)) hd_nonneg
    linarith [hcoeff_mul]
  have hz_sub : z - x = ((1 / α) - 1) • (x - y) := by
    dsimp [z]
    abel_nf
  have hdist_zx : dist z x = ρ := by
    -- The extrapolated point is placed exactly one radius beyond `x`.
    rw [dist_eq_norm, hz_sub, norm_smul, Real.norm_of_nonneg hcoeff_nonneg]
    simpa [d] using hcoeff_mul
  have hy_double : y ∈ Metric.ball x₀ (2 * ρ) := by
    -- Every point of the small ball lies in the doubled ball.
    rw [Metric.mem_ball] at hy ⊢
    linarith
  have hz_double : z ∈ Metric.ball x₀ (2 * ρ) := by
    -- The exact `ρ`-step from `x` keeps `z` inside the doubled ball.
    rw [Metric.mem_ball] at hx ⊢
    have htriangle := dist_triangle z x x₀
    have hdist_zx_le : dist z x ≤ ρ := le_of_eq hdist_zx
    linarith
  have hz_dom : z ∈ effectiveDomain f := hball_dom hz_double
  have hx_decomp : x = α • z + (1 - α) • y := by
    -- This is the textbook convex decomposition of `x`.
    have hx_decomp' : α • z + (1 - α) • y = x := by
      dsimp [z]
      rw [smul_add, smul_smul, hαmul, smul_sub]
      module
    exact hx_decomp'.symm
  have hconv_real :
      (f x : EReal).toReal ≤
        α * (f z : EReal).toReal + (1 - α) * (f y : EReal).toReal := by
    -- Convexity on the effective domain gives the Jensen estimate at `x = α z + (1 - α) y`.
    simpa [hx_decomp] using toReal_le_of_convexOn_ineq f hconv hz_dom hy_dom hα0 hα1
  have hgap_diam :
      (f z : EReal).toReal - (f y : EReal).toReal ≤
        Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) := by
    simpa using point_gap_le_diam_of_mem_real_image_ball f hbounded hz_double hy_double
  have hforward :
      (f x : EReal).toReal - (f y : EReal).toReal ≤
        α * Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) := by
    -- First bound the forward gap by the oscillation between `z` and `y`.
    have hstep :
        (f x : EReal).toReal - (f y : EReal).toReal ≤
          α * ((f z : EReal).toReal - (f y : EReal).toReal) := by
      nlinarith [hconv_real]
    exact le_trans hstep (mul_le_mul_of_nonneg_left hgap_diam hα0.le)
  have hdiam_nonneg :
      0 ≤ Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) :=
    Metric.diam_nonneg
  have hscale :
      α * Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) ≤
        (Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) / ρ) *
          d := by
    -- The scalar estimate on `α` turns the oscillation bound into the Lipschitz constant.
    have hmul :
        α * Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) ≤
          (d / ρ) * Metric.diam
            (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) := by
      exact mul_le_mul_of_nonneg_right hα_le hdiam_nonneg
    simpa [d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact le_trans hforward hscale

/-- Helper for Proposition 8.37: matching one-sided bounds on `a - b` and `b - a` give an
absolute-value bound. -/
private lemma abs_sub_le_of_two_sided_bound {a b L : ℝ}
    (hforward : a - b ≤ L) (hbackward : b - a ≤ L) :
    |a - b| ≤ L := by
  -- Convert the reverse signed estimate into the lower bound required by `abs_le`.
  refine abs_le.mpr ?_
  constructor
  · linarith
  · exact hforward

/-- Helper for Proposition 8.37: swapping the arguments in the extrapolation estimate gives the
reverse signed gap with the same Lipschitz right-hand side. -/
private lemma backward_gap_le_lipschitz_rhs
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H} {ρ : ℝ} (hρ : 0 < ρ)
    (hball_dom : Metric.ball x₀ (2 * ρ) ⊆ effectiveDomain f)
    (hbounded : Bornology.IsBounded
      (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ))
    {x y : H} (hx : x ∈ Metric.ball x₀ ρ) (hy : y ∈ Metric.ball x₀ ρ)
    (hx_dom : x ∈ effectiveDomain f)
    (hxy : x ≠ y) :
    (f y : EReal).toReal - (f x : EReal).toReal ≤
      (Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) / ρ) *
        ‖x - y‖ := by
  -- Reuse the forward estimate after swapping `x` and `y`.
  have hbackward :
      (f y : EReal).toReal - (f x : EReal).toReal ≤
        (Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) / ρ) *
          ‖y - x‖ := by
    exact forward_gap_le_lipschitz_rhs f hconv hρ hball_dom hbounded hy hx hx_dom
      (fun hyx ↦ hxy hyx.symm)
  -- The ambient norm is symmetric, so the right-hand side matches the forward one.
  simpa [norm_sub_rev] using hbackward

-- Proof sketch: for `x ≠ y`, write `x` as a convex combination of `y` and a point `z` at distance
-- `ρ` from `x` in the direction `x - y`; then `y, z ∈ Metric.ball x₀ (2 * ρ)`, convexity bounds
-- `f x - f y` by a fraction of the oscillation on that larger ball, and swapping `x` and `y`
-- yields the absolute-value estimate.
/-- Proposition 8.37 (2): if a convex `]-∞,+∞]`-valued function is finite on
`Metric.ball x₀ (2 * ρ)` and its real values there have bounded diameter, then it is Lipschitz on
`Metric.ball x₀ ρ` with constant
`Metric.diam ((fun y ↦ (f y : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) / ρ`. -/
theorem lipschitz_bound_on_ball_of_bounded_image
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H} {ρ : ℝ} (hρ : 0 < ρ)
    (hx₀ : x₀ ∈ effectiveDomain f)
    (hball_dom : Metric.ball x₀ (2 * ρ) ⊆ effectiveDomain f)
    (hbounded : Bornology.IsBounded
      (((fun y ↦ (f y : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ))
    {x y : H} (hx : x ∈ Metric.ball x₀ ρ) (hy : y ∈ Metric.ball x₀ ρ)
    (hx_dom : x ∈ effectiveDomain f) (hy_dom : y ∈ effectiveDomain f) :
    |((f x : EReal).toReal - (f y : EReal).toReal)| ≤
      (Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) / ρ) *
        ‖x - y‖ := by
  -- Keep the textbook center-domain hypothesis available in the repaired statement.
  let _hx₀ : x₀ ∈ effectiveDomain f := hx₀
  -- Route correction: boundedness of the `toReal` image alone was too weak; the repaired proof
  -- uses `hball_dom` to keep the extrapolated point inside the effective domain.
  by_cases hxy : x = y
  · subst hxy
    simp
  have hforward :
      (f x : EReal).toReal - (f y : EReal).toReal ≤
        (Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) / ρ) *
          ‖x - y‖ := by
    -- Apply the one-sided extrapolation estimate in the forward direction.
    exact forward_gap_le_lipschitz_rhs f hconv hρ hball_dom hbounded hx hy hy_dom hxy
  have hbackward :
      (f y : EReal).toReal - (f x : EReal).toReal ≤
        (Metric.diam (((fun z ↦ (f z : EReal).toReal) '' Metric.ball x₀ (2 * ρ)) : Set ℝ) / ρ) *
          ‖x - y‖ := by
    -- The backward helper packages the swapped extrapolation step and norm symmetry.
    exact backward_gap_le_lipschitz_rhs f hconv hρ hball_dom hbounded hx hy hx_dom hxy
  -- The two one-sided inequalities combine into the absolute-value estimate.
  exact abs_sub_le_of_two_sided_bound hforward hbackward

end ERealFunction
