/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.OneSidedDirectionalDeriv

noncomputable section

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "DualPoint" => StrongDual ℝ X

/-
Domain sampling:
* primary domain: convex and nonsmooth analysis on real normed spaces
* inspected canonical owners in the minimal closure:
  `oneSidedDirectionalDeriv`,
  `clarkeDirectionalDeriv`,
  `clarkeDirectionalDeriv_toReal_of_locallyLipschitzAt`,
  `LocallyLipschitzAt`,
  `clarkeDifferential`
* source/core/bridge triage:
  - source-facing owner kept here: `subdifferential`
  - core/canonical owners reused here: `oneSidedDirectionalDeriv`,
    `clarkeDirectionalDeriv`, `clarkeDifferential`
  - bridge/view layer here: the comparison lemmas relating the convex subdifferential and the
    one-sided directional derivative to the Clarke owners via the canonical `toReal` bridge
* primitive data vs derived API:
  - primitive data: the convex subdifferential set `subdifferential f x`
  - derived API: its membership lemma and the two comparison lemmas below
-/

/-- The convex-analytic subdifferential `∂ f(x)` of `f` at `x` is the set of continuous linear
functionals `ξ` satisfying `f y ≥ f x + ξ (y - x)` for every `y`. -/
def subdifferential (f : X → ℝ) (x : X) : Set DualPoint :=
  {ξ | ∀ y : X, f y ≥ f x + ξ (y - x)}

scoped[Subgradient] notation:100 "∂ " f:arg x:arg => subdifferential f x

open scoped Subgradient ClarkeDirectionalDerivative ClarkeDifferential

/-- Membership in `∂ f(x)` is exactly the affine-support inequality
`f y ≥ f x + ξ (y - x)` for all `y`. -/
theorem mem_subdifferential_iff
    (f : X → ℝ) (x : X) (ξ : DualPoint) :
    ξ ∈ ∂ f x ↔
      ∀ y : X, f y ≥ f x + ξ (y - x) := Iff.rfl

/-- Helper for Chapter14 Lemma 14.1.6: restricting a convex function to the affine ray
`t ↦ x + t • d` preserves convexity on `Set.univ`. -/
lemma convexOn_along_ray
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun t : ℝ ↦ f (x + t • d)) := by
  have hray :
      (fun t : ℝ ↦ f (x + t • d)) =
        f ∘ AffineMap.lineMap (k := ℝ) x (x + d) := by
    funext t
    simp [Function.comp, AffineMap.lineMap_apply_module', sub_eq_add_neg,
      add_assoc, add_comm]
  -- Convexity is stable under precomposition with affine maps.
  simpa [hray] using (h_convex.comp_affineMap (AffineMap.lineMap (k := ℝ) x (x + d)))

/-- Helper for Chapter14 Lemma 14.1.6: for a convex function, the secant quotient along a fixed
ray is monotone in the positive time parameter. -/
lemma convex_secantQuotient_monotone_along_ray
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f) :
    MonotoneOn (fun t : ℝ ↦ (f (x + t • d) - f x) / t) (Set.Ioi 0) := by
  let g : ℝ → ℝ := fun t ↦ f (x + t • d)
  have hg_convex : ConvexOn ℝ Set.univ g :=
    convexOn_along_ray f x d h_convex
  intro s hs t ht hst
  have hs' : s ∈ {y : ℝ | y ∈ Set.univ ∧ 0 < y} := by simpa [Set.Ioi] using hs
  have ht' : t ∈ {y : ℝ | y ∈ Set.univ ∧ 0 < y} := by simpa [Set.Ioi] using ht
  -- The scalar convex-derivative API says exactly that the secant slopes from `0` increase.
  have hmono :=
    hg_convex.monotoneOn_slope_gt (x := 0) (by simp : (0 : ℝ) ∈ Set.univ) hs' ht' hst
  simpa [g, slope_def_field] using hmono

/-- Helper for Chapter14 Lemma 14.1.6: convexity along the ray through `x` in direction `d`
produces the right directional derivative at `x`. -/
lemma convex_hasOneSidedDirectionalDerivAt_along_ray
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f) :
    HasOneSidedDirectionalDerivAt f (oneSidedDirectionalDeriv f x d) x d := by
  let g : ℝ → ℝ := fun t ↦ f (x + t • d)
  have hg_convex : ConvexOn ℝ Set.univ g :=
    convexOn_along_ray f x d h_convex
  have hg_Ioi :
      HasDerivWithinAt g (derivWithin g (Set.Ioi 0) 0) (Set.Ioi 0) 0 :=
    hg_convex.hasDerivWithinAt_rightDeriv_of_mem_interior (x := 0) (by simp)
  have hg_Ici :
      HasDerivWithinAt g (derivWithin g (Set.Ici 0) 0) (Set.Ici 0) 0 := by
    -- Move the right derivative from `Ioi` to the chapter owner `Ici`.
    rw [← derivWithin_Ioi_eq_Ici g 0]
    exact hg_Ioi.Ici_of_Ioi
  simpa [HasOneSidedDirectionalDerivAt, oneSidedDirectionalDeriv, g] using hg_Ici

/-- Helper for Chapter14 Lemma 14.1.6: the convex right directional derivative at `x` is bounded
above by every positive secant quotient along the ray `x + t • d`. -/
lemma oneSidedDirectionalDeriv_le_secant_along_ray_of_convexOn
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    {t : ℝ}
    (ht : 0 < t) :
    oneSidedDirectionalDeriv f x d ≤ (f (x + t • d) - f x) / t := by
  let g : ℝ → ℝ := fun s ↦ f (x + s • d)
  have hg_convex : ConvexOn ℝ Set.univ g :=
    convexOn_along_ray f x d h_convex
  have hbound :
      derivWithin g (Set.Ioi 0) 0 ≤ slope g 0 t :=
    hg_convex.rightDeriv_le_slope_of_mem_interior (x := 0) (by simp) (by simp) ht
  -- Rewrite the scalar right-derivative estimate back to the ray quotient.
  simpa [oneSidedDirectionalDeriv, g, slope_def_field, derivWithin_Ioi_eq_Ici] using hbound

/-- Helper for Chapter14 Lemma 14.1.6: for a convex function, subgradient membership is
equivalent to domination by the one-sided directional derivative in every direction. -/
lemma mem_subdifferential_iff_le_oneSidedDirectionalDeriv_of_convexOn
    (f : X → ℝ)
    (x : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    (ξ : DualPoint) :
    ξ ∈ ∂ f x ↔ ∀ d : X, ξ d ≤ oneSidedDirectionalDeriv f x d := by
  constructor
  · intro hξ d
    let g : ℝ → ℝ := fun t ↦ f (x + t • d)
    have hg_convex : ConvexOn ℝ Set.univ g :=
      convexOn_along_ray f x d h_convex
    have hone :
        oneSidedDirectionalDeriv f x d = sInf (slope g 0 '' Set.Ioi 0) := by
      -- Identify the one-sided derivative with the infimum of positive secant slopes.
      calc
        oneSidedDirectionalDeriv f x d = derivWithin g (Set.Ici 0) 0 := rfl
        _ = derivWithin g (Set.Ioi 0) 0 := by
          symm
          exact derivWithin_Ioi_eq_Ici g 0
        _ = sInf (slope g 0 '' {y : ℝ | y ∈ Set.univ ∧ 0 < y}) := by
          exact hg_convex.rightDeriv_eq_sInf_slope_of_mem_interior (x := 0) (by simp)
        _ = sInf (slope g 0 '' Set.Ioi 0) := by
          congr 1
          ext t
          simp [Set.Ioi]
    have hξ_le :
        ξ d ≤ sInf (slope g 0 '' Set.Ioi 0) := by
      -- Every positive secant slope dominates the subgradient evaluation, so the infimum does too.
      refine le_csInf ?_ ?_
      · simpa [Set.Ioi] using
          Set.Nonempty.image (f := slope g 0) (by exact Set.nonempty_Ioi)
      · rintro _ ⟨t, ht, rfl⟩
        have ht_pos : 0 < t := ht
        have hsupport :
            f (x + t • d) ≥ f x + t * ξ d := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, map_smul] using
            (mem_subdifferential_iff f x ξ).1 hξ (x + t • d)
        have hsupport' : t * ξ d ≤ f (x + t • d) - f x := by
          linarith
        have hquot : ξ d ≤ (f (x + t • d) - f x) / t := by
          exact (le_div_iff₀ ht_pos).2 (by simpa [mul_comm] using hsupport')
        simpa [g, slope_def_field, ht_pos.ne'] using hquot
    simpa [hone] using hξ_le
  · intro hξ
    rw [mem_subdifferential_iff]
    intro y
    let d : X := y - x
    have hdir : ξ d ≤ oneSidedDirectionalDeriv f x d := hξ d
    have hsecant :
        oneSidedDirectionalDeriv f x d ≤ (f (x + (1 : ℝ) • d) - f x) / (1 : ℝ) :=
      oneSidedDirectionalDeriv_le_secant_along_ray_of_convexOn f x d h_convex zero_lt_one
    have hquot : ξ d ≤ f y - f x := by
      calc
        ξ d ≤ oneSidedDirectionalDeriv f x d := hdir
        _ ≤ (f (x + (1 : ℝ) • d) - f x) / (1 : ℝ) := hsecant
        _ = f y - f x := by
          simp [d]
    -- Evaluate the secant estimate at `t = 1` and expand `d = y - x`.
    have hy' : ξ (y - x) ≤ f y - f x := by
      simpa [d] using hquot
    linarith

/-- Helper for Chapter14 Lemma 14.1.6: if a convex ray derivative is strictly below a cutoff
`b`, then every sufficiently small positive fixed-base secant quotient along that ray is also at
most `b`. -/
lemma eventually_secantQuotient_le_of_lt_oneSidedDirectionalDeriv
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    {b : ℝ}
    (hb : oneSidedDirectionalDeriv f x d < b) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ s : ℝ, 0 < s → s ≤ ρ → (f (x + s • d) - f x) / s ≤ b := by
  let g : ℝ → ℝ := fun s ↦ f (x + s • d)
  have hderiv :
      HasDerivWithinAt g (oneSidedDirectionalDeriv f x d) (Set.Ici 0) 0 :=
    convex_hasOneSidedDirectionalDerivAt_along_ray f x d h_convex
  have hslope :
      Filter.Tendsto (slope g 0) (nhdsWithin (0 : ℝ) (Set.Ici 0 \ ({0} : Set ℝ)))
        (nhds (oneSidedDirectionalDeriv f x d)) :=
    (hasDerivWithinAt_iff_tendsto_slope).1 hderiv
  have hlt :
      ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), (f (x + s • d) - f x) / s < b := by
    -- The right derivative controls nearby positive secant slopes.
    have hlt' :
        ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ici 0 \ ({0} : Set ℝ)), slope g 0 s < b :=
      hslope.eventually (Iio_mem_nhds hb)
    simpa [g, slope_def_field] using hlt'
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hlt with ⟨u, hu, hu_sub⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨r, hr_pos, hr_sub⟩
  refine ⟨r / 2, by linarith, ?_⟩
  intro s hs hs_le
  have hs_mem_ball : s ∈ Metric.ball (0 : ℝ) r := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hs.le] using show s < r by linarith
  have hs_mem_u : s ∈ u := hr_sub hs_mem_ball
  have hs_lt : (f (x + s • d) - f x) / s < b := hu_sub ⟨hs_mem_u, hs⟩
  exact hs_lt.le

/-- Helper for Chapter14 Lemma 14.1.6: on a common closed-ball Lipschitz neighborhood, a moving
base secant quotient is bounded by the fixed-base secant quotient plus the textbook error
`2 K δ` once `dist y x ≤ δ s`. -/
lemma secantQuotient_le_fixedBase_add_of_closedBallLipschitz
    (f : X → ℝ)
    (x y d : X)
    (K : NNReal)
    {eps s δ : ℝ}
    (hs : 0 < s)
    (hK : LipschitzOnWith K f (Metric.closedBall x eps))
    (hy : y ∈ Metric.closedBall x eps)
    (hy_step : y + s • d ∈ Metric.closedBall x eps)
    (hx_step : x + s • d ∈ Metric.closedBall x eps)
    (hδ : dist y x ≤ δ * s) :
    (f (y + s • d) - f y) / s ≤
      (f (x + s • d) - f x) / s + 2 * (K : ℝ) * δ := by
  have hε_nonneg : 0 ≤ eps := by
    exact le_trans dist_nonneg (Metric.mem_closedBall.mp hy)
  have hx : x ∈ Metric.closedBall x eps := by
    exact Metric.mem_closedBall.2 (by simpa using hε_nonneg)
  have hstep_le :
      f (y + s • d) ≤ f (x + s • d) + (K : ℝ) * dist y x :=
    by
      simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hK.le_add_mul hy_step hx_step
  have hbase_le :
      f x ≤ f y + (K : ℝ) * dist y x := by
    simpa [dist_comm] using hK.le_add_mul hx hy
  have hnum :
      f (y + s • d) - f y ≤
        f (x + s • d) - f x + 2 * (K : ℝ) * dist y x := by
    linarith
  have hnum' :
      f (y + s • d) - f y ≤
        f (x + s • d) - f x + 2 * (K : ℝ) * δ * s := by
    have hdist :
        2 * (K : ℝ) * dist y x ≤ 2 * (K : ℝ) * δ * s := by
      have hmul :
          (2 * (K : ℝ)) * dist y x ≤ (2 * (K : ℝ)) * (δ * s) :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    linarith
  -- Multiply the target inequality by the positive common denominator `s`.
  have hmul :
      f (y + s • d) - f y ≤
        s * ((f (x + s • d) - f x) / s + 2 * (K : ℝ) * δ) := by
    calc
      f (y + s • d) - f y ≤ f (x + s • d) - f x + 2 * (K : ℝ) * δ * s := hnum'
      _ = s * ((f (x + s • d) - f x) / s + 2 * (K : ℝ) * δ) := by
        symm
        field_simp [hs.ne']
  exact (div_le_iff₀ hs).2 (by simpa [mul_comm] using hmul)

/-- Helper for Chapter14 Lemma 14.1.6: if `b` is strictly above the convex one-sided directional
derivative, then every sufficiently small Clarke quotient is at most `b`. This packages the
source proof's frozen-endpoint-time argument at the product-filter level. -/
lemma clarkeQuotient_eventually_le_of_lt_oneSidedDirectionalDeriv_of_convexOn_of_closedBallLipschitz
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    (K : NNReal)
    {eps b : ℝ}
    (hε : 0 < eps)
    (hK : LipschitzOnWith K f (Metric.closedBall x eps))
    (hb : oneSidedDirectionalDeriv f x d < b) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {p : X × ℝ}, p ∈ Metric.closedBall ((x : X), (0 : ℝ)) ρ → 0 < p.2 →
        (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal) ≤ (b : EReal) := by
  obtain ⟨c, hltc, hcb⟩ := exists_between hb
  let δ : ℝ := (b - c) / (4 * ((K : ℝ) + 1))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_bound : c + 2 * (K : ℝ) * δ < b := by
    have hscale_pos : 0 < 4 * ((K : ℝ) + 1) := by positivity
    have hscaled :
        (4 * ((K : ℝ) + 1)) * (c + 2 * (K : ℝ) * δ) <
          (4 * ((K : ℝ) + 1)) * b := by
      dsimp [δ]
      field_simp [hscale_pos.ne']
      nlinarith [hcb, K.2]
    exact (lt_of_mul_lt_mul_left hscaled hscale_pos.le)
  obtain ⟨ρ0, hρ0_pos, hρ0⟩ :=
    eventually_secantQuotient_le_of_lt_oneSidedDirectionalDeriv f x d h_convex hltc
  let s0 : ℝ := min ρ0 (eps / (δ + ‖d‖ + 1))
  have hs0_pos : 0 < s0 := by
    dsimp [s0]
    positivity
  have hs0_le_ρ0 : s0 ≤ ρ0 := min_le_left _ _
  have hs0_le_eps : s0 ≤ eps / (δ + ‖d‖ + 1) := min_le_right _ _
  have hfixed :
      (f (x + s0 • d) - f x) / s0 ≤ c :=
    hρ0 s0 hs0_pos hs0_le_ρ0
  let ρ : ℝ := min s0 (δ * s0)
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  refine ⟨ρ, hρ_pos, ?_⟩
  intro p hp_ball hp2
  have hp_coords :
      dist p.1 x ≤ ρ ∧ |p.2| ≤ ρ := by
    simpa [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, max_le_iff] using hp_ball
  have hp_dist : dist p.1 x ≤ ρ := hp_coords.1
  have hp_time_abs : |p.2| ≤ ρ := hp_coords.2
  have hp_time_le_ρ : p.2 ≤ ρ := by
    simpa [abs_of_pos hp2] using hp_time_abs
  have hp_time_le_s0 : p.2 ≤ s0 := by
    exact le_trans hp_time_le_ρ (min_le_left _ _)
  have hp_dist_scaled : dist p.1 x ≤ δ * s0 := by
    calc
      dist p.1 x ≤ ρ := hp_dist
      _ ≤ δ * s0 := min_le_right _ _
  have hden_pos : 0 < δ + ‖d‖ + 1 := by positivity
  have hstep_norm :
      s0 * (δ + ‖d‖) ≤ eps := by
    have hδnorm_le : δ + ‖d‖ ≤ δ + ‖d‖ + 1 := by linarith
    calc
      s0 * (δ + ‖d‖) ≤ s0 * (δ + ‖d‖ + 1) := by
        gcongr
      _ ≤ (eps / (δ + ‖d‖ + 1)) * (δ + ‖d‖ + 1) := by
        gcongr
      _ = eps := by
        field_simp [hden_pos.ne']
  have hy_mem : p.1 ∈ Metric.closedBall x eps := by
    have hρ_le_s0 : ρ ≤ s0 := min_le_left _ _
    have hρ_le_eps : ρ ≤ eps := by
      have hdiv_le_eps : eps / (δ + ‖d‖ + 1) ≤ eps := by
        have hden_ge_one : 1 ≤ δ + ‖d‖ + 1 := by
          nlinarith [hδ_pos, norm_nonneg d]
        calc
          eps / (δ + ‖d‖ + 1) ≤ eps / 1 := by
            gcongr
          _ = eps := by ring
      calc
        ρ ≤ s0 := hρ_le_s0
        _ ≤ eps / (δ + ‖d‖ + 1) := hs0_le_eps
        _ ≤ eps := hdiv_le_eps
    exact (Metric.mem_closedBall.2 (le_trans hp_dist hρ_le_eps))
  have hx_step_mem : x + s0 • d ∈ Metric.closedBall x eps := by
    -- The common frozen endpoint stays in the same Lipschitz ball.
    have hδ_nonneg : 0 ≤ δ := hδ_pos.le
    have hnorm_only : s0 * ‖d‖ ≤ s0 * (δ + ‖d‖) := by
      nlinarith [hs0_pos.le, hδ_nonneg, norm_nonneg d]
    refine Metric.mem_closedBall.2 ?_
    simpa [dist_eq_norm, norm_smul, Real.norm_of_nonneg hs0_pos.le, mul_comm, mul_left_comm,
      mul_assoc] using le_trans hnorm_only hstep_norm
  have hstep_mem :
      ∀ {t : ℝ}, 0 ≤ t → t ≤ s0 → p.1 + t • d ∈ Metric.closedBall x eps := by
    intro t ht_nonneg ht_le
    -- The base-point and step-size bounds combine by the triangle inequality.
    have ht_term :
        dist (p.1 + t • d) x ≤ dist p.1 x + t * ‖d‖ := by
      calc
        dist (p.1 + t • d) x ≤ dist (p.1 + t • d) p.1 + dist p.1 x := dist_triangle _ _ _
        _ = t * ‖d‖ + dist p.1 x := by
          simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, norm_smul,
            Real.norm_of_nonneg ht_nonneg]
        _ = dist p.1 x + t * ‖d‖ := by ring
    have ht_scaled :
        dist p.1 x + t * ‖d‖ ≤ s0 * (δ + ‖d‖) := by
      have htt : t * ‖d‖ ≤ s0 * ‖d‖ := by
        gcongr
      have hbase : dist p.1 x ≤ δ * s0 := hp_dist_scaled
      nlinarith [hbase, htt, ht_nonneg, hs0_pos.le, norm_nonneg d, show 0 ≤ δ by linarith]
    exact Metric.mem_closedBall.2 (le_trans ht_term (le_trans ht_scaled hstep_norm))
  have hp_step_mem : p.1 + p.2 • d ∈ Metric.closedBall x eps :=
    hstep_mem hp2.le hp_time_le_s0
  have hs0_step_mem : p.1 + s0 • d ∈ Metric.closedBall x eps :=
    hstep_mem hs0_pos.le le_rfl
  have hmono :
      (f (p.1 + p.2 • d) - f p.1) / p.2 ≤ (f (p.1 + s0 • d) - f p.1) / s0 := by
    -- Convexity lets us move every smaller positive time up to the common endpoint `s0`.
    exact
      convex_secantQuotient_monotone_along_ray f p.1 d h_convex hp2 hs0_pos hp_time_le_s0
  have hcompare :
      (f (p.1 + s0 • d) - f p.1) / s0 ≤
        (f (x + s0 • d) - f x) / s0 + 2 * (K : ℝ) * δ :=
    secantQuotient_le_fixedBase_add_of_closedBallLipschitz f x p.1 d K hs0_pos hK hy_mem
      hs0_step_mem hx_step_mem hp_dist_scaled
  have hreal :
      (f (p.1 + p.2 • d) - f p.1) / p.2 ≤ b := by
    have hstrict :
        (f (p.1 + p.2 • d) - f p.1) / p.2 < b := by
      calc
      (f (p.1 + p.2 • d) - f p.1) / p.2 ≤ (f (p.1 + s0 • d) - f p.1) / s0 := hmono
      _ ≤ (f (x + s0 • d) - f x) / s0 + 2 * (K : ℝ) * δ := hcompare
      _ ≤ c + 2 * (K : ℝ) * δ := by gcongr
      _ < b := hδ_bound
    exact hstrict.le
  exact_mod_cast hreal

/-- Helper for Chapter14 Lemma 14.1.6: a convex function that is Lipschitz on some closed ball
around `x` has Clarke directional derivative bounded above by the convex one-sided directional
derivative. -/
lemma clarkeDirectionalDerivReal_le_oneSidedDirectionalDeriv_of_convexOn_of_closedBallLipschitz
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    {K : NNReal}
    (hK : ∃ eps : ℝ, 0 < eps ∧ LipschitzOnWith K f (Metric.closedBall x eps)) :
    clarkeDirectionalDerivReal f x d ≤ oneSidedDirectionalDeriv f x d := by
  have h_local : LocallyLipschitzAt f x := locallyLipschitzAt_of_closedBall hK
  rcases hK with ⟨eps, hε, hLip⟩
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  let b : ℝ := oneSidedDirectionalDeriv f x d + η
  have hb : oneSidedDirectionalDeriv f x d < b := by
    dsimp [b]
    linarith
  obtain ⟨ρ, hρ_pos, hρ⟩ :=
    clarkeQuotient_eventually_le_of_lt_oneSidedDirectionalDeriv_of_convexOn_of_closedBallLipschitz
      f x d h_convex K hε hLip hb
  let l : Filter (X × ℝ) :=
    nhdsWithin ((x : X), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
  let q : X × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  have hl_ne : l.NeBot := wholeSpaceClarkePairFilter_neBot x d
  have h_event :
      ∀ᶠ p in l, q p ≤ (b : EReal) := by
    -- The frozen-endpoint estimate is uniform on a small closed product ball.
    filter_upwards
        [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds ((x : X), (0 : ℝ)) hρ_pos),
          self_mem_nhdsWithin] with p hp_ball hp_dom
    have hp2 : 0 < p.2 := (mem_clarkeDirectionalDerivWithinDomain.mp hp_dom).2.1
    exact hρ hp_ball hp2
  have h_cobdd : l.IsCoboundedUnder (· ≤ ·) q :=
    Filter.isCoboundedUnder_le_of_le l fun _ ↦ bot_le
  have h_limsup : Filter.limsup q l ≤ (b : EReal) :=
    Filter.limsup_le_of_le h_cobdd h_event
  have h_ereal :
      ((clarkeDirectionalDerivReal f x d : ℝ) : EReal) ≤ (b : EReal) := by
    -- Rewrite the Clarke owner as the limsup of the quotient field we just bounded.
    rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local,
      clarkeDirectionalDeriv_eq_limsup]
    simpa [l, q] using h_limsup
  have h_real : clarkeDirectionalDerivReal f x d ≤ b := by
    exact_mod_cast h_ereal
  simpa [b] using h_real

/-- Helper for Chapter14 Lemma 14.1.6: the convex/Lipschitz comparison reduces to the real-valued
Clarke directional derivative equaling the one-sided directional derivative. -/
theorem clarkeDirectionalDerivReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_lipschitz : LocallyLipschitzAt f x) :
    clarkeDirectionalDerivReal f x d = oneSidedDirectionalDeriv f x d := by
  have h_oneSided :
      HasOneSidedDirectionalDerivAt f (oneSidedDirectionalDeriv f x d) x d :=
    convex_hasOneSidedDirectionalDerivAt_along_ray f x d h_convex
  have h_dirWithin :
      HasDirectionalDerivWithinAt Set.univ f (oneSidedDirectionalDeriv f x d) ⟨x, by simp⟩ d :=
    hasDirectionalDerivWithinAt_univ_iff_hasOneSidedDirectionalDerivAt.mpr h_oneSided
  have h_upperDini :
      upperDiniDirectionalDerivWithin Set.univ f ⟨x, by simp⟩ d =
        ((oneSidedDirectionalDeriv f x d : ℝ) : EReal) := by
    -- The convex ray derivative identifies the upper Dini derivative along the constant base path.
    simpa [directionalDerivWithin_univ_eq_oneSidedDirectionalDeriv] using
      upperDiniDirectionalDerivWithin_eq_of_hasDirectionalDerivWithinAt h_dirWithin
  have h_localWithin : LocallyLipschitzWithinAt Set.univ f ⟨x, by simp⟩ := by
    rcases locallyLipschitzAt_iff.mp h_lipschitz with ⟨ε, hε, K, hK⟩
    -- Reuse the closed-ball Lipschitz witness as a whole-space within-neighborhood witness.
    refine ⟨K, Metric.closedBall x ε, ?_, hK⟩
    simpa using (Metric.closedBall_mem_nhds x hε)
  have h_forward :
      oneSidedDirectionalDeriv f x d ≤ clarkeDirectionalDerivReal f x d := by
    have h_forward_ereal :
        ((oneSidedDirectionalDeriv f x d : ℝ) : EReal) ≤
          clarkeDirectionalDerivWithin Set.univ f ⟨x, by simp⟩ d := by
      calc
        ((oneSidedDirectionalDeriv f x d : ℝ) : EReal) =
            upperDiniDirectionalDerivWithin Set.univ f ⟨x, by simp⟩ d := by
              rw [h_upperDini]
        _ ≤ clarkeDirectionalDerivWithin Set.univ f ⟨x, by simp⟩ d :=
          upperDiniDirectionalDerivWithin_le_clarkeDirectionalDerivWithin h_localWithin
    have h_forward_ereal' :
        ((oneSidedDirectionalDeriv f x d : ℝ) : EReal) ≤
          ((clarkeDirectionalDerivReal f x d : ℝ) : EReal) := by
      have hcoe :
          ((clarkeDirectionalDerivReal f x d : ℝ) : EReal) = fᵒ(x; d) :=
        coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_lipschitz
      simpa [clarkeDirectionalDeriv,
        hcoe] using h_forward_ereal
    exact_mod_cast h_forward_ereal'
  have h_reverse :
      clarkeDirectionalDerivReal f x d ≤ oneSidedDirectionalDeriv f x d := by
    rcases locallyLipschitzAt_iff.mp h_lipschitz with ⟨ε, hε, K, hK⟩
    -- Route correction: freeze one common endpoint time, move all smaller convex secants to that
    -- endpoint, and only then use the Lipschitz comparison from the source proof.
    exact
      clarkeDirectionalDerivReal_le_oneSidedDirectionalDeriv_of_convexOn_of_closedBallLipschitz
        f x d h_convex ⟨ε, hε, hK⟩
  exact le_antisymm h_reverse h_forward

/-- Chapter14 Lemma 14.1.6 (1): if `f` is convex and Lipschitz near `x`, then the Clarke
generalized differential `(∂ᶜ f) x` coincides with the convex subdifferential `∂ f(x)`. -/
theorem clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
    (f : X → ℝ)
    (x : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_lipschitz : LocallyLipschitzAt f x) :
    (∂ᶜ f) x = ∂ f x := by
  ext ξ
  constructor
  · intro hξ
    -- Move Clarke membership to the real support inequality and replace Clarke by the
    -- convex one-sided derivative.
    refine (mem_subdifferential_iff_le_oneSidedDirectionalDeriv_of_convexOn
      f x h_convex ξ).2 ?_
    intro d
    have hclarke :
        ξ d ≤ clarkeDirectionalDerivReal f x d :=
      (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
        (f := f) (x := x) h_lipschitz ξ).1 hξ d
    simpa [clarkeDirectionalDerivReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
      f x d h_convex h_lipschitz] using hclarke
  · intro hξ
    -- Conversely, the convex support inequality already implies the Clarke support inequality once
    -- the directional values are identified.
    refine (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
      (f := f) (x := x) h_lipschitz ξ).2 ?_
    intro d
    have hsub :
        ξ d ≤ oneSidedDirectionalDeriv f x d :=
      (mem_subdifferential_iff_le_oneSidedDirectionalDeriv_of_convexOn
        f x h_convex ξ).1 hξ d
    simpa [clarkeDirectionalDerivReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
      f x d h_convex h_lipschitz] using hsub

/-- Chapter14 Lemma 14.1.6 (2): if `f` is convex and Lipschitz near `x`, then for each
direction `d`, the finite real-valued specialization `((fᵒ(x; d)).toReal)` of the canonical
Clarke owner `fᵒ(x; d)` coincides with the right directional derivative owner
`oneSidedDirectionalDeriv f x d`. -/
theorem clarkeDirectionalDeriv_toReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
    (f : X → ℝ)
    (x d : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_lipschitz : LocallyLipschitzAt f x) :
    (fᵒ(x; d)).toReal = oneSidedDirectionalDeriv f x d := by
  simpa [clarkeDirectionalDerivReal] using
    clarkeDirectionalDerivReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
      f x d h_convex h_lipschitz

#print axioms subdifferential

end
