/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sign
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.InitialSublevelSet

open Filter
open scoped Gradient

section Theorem224

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling:
-- * source-facing layer: this theorem is the textbook global-convergence statement for the
--   exact-line-search iterate, direction, and steplength sequences of Algorithm 2.2.1;
-- * core/canonical candidates inspected upstream in the chapter:
--   `GeneralUnconstrainedOptimizationMethod` from `Algorithm_2_2_1` and
--   `IsExactLineSearchStepOnNonnegativeRay` from
--   `Definition_2_2_extra_1`;
-- * bridge/view pattern inspected nearby: `InexactLineSearchMethod` records step data only on
--   nonstationary iterates, which matches the source semantics better than forcing a descent
--   direction at every iterate.
-- The best owner abstraction available for this file is therefore the one-step exact line-search
-- owner `IsExactLineSearchStepOnNonnegativeRay`; the theorem itself stays source-facing because
-- the current chapter-wide method packages are stronger than the source statement. The initial
-- sublevel-set owner is therefore recorded canonically as `initialSublevelSet f (x 0)` rather
-- than through a redundant separate starting-point parameter. The labeled theorem follows the
-- book by exposing the ambient Euclidean gradient regularity needed to interpret `∇ f`, together
-- with level-set uniform continuity and angle hypotheses on that canonical sublevel-set owner.

/-- Helper for Chapter02 Theorem 2.2.4: on any nonstationary iterate, exact line search beats a
small locally decreasing trial step and therefore strictly decreases the objective. -/
private lemma exact_line_search_strict_decrease_of_gradient_ne_zero
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (k : ℕ)
    (hk : ∇ f (x k) ≠ 0) :
    f (x (k + 1)) < f (x k) := by
  -- Compare the exact step with a short positive step given by local decrease of the ray profile.
  have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k hk
  rcases hdesc.exists_localDecrease_lineSearchObjective with ⟨δ, hδpos, hδdecrease⟩
  have hhalf_pos : 0 < δ / 2 := by positivity
  have hhalf_lt : δ / 2 < δ := by linarith
  have htrial :
      lineSearchObjective f (x k) (d k) (δ / 2) <
        lineSearchObjective f (x k) (d k) 0 :=
    hδdecrease (δ / 2) hhalf_pos hhalf_lt
  have hmin :
      lineSearchObjective f (x k) (d k) (α k) ≤
        lineSearchObjective f (x k) (d k) (δ / 2) :=
    (h_exactLineSearch k).optimal (by positivity)
  have hstrict :
      lineSearchObjective f (x k) (d k) (α k) <
        lineSearchObjective f (x k) (d k) 0 :=
    lt_of_le_of_lt hmin htrial
  -- Rewriting the exact-step value through the iterate update gives the textbook descent step.
  simpa [lineSearchObjective_apply, lineSearchObjective_zero, h_update k] using hstrict

/-- Helper for Chapter02 Theorem 2.2.4: if no iterate is stationary, every iterate stays inside
the initial sublevel set. -/
private lemma exact_line_search_iterates_mem_initialSublevelSet
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0) :
    ∀ k : ℕ, x k ∈ initialSublevelSet f (x 0) := by
  intro k
  induction k with
  | zero =>
      -- The starting point belongs to its own initial sublevel set.
      simp
  | succ k hk =>
      -- Strict descent at step `k` propagates the initial-sublevel-set invariant.
      rw [mem_initialSublevelSet] at hk ⊢
      have hstrict :
          f (x (k + 1)) < f (x k) :=
        exact_line_search_strict_decrease_of_gradient_ne_zero
          f x d α h_descent h_exactLineSearch h_update k (hgrad_ne k)
      linarith

/-- Helper for Chapter02 Theorem 2.2.4: in the nonstationary branch the objective sequence is
antitone. -/
private lemma exact_line_search_objective_antitone
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0) :
    Antitone (fun k : ℕ ↦ f (x k)) := by
  -- The one-step strict decrease immediately upgrades to an antitone sequence on `ℕ`.
  refine antitone_nat_of_succ_le fun k ↦ ?_
  exact (exact_line_search_strict_decrease_of_gradient_ne_zero
    f x d α h_descent h_exactLineSearch h_update k (hgrad_ne k)).le

/-- Helper for Chapter02 Theorem 2.2.4: once the objective sequence is antitone and does not
escape to `-∞`, its successive decreases tend to `0`. -/
private lemma decrease_gap_tendsto_zero_of_not_atBot
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (h_not_atBot : ¬ Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot) :
    Tendsto (fun k : ℕ ↦ f (x k) - f (x (k + 1))) atTop (nhds 0) := by
  -- Antitonicity reduces the bounded-below branch to monotone convergence on `ℝ`.
  have hanti : Antitone (fun k : ℕ ↦ f (x k)) :=
    exact_line_search_objective_antitone f x d α h_descent h_exactLineSearch h_update hgrad_ne
  rcases tendsto_atTop_of_antitone hanti with hbot | ⟨l, hl⟩
  · exact False.elim (h_not_atBot hbot)
  · have hl_shift : Tendsto (fun k : ℕ ↦ f (x (k + 1))) atTop (nhds l) :=
      hl.comp (tendsto_add_atTop_nat 1)
    -- Subtracting the shifted limit from the original limit gives the vanishing decrease gap.
    simpa using hl.sub hl_shift

/-- Helper for Chapter02 Theorem 2.2.4: if the gradients do not converge to `0`, then some
positive lower bound for their norms occurs frequently along the sequence. -/
private lemma frequently_gradient_norm_ge_of_not_tendsto_zero
    (f : Point → ℝ)
    (x : ℕ → Point)
    (h_not :
      ¬ Tendsto (fun k : ℕ ↦ ∇ f (x k)) atTop (nhds (0 : Point))) :
    ∃ ε > 0, ∃ᶠ k : ℕ in atTop, ε ≤ ‖∇ f (x k)‖ := by
  -- Convert failure of vector convergence to failure of norm convergence.
  have h_not_norm :
      ¬ Tendsto (fun k : ℕ ↦ ‖∇ f (x k)‖) atTop (nhds (0 : ℝ)) := by
    intro hnorm
    apply h_not
    simpa [tendsto_iff_dist_tendsto_zero, dist_eq_norm] using hnorm
  have hnorm_char :
      Tendsto (fun k : ℕ ↦ ‖∇ f (x k)‖) atTop (nhds (0 : ℝ)) ↔
        ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (‖∇ f (x n)‖) 0 < ε := by
    exact Metric.tendsto_atTop
  rw [hnorm_char] at h_not_norm
  push Not at h_not_norm
  rcases h_not_norm with ⟨ε, hε, hεfail⟩
  refine ⟨ε, hε, ?_⟩
  rw [frequently_atTop]
  intro N
  rcases hεfail N with ⟨n, hnN, hn⟩
  refine ⟨n, hnN, ?_⟩
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hn

/-- Helper for Chapter02 Theorem 2.2.4: once a point on the normalized short ray is known to stay
inside the initial sublevel set, the directional derivative there is uniformly bounded above by
the source half-gap `-((ε * sin μ) / 2)`. -/
private lemma normalized_short_ray_deriv_le_neg_half_gap
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (μ αbar ε : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_spec :
      ∀ ⦃y z : Point⦄,
        y ∈ initialSublevelSet f (x 0) →
        z ∈ initialSublevelSet f (x 0) →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2)
    {k : ℕ}
    (hkε : ε ≤ ‖∇ f (x k)‖)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) αbar)
    (hy : x k + t • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0)) :
    deriv (lineSearchObjective f (x k) ((‖d k‖)⁻¹ • d k)) t ≤
      -((ε * Real.sin μ) / 2) := by
  let u : Point := (‖d k‖)⁻¹ • d k
  let y : Point := x k + t • u
  have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k (hgrad_ne k)
  have hdk_ne : d k ≠ 0 := by
    intro hdk
    have : ¬ inner ℝ (∇ f (x k)) (d k) < 0 := by simp [hdk]
    exact this hdesc
  have hsin_pos : 0 < Real.sin μ := by
    have hmu_lt_pi : μ < Real.pi := by
      have hmu_le_pi_div_two : μ ≤ Real.pi / 2 := by
        have hang_nonneg :
            0 ≤ InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) :=
          InnerProductGeometry.angle_nonneg _ _
        have hang_le :
            InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) ≤ Real.pi / 2 - μ :=
          h_angle 0 (hgrad_ne 0)
        linarith
      linarith [Real.pi_pos, hmu_le_pi_div_two]
    exact Real.sin_pos_of_pos_of_lt_pi hμ hmu_lt_pi
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hdk_ne))]
    field_simp [norm_ne_zero_iff.mpr hdk_ne]
  have hmem : ∀ n : ℕ, x n ∈ initialSublevelSet f (x 0) :=
    exact_line_search_iterates_mem_initialSublevelSet
      f x d α h_descent h_exactLineSearch h_update hgrad_ne
  have hdist_le : dist (x k) y ≤ αbar := by
    calc
      dist (x k) y = ‖t • u‖ := by
        simp [y, dist_eq_norm, sub_eq_add_neg, u, add_comm]
      _ = |t| * ‖u‖ := norm_smul t u
      _ = t := by
        rw [hu_norm, abs_of_nonneg ht.1]
        simp
      _ ≤ αbar := ht.2
  have h_grad_close :
      ‖∇ f y - ∇ f (x k)‖ ≤ (ε * Real.sin μ) / 2 :=
    hαbar_spec hy (hmem k) (by simpa [y, dist_comm] using hdist_le)
  have hangle_nonneg :
      0 ≤ InnerProductGeometry.angle (d k) (-(∇ f (x k))) :=
    InnerProductGeometry.angle_nonneg _ _
  have hhalf_pi_minus_mu_nonneg : 0 ≤ Real.pi / 2 - μ := by
    linarith [hangle_nonneg, h_angle k (hgrad_ne k)]
  have hcos_lower :
      Real.sin μ ≤ Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) := by
    have hcos :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        hangle_nonneg
        (by linarith [Real.pi_pos])
        (h_angle k (hgrad_ne k))
    simpa [Real.cos_pi_div_two_sub] using hcos
  have hbase_dir :
      ε * Real.sin μ ≤ -(inner ℝ (∇ f (x k)) (d k) / ‖d k‖) := by
    have hmul_cos_lower :
        ‖∇ f (x k)‖ * Real.sin μ ≤
          ‖∇ f (x k)‖ * Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) := by
      exact mul_le_mul_of_nonneg_left hcos_lower (norm_nonneg _)
    calc
      ε * Real.sin μ ≤ ‖∇ f (x k)‖ * Real.sin μ := by
        exact mul_le_mul_of_nonneg_right hkε (le_of_lt hsin_pos)
      _ ≤ ‖∇ f (x k)‖ * Real.cos (InnerProductGeometry.angle (d k) (-(∇ f (x k)))) :=
        hmul_cos_lower
      _ = -(inner ℝ (∇ f (x k)) (d k) / ‖d k‖) := by
        simpa using
          gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm
            f (x k) (d k)
  have hbase_u :
      inner ℝ (∇ f (x k)) u ≤ -(ε * Real.sin μ) := by
    have hrewrite :
        inner ℝ (∇ f (x k)) u = inner ℝ (∇ f (x k)) (d k) / ‖d k‖ := by
      dsimp [u]
      rw [inner_smul_right, div_eq_mul_inv, mul_comm]
    have hbase_u' :
        ε * Real.sin μ ≤ -inner ℝ (∇ f (x k)) u := by
      simpa [hrewrite] using hbase_dir
    linarith
  have hGradAt : HasGradientAt f (∇ f y) y := h_hasGradient y hy
  have hderiv :
      deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f y) u := by
    simpa [y] using
      (hGradAt.deriv_lineSearchObjective_apply :
        deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f y) u)
  have hdiff_inner :
      inner ℝ (∇ f y - ∇ f (x k)) u ≤ (ε * Real.sin μ) / 2 := by
    have hnorm_bound :
        inner ℝ (∇ f y - ∇ f (x k)) u ≤ ‖∇ f y - ∇ f (x k)‖ * ‖u‖ :=
      real_inner_le_norm _ _
    rw [hu_norm, mul_one] at hnorm_bound
    exact le_trans hnorm_bound h_grad_close
  have hsum :
      inner ℝ (∇ f y) u =
        inner ℝ (∇ f y - ∇ f (x k)) u + inner ℝ (∇ f (x k)) u := by
    rw [inner_sub_left]
    ring
  -- Split the current slope into the base-point slope plus a gradient-difference error term.
  rw [hderiv, hsum]
  linarith

/-- Helper for Chapter02 Theorem 2.2.4: after fixing the uniform-continuity radius, the
normalized ray has a positive initial prefix that stays inside the initial sublevel set. -/
private lemma normalized_ray_has_initial_good_prefix
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (αbar : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_pos : 0 < αbar) :
    ∀ k : ℕ,
      ∃ δ > 0, δ ≤ αbar ∧
        ∀ s ∈ Set.Icc (0 : ℝ) δ,
          x k + s • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0) := by
  intro k
  let u : Point := (‖d k‖)⁻¹ • d k
  have hmem : ∀ n : ℕ, x n ∈ initialSublevelSet f (x 0) :=
    exact_line_search_iterates_mem_initialSublevelSet
      f x d α h_descent h_exactLineSearch h_update hgrad_ne
  have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k (hgrad_ne k)
  have hdk_pos : 0 < ‖d k‖ := norm_pos_iff.mpr hdesc.direction_ne
  have hu_desc : IsDescentDirectionAt f (x k) u := by
    -- Positive rescaling preserves the source descent direction.
    dsimp [u, IsDescentDirectionAt]
    rw [inner_smul_right]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hdk_pos) hdesc
  rcases hu_desc.exists_localDecrease_lineSearchObjective with ⟨ρ, hρ_pos, hρ_drop⟩
  refine ⟨min (ρ / 2) αbar, by positivity, min_le_right _ _, ?_⟩
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
  · simpa [u] using hmem k
  · have hs_lt_ρ : s < ρ := by
      calc
        s ≤ min (ρ / 2) αbar := hs.2
        _ ≤ ρ / 2 := min_le_left _ _
        _ < ρ := by linarith
    have hs_drop :
        lineSearchObjective f (x k) u s <
          lineSearchObjective f (x k) u 0 :=
      hρ_drop s hs_pos hs_lt_ρ
    -- Strict decrease from the current iterate keeps the whole seeded prefix inside the
    -- initial sublevel set.
    rw [mem_initialSublevelSet]
    have hk_mem : f (x k) ≤ f (x 0) := by
      simpa [mem_initialSublevelSet] using hmem k
    have hk_mem0 : lineSearchObjective f (x k) u 0 ≤ f (x 0) := by
      simpa [lineSearchObjective_zero] using hk_mem
    simpa [u, lineSearchObjective_apply, lineSearchObjective_zero] using
      le_of_lt (lt_of_lt_of_le hs_drop hk_mem0)

/-- Helper for Chapter02 Theorem 2.2.4: on any already-good normalized prefix, the ray objective
stays below the affine barrier from the source proof. -/
private lemma normalized_ray_affine_barrier_on_prefix
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (μ αbar ε β : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_spec :
      ∀ ⦃y z : Point⦄,
        y ∈ initialSublevelSet f (x 0) →
        z ∈ initialSublevelSet f (x 0) →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2)
    {k : ℕ}
    (hkε : ε ≤ ‖∇ f (x k)‖)
    (hβ_le : β ≤ αbar)
    (hprefix :
      ∀ s ∈ Set.Icc (0 : ℝ) β,
        x k + s • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0)) :
      ∀ t ∈ Set.Icc (0 : ℝ) β,
      f (x k + t • ((‖d k‖)⁻¹ • d k)) ≤
        f (x k) - t * ((ε * Real.sin μ) / 2) := by
  let u : Point := (‖d k‖)⁻¹ • d k
  let φ : ℝ → ℝ := lineSearchObjective f (x k) u
  let B : ℝ → ℝ := fun t ↦ f (x k) - t * ((ε * Real.sin μ) / 2)
  have hRayDiff :
      ∀ t : ℝ, DifferentiableAt ℝ (fun s : ℝ ↦ x k + s • u) t := by
    intro t
    exact (((hasDerivAt_id' t).smul_const u).const_add (x k)).differentiableAt
  have hφ_cont : ContinuousOn φ (Set.Icc (0 : ℝ) β) := by
    intro t ht
    have hφ_diff : DifferentiableAt ℝ φ t := by
      have hyt : x k + t • u ∈ initialSublevelSet f (x 0) := by
        simpa [u] using hprefix t ht
      have hGradAt :
          HasGradientAt f (∇ f (x k + t • u)) (x k + t • u) :=
        h_hasGradient (x k + t • u) hyt
      -- On a good prefix, each ray point is differentiable, so the scalar profile is continuous.
      dsimp [φ]
      exact hGradAt.differentiableAt.comp t (hRayDiff t)
    exact hφ_diff.continuousAt.continuousWithinAt
  have hφ_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) β, HasDerivWithinAt φ (deriv φ t) (Set.Ici t) t := by
    intro t ht
    have hφ_diff : DifferentiableAt ℝ φ t := by
      have hyt : x k + t • u ∈ initialSublevelSet f (x 0) := by
        simpa [u] using hprefix t ⟨ht.1, ht.2.le⟩
      have hGradAt :
          HasGradientAt f (∇ f (x k + t • u)) (x k + t • u) :=
        h_hasGradient (x k + t • u) hyt
      -- The right-derivative comparison works with the ordinary derivative of the ray profile.
      dsimp [φ]
      exact hGradAt.differentiableAt.comp t (hRayDiff t)
    exact hφ_diff.hasDerivAt.hasDerivWithinAt
  have hB_cont : ContinuousOn B (Set.Icc (0 : ℝ) β) := by
    intro t ht
    -- The barrier is affine, hence continuous on every interval.
    dsimp [B]
    exact ((continuous_const.continuousAt).sub
      (continuous_id.continuousAt.mul continuous_const.continuousAt)).continuousWithinAt
  have hB_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) β,
        HasDerivWithinAt B (-((ε * Real.sin μ) / 2)) (Set.Ici t) t := by
    intro t ht
    have hB_derivAt : HasDerivAt B (-((ε * Real.sin μ) / 2)) t := by
      -- Differentiate the affine barrier explicitly.
      dsimp [B]
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id' t).mul_const ((ε * Real.sin μ) / 2)).neg).const_add (f (x k)))
    exact hB_derivAt.hasDerivWithinAt
  have hbase : φ 0 ≤ B 0 := by
    simp [φ, B, lineSearchObjective_zero]
  have hbound :
      ∀ t ∈ Set.Ico (0 : ℝ) β, deriv φ t ≤ -((ε * Real.sin μ) / 2) := by
    intro t ht
    exact normalized_short_ray_deriv_le_neg_half_gap
      f x d α μ αbar ε h_descent h_exactLineSearch h_update h_hasGradient hμ h_angle
      hgrad_ne hαbar_spec hkε ⟨ht.1, le_trans ht.2.le hβ_le⟩
      (by simpa [u] using hprefix t ⟨ht.1, ht.2.le⟩)
  have hbarrier :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) β → φ t ≤ B t :=
    image_le_of_deriv_right_le_deriv_boundary hφ_cont hφ_deriv hbase hB_cont hB_deriv hbound
  intro t ht
  -- The one-dimensional comparison recovers the desired source affine drop on the good prefix.
  simpa [φ, B, u, lineSearchObjective_apply, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc] using hbarrier ht

/-- Helper for Chapter02 Theorem 2.2.4: every scalar time strictly below the supremum of the
good-prefix set already belongs to one previously verified good prefix. -/
private lemma good_prefix_mem_of_lt_csSup
    (f : Point → ℝ)
    (x0 : Point)
    (ray : ℝ → Point)
    (Good : ℝ → Prop)
    (hGood_nonempty : ∃ β : ℝ, Good β)
    (hGood_prefix :
      ∀ ⦃β s : ℝ⦄, Good β → s ∈ Set.Icc (0 : ℝ) β → ray s ∈ initialSublevelSet f x0)
    {s : ℝ}
    (hs_nonneg : 0 ≤ s)
    (hs_lt : s < sSup {β : ℝ | Good β}) :
    ray s ∈ initialSublevelSet f x0 := by
  let S : Set ℝ := {β : ℝ | Good β}
  have hS_nonempty : S.Nonempty := by
    rcases hGood_nonempty with ⟨β, hβ⟩
    exact ⟨β, by simpa [S] using hβ⟩
  rcases exists_lt_of_lt_csSup hS_nonempty (by simpa [S] using hs_lt) with
    ⟨β, hβS, hsβ⟩
  -- Choose one good prefix extending past `s`, then read off membership from its prefix witness.
  exact hGood_prefix (by simpa [S] using hβS) ⟨hs_nonneg, hsβ.le⟩

/-- Helper for Chapter02 Theorem 2.2.4: once the scalar ray objective is known to be continuous
from the left at the supremum time, the endpoint itself still lies in the initial sublevel set. -/
private lemma good_prefix_endpoint_mem_of_continuousWithinAt
    (f : Point → ℝ)
    (x0 : Point)
    (ray : ℝ → Point)
    {τ : ℝ}
    (hτ_pos : 0 < τ)
    (hcont : ContinuousWithinAt (fun s : ℝ ↦ f (ray s)) (Set.Iic τ) τ)
    (hleft :
      ∀ s ∈ Set.Icc (0 : ℝ) τ, s < τ → ray s ∈ initialSublevelSet f x0) :
    ray τ ∈ initialSublevelSet f x0 := by
  let seq : ℕ → ℝ := fun n ↦ τ - (τ / 2) * ((n + 1 : ℝ)⁻¹)
  have hseq_mem : ∀ n : ℕ, seq n ∈ Set.Icc (0 : ℝ) τ := by
    intro n
    have hden_ge : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hdiv_le_one : ((n + 1 : ℝ)⁻¹) ≤ 1 := by
      exact inv_le_one_of_one_le₀ hden_ge
    constructor
    · -- The sampled times stay nonnegative because they remain above `τ / 2`.
      dsimp [seq]
      nlinarith
    · -- They stay below `τ`, so the sequence approaches `τ` from the left.
      dsimp [seq]
      have hterm_nonneg : 0 ≤ (τ / 2) * ((n + 1 : ℝ)⁻¹) := by positivity
      exact sub_le_self _ hterm_nonneg
  have hseq_lt : ∀ n : ℕ, seq n < τ := by
    intro n
    have hterm_pos : 0 < (τ / 2) * ((n + 1 : ℝ)⁻¹) := by positivity
    dsimp [seq]
    linarith
  have hseq_tendsto : Tendsto seq atTop (nhds τ) := by
    have hInv_shift :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0))
    have hterm_tendsto :
        Tendsto (fun n : ℕ ↦ (τ / 2) * ((n + 1 : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hInv_shift)
    -- The left-approximating scalar sequence converges to the endpoint `τ`.
    dsimp [seq]
    simpa using tendsto_const_nhds.sub hterm_tendsto
  have hseq_tendstoWithin : Tendsto seq atTop (nhdsWithin τ (Set.Iic τ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hseq_tendsto, ?_⟩
    exact Filter.Eventually.of_forall fun n ↦ (hseq_mem n).2
  have himage_tendsto :
      Tendsto (fun n : ℕ ↦ f (ray (seq n))) atTop (nhds (f (ray τ))) :=
    hcont.tendsto.comp hseq_tendstoWithin
  have himage_mem :
      ∀ n : ℕ, f (ray (seq n)) ∈ Set.Iic (f x0) := by
    intro n
    exact mem_initialSublevelSet.mp (hleft (seq n) (hseq_mem n) (hseq_lt n))
  -- Closedness of `Set.Iic (f x0)` passes the left-limit inequality to the endpoint value.
  exact isClosed_Iic.mem_of_tendsto himage_tendsto (Filter.Eventually.of_forall himage_mem)

/-- Helper for Chapter02 Theorem 2.2.4: on every already-good normalized prefix, the scalar ray
profile has a uniform derivative bound coming from the gradient modulus on the initial sublevel
set. -/
private lemma rayObjective_derivNormBound_on_goodPrefix
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (μ αbar ε β : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_spec :
      ∀ ⦃y z : Point⦄,
        y ∈ initialSublevelSet f (x 0) →
        z ∈ initialSublevelSet f (x 0) →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2)
    {k : ℕ}
    (hxk : x k ∈ initialSublevelSet f (x 0))
    (hβ_le : β ≤ αbar)
    (hprefix :
      ∀ s ∈ Set.Icc (0 : ℝ) β,
        x k + s • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0)) :
    ∀ t ∈ Set.Icc (0 : ℝ) β,
      ‖deriv (lineSearchObjective f (x k) ((‖d k‖)⁻¹ • d k)) t‖ ≤
        ‖∇ f (x k)‖ + (ε * Real.sin μ) / 2 := by
  intro t ht
  let u : Point := (‖d k‖)⁻¹ • d k
  let y : Point := x k + t • u
  have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k (hgrad_ne k)
  have hdk_ne : d k ≠ 0 := hdesc.direction_ne
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hdk_ne))]
    field_simp [norm_ne_zero_iff.mpr hdk_ne]
  have hy : y ∈ initialSublevelSet f (x 0) := by
    simpa [y, u] using hprefix t ht
  have hdist_le : dist (x k) y ≤ αbar := by
    calc
      dist (x k) y = ‖t • u‖ := by
        simp [y, dist_eq_norm, sub_eq_add_neg, u, add_comm]
      _ = |t| * ‖u‖ := norm_smul t u
      _ = t := by
        rw [hu_norm, abs_of_nonneg ht.1]
        simp
      _ ≤ β := ht.2
      _ ≤ αbar := hβ_le
  have hGradAt : HasGradientAt f (∇ f y) y := h_hasGradient y hy
  have hderiv :
      deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f y) u := by
    simpa [y] using
      (hGradAt.deriv_lineSearchObjective_apply :
        deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f y) u)
  have hGradClose :
      ‖∇ f y - ∇ f (x k)‖ ≤ (ε * Real.sin μ) / 2 :=
    hαbar_spec hy hxk (by simpa [y, dist_comm] using hdist_le)
  -- Split the current gradient into its base-point value and a controlled perturbation.
  calc
    ‖deriv (lineSearchObjective f (x k) ((‖d k‖)⁻¹ • d k)) t‖
        = ‖inner ℝ (∇ f y) u‖ := by simpa [u] using congrArg norm hderiv
    _ ≤ ‖∇ f y‖ * ‖u‖ := norm_inner_le_norm _ _
    _ = ‖∇ f y‖ := by rw [hu_norm, mul_one]
    _ = ‖(∇ f y - ∇ f (x k)) + ∇ f (x k)‖ := by
      congr 1
      abel_nf
    _ ≤ ‖∇ f y - ∇ f (x k)‖ + ‖∇ f (x k)‖ := norm_add_le _ _
    _ ≤ ‖∇ f (x k)‖ + (ε * Real.sin μ) / 2 := by
      linarith

/-- Helper for Chapter02 Theorem 2.2.4: the explicit sequence approaching the `sSup` boundary from
the left has a convergent objective profile, and the limit still lies below the initial objective
value. -/
private lemma rayObjective_leftLimit_of_csSupGoodPrefix
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (μ αbar ε : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_spec :
      ∀ ⦃y z : Point⦄,
        y ∈ initialSublevelSet f (x 0) →
        z ∈ initialSublevelSet f (x 0) →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2)
    {k : ℕ}
    (hxk : x k ∈ initialSublevelSet f (x 0))
    {τ : ℝ}
    (hτ_pos : 0 < τ)
    (hτ_le : τ ≤ αbar)
    (hleft :
      ∀ s ∈ Set.Icc (0 : ℝ) τ, s < τ →
        x k + s • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0)) :
    ∃ ℓ ≤ f (x 0), Tendsto
      (fun n : ℕ ↦ f (x k + (τ - (τ / 2) * ((n + 1 : ℝ)⁻¹)) • ((‖d k‖)⁻¹ • d k)))
      atTop (nhds ℓ) := by
  let u : Point := (‖d k‖)⁻¹ • d k
  let ray : ℝ → Point := fun s ↦ x k + s • u
  let φ : ℝ → ℝ := fun s ↦ f (x k + s • u)
  let seq : ℕ → ℝ := fun n ↦ τ - (τ / 2) * ((n + 1 : ℝ)⁻¹)
  let C : ℝ := ‖∇ f (x k)‖ + (ε * Real.sin μ) / 2
  have hαbar_nonneg : 0 ≤ αbar := by
    linarith
  have hhalf_nonneg : 0 ≤ (ε * Real.sin μ) / 2 := by
    have hzero := hαbar_spec hxk hxk (by simpa using hαbar_nonneg)
    simpa using hzero
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    linarith [norm_nonneg (∇ f (x k)), hhalf_nonneg]
  have hseq_mem : ∀ n : ℕ, seq n ∈ Set.Icc (0 : ℝ) τ := by
    intro n
    have hden_ge : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hdiv_le_one : ((n + 1 : ℝ)⁻¹) ≤ 1 := by
      exact inv_le_one_of_one_le₀ hden_ge
    constructor
    · dsimp [seq]
      nlinarith
    · dsimp [seq]
      have hterm_nonneg : 0 ≤ (τ / 2) * ((n + 1 : ℝ)⁻¹) := by positivity
      exact sub_le_self _ hterm_nonneg
  have hseq_lt : ∀ n : ℕ, seq n < τ := by
    intro n
    have hterm_pos : 0 < (τ / 2) * ((n + 1 : ℝ)⁻¹) := by positivity
    dsimp [seq]
    linarith
  have hseq_mono : Monotone seq := by
    intro n m hnm
    have hinv :
        ((m + 1 : ℝ)⁻¹) ≤ ((n + 1 : ℝ)⁻¹) := by
      have hnm' : (n + 1 : ℝ) ≤ (m + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ hnm
      simpa [one_div] using one_div_le_one_div_of_le (by positivity) hnm'
    dsimp [seq]
    nlinarith [hinv, hτ_pos]
  have hseq_tendsto : Tendsto seq atTop (nhds τ) := by
    have hInv_shift :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0))
    have hterm_tendsto :
        Tendsto (fun n : ℕ ↦ (τ / 2) * ((n + 1 : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hInv_shift)
    -- The sampled times converge to the `sSup` boundary from the left.
    dsimp [seq]
    simpa using tendsto_const_nhds.sub hterm_tendsto
  have hpair :
      ∀ n m : ℕ, n ≤ m →
        dist (φ (seq n)) (φ (seq m)) ≤ C * dist (seq n) τ := by
    intro n m hnm
    let β : ℝ := seq m
    have hβ_mem : β ∈ Set.Icc (0 : ℝ) τ := hseq_mem m
    have hβ_lt : β < τ := hseq_lt m
    have hprefixβ :
        ∀ s ∈ Set.Icc (0 : ℝ) β, ray s ∈ initialSublevelSet f (x 0) := by
      intro s hs
      exact hleft s ⟨hs.1, le_trans hs.2 hβ_mem.2⟩ (lt_of_le_of_lt hs.2 hβ_lt)
    have hcomp_eq :
        lineSearchObjective f (x k) u =
          ((fun z : Point ↦ f z) ∘ fun t : ℝ ↦ x k + t • u) := by
      funext t
      simp [Function.comp, lineSearchObjective_apply, u]
    have hφ_diff :
        ∀ s ∈ Set.Icc (0 : ℝ) β, DifferentiableAt ℝ φ s := by
      intro s hs
      have hray_mem : ray s ∈ initialSublevelSet f (x 0) := hprefixβ s hs
      have hGradAt : HasGradientAt f (∇ f (ray s)) (ray s) :=
        h_hasGradient (ray s) hray_mem
      have hRayDiff : DifferentiableAt ℝ (fun t : ℝ ↦ x k + t • u) s := by
        exact (((hasDerivAt_id' s).smul_const u).const_add (x k)).differentiableAt
      -- Every point of the chosen left prefix is differentiable along the scalar ray.
      change DifferentiableAt ℝ ((fun z : Point ↦ f z) ∘ fun t : ℝ ↦ x k + t • u) s
      exact hGradAt.differentiableAt.comp s hRayDiff
    have hderiv_bound :
        ∀ s ∈ Set.Icc (0 : ℝ) β, ‖deriv φ s‖ ≤ C := by
      intro s hs
      change ‖deriv ((fun z : Point ↦ f z) ∘ fun t : ℝ ↦ x k + t • u) s‖ ≤ C
      have hbound :=
        rayObjective_derivNormBound_on_goodPrefix
          f x d μ αbar ε β h_descent h_hasGradient hgrad_ne hαbar_spec
          hxk (le_trans hβ_mem.2 hτ_le)
          (by simpa [ray, u] using hprefixβ)
          s hs
      have hderiv_eq :
          deriv ((fun z : Point ↦ f z) ∘ fun t : ℝ ↦ x k + t • u) s =
            deriv (lineSearchObjective f (x k) u) s := by
        simpa using congrArg (fun g : ℝ → ℝ ↦ deriv g s) hcomp_eq.symm
      simpa [hderiv_eq, C] using hbound
    have hdist_image :
        dist (φ (seq n)) (φ (seq m)) ≤ C * dist (seq n) (seq m) := by
      have hn_mem : seq n ∈ Set.Icc (0 : ℝ) β := by
        exact ⟨(hseq_mem n).1, by simpa [β] using hseq_mono hnm⟩
      have hm_mem : seq m ∈ Set.Icc (0 : ℝ) β := by
        exact ⟨hβ_mem.1, le_rfl⟩
      -- Use the uniform derivative bound to get a Lipschitz estimate on the chosen left prefix.
      simpa [Real.dist_eq, abs_sub_comm, dist_comm, φ] using
        Convex.norm_image_sub_le_of_norm_deriv_le
          hφ_diff hderiv_bound (convex_Icc _ _) hn_mem hm_mem
    have hdist_seq :
        dist (seq n) (seq m) ≤ dist (seq n) τ := by
      have hnm' : seq n ≤ seq m := hseq_mono hnm
      have hnτ : seq n ≤ τ := (hseq_mem n).2
      rw [Real.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hnm'),
        abs_of_nonpos (sub_nonpos.mpr hnτ)]
      linarith
    exact le_trans hdist_image (mul_le_mul_of_nonneg_left hdist_seq hC_nonneg)
  have hCtendsto :
      Tendsto (fun n : ℕ ↦ C * dist (seq n) τ) atTop (nhds 0) := by
    have hdist_tendsto : Tendsto (fun n : ℕ ↦ dist (seq n) τ) atTop (nhds 0) := by
      have hconstτ : Tendsto (fun _ : ℕ ↦ τ) atTop (nhds τ) := tendsto_const_nhds
      have hsub : Tendsto (fun n : ℕ ↦ seq n - τ) atTop (nhds 0) := by
        simpa using hseq_tendsto.sub hconstτ
      simpa [Real.dist_eq] using hsub.norm
    simpa [C] using tendsto_const_nhds.mul hdist_tendsto
  have himage_cauchy : CauchySeq (fun n : ℕ ↦ φ (seq n)) :=
    cauchySeq_of_le_tendsto_0' (fun n : ℕ ↦ C * dist (seq n) τ) hpair hCtendsto
  obtain ⟨ℓ, hℓ_tendsto⟩ := cauchySeq_tendsto_of_complete himage_cauchy
  have himage_mem :
      ∀ n : ℕ, φ (seq n) ∈ Set.Iic (f (x 0)) := by
    intro n
    exact mem_initialSublevelSet.mp (hleft (seq n) (hseq_mem n) (hseq_lt n))
  have hℓ_mem : ℓ ∈ Set.Iic (f (x 0)) :=
    isClosed_Iic.mem_of_tendsto hℓ_tendsto (Filter.Eventually.of_forall himage_mem)
  refine ⟨ℓ, hℓ_mem, ?_⟩
  -- The explicit sampled objective sequence is exactly the ray profile sampled along `seq`.
  simpa [φ, u, seq] using hℓ_tendsto

/-- Helper for Chapter02 Theorem 2.2.4: on a nonstationary iterate, exact optimality makes the
ray-profile derivative vanish at the selected exact step. -/
private lemma exact_line_search_deriv_eq_zero_at_step
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    {k : ℕ}
    (hk : ∇ f (x k) ≠ 0) :
    deriv (lineSearchObjective f (x k) (d k)) (α k) = 0 := by
  have hstrict :
      f (x (k + 1)) < f (x k) :=
    exact_line_search_strict_decrease_of_gradient_ne_zero
      f x d α h_descent h_exactLineSearch h_update k hk
  have hα_ne : α k ≠ 0 := by
    intro hα_zero
    have hxeq : x (k + 1) = x k := by
      rw [h_update k, hα_zero, zero_smul, add_zero]
    rw [hxeq] at hstrict
    exact lt_irrefl _ hstrict
  have hα_pos : 0 < α k := by
    exact lt_of_le_of_ne (h_exactLineSearch k).nonneg (by simpa [eq_comm] using hα_ne)
  have hnhds : Set.Ici 0 ∈ nhds (α k) := Ici_mem_nhds hα_pos
  have hlocal : IsLocalMin (lineSearchObjective f (x k) (d k)) (α k) :=
    (h_exactLineSearch k).isMinOn.isLocalMin hnhds
  -- Interior optimality on the nonnegative ray forces a zero derivative at the exact step.
  exact hlocal.deriv_eq_zero

/-- Helper for Chapter02 Theorem 2.2.4: once the normalized ray is already in the initial
sublevel set at `τ` and the scalar derivative there is negative, the ray stays in that
sublevel set on a short right interval. -/
private lemma normalizedRay_extendPast_of_endpoint_deriv_neg
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (αbar : ℝ)
    {k : ℕ}
    {τ : ℝ}
    (hτ_lt : τ < αbar)
    (hy : x k + τ • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0))
    (hderiv :
      deriv (lineSearchObjective f (x k) ((‖d k‖)⁻¹ • d k)) τ < 0) :
    ∃ η > 0, ∀ s ∈ Set.Ioc τ (min αbar (τ + η)),
      x k + s • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0) := by
  let u : Point := (‖d k‖)⁻¹ • d k
  let φ : ℝ → ℝ := lineSearchObjective f (x k) u
  let g : ℝ → ℝ := fun s ↦ φ s - φ τ
  have hsign :
      ∀ᶠ s in nhds τ, SignType.sign (g s) = SignType.sign (τ - s) := by
    -- Apply the one-dimensional derivative test to the shifted ray profile `g`.
    exact eventually_nhdsWithin_sign_eq_of_deriv_neg
      (by simpa [g, φ] using hderiv)
      (by simp [g])
  have hgt_eventually :
      {s : ℝ | s ≤ αbar ∧ g s < 0} ∈ nhdsWithin τ (Set.Ioi τ) := by
    have hsign_gt :
        {s : ℝ | g s < 0} ∈ nhdsWithin τ (Set.Ioi τ) := by
      filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hτs
      have hsign_tau_sub : SignType.sign (τ - s) = -1 := by
        exact sign_eq_neg_one_iff.mpr (sub_neg.mpr (show τ < s from hτs))
      have hsign_g : SignType.sign (g s) = -1 := by
        rw [hsign_tau_sub] at hs
        exact hs
      exact sign_eq_neg_one_iff.mp hsign_g
    have hle_eventually :
        {s : ℝ | s ≤ αbar} ∈ nhdsWithin τ (Set.Ioi τ) := by
      exact mem_of_superset (Ioc_mem_nhdsGT hτ_lt) fun s hs ↦ hs.2
    exact inter_mem hle_eventually hsign_gt
  rcases (mem_nhdsGT_iff_exists_Ioc_subset.mp (by simpa using hgt_eventually)) with
    ⟨u', hu'_gt, hu'_subset⟩
  have hmin_gt : τ < min αbar u' := lt_min hτ_lt hu'_gt
  refine ⟨min αbar u' - τ, sub_pos.mpr hmin_gt, ?_⟩
  intro s hs
  have hs_bound :
      s ≤ min αbar u' := by
    have hsum : τ + (min αbar u' - τ) = min αbar u' := by ring_nf
    have hendpoint : min αbar (τ + (min αbar u' - τ)) = min αbar u' := by
      rw [hsum, min_eq_right (min_le_left _ _)]
    simpa [hendpoint] using hs.2
  have hs' : s ∈ Set.Ioc τ u' := by
    exact ⟨hs.1, le_trans hs_bound (min_le_right _ _)⟩
  have hsg : g s < 0 := (hu'_subset hs').2
  have hphi_le : φ s ≤ f (x 0) := by
    have hphi_tau : φ τ ≤ f (x 0) := by
      simpa [φ, u, lineSearchObjective_apply] using mem_initialSublevelSet.mp hy
    have hphi_lt : φ s < φ τ := by
      simpa [g] using hsg
    exact le_trans (le_of_lt hphi_lt) hphi_tau
  -- The sign control translates back to the normalized ray staying below the base objective.
  simpa [φ, u, lineSearchObjective_apply] using hphi_le

/-- Helper for Chapter02 Theorem 2.2.4: ambient differentiability of `f` at a normalized-ray
endpoint gives the left-continuity bridge needed in the first-exit argument. -/
private lemma rayObjective_continuousWithinAtEndpoint
    (f : Point → ℝ)
    {x u : Point}
    {τ : ℝ}
    (hGradAt : HasGradientAt f (∇ f (x + τ • u)) (x + τ • u)) :
    ContinuousWithinAt (fun s : ℝ ↦ f (x + s • u)) (Set.Iic τ) τ := by
  have hRayDiff : DifferentiableAt ℝ (fun s : ℝ ↦ x + s • u) τ := by
    -- The scalar affine ray is smooth at every time parameter.
    exact (((hasDerivAt_id' τ).smul_const u).const_add x).differentiableAt
  have hCompDiff : DifferentiableAt ℝ (fun s : ℝ ↦ f (x + s • u)) τ := by
    -- Compose the ambient differentiability of `f` with the affine ray.
    exact hGradAt.differentiableAt.comp τ hRayDiff
  exact hCompDiff.continuousAt.continuousWithinAt

/-- Helper for Chapter02 Theorem 2.2.4: once a normalized-ray endpoint is already known to stay
inside the initial sublevel set, its scalar derivative is strictly negative. -/
private lemma normalizedRay_derivNegAtGoodEndpoint
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (μ αbar ε : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_spec :
      ∀ ⦃y z : Point⦄,
        y ∈ initialSublevelSet f (x 0) →
        z ∈ initialSublevelSet f (x 0) →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2)
    {k : ℕ}
    (hkε : ε ≤ ‖∇ f (x k)‖)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) αbar)
    (hy : x k + t • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0)) :
    deriv (lineSearchObjective f (x k) ((‖d k‖)⁻¹ • d k)) t < 0 := by
  let u : Point := (‖d k‖)⁻¹ • d k
  let y : Point := x k + t • u
  have hmem : ∀ n : ℕ, x n ∈ initialSublevelSet f (x 0) :=
    exact_line_search_iterates_mem_initialSublevelSet
      f x d α h_descent h_exactLineSearch h_update hgrad_ne
  have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k (hgrad_ne k)
  have hdk_ne : d k ≠ 0 := hdesc.direction_ne
  have hmu_le_pi_div_two : μ ≤ Real.pi / 2 := by
    have hang_nonneg :
        0 ≤ InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) :=
      InnerProductGeometry.angle_nonneg _ _
    have hang_le :
        InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) ≤ Real.pi / 2 - μ :=
      h_angle 0 (hgrad_ne 0)
    linarith
  have hmu_lt_pi : μ < Real.pi := by
    linarith [Real.pi_pos, hmu_le_pi_div_two]
  have hsin_pos : 0 < Real.sin μ := Real.sin_pos_of_pos_of_lt_pi hμ hmu_lt_pi
  have hαbar_nonneg : 0 ≤ αbar := le_trans ht.1 ht.2
  have hhalf_nonneg : 0 ≤ (ε * Real.sin μ) / 2 := by
    have hzero := hαbar_spec (hmem k) (hmem k) (by simpa using hαbar_nonneg)
    simpa using hzero
  have hε_nonneg : 0 ≤ ε := by
    nlinarith [hhalf_nonneg, hsin_pos]
  have hderiv_le :
      deriv (lineSearchObjective f (x k) ((‖d k‖)⁻¹ • d k)) t ≤
        -((ε * Real.sin μ) / 2) :=
    normalized_short_ray_deriv_le_neg_half_gap
      f x d α μ αbar ε h_descent h_exactLineSearch h_update h_hasGradient hμ h_angle
      hgrad_ne hαbar_spec hkε ht hy
  rcases eq_or_lt_of_le hε_nonneg with hε_zero | hε_pos
  · have hdist_le : dist (x k) y ≤ αbar := by
      have hu_norm : ‖u‖ = 1 := by
        dsimp [u]
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hdk_ne))]
        field_simp [norm_ne_zero_iff.mpr hdk_ne]
      calc
        dist (x k) y = ‖t • u‖ := by
          simp [y, dist_eq_norm, sub_eq_add_neg, u, add_comm]
        _ = |t| * ‖u‖ := norm_smul t u
        _ = t := by
          rw [hu_norm, abs_of_nonneg ht.1]
          simp
        _ ≤ αbar := ht.2
    have hGradAt : HasGradientAt f (∇ f y) y := h_hasGradient y hy
    have hgrad_close : ‖∇ f y - ∇ f (x k)‖ ≤ 0 := by
      simpa [y, hε_zero.symm] using
        hαbar_spec hy (hmem k) (by simpa [y, dist_comm] using hdist_le)
    have hgrad_eq : ∇ f y = ∇ f (x k) := by
      have hsub_eq_zero : ∇ f y - ∇ f (x k) = 0 := by
        apply norm_eq_zero.mp
        exact le_antisymm hgrad_close (norm_nonneg _)
      exact sub_eq_zero.mp hsub_eq_zero
    have hderiv_eq :
        deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f (x k)) u := by
      have hderiv_y :
          deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f y) u := by
        simpa [y] using
          (hGradAt.deriv_lineSearchObjective_apply :
            deriv (lineSearchObjective f (x k) u) t = inner ℝ (∇ f y) u)
      simpa [hgrad_eq] using hderiv_y
    have hbase_neg : inner ℝ (∇ f (x k)) u < 0 := by
      -- Rescaling the direction by the positive factor `‖d k‖⁻¹` preserves descent.
      dsimp [u]
      rw [inner_smul_right]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr hdk_ne)) hdesc
    simpa [u] using hderiv_eq.trans_lt hbase_neg
  · have hhalf_pos : 0 < (ε * Real.sin μ) / 2 := by
      positivity
    linarith

/-- Helper for Chapter02 Theorem 2.2.4: the missing source-faithful first-exit step says that the
whole normalized short ray stays inside the initial sublevel set. -/
private lemma short_normalized_ray_stays_in_initialSublevelSet
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (μ αbar ε : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_hasGradient_all : ∀ y : Point, HasGradientAt f (∇ f y) y)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_pos : 0 < αbar)
    (hαbar_spec :
      ∀ ⦃y z : Point⦄,
        y ∈ initialSublevelSet f (x 0) →
        z ∈ initialSublevelSet f (x 0) →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2) :
    ∀ k : ℕ, ε ≤ ‖∇ f (x k)‖ →
      ∀ t ∈ Set.Icc (0 : ℝ) αbar,
        x k + t • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0) := by
  intro k hkε t ht
  let u : Point := (‖d k‖)⁻¹ • d k
  let ray : ℝ → Point := fun s ↦ x k + s • u
  let Good : ℝ → Prop := fun β ↦
    β ∈ Set.Icc (0 : ℝ) αbar ∧
      ∀ s ∈ Set.Icc (0 : ℝ) β, ray s ∈ initialSublevelSet f (x 0)
  let S : Set ℝ := {β : ℝ | Good β}
  have h_hasGradient :
      ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y := by
    intro y hy
    exact h_hasGradient_all y
  obtain ⟨δ, hδ_pos, hδ_le, hδ_prefix⟩ :=
    normalized_ray_has_initial_good_prefix
      f x d α αbar h_descent h_exactLineSearch h_update hgrad_ne hαbar_pos k
  have hδ_good : Good δ := by
    refine ⟨⟨hδ_pos.le, hδ_le⟩, ?_⟩
    simpa [ray, u] using hδ_prefix
  have hS_nonempty : S.Nonempty := by
    exact ⟨δ, by simpa [S] using hδ_good⟩
  have hS_bdd : BddAbove S := by
    refine ⟨αbar, ?_⟩
    intro β hβS
    exact (show Good β from by simpa [S] using hβS).1.2
  let τ : ℝ := sSup S
  have hτ_pos : 0 < τ := by
    have hδ_le_τ : δ ≤ τ := by
      exact le_csSup hS_bdd (by simpa [S] using hδ_good)
    exact lt_of_lt_of_le hδ_pos hδ_le_τ
  have hτ_le : τ ≤ αbar := by
    exact csSup_le hS_nonempty fun β hβS ↦ (show Good β from by simpa [S] using hβS).1.2
  have hGood_prefix :
      ∀ ⦃β s : ℝ⦄, Good β → s ∈ Set.Icc (0 : ℝ) β →
        ray s ∈ initialSublevelSet f (x 0) := by
    intro β s hβ hs
    exact hβ.2 s hs
  have hleft :
      ∀ s ∈ Set.Icc (0 : ℝ) τ, s < τ → ray s ∈ initialSublevelSet f (x 0) := by
    intro s hs hs_lt
    -- Every strict-left time is already contained in some earlier verified good prefix.
    exact good_prefix_mem_of_lt_csSup
      f (x 0) ray Good
      (by exact ⟨δ, hδ_good⟩)
      hGood_prefix hs.1 (by simpa [τ, S] using hs_lt)
  have hcont :
      ContinuousWithinAt (fun s : ℝ ↦ f (ray s)) (Set.Iic τ) τ := by
    -- Route correction: the endpoint continuity must come from the ambient gradient hypothesis.
    have hGradAt : HasGradientAt f (∇ f (ray τ)) (ray τ) := h_hasGradient_all (ray τ)
    simpa [ray, u] using
      (rayObjective_continuousWithinAtEndpoint (f := f) (x := x k) (u := u) (τ := τ) hGradAt)
  have hτ_mem : ray τ ∈ initialSublevelSet f (x 0) := by
    -- Left continuity upgrades the good-prefix invariant from strict-left times to the endpoint.
    exact good_prefix_endpoint_mem_of_continuousWithinAt
      f (x 0) ray hτ_pos hcont hleft
  have hτ_eq : τ = αbar := by
    rcases eq_or_lt_of_le hτ_le with hEq | hLt
    · exact hEq
    · have hderiv_neg :
        deriv (lineSearchObjective f (x k) u) τ < 0 := by
        have hτ_memIcc : τ ∈ Set.Icc (0 : ℝ) αbar := ⟨hτ_pos.le, hτ_le⟩
        simpa [ray, u] using
          (normalizedRay_derivNegAtGoodEndpoint
            f x d α μ αbar ε h_descent h_exactLineSearch h_update h_hasGradient hμ h_angle
            hgrad_ne hαbar_spec hkε hτ_memIcc hτ_mem)
      obtain ⟨η, hη_pos, hη_extend⟩ :=
        normalizedRay_extendPast_of_endpoint_deriv_neg
          f x d αbar hLt (by simpa [ray, u] using hτ_mem) (by simpa [u] using hderiv_neg)
      let β : ℝ := min αbar (τ + η / 2)
      have hβ_gt : τ < β := by
        dsimp [β]
        apply lt_min hLt
        linarith
      have hβ_le : β ≤ αbar := by
        dsimp [β]
        exact min_le_left _ _
      have hβ_good : Good β := by
        have hβ_nonneg : 0 ≤ β := le_of_lt (lt_trans hτ_pos hβ_gt)
        refine ⟨⟨hβ_nonneg, hβ_le⟩, ?_⟩
        intro s hs
        by_cases hs_le_τ : s ≤ τ
        · rcases lt_or_eq_of_le hs_le_τ with hs_lt_τ | hs_eq_τ
          · exact hleft s ⟨hs.1, hs_le_τ⟩ hs_lt_τ
          · simpa [ray, hs_eq_τ] using hτ_mem
        · have hs_gt_τ : τ < s := lt_of_not_ge hs_le_τ
          have hβ_le_extend : β ≤ min αbar (τ + η) := by
            dsimp [β]
            apply min_le_min
            · rfl
            · linarith
          have hs_extend : s ∈ Set.Ioc τ (min αbar (τ + η)) := by
            exact ⟨hs_gt_τ, le_trans hs.2 hβ_le_extend⟩
          exact hη_extend s hs_extend
      have hβ_le_τ : β ≤ τ := by
        exact le_csSup hS_bdd (by simpa [S] using hβ_good)
      exact (not_lt_of_ge hβ_le_τ hβ_gt).elim
  rcases eq_or_lt_of_le ht.2 with ht_eq | ht_lt
  · simpa [ray, u, hτ_eq, ht_eq] using hτ_mem
  · exact hleft t (by simpa [hτ_eq] using ht) (by simpa [hτ_eq] using ht_lt)

/-- Helper for Chapter02 Theorem 2.2.4: after fixing the uniform-continuity radius, the
normalized source trial point should already realize the uniform objective decrease. -/
private lemma uniform_trial_drop_on_normalized_ray
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (μ αbar ε : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_hasGradient_all : ∀ y : Point, HasGradientAt f (∇ f y) y)
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (hαbar_pos : 0 < αbar)
    (hαbar_spec :
      ∀ ⦃y z : Point⦄,
        y ∈ initialSublevelSet f (x 0) →
        z ∈ initialSublevelSet f (x 0) →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2) :
    ∀ k : ℕ, ε ≤ ‖∇ f (x k)‖ →
      f (x k + αbar • ((‖d k‖)⁻¹ • d k)) ≤
        f (x k) - αbar * (ε * Real.sin μ) / 2 := by
  intro k hkε
  have h_hasGradient :
      ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y := by
    intro y hy
    exact h_hasGradient_all y
  have hshort :
      ∀ t ∈ Set.Icc (0 : ℝ) αbar,
        x k + t • ((‖d k‖)⁻¹ • d k) ∈ initialSublevelSet f (x 0) :=
    short_normalized_ray_stays_in_initialSublevelSet
      f x d α μ αbar ε h_descent h_exactLineSearch h_update h_hasGradient_all hμ h_angle
      hgrad_ne hαbar_pos hαbar_spec k hkε
  have hbarrier :
      f (x k + αbar • ((‖d k‖)⁻¹ • d k)) ≤
        f (x k) - αbar * ((ε * Real.sin μ) / 2) :=
    normalized_ray_affine_barrier_on_prefix
      f x d α μ αbar ε αbar h_descent h_exactLineSearch h_update
      h_hasGradient hμ
      h_angle hgrad_ne hαbar_spec hkε le_rfl hshort αbar ⟨hαbar_pos.le, le_rfl⟩
  -- Once the whole short ray is good, the affine barrier can be read at the endpoint `αbar`.
  have hrewrite :
      f (x k) - αbar * ((ε * Real.sin μ) / 2) =
        f (x k) - αbar * (ε * Real.sin μ) / 2 := by
    ring
  rwa [hrewrite] at hbarrier

/-- Helper for Chapter02 Theorem 2.2.4: along any subsequence whose gradient norms stay above a
fixed positive threshold, uniform continuity of `∇ f` on the initial sublevel set should force a
uniform objective decrease. -/
private lemma uniform_exact_step_drop_of_gradient_norm_lower_bound
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (μ : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_hasGradient_all : ∀ y : Point, HasGradientAt f (∇ f y) y)
    (h_gradUniform :
      UniformContinuousOn (∇ f) (initialSublevelSet f (x 0)))
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ αbar > 0, ∀ k : ℕ, ε ≤ ‖∇ f (x k)‖ →
        f (x (k + 1)) ≤ f (x k) - αbar * (ε * Real.sin μ) / 2 := by
  intro ε hε
  have hmu_le_pi_div_two : μ ≤ Real.pi / 2 := by
    have hang_nonneg :
        0 ≤ InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) :=
      InnerProductGeometry.angle_nonneg _ _
    have hang_le :
        InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) ≤ Real.pi / 2 - μ :=
      h_angle 0 (hgrad_ne 0)
    linarith
  have hmu_lt_pi : μ < Real.pi := by
    linarith [Real.pi_pos, hmu_le_pi_div_two]
  have hsin_pos : 0 < Real.sin μ :=
    Real.sin_pos_of_pos_of_lt_pi hμ hmu_lt_pi
  have hhalf_pos : 0 < (ε * Real.sin μ) / 2 := by
    positivity
  rcases (Metric.uniformContinuousOn_iff_le.mp h_gradUniform) ((ε * Real.sin μ) / 2) hhalf_pos with
    ⟨αbar, hαbar_pos, hαbar_spec_dist⟩
  have hαbar_spec :
      ∀ ⦃y z : Point⦄,
        y ∈ initialSublevelSet f (x 0) →
        z ∈ initialSublevelSet f (x 0) →
        dist y z ≤ αbar →
        ‖∇ f y - ∇ f z‖ ≤ (ε * Real.sin μ) / 2 := by
    intro y z hy hz hdist
    simpa [dist_eq_norm] using hαbar_spec_dist y hy z hz hdist
  refine ⟨αbar, hαbar_pos, ?_⟩
  intro k hkε
  have hdesc : IsDescentDirectionAt f (x k) (d k) := h_descent k (hgrad_ne k)
  have hdk_pos : 0 < ‖d k‖ := norm_pos_iff.mpr hdesc.direction_ne
  have htrial_drop :
      f (x k + αbar • ((‖d k‖)⁻¹ • d k)) ≤
        f (x k) - αbar * (ε * Real.sin μ) / 2 :=
    uniform_trial_drop_on_normalized_ray
      f x d α μ αbar ε h_descent h_exactLineSearch h_update h_hasGradient_all hμ h_angle
      hgrad_ne hαbar_pos hαbar_spec k hkε
  have hmin :
      f (x (k + 1)) ≤ f (x k + αbar • ((‖d k‖)⁻¹ • d k)) := by
    have hopt :
        lineSearchObjective f (x k) (d k) (α k) ≤
          lineSearchObjective f (x k) (d k) (αbar / ‖d k‖) :=
      (h_exactLineSearch k).optimal (by positivity)
    -- Exact optimality lets us compare the accepted step directly with the normalized trial step.
    simpa [lineSearchObjective_apply, h_update k, div_eq_mul_inv, smul_smul, mul_assoc,
      mul_left_comm, mul_comm] using hopt
  exact le_trans hmin htrial_drop

/-- Helper for Chapter02 Theorem 2.2.4: a uniform one-step objective drop along a frequently
large-gradient subsequence yields a frequent lower bound on the decrease gaps. -/
private lemma frequentlyGapGe_of_uniformExactDrop
    (f : Point → ℝ)
    (x : ℕ → Point)
    (ε c : ℝ)
    (hfreq : ∃ᶠ k : ℕ in atTop, ε ≤ ‖∇ f (x k)‖)
    (hdrop : ∀ k : ℕ, ε ≤ ‖∇ f (x k)‖ → f (x (k + 1)) ≤ f (x k) - c) :
    ∃ᶠ k : ℕ in atTop, c ≤ f (x k) - f (x (k + 1)) := by
  -- Rewrite each one-step estimate into the corresponding decrease-gap lower bound.
  refine hfreq.mono ?_
  intro k hk
  have hk_drop : f (x (k + 1)) ≤ f (x k) - c := hdrop k hk
  linarith

/-- Helper for Chapter02 Theorem 2.2.4: in the nonstationary bounded-below branch, the textbook
uniform-drop contradiction forces `∇ f (x k) ⟶ 0`. -/
private lemma gradientTendstoZero_of_nonstationary_notAtBot
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (μ : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, x (k + 1) = x k + α k • d k)
    (h_hasGradient_all : ∀ y : Point, HasGradientAt f (∇ f y) y)
    (h_gradUniform :
      UniformContinuousOn (∇ f) (initialSublevelSet f (x 0)))
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ)
    (hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0)
    (h_not_atBot : ¬ Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot) :
    Tendsto (fun k : ℕ ↦ ∇ f (x k)) atTop (nhds 0) := by
  by_contra h_not_tendsto
  have hgap_zero :
      Tendsto (fun k : ℕ ↦ f (x k) - f (x (k + 1))) atTop (nhds 0) :=
    decrease_gap_tendsto_zero_of_not_atBot
      f x d α h_descent h_exactLineSearch h_update hgrad_ne h_not_atBot
  rcases frequently_gradient_norm_ge_of_not_tendsto_zero f x h_not_tendsto with
    ⟨ε, hε_pos, hfreqε⟩
  rcases uniform_exact_step_drop_of_gradient_norm_lower_bound
      f x d α μ h_descent h_exactLineSearch h_update h_hasGradient_all h_gradUniform hμ h_angle
      hgrad_ne hε_pos with
    ⟨αbar, hαbar_pos, hdrop⟩
  have hmu_le_pi_div_two : μ ≤ Real.pi / 2 := by
    have hang_nonneg :
        0 ≤ InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) :=
      InnerProductGeometry.angle_nonneg _ _
    have hang_le :
        InnerProductGeometry.angle (d 0) (-(∇ f (x 0))) ≤ Real.pi / 2 - μ :=
      h_angle 0 (hgrad_ne 0)
    linarith
  have hmu_lt_pi : μ < Real.pi := by
    linarith [Real.pi_pos, hmu_le_pi_div_two]
  have hsin_pos : 0 < Real.sin μ := Real.sin_pos_of_pos_of_lt_pi hμ hmu_lt_pi
  let c : ℝ := αbar * (ε * Real.sin μ) / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hfreq_gap :
      ∃ᶠ k : ℕ in atTop, c ≤ f (x k) - f (x (k + 1)) :=
    frequentlyGapGe_of_uniformExactDrop f x ε c hfreqε (fun k hk ↦ by
      simpa [c] using hdrop k hk)
  have hgap_char :
      Tendsto (fun k : ℕ ↦ f (x k) - f (x (k + 1))) atTop (nhds (0 : ℝ)) ↔
        ∀ δ > 0, ∃ N, ∀ n ≥ N, dist (f (x n) - f (x (n + 1))) 0 < δ := by
    exact Metric.tendsto_atTop
  rw [hgap_char] at hgap_zero
  rcases hgap_zero c hc_pos with ⟨N, hN⟩
  have h_eventually_lt :
      ∀ᶠ k : ℕ in atTop, f (x k) - f (x (k + 1)) < c := by
    rw [eventually_atTop]
    refine ⟨N, ?_⟩
    intro n hn
    have hdist : dist (f (x n) - f (x (n + 1))) 0 < c := hN n hn
    have habs : |f (x n) - f (x (n + 1))| < c := by
      simpa [Real.dist_eq] using hdist
    exact (abs_lt.mp habs).2
  have hFalse : ∃ᶠ k : ℕ in atTop, False := by
    refine (hfreq_gap.and_eventually h_eventually_lt).mono ?_
    intro k hk
    exact (not_lt_of_ge hk.1 hk.2).elim
  simp at hFalse

/- Chapter02 Theorem 2.2.4 stays source-facing in the book setting `Point = ℝ^n`; the
local notation `Point` abbreviates `EuclideanSpace ℝ (Fin n)` for readability. -/
/-- Chapter02 Theorem 2.2.4: let `x`, `d`, and `α` be generated by the exact-line-search
scheme of Chapter02 Algorithm 2.2.1 for `f : Point → ℝ`, meaning that on each
nonstationary iterate `x k` the direction `d k` is a descent direction in the canonical
Chapter 1 sense `IsDescentDirectionAt f (x k) (d k)`, the steplength `α k` is an exact
line-search step on the nonnegative ray from `x k` along `d k`, and the next iterate satisfies
`x (k + 1) = x k + α k • d k`. Assume `∇ f` is uniformly continuous on the initial sublevel set
`initialSublevelSet f (x 0) = {y | f y ≤ f (x 0)}`, and that the displayed field `∇ f` is the
genuine gradient of `f` at every ambient point of `Point`. Assume further
that the angle between `d k` and `-gradient f (x k)` is uniformly bounded away from `π / 2` on
every nonstationary iterate,
i.e. there exists `μ > 0` such that
`InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ` whenever
`∇ f (x k) ≠ 0`. Then either `∇ f (x k) = 0` for some `k`, or `f (x k) ⟶ -∞`, or
`∇ f (x k) ⟶ 0`. -/
theorem exactLineSearch_globalConvergence
    (f : Point → ℝ)
    (x d : ℕ → Point)
    (α : ℕ → ℝ)
    (μ : ℝ)
    (h_descent : ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsDescentDirectionAt f (x k) (d k))
    (h_exactLineSearch :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 → IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k))
    (h_update : ∀ k : ℕ, ∇ f (x k) ≠ 0 → x (k + 1) = x k + α k • d k)
    (h_hasGradient : ∀ y : Point, HasGradientAt f (∇ f y) y)
    (h_gradUniform :
      UniformContinuousOn (∇ f) (initialSublevelSet f (x 0)))
    (hμ : 0 < μ)
    (h_angle :
      ∀ k : ℕ, ∇ f (x k) ≠ 0 →
        InnerProductGeometry.angle (d k) (-(∇ f (x k))) ≤ Real.pi / 2 - μ) :
    (∃ k : ℕ, ∇ f (x k) = 0) ∨
      Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot ∨
      Tendsto (fun k : ℕ ↦ ∇ f (x k)) atTop (nhds 0) := by
  by_cases hstationary : ∃ k : ℕ, ∇ f (x k) = 0
  · -- The stationary branch is the first textbook alternative.
    exact Or.inl hstationary
  · have hgrad_ne : ∀ k : ℕ, ∇ f (x k) ≠ 0 := by
      intro k hk
      exact hstationary ⟨k, hk⟩
    have h_exactLineSearch' :
        ∀ k : ℕ, IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k) := by
      intro k
      exact h_exactLineSearch k (hgrad_ne k)
    have h_update' : ∀ k : ℕ, x (k + 1) = x k + α k • d k := by
      intro k
      exact h_update k (hgrad_ne k)
    by_cases h_atBot : Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot
    · -- The unbounded-descent branch is the second textbook alternative.
      exact Or.inr (Or.inl h_atBot)
    · -- In the remaining branch, the uniform-drop contradiction yields gradient convergence.
      refine Or.inr (Or.inr ?_)
      exact gradientTendstoZero_of_nonstationary_notAtBot
        f x d α μ h_descent h_exactLineSearch' h_update' h_hasGradient
        h_gradUniform hμ
        h_angle hgrad_ne h_atBot

end Theorem224
