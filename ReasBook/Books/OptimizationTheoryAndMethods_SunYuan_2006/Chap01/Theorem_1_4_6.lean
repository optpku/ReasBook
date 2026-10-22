/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_14

section Chapter01Theorem146

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open AffineMap
open scoped Topology

-- Domain sampling:
-- * primary domain: second-order local optimality in finite-dimensional real inner-product spaces
-- * source-facing layer: Chapter 1 second-order sufficient condition
-- * owner abstractions inspected:
--   `IsStrictLocalMin`, `IsStationaryPoint`, `IsLocalMin`, `ContDiffAt`
-- * Hessian positivity surface inspected:
--   `QuadraticMap.PosDef` is a canonical quadratic-form owner in mathlib, but this chapter's
--   Hessian API is already standardized on the multilinear evaluation
--   `(iteratedFDeriv ℝ 2 f x) ![y, y]`, so the theorem keeps that owner surface
-- Primitive data vs derived API:
-- * primitive data: local `C²` regularity at `xStar`, a stationary-point owner, and positive
--   Hessian quadratic form in every nonzero direction
-- * derived API: the strict-local-minimum conclusion
-- The main theorem should use the chapter owners `IsStationaryPoint` and `IsStrictLocalMin`;
-- the raw zero-gradient form is kept only as a thin bridge.

/-- Helper for Chapter01 Theorem 1.4.6: positive definiteness of the Hessian quadratic form at
`xStar` persists on a sufficiently small ball around `xStar`. -/
lemma iteratedFDeriv_pos_on_small_ball
    [Nontrivial E]
    (f : E → ℝ) (xStar : E) (hC2 : ContDiffAt ℝ 2 f xStar)
    (hPosDef :
      ∀ y : E, y ≠ 0 → 0 < (iteratedFDeriv ℝ 2 f xStar) ![y, y]) :
    ∃ δ > 0, ∀ z ∈ Metric.ball xStar δ, ∀ y : E, y ≠ 0 →
      0 < (iteratedFDeriv ℝ 2 f z) ![y, y] := by
  let A0 := iteratedFDeriv ℝ 2 f xStar
  let q : E → ℝ := fun y ↦ A0 ![y, y]
  -- First control the quadratic form on the unit sphere by compactness.
  have hq_cont : Continuous q := by
    fun_prop
  have hsphere_compact : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere _ _
  have hsphere_nonempty : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u0, hu0, hu0min⟩ :=
    hsphere_compact.exists_isMinOn hsphere_nonempty hq_cont.continuousOn
  have hu0_norm : ‖u0‖ = 1 := by
    simp [Metric.mem_sphere, dist_eq_norm] at hu0
    exact hu0
  have hu0_ne : u0 ≠ 0 := by
    intro hu0_zero
    have : ‖u0‖ = 0 := by simpa [hu0_zero]
    linarith
  let m : ℝ := q u0
  have hm_pos : 0 < m := hPosDef u0 hu0_ne
  have hm_lower : ∀ u ∈ Metric.sphere (0 : E) 1, m ≤ q u := by
    intro u hu
    exact hu0min hu
  -- Then continuity of the Hessian in operator norm lets us transfer this positivity nearby.
  have hm_half_pos : 0 < m / 2 := by positivity
  have hcontA : ContinuousAt (iteratedFDeriv ℝ 2 f) xStar :=
    hC2.continuousAt_iteratedFDeriv (by norm_num)
  have hA_ball :
      (iteratedFDeriv ℝ 2 f) ⁻¹' Metric.ball A0 (m / 2) ∈ 𝓝 xStar :=
    hcontA.preimage_mem_nhds (Metric.ball_mem_nhds A0 hm_half_pos)
  rcases Metric.mem_nhds_iff.mp hA_ball with ⟨δ, hδ, hδball⟩
  refine ⟨δ, hδ, ?_⟩
  intro z hz y hy
  set u : E := ‖y‖⁻¹ • y
  have hy_norm_ne : ‖y‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hy
  have hu_sphere : u ∈ Metric.sphere (0 : E) 1 := by
    simp [u, hy_norm_ne, norm_smul]
  have hu_norm : ‖u‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hu_sphere
  have hzA :
      ‖iteratedFDeriv ℝ 2 f z - A0‖ < m / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hδball hz
  have hOp :
      ‖(iteratedFDeriv ℝ 2 f z - A0) ![u, u]‖ ≤ ‖iteratedFDeriv ℝ 2 f z - A0‖ := by
    have hle := (iteratedFDeriv ℝ 2 f z - A0).le_opNorm ![u, u]
    simpa [hu_norm] using hle
  have habs :
      |(iteratedFDeriv ℝ 2 f z) ![u, u] - A0 ![u, u]| < m / 2 := by
    have hzA' :
        ‖(iteratedFDeriv ℝ 2 f z - A0) ![u, u]‖ < m / 2 :=
      lt_of_le_of_lt hOp hzA
    simpa [A0, Real.norm_eq_abs] using hzA'
  have hA0_lower : m ≤ A0 ![u, u] := hm_lower u hu_sphere
  have hunit_pos : 0 < (iteratedFDeriv ℝ 2 f z) ![u, u] := by
    have hdiff_lower :
        -(m / 2) < (iteratedFDeriv ℝ 2 f z) ![u, u] - A0 ![u, u] :=
      (abs_lt.mp habs).1
    have hA0_half : m / 2 < A0 ![u, u] := by
      nlinarith [hA0_lower, hm_pos]
    linarith
  -- Finally rescale an arbitrary nonzero direction to the unit sphere.
  have hy_expand : y = ‖y‖ • u := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hy_norm_ne, one_smul]
  have hy_eval :
      (iteratedFDeriv ℝ 2 f z) ![y, y] =
        (‖y‖ * ‖y‖) * (iteratedFDeriv ℝ 2 f z) ![u, u] := by
    have hyy : (![y, y] : Fin 2 → E) = fun _ : Fin 2 ↦ ‖y‖ • u := by
      ext i
      fin_cases i <;> exact hy_expand
    have huu : (![u, u] : Fin 2 → E) = fun _ : Fin 2 ↦ u := by
      ext i
      fin_cases i <;> rfl
    have hmap :
        (iteratedFDeriv ℝ 2 f z) ![y, y] =
          ‖y‖ ^ (2 : ℕ) * (iteratedFDeriv ℝ 2 f z) ![u, u] := by
      simpa [hyy, huu] using
        (iteratedFDeriv ℝ 2 f z).map_smul_univ (fun _ : Fin 2 ↦ ‖y‖) (fun _ ↦ u)
    simpa [pow_two] using hmap
  have : 0 < (‖y‖ * ‖y‖) * (iteratedFDeriv ℝ 2 f z) ![u, u] := by
    positivity
  simpa [hy_eval] using this

/-- Helper for Chapter01 Theorem 1.4.6: a positive definite Hessian at `xStar` yields strict
convexity on a sufficiently small ball around `xStar`. -/
lemma strictConvexOn_ball_of_iteratedFDeriv_pos_at
    [Nontrivial E]
    (f : E → ℝ) (xStar : E) (hC2 : ContDiffAt ℝ 2 f xStar)
    (hPosDef :
      ∀ y : E, y ≠ 0 → 0 < (iteratedFDeriv ℝ 2 f xStar) ![y, y]) :
    ∃ δ > 0, StrictConvexOn ℝ (Metric.ball xStar δ) f := by
  rcases hC2.contDiffOn' (m := 2) le_rfl (by simp) with ⟨u, hu_open, hxu, hC2u_raw⟩
  have hC2u : ContDiffOn ℝ 2 f u := by
    simpa using hC2u_raw
  rcases Metric.mem_nhds_iff.mp (hu_open.mem_nhds hxu) with ⟨r, hr, hr_sub⟩
  rcases iteratedFDeriv_pos_on_small_ball f xStar hC2 hPosDef with ⟨δ0, hδ0, hPos0⟩
  let δ := min r δ0
  have hδ : 0 < δ := lt_min hr hδ0
  have hball_sub_u : Metric.ball xStar δ ⊆ u := by
    exact Set.Subset.trans (Metric.ball_subset_ball (min_le_left _ _)) hr_sub
  have hC2ball : ContDiffOn ℝ 2 f (Metric.ball xStar δ) := hC2u.mono hball_sub_u
  have hPosball :
      ∀ z ∈ Metric.ball xStar δ, ∀ y : E, y ≠ 0 →
        0 < (iteratedFDeriv ℝ 2 f z) ![y, y] := by
    intro z hz y hy
    exact hPos0 z (Metric.ball_subset_ball (min_le_right _ _) hz) y hy
  refine ⟨δ, hδ, ?_⟩
  -- Route correction: `ContDiffAt` is first localized to an open neighborhood before invoking
  -- the chapter's strict-convexity theorem on the smaller ball.
  exact strictConvexOn_of_iteratedFDeriv_pos Metric.isOpen_ball (convex_ball xStar δ) hC2ball
    hPosball

/-- Helper for Chapter01 Theorem 1.4.6: on a ball where `f` is strictly convex, a stationary
point at the center has strictly smaller value than any distinct point of the ball. -/
lemma lt_of_ne_of_mem_ball_of_strictConvexOn_of_isStationaryPoint
    {f : E → ℝ} {xStar y : E} {δ : ℝ}
    (hy : y ∈ Metric.ball xStar δ) (hxy : y ≠ xStar)
    (hStrict : StrictConvexOn ℝ (Metric.ball xStar δ) f)
    (hStat : IsStationaryPoint f xStar) :
    f xStar < f y := by
  let g : ℝ → ℝ := f ∘ lineMap xStar y
  have hMaps : Set.Icc (0 : ℝ) 1 ⊆ (lineMap xStar y) ⁻¹' Metric.ball xStar δ := by
    intro t ht
    have hδ : 0 < δ := by
      simpa [dist_eq_norm] using (dist_nonneg.trans_lt hy)
    have hxBall : xStar ∈ Metric.ball xStar δ := Metric.mem_ball_self hδ
    have hseg :
        segment ℝ xStar y ⊆ Metric.ball xStar δ :=
      (convex_ball xStar δ).segment_subset hxBall hy
    exact hseg <| by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
  have hStrict_g : StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
    intro s hs t ht hst a b ha hb hab
    have hsBall : lineMap xStar y s ∈ Metric.ball xStar δ := hMaps hs
    have htBall : lineMap xStar y t ∈ Metric.ball xStar δ := hMaps ht
    have hline_ne : lineMap xStar y s ≠ lineMap xStar y t := by
      intro hEq
      exact hst ((AffineMap.lineMap_injective (k := ℝ) hxy.symm) hEq)
    -- The affine line through `xStar` and `y` transports strict convexity to `[0,1]`.
    calc
      g (a • s + b • t) = f (lineMap xStar y (a • s + b • t)) := rfl
      _ = f (a • lineMap xStar y s + b • lineMap xStar y t) := by
        rw [Convex.combo_affine_apply hab]
      _ < a • f (lineMap xStar y s) + b • f (lineMap xStar y t) :=
        hStrict.2 hsBall htBall hline_ne ha hb hab
      _ = a • g s + b • g t := rfl
  have hgDeriv : HasDerivAt g 0 0 := by
    -- The stationary-point hypothesis makes the directional derivative vanish at `t = 0`.
    have hLine : HasDerivAt (lineMap xStar y : ℝ → E) (y - xStar) 0 :=
      hasDerivAt_lineMap
    have hFDeriv : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) 0) xStar :=
      hStat.hasGradientAt.hasFDerivAt
    simpa [g] using
      (hFDeriv.comp_hasDerivAt_of_eq (0 : ℝ) hLine (lineMap_apply_zero xStar y).symm)
  have hslope : 0 < slope g 0 1 := by
    simpa [hgDeriv.deriv] using
      hStrict_g.deriv_lt_slope (by simp) (by simp) zero_lt_one hgDeriv.differentiableAt
  -- The positive secant slope is exactly the desired strict increase from `0` to `1`.
  simpa [g, slope_def_field, lineMap_apply_zero, lineMap_apply_one] using hslope

/-- Chapter01 Theorem 1.4.6 (Second-Order Sufficient Condition): on a finite-dimensional real
inner-product space, if `f` is `C²` at `xStar`, `xStar` is a stationary point of `f`, and the
Hessian quadratic form at `xStar` is positive in every nonzero direction, then `xStar` is a
strict local minimizer of `f`, formalized by the Chapter 1 owner `IsStrictLocalMin`. This is the
invariant form of the book's `ℝⁿ` statement. -/
theorem isStrictLocalMin_of_isStationaryPoint_of_iteratedFDeriv_pos
    (f : E → ℝ) (xStar : E) (hC2 : ContDiffAt ℝ 2 f xStar)
    (hStat : IsStationaryPoint f xStar)
    (hPosDef :
      ∀ y : E, y ≠ 0 → 0 < (iteratedFDeriv ℝ 2 f xStar) ![y, y]) :
    IsStrictLocalMin f xStar := by
  by_cases hE : Subsingleton E
  · rw [isStrictLocalMin_iff_exists_forall_mem_ball]
    refine ⟨1, zero_lt_one, ?_⟩
    intro y _ hy
    exact (hy (hE.elim _ _)).elim
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    rcases strictConvexOn_ball_of_iteratedFDeriv_pos_at f xStar hC2 hPosDef with
      ⟨δ, hδ, hStrict⟩
    rw [isStrictLocalMin_iff_exists_forall_mem_ball]
    refine ⟨δ, hδ, ?_⟩
    intro y hy hy_ne
    -- The source proof's Taylor-line argument is encoded on the affine segment from `xStar` to `y`.
    exact lt_of_ne_of_mem_ball_of_strictConvexOn_of_isStationaryPoint hy hy_ne hStrict hStat

/-- Gradient-zero bridge for Chapter01 Theorem 1.4.6: under the local `C²` hypothesis, the
stationary-point owner is equivalent to the usual vanishing-gradient formulation. -/
theorem isStrictLocalMin_of_gradient_eq_zero_of_iteratedFDeriv_pos
    (f : E → ℝ) (xStar : E) (hC2 : ContDiffAt ℝ 2 f xStar)
    (hGrad : gradient f xStar = 0)
    (hPosDef :
      ∀ y : E, y ≠ 0 → 0 < (iteratedFDeriv ℝ 2 f xStar) ![y, y]) :
    IsStrictLocalMin f xStar := by
  refine isStrictLocalMin_of_isStationaryPoint_of_iteratedFDeriv_pos f xStar hC2 ?_ hPosDef
  rw [isStationaryPoint_iff]
  exact ⟨hGrad, hC2.differentiableAt (by decide)⟩

end Chapter01Theorem146
