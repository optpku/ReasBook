/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {X : Type u} [MetricSpace X]

/-- The pointwise growth function `ω_f(xBar; t)` is the supremum of the increments
`f y - f xBar` over the closed ball of radius `t` around `xBar`, recorded in `WithTop ℝ` so that
unbounded growth is represented by `⊤`; it is set to `0` for negative radii. -/
def pointwiseGrowthFunction (f : X → ℝ) (xBar : X) (t : ℝ) : WithTop ℝ :=
  if 0 ≤ t then
    sSup ((fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) '' Metric.closedBall xBar t)
  else
    0

/- Source-facing Lean notation for the textbook growth profile `ω_f(xBar; t)`. -/
scoped[PointwiseGrowthFunction] notation:max "ω[" f ";" xBar "]" =>
  pointwiseGrowthFunction f xBar

open scoped PointwiseGrowthFunction

/-- The growth function is `0` at every negative radius. -/
-- Proof sketch: unfold `pointwiseGrowthFunction` and simplify the defining `if` using `t < 0`.
theorem pointwiseGrowthFunction_eq_zero_of_neg
    {f : X → ℝ} {xBar : X} {t : ℝ} (ht : t < 0) :
    ω[f; xBar] t = 0 := by
  simp [pointwiseGrowthFunction, not_le_of_gt ht]

end

section

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {f : V → ℝ} {g : V → V}

open scoped PointwiseGrowthFunction

/-- The localization measure `v_f(xBar; x)` associated to a chosen subgradient selection `g`,
generalized from the textbook Euclidean setting to an arbitrary real inner product space. It is
the signed projection of `x - xBar` onto the normalized subgradient direction at `x`, and it is
defined to be `0` when the chosen subgradient vanishes. -/
def subgradientLocalizationMeasure (g : V → V) (xBar x : V) : ℝ :=
  by
    classical
    exact if g x = 0 then 0 else inner ℝ (g x) (x - xBar) / ‖g x‖

/- Source-facing Lean notation for the textbook localization measure `v_f(xBar; x)`, with the
chosen subgradient selection `g` supplying the formalized owner data. -/
scoped[SubgradientLocalizationMeasure] notation:max "v[" g ";" xBar "]" =>
  subgradientLocalizationMeasure g xBar

open scoped SubgradientLocalizationMeasure

/-- The localization measure vanishes whenever the chosen subgradient at `x` is `0`. -/
-- Proof sketch: unfold `subgradientLocalizationMeasure` and simplify the defining `if` by the
-- assumption `g x = 0`.
theorem subgradientLocalizationMeasure_eq_zero_of_eq_zero
    {xBar x : V} (hg : g x = 0) :
    v[g; xBar] x = 0 := by
  classical
  simp [subgradientLocalizationMeasure, hg]

/-- For a nonzero chosen subgradient, the localization measure is the normalized inner product
`⟪g x, x - xBar⟫ / ‖g x‖`. -/
-- Proof sketch: unfold `subgradientLocalizationMeasure`; the defining `if` reduces to its
-- nonzero branch under the hypothesis `g x ≠ 0`.
theorem subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero
    {xBar x : V} (hg : g x ≠ 0) :
    v[g; xBar] x = inner ℝ (g x) (x - xBar) / ‖g x‖ := by
  classical
  simp [subgradientLocalizationMeasure, hg]

/-- If `g x` is a subgradient at `x` and `xBar` does not have larger function value than `x`,
then the localization measure relative to `xBar` is nonnegative. -/
theorem subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
    {xBar x : V}
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x))
    (hfx : f xBar ≤ f x) :
    0 ≤ v[g; xBar] x := by
  classical
  by_cases hzero : g x = 0
  · simp [subgradientLocalizationMeasure, hzero]
  · rw [subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero hzero]
    exact
      div_nonneg
        (hgx.nonneg_inner_sub_of_le (by exact_mod_cast hfx))
        (norm_nonneg _)

/-- Helper for Lemma 3.2.1: evaluating the subgradient inequality at `xBar` bounds the increment
`f x - f xBar` by the pairing with `x - xBar`. -/
theorem subgradient_gap_le_inner_sub
    {xBar x : V}
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x)) :
    f x - f xBar ≤ inner ℝ (g x) (x - xBar) := by
  -- Evaluate the real-valued subgradient inequality at the comparison point `xBar`.
  have hgx' : ∀ y : V, f y ≥ f x + inner ℝ (g x) (y - x) :=
    IsSubgradientAt.coe_real_iff.mp hgx
  have hbar : f x + inner ℝ (g x) (xBar - x) ≤ f xBar := by
    linarith [hgx' xBar]
  -- Rewrite the pairing against `xBar - x` as the negative of the pairing against `x - xBar`.
  have hinner : inner ℝ (g x) (xBar - x) = -inner ℝ (g x) (x - xBar) := by
    rw [show xBar - x = -(x - xBar) by
      rw [sub_eq_neg_add, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm]]
    rw [inner_neg_right]
  linarith

/-- Helper for Lemma 3.2.1: the growth function is nonnegative at every nonnegative radius
because `xBar` itself contributes the increment `0` to the defining supremum. -/
theorem pointwiseGrowthFunction_nonneg_of_nonneg_radius
    {xBar : V} {t : ℝ} (ht : 0 ≤ t) :
    ((0 : ℝ) : WithTop ℝ) ≤ ω[f; xBar] t := by
  -- Insert the center point `xBar` into the image set defining the supremum.
  rw [pointwiseGrowthFunction, if_pos ht]
  have hzero_mem :
      (0 : WithTop ℝ) ∈
        (fun y : V ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) '' Metric.closedBall xBar t := by
    simpa using Set.mem_image_of_mem
      (fun y : V ↦ ((f y - f xBar : ℝ) : WithTop ℝ))
      (Metric.mem_closedBall_self ht)
  exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hzero_mem

/-- Helper for Lemma 3.2.1: when the localization measure is nonnegative and the chosen
subgradient is nonzero, the source proof's ray point lies on the radius-`v_f(xBar; x)` sphere
and has function value at least `f x`. -/
theorem exists_localization_contact_point
    {xBar x : V}
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x))
    (hgz : g x ≠ 0)
    (hv : 0 ≤ v[g; xBar] x) :
    ∃ yBar : V, yBar ∈ Metric.closedBall xBar (v[g; xBar] x) ∧ f x ≤ f yBar := by
  let yBar : V := xBar + (v[g; xBar] x / ‖g x‖) • g x
  have hnorm_pos : 0 < ‖g x‖ := norm_pos_iff.mpr hgz
  have hloc :
      v[g; xBar] x = inner ℝ (g x) (x - xBar) / ‖g x‖ :=
    subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero (g := g) (xBar := xBar) (x := x) hgz
  -- The chosen point is exactly at distance `v[g; xBar] x` from `xBar`.
  have hyBall : yBar ∈ Metric.closedBall xBar (v[g; xBar] x) := by
    rw [Metric.mem_closedBall]
    have hdist :
        dist yBar xBar = v[g; xBar] x := by
      have hshift :
          ‖(v[g; xBar] x / ‖g x‖) • g x‖ = v[g; xBar] x := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg hv (norm_nonneg _))]
        field_simp [hnorm_pos.ne']
      simpa [yBar, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift
    exact le_of_eq hdist
  -- The ray point makes the pairing with `g x` vanish, so the subgradient inequality gives
  -- `f x ≤ f yBar`.
  have hy_inner : inner ℝ (g x) (yBar - x) = 0 := by
    calc
      inner ℝ (g x) (yBar - x)
          = inner ℝ (g x) (xBar - x) + inner ℝ (g x) ((v[g; xBar] x / ‖g x‖) • g x) := by
              simp [yBar, sub_eq_add_neg, inner_add_right, add_comm, add_left_comm, add_assoc]
      _ = inner ℝ (g x) (xBar - x) + v[g; xBar] x * ‖g x‖ := by
            rw [inner_smul_right, real_inner_self_eq_norm_sq]
            field_simp [hnorm_pos.ne']
      _ = inner ℝ (g x) (xBar - x) + inner ℝ (g x) (x - xBar) := by
            rw [hloc]
            have hcancel :
                (inner ℝ (g x) (x - xBar) / ‖g x‖) * ‖g x‖ =
                  inner ℝ (g x) (x - xBar) := by
              field_simp [hnorm_pos.ne']
            rw [hcancel]
      _ = 0 := by
            rw [show inner ℝ (g x) (xBar - x) = -inner ℝ (g x) (x - xBar) by
              rw [show xBar - x = -(x - xBar) by
                rw [sub_eq_neg_add, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm]]
              rw [inner_neg_right]]
            ring
  have hgx' : ∀ y : V, f y ≥ f x + inner ℝ (g x) (y - x) :=
    IsSubgradientAt.coe_real_iff.mp hgx
  have hvalue : f x ≤ f yBar := by
    linarith [hgx' yBar, hy_inner]
  exact ⟨yBar, hyBall, hvalue⟩

/-- Lemma 3.2.1, generalized from the textbook Euclidean setting: if `g x` is a subgradient of
`f` at `x`, then the increment `f x - f xBar` is bounded by the growth function
`ω_f(xBar; v_f(xBar; x))` built from the same chosen value `g x`, i.e. formula `(3.2.11)`. -/
-- Proof sketch: if `g x = 0`, the subgradient inequality at `x` already gives `f x ≤ f xBar`.
-- Otherwise split on the sign of `⟪g x, x - xBar⟫`. In the negative case one again gets
-- `f x ≤ f xBar`, and the radius is negative so the growth function is `0`. In the nonnegative
-- case, set `yBar = xBar + v_f(xBar; x) • (g x / ‖g x‖)`, check that `⟪g x, yBar - x⟫ = 0`,
-- deduce `f yBar ≥ f x` from the subgradient inequality at `x`, and then bound
-- `f yBar - f xBar` by the defining supremum of the growth function at radius `v_f(xBar; x)`.
theorem sub_le_pointwiseGrowthFunction_of_localizationMeasure
    (xBar x : V)
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x)) :
    f x - f xBar ≤ ω[f; xBar] (v[g; xBar] x) := by
  by_cases hzero : g x = 0
  · -- If the chosen subgradient vanishes, the subgradient gap is already nonpositive.
    rw [subgradientLocalizationMeasure_eq_zero_of_eq_zero (g := g) (xBar := xBar) hzero]
    have hgap : f x - f xBar ≤ 0 := by
      simpa [hzero] using subgradient_gap_le_inner_sub (f := f) (g := g) (xBar := xBar) hgx
    exact
      le_trans
        (by exact_mod_cast hgap)
        (pointwiseGrowthFunction_nonneg_of_nonneg_radius (f := f) (xBar := xBar) (t := 0) le_rfl)
  by_cases hv_nonneg : 0 ≤ v[g; xBar] x
  · -- In the source's geometric branch, the ray point gives a witness for the defining supremum.
    obtain ⟨yBar, hyBall, hxyBar⟩ :=
      exists_localization_contact_point (f := f) (g := g) (xBar := xBar) hgx hzero hv_nonneg
    have hgap : f x - f xBar ≤ f yBar - f xBar := by
      linarith
    rw [pointwiseGrowthFunction, if_pos hv_nonneg]
    have hy_mem :
        ((f yBar - f xBar : ℝ) : WithTop ℝ) ∈
          (fun y : V ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) ''
            Metric.closedBall xBar (v[g; xBar] x) := by
      exact Set.mem_image_of_mem (fun y : V ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) hyBall
    exact
      le_trans
        (by exact_mod_cast hgap)
        (le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hy_mem)
  · -- A negative localization measure forces `f x < f xBar`, so the growth bound is trivial.
    have hv_neg : v[g; xBar] x < 0 := lt_of_not_ge hv_nonneg
    have hlt : f x < f xBar := by
      by_contra hfx
      exact hv_nonneg <|
        subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
          (f := f) (g := g) hgx (le_of_not_gt hfx)
    have hgap : f x - f xBar ≤ 0 := by
      linarith
    rw [pointwiseGrowthFunction_eq_zero_of_neg (f := f) (xBar := xBar) hv_neg]
    exact by exact_mod_cast hgap

/-- If `f` is Lipschitz on the closed ball `Metric.closedBall xBar R` with constant `M`, then the
same increment is bounded by `M` times the positive part of the localization measure whenever
`g x` is a subgradient at `x` and `v_f(xBar; x) ≤ R`, i.e. formula `(3.2.12)`. -/
-- Proof sketch: use the previous geometric construction of `yBar`. When
-- `subgradientLocalizationMeasure g xBar x ≤ 0`, the first inequality gives the claim because the
-- positive part is `0`. When `0 ≤ subgradientLocalizationMeasure g xBar x ≤ R`, the point `yBar`
-- lies in `Metric.closedBall xBar R`, so the Lipschitz estimate bounds `f yBar - f xBar` by
-- `M * subgradientLocalizationMeasure g xBar x`, and hence by `M * max (v_f(xBar; x)) 0`.
theorem sub_le_lipschitz_mul_max_localizationMeasure
    {R : ℝ} {M : NNReal} (xBar x : V)
    (hgx : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x))
    (hLip : LipschitzOnWith M f (Metric.closedBall xBar R))
    (hv : v[g; xBar] x ≤ R) :
    f x - f xBar ≤ (M : ℝ) * max (v[g; xBar] x) 0 := by
  by_cases hzero : g x = 0
  · -- With a zero chosen subgradient, the localization measure is zero and the gap is nonpositive.
    rw [subgradientLocalizationMeasure_eq_zero_of_eq_zero (g := g) (xBar := xBar) hzero]
    have hgap : f x - f xBar ≤ 0 := by
      simpa [hzero] using subgradient_gap_le_inner_sub (f := f) (g := g) (xBar := xBar) hgx
    simpa using hgap
  by_cases hv_nonneg : 0 ≤ v[g; xBar] x
  · -- Reuse the source's contact point and then apply the Lipschitz estimate on the larger ball.
    obtain ⟨yBar, hyBall, hxyBar⟩ :=
      exists_localization_contact_point (f := f) (g := g) (xBar := xBar) hgx hzero hv_nonneg
    have hxBarR : xBar ∈ Metric.closedBall xBar R := Metric.mem_closedBall_self (le_trans hv_nonneg hv)
    have hyR : yBar ∈ Metric.closedBall xBar R :=
      Metric.closedBall_subset_closedBall hv hyBall
    have hdist_le : dist yBar xBar ≤ v[g; xBar] x := by
      simpa [Metric.mem_closedBall] using hyBall
    have hyLip : f yBar - f xBar ≤ (M : ℝ) * v[g; xBar] x := by
      have hbound : f yBar ≤ f xBar + M * dist yBar xBar := hLip.le_add_mul hyR hxBarR
      have hmul :
          (M : ℝ) * dist yBar xBar ≤ (M : ℝ) * v[g; xBar] x := by
        gcongr
      linarith
    have hgap : f x - f xBar ≤ f yBar - f xBar := by
      linarith
    rw [max_eq_left hv_nonneg]
    exact le_trans hgap hyLip
  · -- A negative localization measure again forces a nonpositive gap, while the positive part is `0`.
    have hlt : f x < f xBar := by
      by_contra hfx
      exact hv_nonneg <|
        subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
          (f := f) (g := g) hgx (le_of_not_gt hfx)
    have hgap : f x - f xBar ≤ 0 := by
      linarith
    rw [max_eq_right (le_of_not_ge hv_nonneg)]
    simpa using hgap

end
