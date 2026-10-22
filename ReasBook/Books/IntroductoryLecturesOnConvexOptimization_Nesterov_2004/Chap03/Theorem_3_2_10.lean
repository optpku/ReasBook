/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_31

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open MeasureTheory
open scoped SubgradientLocalizationMeasure
open CenterOfGravityMethod

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

local notation "dim" => Module.finrank ℝ E

local instance instMeasurableSpaceTheorem3210 : MeasurableSpace E := borel E
local instance instBorelSpaceTheorem3210 : BorelSpace E := ⟨rfl⟩

/-
Primary domain: center-of-gravity cutting-plane complexity bounds for bounded convex minimization
problems.

Relevant owner-style declarations sampled before refinement:
- `CenterOfGravityMethod.iterate` and `CenterOfGravityMethod.localizer` in `Algorithm_3_7`, the
  chapter owners for the centroid iterates `x_k` and localization sets `S_k`;
- `CenterOfGravityMethod.localizer_eq_localizationSets` in `Algorithm_3_7`, the bridge from the
  owner centroid recursion to the canonical recursive localization family;
- `centerOfGravityCut_volumeRatio_le_one_sub_inv_e_of_bounded_convex_nonemptyInterior` in
  `Lemma_3_31`, the intrinsic owner centroid-cut volume estimate supplying the factor
  `1 - 1 / e`;
- `localization_radius_le_outer_radius_mul_volume_ratio_rpow` in `Theorem_3_2_9`, the owner
  radius/volume comparison converting stagewise volume decay into the `k / dim` radius exponent.

Best owner abstraction:
- source-facing: the best sampled objective value along the chapter's center-of-gravity iterates;
- core/canonical: `ConvexMinimizationWithSeparationOracle E` together with
  `CenterOfGravityMethod.iterate`;
- bridge/view: the derived centroid-cut volume decay and localization-radius estimate.

Primitive data:
- the owner cutting-plane problem `problem`;
- the minimizer `xStar`, outer radius `D`, and Lipschitz constant `M`.

Derived API:
- the iterate sequence `iterate problem`;
- the best sampled value `bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k`;
- the geometric decay factor obtained by combining centroid-cut volume contraction with the owner
  radius/volume theorem.

Source/core/bridge triage:
- source-facing: the center-of-gravity complexity bound itself;
- core/canonical: `ConvexMinimizationWithSeparationOracle E` and `CenterOfGravityMethod.iterate`;
- bridge/view: centroid-cut volume decay and localization-radius comparison.

The previous version erased the center-of-gravity method and kept only a generic metric-space
recursion hypothesis. This refinement restores the actual source-facing theorem on the chapter's
owner method abstraction and leaves the geometric-decay recursion as a derived proof ingredient
rather than primitive public data. The centroid-cut ingredient now lives at the same intrinsic
finite-dimensional owner level as the localization-radius theorem, so the theorem no longer
over-generalizes the existing chapter owner graph.
-/

-- Proof sketch: `CenterOfGravityMethod.localizer_succ` identifies each update as the centroid cut
-- of the previous localization set. Apply the centroid-cut volume estimate
-- `centerOfGravityCut_volumeRatio_le_one_sub_inv_e_of_bounded_convex_nonemptyInterior` at every
-- step to obtain geometric decay of the localizer volumes. Then use
-- `localization_radius_le_outer_radius_mul_volume_ratio_rpow` together with
-- `CenterOfGravityMethod.localizer_eq_localizationSets` to bound the localization radius by
-- `D * (1 - 1 / e)^(k / dim)`. Finally, every iterate lies in the corresponding localization set,
-- so Lipschitz continuity on `B₂(xStar, D)` converts that radius estimate into the displayed
-- best-value gap bound.
/-- Helper for Theorem 3.2.10: every centroid iterate has nonnegative localization measure, and
the outer-ball hypothesis bounds that measure by `D`. -/
lemma iterate_localizationMeasure_bounds
    (problem : ConvexMinimizationWithSeparationOracle E)
    {xStar : E} {D : ℝ}
    (hxStar : IsMinOn problem problem.feasibleSet xStar)
    (hQ_subset : problem.feasibleSet ⊆ Metric.closedBall xStar D)
    {k : ℕ} (i : Fin (k + 1)) :
    0 ≤ v[problem.oracle; xStar] (iterate problem i) ∧
      v[problem.oracle; xStar] (iterate problem i) ≤ D := by
  have hiterate_feasible : iterate problem i ∈ problem.feasibleSet :=
    iterate_mem_feasibleSet problem i
  have hsubgrad :
      IsSubgradientAt (fun x ↦ (problem x : WithTop ℝ))
        (iterate problem i) (problem.oracle (iterate problem i)) := by
    simpa [cuttingVector] using cuttingVector_isSubgradientAt problem i
  have hxStar_le_iterate : problem xStar ≤ problem (iterate problem i) :=
    (isMinOn_iff.mp hxStar) _ hiterate_feasible
  have hdist : ‖iterate problem i - xStar‖ ≤ D := by
    simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm] using hQ_subset hiterate_feasible
  have hD_nonneg : 0 ≤ D := le_trans (norm_nonneg _) hdist
  constructor
  · -- The minimizer inequality makes the subgradient localization measure nonnegative.
    exact
      subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
        (f := problem) (g := problem.oracle) hsubgrad hxStar_le_iterate
  · -- Cauchy-Schwarz converts the normalized pairing into the outer-ball radius bound.
    by_cases hzero : problem.oracle (iterate problem i) = 0
    · simpa [subgradientLocalizationMeasure, hzero] using hD_nonneg
    · rw [subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero
        (g := problem.oracle) (xBar := xStar) (x := iterate problem i) hzero]
      have hinner_le :
          inner ℝ (problem.oracle (iterate problem i)) (iterate problem i - xStar) ≤
            ‖problem.oracle (iterate problem i)‖ * ‖iterate problem i - xStar‖ := by
        exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
      have hnorm_pos : 0 < ‖problem.oracle (iterate problem i)‖ := norm_pos_iff.mpr hzero
      have hratio_le :
          inner ℝ (problem.oracle (iterate problem i)) (iterate problem i - xStar) /
              ‖problem.oracle (iterate problem i)‖ ≤
            ‖iterate problem i - xStar‖ := by
        exact (div_le_iff₀ hnorm_pos).2 <| by simpa [mul_comm] using hinner_le
      exact hratio_le.trans hdist

/-- Helper for Theorem 3.2.10: the best sampled objective gap is controlled by the best
localization radius. -/
lemma best_gap_le_lipschitz_mul_localization_radius
    (problem : ConvexMinimizationWithSeparationOracle E)
    {xStar : E} {D : ℝ} {M : NNReal}
    (hxStar : IsMinOn problem problem.feasibleSet xStar)
    (hQ_subset : problem.feasibleSet ⊆ Metric.closedBall xStar D)
    (hLip : LipschitzOnWith M problem (Metric.closedBall xStar D))
    (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k - problem xStar ≤
      (M : ℝ) * localization_radius xStar problem.oracle (iterate problem) k := by
  obtain ⟨j, hjradius⟩ :=
    bestFunctionValueUpTo_exists_eq
      (fun i ↦ v[problem.oracle; xStar] (iterate problem i)) k
  have hbest_le_point :
      bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k - problem xStar ≤
        problem (iterate problem j) - problem xStar := by
    exact sub_le_sub_right (bestFunctionValueUpTo_le j) _
  have hmeasure :=
    iterate_localizationMeasure_bounds problem hxStar hQ_subset j
  have hpoint_gap :
      problem (iterate problem j) - problem xStar ≤
        (M : ℝ) * max (v[problem.oracle; xStar] (iterate problem j)) 0 := by
    -- Apply the one-point Lipschitz/subgradient estimate at the iterate realizing the best radius.
    exact
      sub_le_lipschitz_mul_max_localizationMeasure
        (f := problem) (g := problem.oracle) (R := D) (M := M)
        xStar (iterate problem j)
        (by simpa [cuttingVector] using cuttingVector_isSubgradientAt problem j)
        hLip
        hmeasure.2
  have hjradius' :
      v[problem.oracle; xStar] (iterate problem j) =
        localization_radius xStar problem.oracle (iterate problem) k := by
    simpa [localization_radius, bestRadiusUpTo] using hjradius
  -- The minimizing iterate has nonnegative localization measure, so the `max` disappears.
  rw [max_eq_left hmeasure.1, hjradius'] at hpoint_gap
  exact hbest_le_point.trans hpoint_gap

/-- Helper for Theorem 3.2.10: every nonzero centroid cut contracts the current localizer volume
by the factor `1 - 1 / e`. -/
lemma localizer_volume_ratio_step_le_one_sub_inv_e
    (problem : ConvexMinimizationWithSeparationOracle E)
    {j : ℕ} (hcut : cuttingVector problem j ≠ 0) :
    (volume (localizer problem (j + 1))).toReal / (volume (localizer problem j)).toReal ≤
      1 - 1 / Real.exp 1 := by
  -- Rewrite the recursive update as the centroid cut of the previous localizer.
  rw [localizer_succ]
  -- Grünbaum's centroid inequality now applies directly to the current localizer.
  simpa [iterate_eq_centerOfGravity_localizer] using
    centerOfGravityCut_volumeRatio_le_one_sub_inv_e_of_bounded_convex_nonemptyInterior
      (localizer problem j)
      (cuttingVector problem j)
      (localizer_bounded problem j)
      (localizer_convex problem j)
      (localizer_interior_nonempty problem j)
      hcut

/-- Helper for Theorem 3.2.10: if the first `m` centroid cuts are nonzero, then the stage-`m`
localizer volume decays geometrically like `(1 - 1 / e)^m`. -/
lemma localizer_real_volume_ratio_le_pow_one_sub_inv_e
    (problem : ConvexMinimizationWithSeparationOracle E)
    (m : ℕ)
    (hcut_nonzero : ∀ i : Fin m, cuttingVector problem i ≠ 0) :
    volume.real (localizer problem m) / volume.real problem.feasibleSet ≤
      (1 - 1 / Real.exp 1) ^ m := by
  have hQ_lt_top : volume problem.feasibleSet < ⊤ :=
    problem.feasibleSet_bounded.measure_lt_top
  have hQ_pos_meas : 0 < volume problem.feasibleSet :=
    Measure.measure_pos_of_nonempty_interior volume problem.feasibleSet_interior_nonempty
  have hQ_pos : 0 < volume.real problem.feasibleSet := by
    simpa [Measure.real] using ENNReal.toReal_pos hQ_pos_meas.ne' hQ_lt_top.ne
  have hbase_nonneg : 0 ≤ 1 - 1 / Real.exp 1 := by
    have hExp_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_two]
    have hInv_le_one : (1 / Real.exp 1 : ℝ) ≤ 1 := by
      simpa [one_div] using (inv_le_one_of_one_le₀ hExp_ge_one)
    exact sub_nonneg.mpr hInv_le_one
  induction m with
  | zero =>
      -- At stage zero the localizer is exactly the feasible set.
      rw [localizer_zero]
      rw [div_self hQ_pos.ne', pow_zero]
  | succ m hm =>
      have hcut_prefix : ∀ i : Fin m, cuttingVector problem i ≠ 0 := by
        intro i
        exact hcut_nonzero ⟨i, Nat.lt_succ_of_lt i.2⟩
      have hm_ratio :
          volume.real (localizer problem m) / volume.real problem.feasibleSet ≤
            (1 - 1 / Real.exp 1) ^ m :=
        hm hcut_prefix
      have hstep_ratio :
          volume.real (localizer problem (m + 1)) / volume.real (localizer problem m) ≤
            1 - 1 / Real.exp 1 := by
        simpa [Measure.real] using
          localizer_volume_ratio_step_le_one_sub_inv_e problem
            (hcut_nonzero ⟨m, Nat.lt_succ_self m⟩)
      have hm_lt_top : volume (localizer problem m) < ⊤ :=
        (localizer_bounded problem m).measure_lt_top
      have hm_pos_meas : 0 < volume (localizer problem m) :=
        Measure.measure_pos_of_nonempty_interior volume (localizer_interior_nonempty problem m)
      have hm_pos : 0 < volume.real (localizer problem m) := by
        simpa [Measure.real] using ENNReal.toReal_pos hm_pos_meas.ne' hm_lt_top.ne
      have hfactorization :
          volume.real (localizer problem (m + 1)) / volume.real problem.feasibleSet =
            (volume.real (localizer problem (m + 1)) / volume.real (localizer problem m)) *
              (volume.real (localizer problem m) / volume.real problem.feasibleSet) := by
        field_simp [hm_pos.ne', hQ_pos.ne']
      have hratio_nonneg :
          0 ≤ volume.real (localizer problem m) / volume.real problem.feasibleSet := by
        positivity
      calc
        volume.real (localizer problem (m + 1)) / volume.real problem.feasibleSet
            = (volume.real (localizer problem (m + 1)) / volume.real (localizer problem m)) *
                (volume.real (localizer problem m) / volume.real problem.feasibleSet) :=
              hfactorization
        _ ≤ (1 - 1 / Real.exp 1) * ((1 - 1 / Real.exp 1) ^ m) := by
              exact mul_le_mul hstep_ratio hm_ratio hratio_nonneg hbase_nonneg
        _ = (1 - 1 / Real.exp 1) ^ (m + 1) := by
              rw [pow_succ]
              ring

/-- Helper for Theorem 3.2.10: the stage-`k` best localization radius is bounded by the outer
radius times the `dim`-th root of the next localizer volume ratio. -/
lemma localization_radius_le_outer_radius_mul_localizer_volume_ratio_rpow
    (problem : ConvexMinimizationWithSeparationOracle E)
    {xStar : E} {D : ℝ}
    (hdim : 0 < dim)
    (hxStar : IsMinOn problem problem.feasibleSet xStar)
    (hxStar_mem : xStar ∈ problem.feasibleSet)
    (hQ_subset : problem.feasibleSet ⊆ Metric.closedBall xStar D)
    (k : ℕ) :
    localization_radius xStar problem.oracle (iterate problem) k ≤
      D *
        Real.rpow
          (volume.real (localizer problem (k + 1)) / volume.real problem.feasibleSet)
          (1 / (dim : ℝ)) := by
  have hQ_lt_top : volume problem.feasibleSet < ⊤ :=
    problem.feasibleSet_bounded.measure_lt_top
  have hQ_pos_meas : 0 < volume problem.feasibleSet :=
    Measure.measure_pos_of_nonempty_interior volume problem.feasibleSet_interior_nonempty
  have hQ_pos : 0 < volume.real problem.feasibleSet := by
    simpa [Measure.real] using ENNReal.toReal_pos hQ_pos_meas.ne' hQ_lt_top.ne
  have hD_pos : 0 < D := by
    -- Positive volume forces the enclosing radius `D` to be strictly positive.
    exact outer_radius_pos_of_positive_measure (μ := volume) hdim hxStar_mem hQ_pos hQ_subset
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  have hloc_le_D :
      localization_radius xStar problem.oracle (iterate problem) k ≤ D := by
    -- The first iterate already lies in the outer ball, so the best radius cannot exceed `D`.
    exact
      (localization_radius_le_measure
        (xStar := xStar) (g := problem.oracle) (xSeq := iterate problem) (k := k)
        (0 : Fin (k + 1))).trans <|
        (iterate_localizationMeasure_bounds problem hxStar hQ_subset (0 : Fin (k + 1))).2
  have hlocalizer_measurable : MeasurableSet (localizer problem (k + 1)) := by
    -- Each centroid localizer is closed, hence measurable.
    exact (localizer_closed problem (k + 1)).measurableSet
  have hlocalizer_subset : localizer problem (k + 1) ⊆ problem.feasibleSet :=
    localizer_subset_feasibleSet problem (k + 1)
  by_cases hloc_nonneg : 0 ≤ localization_radius xStar problem.oracle (iterate problem) k
  · let r : NNReal := ⟨localization_radius xStar problem.oracle (iterate problem) k, hloc_nonneg⟩
    have hball :
        Metric.closedBall xStar (localization_radius xStar problem.oracle (iterate problem) k) ∩
            problem.feasibleSet ⊆
          localizer problem (k + 1) := by
      -- Route correction: rewrite the next localizer to the canonical localization set and apply
      -- the standard closed-ball inclusion at radius `v_k^*`.
      have hball'' :
          Metric.closedBall xStar (localization_radius xStar problem.oracle (iterate problem) k) ∩
              problem.feasibleSet ⊆
            localizationSet problem.feasibleSet (iterate problem) (cuttingVector problem) k := by
        simpa [cuttingVector, Function.comp, r] using
          (closedBall_inter_subset_localizationSet_of_le_localization_radius
            (Q := problem.feasibleSet)
            (xStar := xStar)
            (g := problem.oracle)
            (xSeq := iterate problem)
            (k := k)
            r
            le_rfl)
      have hball' :
          Metric.closedBall xStar (localization_radius xStar problem.oracle (iterate problem) k) ∩
              problem.feasibleSet ⊆
            localizationSets
              problem.feasibleSet
              (iterate problem)
              (cuttingVector problem)
              (k + 1) := by
        intro x hx
        rw [localizationSets_succ_eq_localizationSet]
        exact hball'' hx
      simpa [localizer_eq_localizationSets] using hball'
    -- Invoke the intrinsic radius/volume comparison on the next localizer itself.
    simpa [r] using
      inner_ball_radius_le_outer_radius_mul_volume_ratio_rpow_of_convex
        (μ := volume)
        hdim
        problem.feasibleSet_convex
        hxStar_mem
        hQ_pos
        hD_pos
        hloc_le_D
        hQ_subset
        hlocalizer_measurable
        hlocalizer_subset
        hball
  · have hloc_nonpos :
        localization_radius xStar problem.oracle (iterate problem) k ≤ 0 :=
      le_of_not_ge hloc_nonneg
    have hratio_nonneg :
        0 ≤ volume.real (localizer problem (k + 1)) / volume.real problem.feasibleSet := by
      positivity
    have hbound_nonneg :
        0 ≤
          D *
            Real.rpow
              (volume.real (localizer problem (k + 1)) / volume.real problem.feasibleSet)
              (1 / (dim : ℝ)) := by
      exact mul_nonneg hD_nonneg (Real.rpow_nonneg hratio_nonneg _)
    exact hloc_nonpos.trans hbound_nonneg

/-- Helper for Theorem 3.2.10: once `xStar` is known to lie in the feasible set, the source
center-of-gravity proof closes exactly as stated in the book. -/
theorem bestFunctionValueUpTo_sub_optimalValue_le_lipschitz_geometricDecay_of_mem
    (problem : ConvexMinimizationWithSeparationOracle E)
    {xStar : E} {D : ℝ} {M : NNReal}
    (hxStar : IsMinOn problem problem.feasibleSet xStar)
    (hxStar_mem : xStar ∈ problem.feasibleSet)
    (hQ_subset : problem.feasibleSet ⊆ Metric.closedBall xStar D)
    (hLip : LipschitzOnWith M problem (Metric.closedBall xStar D))
    (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k - problem xStar ≤
      (M : ℝ) * D * Real.rpow (1 - 1 / Real.exp 1) ((k : ℝ) / dim) := by
  have hgap_radius :=
    best_gap_le_lipschitz_mul_localization_radius problem hxStar hQ_subset hLip k
  have hD_nonneg : 0 ≤ D := by
    have hxBall : xStar ∈ Metric.closedBall xStar D := hQ_subset hxStar_mem
    simpa [Metric.mem_closedBall] using hxBall
  have hbase_nonneg : 0 ≤ 1 - 1 / Real.exp 1 := by
    have hExp_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_two]
    have hInv_le_one : (1 / Real.exp 1 : ℝ) ≤ 1 := by
      simpa [one_div] using (inv_le_one_of_one_le₀ hExp_ge_one)
    exact sub_nonneg.mpr hInv_le_one
  by_cases hzero_cut : ∃ i : Fin (k + 1), cuttingVector problem i = 0
  · rcases hzero_cut with ⟨i, hi_zero⟩
    have hmeasure_zero : v[problem.oracle; xStar] (iterate problem i) = 0 := by
      simpa [cuttingVector] using
        (subgradientLocalizationMeasure_eq_zero_of_eq_zero
          (g := problem.oracle) (xBar := xStar) (x := iterate problem i) hi_zero)
    have hradius_nonneg :
        0 ≤ localization_radius xStar problem.oracle (iterate problem) k := by
      simpa [localization_radius, bestRadiusUpTo, bestFunctionValueUpTo] using
        (le_ciInf fun j ↦
          (iterate_localizationMeasure_bounds problem hxStar hQ_subset j).1)
    have hradius_nonpos :
        localization_radius xStar problem.oracle (iterate problem) k ≤ 0 := by
      exact
        (localization_radius_le_measure
          (xStar := xStar) (g := problem.oracle) (xSeq := iterate problem) (k := k) i).trans <|
          by simp [hmeasure_zero]
    have hradius_zero :
        localization_radius xStar problem.oracle (iterate problem) k = 0 :=
      le_antisymm hradius_nonpos hradius_nonneg
    have hgap_nonpos :
        bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k - problem xStar ≤ 0 := by
      simpa [hradius_zero] using hgap_radius
    have hrhs_nonneg :
        0 ≤ (M : ℝ) * D * Real.rpow (1 - 1 / Real.exp 1) ((k : ℝ) / dim) := by
      exact mul_nonneg (mul_nonneg M.2 hD_nonneg) (Real.rpow_nonneg hbase_nonneg _)
    exact hgap_nonpos.trans hrhs_nonneg
  · have hcut_nonzero : ∀ i : Fin (k + 1), cuttingVector problem i ≠ 0 := by
      intro i
      exact fun hi ↦ hzero_cut ⟨i, hi⟩
    have hdim : 0 < dim := by
      exact
        Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨cuttingVector problem 0, hcut_nonzero 0⟩
    have hQ_lt_top : volume problem.feasibleSet < ⊤ :=
      problem.feasibleSet_bounded.measure_lt_top
    have hQ_pos_meas : 0 < volume problem.feasibleSet :=
      Measure.measure_pos_of_nonempty_interior volume problem.feasibleSet_interior_nonempty
    have hQ_pos : 0 < volume.real problem.feasibleSet := by
      simpa [Measure.real] using ENNReal.toReal_pos hQ_pos_meas.ne' hQ_lt_top.ne
    have hstage_radius :
        localization_radius xStar problem.oracle (iterate problem) k ≤
          D *
            Real.rpow
              (volume.real (localizer problem (k + 1)) / volume.real problem.feasibleSet)
              (1 / (dim : ℝ)) := by
      -- Route correction: use the local bridge on centroid localizers instead of the stale
      -- imported theorem from `Theorem_3_2_9`.
      exact
        localization_radius_le_outer_radius_mul_localizer_volume_ratio_rpow
          problem hdim hxStar hxStar_mem hQ_subset k
    have hlocalizer_mono : localizer problem (k + 1) ⊆ localizer problem k := by
      rw [localizer_succ]
      exact Set.inter_subset_left
    have hk_lt_top : volume (localizer problem k) < ⊤ :=
      (localizer_bounded problem k).measure_lt_top
    have hratio_mono :
        volume.real (localizer problem (k + 1)) / volume.real problem.feasibleSet ≤
          volume.real (localizer problem k) / volume.real problem.feasibleSet := by
      have hreal_mono :
          volume.real (localizer problem (k + 1)) ≤ volume.real (localizer problem k) := by
        exact measureReal_mono hlocalizer_mono hk_lt_top.ne
      exact div_le_div_of_nonneg_right hreal_mono hQ_pos.le
    have hradius_bound :
        localization_radius xStar problem.oracle (iterate problem) k ≤
          D *
            Real.rpow
              (volume.real (localizer problem k) / volume.real problem.feasibleSet)
              (1 / (dim : ℝ)) := by
      have hratio_nonneg :
          0 ≤ volume.real (localizer problem (k + 1)) / volume.real problem.feasibleSet := by
        positivity
      refine hstage_radius.trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hratio_nonneg hratio_mono (by positivity))
        hD_nonneg
    have hvol_ratio :
        volume.real (localizer problem k) / volume.real problem.feasibleSet ≤
          (1 - 1 / Real.exp 1) ^ k :=
      localizer_real_volume_ratio_le_pow_one_sub_inv_e problem k
        (fun i ↦ hcut_nonzero ⟨i, Nat.lt_succ_of_lt i.2⟩)
    have hratio_nonneg :
        0 ≤ volume.real (localizer problem k) / volume.real problem.feasibleSet := by
      positivity
    have hroot_bound :
        Real.rpow
            (volume.real (localizer problem k) / volume.real problem.feasibleSet)
            (1 / (dim : ℝ)) ≤
          Real.rpow (1 - 1 / Real.exp 1) ((k : ℝ) / dim) := by
      calc
        Real.rpow
            (volume.real (localizer problem k) / volume.real problem.feasibleSet)
            (1 / (dim : ℝ))
            ≤ Real.rpow ((1 - 1 / Real.exp 1) ^ k) (1 / (dim : ℝ)) := by
              exact Real.rpow_le_rpow hratio_nonneg hvol_ratio (by positivity)
        _ = Real.rpow (1 - 1 / Real.exp 1) (((k : ℝ)) * (1 / (dim : ℝ))) := by
              have hpow :
                  ((1 - 1 / Real.exp 1) ^ k : ℝ) = Real.rpow (1 - 1 / Real.exp 1) k := by
                symm
                exact Real.rpow_natCast (1 - 1 / Real.exp 1) k
              rw [hpow]
              exact (Real.rpow_mul hbase_nonneg (k : ℝ) (1 / (dim : ℝ))).symm
        _ = Real.rpow (1 - 1 / Real.exp 1) ((k : ℝ) / dim) := by
              simp [div_eq_mul_inv]
    -- Chain the optimization-to-geometry bridge with the geometric radius decay.
    calc
      bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k - problem xStar ≤
          (M : ℝ) * localization_radius xStar problem.oracle (iterate problem) k :=
        hgap_radius
      _ ≤ (M : ℝ) *
            (D *
              Real.rpow
                (volume.real (localizer problem k) / volume.real problem.feasibleSet)
                (1 / (dim : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hradius_bound M.2
      _ ≤ (M : ℝ) * (D * Real.rpow (1 - 1 / Real.exp 1) ((k : ℝ) / dim)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hroot_bound hD_nonneg)
                M.2
      _ = (M : ℝ) * D * Real.rpow (1 - 1 / Real.exp 1) ((k : ℝ) / dim) := by
              ring

/-- Theorem 3.2.10: at the chapter owner level, for the center-of-gravity cutting-plane method on
a bounded convex minimization problem, if `xStar` minimizes the objective on the feasible set
`Q = problem.feasibleSet`, if `xStar ∈ Q`, if `Q ⊆ B₂(xStar, D)`, and if the objective is
`M`-Lipschitz on that ball, then the best sampled value
`f_k^* = bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k` along the centroid
iterates satisfies
`f_k^* - problem xStar ≤ M D (1 - 1 / e)^(k / dim)`, where `dim = Module.finrank ℝ E`. The
factor `(1 - 1 / e)^(k / dim)` is derived from the centroid-cut volume contraction and the
localization-radius/volume comparison, not assumed as primitive data. -/
theorem CenterOfGravityMethod.bestFunctionValueUpTo_sub_optimalValue_le_lipschitz_geometricDecay
    (problem : ConvexMinimizationWithSeparationOracle E)
    {xStar : E} {D : ℝ} {M : NNReal}
    (hxStar : IsMinOn problem problem.feasibleSet xStar)
    (hxStar_mem : xStar ∈ problem.feasibleSet)
    (hQ_subset : problem.feasibleSet ⊆ Metric.closedBall xStar D)
    (hLip : LipschitzOnWith M problem (Metric.closedBall xStar D))
    (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k - problem xStar ≤
      (M : ℝ) * D * Real.rpow (1 - 1 / Real.exp 1) ((k : ℝ) / dim) := by
  exact
    bestFunctionValueUpTo_sub_optimalValue_le_lipschitz_geometricDecay_of_mem
      problem hxStar hxStar_mem hQ_subset hLip k

end

end
