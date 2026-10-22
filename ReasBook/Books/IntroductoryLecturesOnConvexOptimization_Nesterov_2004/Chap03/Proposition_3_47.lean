/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_53
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_59
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_45
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_52
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_54

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open EllipsoidMethod
open MeasureTheory
open scoped ConstrainedArgmin

attribute [local instance] Classical.decPred

/- Proposition 3.47 lies in the chapter's ellipsoid-method selected-feasible sampled-value
domain.

Mandatory domain-style sampling before refinement:
- `feasibleSubsequence` and
  `feasibleSubsequence_count_eq_self_of_feasible` from `Definition_3_53`, the chapter owners for
  the selected feasible subsequence of queried centers;
- `Nat.count` from `Definition_3_53`, the canonical owner for the selected feasible index;
- `bestFunctionValueUpTo` from `Definition_3_55`, the chapter owner for best sampled objective
  values along a finite prefix;
- `argmin[problem.feasibleSet] problem`, `problem.optimalValue`, and
  `problem.IsApproximateMinimizer` from `Chap01/Definition_1_3_7`, the canonical constrained
  optimum / approximate-solution owners for the feasible-set objective;
- `selected_index_pos_of_log_threshold_under_interior_ball_condition` from `Proposition_3_45`,
  the chapter bridge from the interior-ball logarithmic feasibility threshold to positivity of the
  selected-feasible prefix count;
- `selected_radius_bound_of_positive_index` from `Theorem_3_52`, the bridge from the selected
  feasible ellipsoid centers to the canonical localization-radius estimate;
- `selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_`
  `le_lipschitz_radius_mul_geometricDecay_volumeRatio` from `Theorem_3_54`, the chapter owner
  theorem converting the selected-radius estimate into a best-value bound on
  `bestFunctionValueUpTo`.

Best owner abstraction:
- source-facing: the ellipsoid-method queried-center complexity guarantee;
- core/canonical: `Nat.count`, `feasibleSubsequence`, and `bestFunctionValueUpTo`;
- bridge/view: the selected-feasible owner inequality on `bestFunctionValueUpTo`.

Primitive data:
- the ambient convex minimization problem with separation oracle;
- the initial center `y₀`, radius `R`, and the ellipsoid recursion data from `Algorithm_3_8`;
- the Lipschitz, interior-ball, dimension, nonzero-cut, and positive-definite hypotheses;
- a chosen constrained minimizer `xStar ∈ argmin[problem.feasibleSet] problem` and the
  optimizer-centered outer-ball inclusion `problem.feasibleSet ⊆ Metric.closedBall xStar R`;
- the small-accuracy regime `ε ≤ (M : ℝ) * R`, which makes the stated accuracy budget dominate
  the feasibility threshold `2 (n + 1)^2 log (R / ρ)`;
- the initial ellipsoid cover hypothesis.

Derived API:
- the queried center sequence `center problem initialCenter R`;
- the selected feasible subsequence
  `feasibleSubsequence problem.feasibleSet (center problem initialCenter R)`;
- the positive selected-feasible prefix count
  `Nat.count (fun j ↦ center problem initialCenter R j ∈ problem.feasibleSet) (N + 1)`;
- the canonical feasible-set optimum `problem.optimalValue`;
- the source-facing queried-center consequence extracted from the canonical sampled-value owner;
- the owner sampled-value bound on `bestFunctionValueUpTo` over the selected feasible prefix
  contained in the first `N + 1` queried centers, now stated relative to the canonical
  feasible-set optimum `problem.optimalValue`.

Source/core/bridge triage:
- source-facing: Proposition 3.47's queried-center logarithmic-complexity guarantee for the
  ellipsoid method;
- core/canonical: `Nat.count`, `feasibleSubsequence`, `bestFunctionValueUpTo`,
  `problem.optimalValue`, `problem.IsApproximateMinimizer`,
  `selected_radius_bound_of_positive_index`, and
  `selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_`
  `le_lipschitz_radius_mul_geometricDecay_volumeRatio`;
- bridge/view: the selected-feasible owner inequality on `bestFunctionValueUpTo`, specialized to
  the feasible subsequence of ellipsoid centers and the canonical constrained optimum.

This refinement removes the duplicate local feasible-set infimum API and restores Proposition 3.47
to the chapter owner surface: the comparison point is now a constrained minimizer
`xStar ∈ argmin[problem.feasibleSet] problem`, the main conclusion is the owner predicate
`problem.IsApproximateMinimizer ε (y k)`, and the companion sampled-value theorem is stated
directly against `problem.optimalValue`.
-/

section

variable
    (problem : ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n)))
    (initialCenter xStar : E) (M : NNReal) {R ρ ε : ℝ}
    (hε : 0 < ε) (hε_le : ε ≤ (M : ℝ) * R)
    (hf_lipschitz : LipschitzOnWith M problem (Metric.closedBall xStar R))
    (hfeasible_ball : problem.feasibleSet.SatisfiesInteriorBallCondition ρ)
    (hxStar : xStar ∈ argmin[problem.feasibleSet] problem)
    (hfeasible_subset_ball : problem.feasibleSet ⊆ Metric.closedBall xStar R)
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter R k ≠ 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter R k).PosDef)
    (hE0_cover : problem.feasibleSet ⊆ associatedEllipsoid problem initialCenter R 0)

local notation "y" => center problem initialCenter R
local notation "Y" => feasibleSubsequence problem.feasibleSet y

include initialCenter xStar hε hε_le hf_lipschitz hfeasible_ball hxStar
  hfeasible_subset_ball hn hcut_nonzero hshape_pos hE0_cover

/-- Helper for Proposition 3.47: the associated ellipsoid volumes decay geometrically along the
ellipsoid recursion, relative to the initial radius-`R` ball. -/
lemma associated_ellipsoid_volume_decay_real
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter R k ≠ 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter R k).PosDef)
    (hR : 0 ≤ R)
    (k : ℕ) :
    (volume (associatedEllipsoid problem initialCenter R k)).toReal ≤
      Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) (((k * n : ℕ) : ℝ) / 2) *
        (volume (Metric.closedBall initialCenter R)).toReal := by
  let δ : ℝ := 1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hone_le : (1 : ℝ) ≤ (((n : ℝ) + 1) ^ (2 : ℕ)) := by
      nlinarith
    have hdiv_le : 1 / (((n : ℝ) + 1) ^ (2 : ℕ)) ≤ 1 := by
      simpa using (one_div_le_one_div_of_le zero_lt_one hone_le)
    linarith
  induction k with
  | zero =>
      -- The initial associated ellipsoid is exactly the radius-`R` closed ball.
      have hzero_set :
          associatedEllipsoid problem initialCenter R 0 = Metric.closedBall initialCenter R := by
        ext x
        simp [EllipsoidMethod.associatedEllipsoid, EllipsoidMethod.shape_zero,
          EllipsoidMethod.center_zero, affineEllipsoid, Metric.mem_closedBall, dist_eq_norm, hR]
      rw [hzero_set]
      simp [δ]
  | succ k ih =>
      -- One ellipsoid update contributes the standard geometric decay factor.
      have hstep :
          (volume (associatedEllipsoid problem initialCenter R (k + 1))).toReal ≤
            Real.rpow δ ((n : ℝ) / 2) *
              (volume (associatedEllipsoid problem initialCenter R k)).toReal := by
        simpa [δ, EllipsoidMethod.associatedEllipsoid, EllipsoidMethod.center_succ,
          EllipsoidMethod.shape_succ] using
          (centerCutEllipsoid_subset_updatedEllipsoid_and_volume_le
            (shape problem initialCenter R k)
            (hshape_pos k)
            (center problem initialCenter R k)
            (cuttingVector problem initialCenter R k)
            (hcut_nonzero k)
            hn).2
      have hmul :
          Real.rpow δ ((n : ℝ) / 2) *
              (volume (associatedEllipsoid problem initialCenter R k)).toReal ≤
            Real.rpow δ ((n : ℝ) / 2) *
              (Real.rpow δ (((k * n : ℕ) : ℝ) / 2) *
                (volume (Metric.closedBall initialCenter R)).toReal) := by
        exact mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg hδ_nonneg _)
      have hadd :
          ((n : ℝ) / 2) + (((k * n : ℕ) : ℝ) / 2) =
            ((((k + 1) * n : ℕ) : ℝ) / 2) := by
        rw [Nat.succ_mul, Nat.cast_add]
        ring
      calc
        (volume (associatedEllipsoid problem initialCenter R (k + 1))).toReal ≤
            Real.rpow δ ((n : ℝ) / 2) *
              (volume (associatedEllipsoid problem initialCenter R k)).toReal := hstep
        _ ≤
            Real.rpow δ ((n : ℝ) / 2) *
              (Real.rpow δ (((k * n : ℕ) : ℝ) / 2) *
                (volume (Metric.closedBall initialCenter R)).toReal) := hmul
        _ =
            (Real.rpow δ ((n : ℝ) / 2) * Real.rpow δ (((k * n : ℕ) : ℝ) / 2)) *
              (volume (Metric.closedBall initialCenter R)).toReal := by ring
        _ =
            Real.rpow δ ((((k + 1) * n : ℕ) : ℝ) / 2) *
              (volume (Metric.closedBall initialCenter R)).toReal := by
            rw [← Real.rpow_add hδ_nonneg, hadd]

/-- Helper for Proposition 3.47: the same geometric ellipsoid-volume decay can be stated directly
in the `ENNReal` form required by Proposition 3.45. -/
lemma associated_ellipsoid_volume_decay_ennreal
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter R k ≠ 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter R k).PosDef)
    (hR : 0 ≤ R)
    (k : ℕ) :
    volume (associatedEllipsoid problem initialCenter R k) ≤
      ENNReal.ofReal
          (Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) (((k * n : ℕ) : ℝ) / 2)) *
        volume (Metric.closedBall initialCenter R) := by
  let δ : ℝ := 1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hs_ge_one : (1 : ℝ) ≤ (((n : ℝ) + 1) ^ (2 : ℕ)) := by
      nlinarith
    have hfrac_le_one : 1 / (((n : ℝ) + 1) ^ (2 : ℕ)) ≤ 1 := by
      simpa using (one_div_le_one_div_of_le zero_lt_one hs_ge_one)
    linarith
  have hball_lt_top : volume (Metric.closedBall initialCenter R) < ⊤ := by
    simpa using (measure_closedBall_lt_top : volume (Metric.closedBall initialCenter R) < ⊤)
  have hrhs_ne_top :
      ENNReal.ofReal (Real.rpow δ (((k * n : ℕ) : ℝ) / 2)) *
          volume (Metric.closedBall initialCenter R) ≠
        ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hball_lt_top.ne
  have hEll_ne_top : volume (associatedEllipsoid problem initialCenter R k) ≠ ⊤ := by
    exact
      (EllipsoidMethod.associatedEllipsoid_bounded
        (problem := problem) initialCenter R k (hshape_pos k)).measure_lt_top.ne
  have htoReal :
      (volume (associatedEllipsoid problem initialCenter R k)).toReal ≤
        (ENNReal.ofReal (Real.rpow δ (((k * n : ℕ) : ℝ) / 2)) *
          volume (Metric.closedBall initialCenter R)).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
    · simpa [δ] using
        associated_ellipsoid_volume_decay_real
          (problem := problem) (initialCenter := initialCenter) (R := R)
          hn hcut_nonzero hshape_pos hR k
    · exact Real.rpow_nonneg hδ_nonneg _
  exact (ENNReal.toReal_le_toReal hEll_ne_top hrhs_ne_top).1 htoReal

/-- Helper for Proposition 3.47: the accuracy budget forces the strict next-stage logarithmic
threshold and the final scalar decay estimate used to reach `ε / M`. -/
lemma accuracy_budget_implies_next_stage_log_threshold
    {N : ℕ}
    (hε : 0 < ε)
    (hε_le : ε ≤ (M : ℝ) * R)
    (hρ : 0 < ρ)
    (hN :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) ≤
        (N : ℝ)) :
    2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) <
        (N + 1 : ℝ) ∧
      R *
          ((R / ρ) *
            Real.exp (-((N + 1 : ℝ) / (2 * (((n : ℝ) + 1) ^ (2 : ℕ)))))) <
        ε / (M : ℝ) := by
  -- The small-accuracy regime already forces positivity of `M` and `R`.
  have hM_pos : 0 < (M : ℝ) := by
    by_contra hM
    have hM_eq : (M : ℝ) = 0 := by
      have hM_nonneg : 0 ≤ (M : ℝ) := M.2
      linarith [hM_nonneg, le_of_not_gt hM]
    have hε_nonpos : ε ≤ 0 := by
      simpa [hM_eq] using hε_le
    linarith
  have hstage :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) <
        (N + 1 : ℝ) := by
    have hlt : (N : ℝ) < (N + 1 : ℝ) := by
      exact_mod_cast Nat.lt_succ_self N
    exact lt_of_le_of_lt hN hlt
  have hratio_decay :
      (((M : ℝ) * R ^ (2 : ℕ)) / (ρ * ε)) *
          Real.exp (-((N + 1 : ℝ) / (2 * (((n : ℝ) + 1) ^ (2 : ℕ))))) <
        1 := by
    -- Apply the logarithmic-threshold lemma to the larger ratio `(M R² / ε) / ρ`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (radiusRatio_exp_neg_lt_one_of_log_threshold
        (d := n)
        (k := N + 1)
        (ρ := ρ)
        (R := (M : ℝ) * R ^ (2 : ℕ) / ε)
        (by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstage))
  have hscaled :
      (M : ℝ) * R *
          ((R / ρ) *
            Real.exp (-((N + 1 : ℝ) / (2 * (((n : ℝ) + 1) ^ (2 : ℕ)))))) <
        ε := by
    have hrewrite :
        ((((M : ℝ) * R ^ (2 : ℕ)) / (ρ * ε)) *
            Real.exp (-((N + 1 : ℝ) / (2 * (((n : ℝ) + 1) ^ (2 : ℕ)))))) *
          ε =
        (M : ℝ) * R *
          ((R / ρ) *
            Real.exp (-((N + 1 : ℝ) / (2 * (((n : ℝ) + 1) ^ (2 : ℕ)))))) := by
      field_simp [hρ.ne', hε.ne', hM_pos.ne']
    have haux := mul_lt_mul_of_pos_right hratio_decay hε
    rw [hrewrite] at haux
    simpa [mul_assoc, mul_left_comm, mul_comm] using haux
  have hfinal :
      R *
          ((R / ρ) *
            Real.exp (-((N + 1 : ℝ) / (2 * (((n : ℝ) + 1) ^ (2 : ℕ)))))) <
        ε / (M : ℝ) := by
    exact (lt_div_iff₀ hM_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)
  exact ⟨hstage, hfinal⟩

/-- Helper for Proposition 3.47: the accuracy budget already implies the weaker logarithmic
threshold `log (R / ρ)` needed by Proposition 3.45. -/
lemma log_threshold_of_accuracy_budget_for_outer_radius
    {N : ℕ}
    (hε : 0 < ε)
    (hε_le : ε ≤ (M : ℝ) * R)
    (hρ : 0 < ρ)
    (hN :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) ≤
        (N : ℝ)) :
    2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) < (N + 1 : ℝ) := by
  have hM_pos : 0 < (M : ℝ) := by
    by_contra hM
    have hM_nonneg : 0 ≤ (M : ℝ) := M.2
    have hM_eq : (M : ℝ) = 0 := by linarith
    have hε_nonpos : ε ≤ 0 := by
      simpa [hM_eq] using hε_le
    linarith
  have hR_pos : 0 < R := by
    by_contra hR
    have hR_nonpos : R ≤ 0 := le_of_not_gt hR
    have hε_nonpos : ε ≤ 0 := by
      nlinarith [hε_le, M.2, hR_nonpos]
    linarith
  have hratio_pos : 0 < R / ρ := by positivity
  have hbig_pos : 0 < (M : ℝ) * R ^ (2 : ℕ) / (ρ * ε) := by positivity
  have hfactor_ge_one : 1 ≤ (M : ℝ) * R / ε := by
    exact (one_le_div hε).2 hε_le
  have hratio_le_big :
      R / ρ ≤ (M : ℝ) * R ^ (2 : ℕ) / (ρ * ε) := by
    have hratio_nonneg : 0 ≤ R / ρ := le_of_lt hratio_pos
    have hmul_le :
        (R / ρ) * 1 ≤ (R / ρ) * ((M : ℝ) * R / ε) := by
      exact mul_le_mul_of_nonneg_left hfactor_ge_one hratio_nonneg
    have hrewrite :
        (R / ρ) * ((M : ℝ) * R / ε) = (M : ℝ) * R ^ (2 : ℕ) / (ρ * ε) := by
      field_simp [hρ.ne', hε.ne']
    simpa [one_mul, hrewrite] using hmul_le
  have hlog_le :
      Real.log (R / ρ) ≤ Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) := by
    exact Real.log_le_log hratio_pos hratio_le_big
  have hscale_nonneg : 0 ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by positivity
  have hscaled_le :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) ≤
        2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) := by
    exact mul_le_mul_of_nonneg_left hlog_le hscale_nonneg
  have hbig_stage :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) <
        (N + 1 : ℝ) := by
    exact lt_of_le_of_lt hN (by exact_mod_cast Nat.lt_succ_self N)
  exact lt_of_le_of_lt hscaled_le hbig_stage

/-- Helper for Proposition 3.47: the same budget already guarantees a positive selected-feasible
count among the first `N + 1` ellipsoid centers. -/
lemma selected_feasible_count_pos_of_accuracy_budget
    {N : ℕ}
    (hε : 0 < ε)
    (hε_le : ε ≤ (M : ℝ) * R)
    (hfeasible_ball : problem.feasibleSet.SatisfiesInteriorBallCondition ρ)
    (hfeasible_subset_ball : problem.feasibleSet ⊆ Metric.closedBall xStar R)
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter R k ≠ 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter R k).PosDef)
    (hE0_cover : problem.feasibleSet ⊆ associatedEllipsoid problem initialCenter R 0)
    (hN :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) ≤
        (N : ℝ)) :
    0 < Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) := by
  rcases hfeasible_ball with ⟨hρ, _, _⟩
  have hdim : 0 < n := by linarith
  have hfinrank_pos : 0 < Module.finrank ℝ E := by
    simpa using hdim
  have hR_pos : 0 < R := by
    by_contra hR
    have hR_nonpos : R ≤ 0 := le_of_not_gt hR
    have hε_nonpos : ε ≤ 0 := by
      nlinarith [hε_le, M.2, hR_nonpos]
    linarith
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
  have hE0_eq :
      associatedEllipsoid problem initialCenter R 0 = Metric.closedBall initialCenter R := by
    ext x
    simp [EllipsoidMethod.associatedEllipsoid, EllipsoidMethod.shape_zero,
      EllipsoidMethod.center_zero, affineEllipsoid, Metric.mem_closedBall, dist_eq_norm, hR_nonneg]
  have hQ_subset :
      problem.feasibleSet ⊆ Metric.closedBall initialCenter R := by
    intro x hx
    have hxE0 : x ∈ associatedEllipsoid problem initialCenter R 0 := hE0_cover hx
    rw [hE0_eq] at hxE0
    simpa using hxE0
  have hstage_subset :
      localizationSets
          problem.feasibleSet
          Y
          (problem.oracle ∘ Y)
          (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1)) ⊆
        associatedEllipsoid problem initialCenter R (N + 1) := by
    simpa [Y] using
      EllipsoidMethod.selectedLocalizationSets_subset_associatedEllipsoid
        (problem := problem) initialCenter R hn hcut_nonzero hE0_cover hshape_pos (N + 1)
  have hstage :
      volume
          (localizationSets
            problem.feasibleSet
            Y
            (problem.oracle ∘ Y)
            (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1))) ≤
        volume (associatedEllipsoid problem initialCenter R (N + 1)) := by
    exact measure_mono hstage_subset
  have hvol_decay :
      volume (associatedEllipsoid problem initialCenter R (N + 1)) ≤
        ENNReal.ofReal
            (Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((((N + 1) * n : ℕ) : ℝ) / 2)) *
          volume (Metric.closedBall initialCenter R) := by
    simpa using
      associated_ellipsoid_volume_decay_ennreal
        (problem := problem) (initialCenter := initialCenter) (R := R)
        hn hcut_nonzero hshape_pos hR_nonneg (N + 1)
  have hk :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) < (N + 1 : ℝ) :=
    log_threshold_of_accuracy_budget_for_outer_radius
      (problem := problem) (initialCenter := initialCenter) (xStar := xStar)
      (M := M) (R := R) (ρ := ρ) (ε := ε)
      hε hε_le hρ hN
  -- Route correction: the Proposition 3.45 instantiation uses the initial-center outer ball and
  -- the ENNReal ellipsoid decay, not the optimizer-centered outer ball from the later value step.
  exact
    @selected_index_pos_of_log_threshold_under_interior_ball_condition
      (EuclideanSpace ℝ (Fin n)) _ _ _ _ _ _
      hfinrank_pos
      problem.feasibleSet
      ρ
      hfeasible_ball
      y
      problem.oracle
      (associatedEllipsoid problem initialCenter R (N + 1))
      initialCenter
      R
      (N + 1)
      hQ_subset
      hstage
      hvol_decay
      hk

/-- Helper for Proposition 3.47: every selected feasible sample among the first `N + 1` queries
lies in the radius-`R` outer ball around `xStar`, so its pointwise localization measure is at most
`R`. -/
lemma localization_measure_le_of_mem_closedBall
    (xRef : E)
    {x : E}
    (hx : x ∈ Metric.closedBall xRef R) :
    subgradientLocalizationMeasure problem.oracle xRef x ≤ R := by
  -- The closed-ball membership provides both the nonnegativity of `R` and the distance bound.
  have hR_nonneg : 0 ≤ R := by
    exact le_trans dist_nonneg (by simpa [Metric.mem_closedBall] using hx)
  have hdist : ‖x - xRef‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm] using hx
  by_cases hzero : problem.oracle x = 0
  · -- A zero oracle vector makes the localization measure vanish.
    simpa [subgradientLocalizationMeasure, hzero] using hR_nonneg
  · -- Otherwise Cauchy-Schwarz bounds the normalized pairing by the distance to `xStar`.
    rw [subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero
      (g := problem.oracle) (xBar := xRef) (x := x) hzero]
    have hinner_le :
        inner ℝ (problem.oracle x) (x - xRef) ≤ ‖problem.oracle x‖ * ‖x - xRef‖ := by
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    have hnorm_pos : 0 < ‖problem.oracle x‖ := norm_pos_iff.mpr hzero
    have hratio_le :
        inner ℝ (problem.oracle x) (x - xRef) / ‖problem.oracle x‖ ≤ ‖x - xRef‖ := by
      exact (div_le_iff₀ hnorm_pos).2 <| by simpa [mul_comm] using hinner_le
    exact hratio_le.trans hdist

/-- Helper for Proposition 3.47: every selected feasible sample among the first `N + 1` queries
lies in the radius-`R` outer ball around `xStar`, so its pointwise localization measure is at most
`R`. -/
lemma selected_point_localization_measure_le_outer_radius
    {N : ℕ}
    (j : Fin (Nat.count (fun t ↦ y t ∈ problem.feasibleSet) (N + 1))) :
    subgradientLocalizationMeasure problem.oracle xStar (Y j) ≤ R := by
  -- The selected feasible subsequence is defined through `Nat.nth`, so every selected point is
  -- genuinely feasible.
  have hY_feasible : Y j ∈ problem.feasibleSet := by
    have hmem :
        y (Nat.nth (fun t ↦ y t ∈ problem.feasibleSet) j) ∈ problem.feasibleSet := by
      simpa using
        (Nat.nth_mem j fun hf ↦ j.2.trans_le (Nat.count_le_card hf (N + 1)))
    simpa [Y, feasibleSubsequence] using hmem
  -- The optimizer-centered outer-ball hypothesis then gives the desired localization bound.
  exact localization_measure_le_of_mem_closedBall
    (problem := problem) (R := R) xStar
    (x := Y j) (hfeasible_subset_ball hY_feasible)

/-- Helper for Proposition 3.47: a selected feasible sample whose value realizes the canonical
best sampled prefix value yields the required raw queried center witness. -/
lemma selected_best_value_witness_is_approximate_minimizer
    {N : ℕ}
    (hm : 0 < Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1))
    (hbest :
      (bestFunctionValueUpTo
          (problem ∘ Y)
          (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1) : EReal) ≤
        problem.optimalValue + ε) :
    ∃ k ≤ N, problem.IsApproximateMinimizer ε (y k) := by
  let m := Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1)
  have hm_pos : 0 < m := by
    simpa [m] using hm
  -- Choose a selected feasible sample that realizes the best sampled value on the selected prefix.
  obtain ⟨j, hj⟩ := by
    simpa [m, Nat.succ_pred_eq_of_pos hm_pos] using
      (bestFunctionValueUpTo_exists_eq (problem ∘ Y) (m - 1))
  let k := Nat.nth (fun t ↦ y t ∈ problem.feasibleSet) j
  have hk_lt : k < N + 1 := by
    -- The selected index `j` enumerates a feasible query strictly before `N + 1`.
    exact Nat.nth_lt_of_lt_count (by simpa [m, k] using j.2)
  have hyk_feasible : y k ∈ problem.feasibleSet := by
    -- The same `Nat.nth` index lands in the feasible prefix by construction.
    have hmem : y (Nat.nth (fun t ↦ y t ∈ problem.feasibleSet) j) ∈ problem.feasibleSet := by
      simpa using
        (Nat.nth_mem j fun hf ↦ by
          have hj_bound :
              (j : ℕ) < Nat.count (fun t ↦ y t ∈ problem.feasibleSet) (N + 1) := by
            simpa [m] using j.2
          exact hj_bound.trans_le (Nat.count_le_card hf (N + 1)))
    simpa [k, Y, feasibleSubsequence] using hmem
  have hk_value :
      problem (y k) =
        bestFunctionValueUpTo (problem ∘ Y) (m - 1) := by
    -- Rewriting the selected sequence at the realizing index exposes the raw queried center.
    simpa [k, Y, feasibleSubsequence, Function.comp_apply] using hj
  refine ⟨k, Nat.lt_succ_iff.mp hk_lt, ?_⟩
  change y k ∈ problem.feasibleSet ∧
      (problem (y k) : EReal) ≤ problem.optimalValue + ε
  constructor
  · exact hyk_feasible
  · calc
      (problem (y k) : EReal) =
          (bestFunctionValueUpTo (problem ∘ Y) (m - 1) : EReal) := by
            exact_mod_cast hk_value
      _ ≤ problem.optimalValue + ε := by simpa [m] using hbest

/-- Companion owner theorem for Proposition 3.47: under the same hypotheses, the canonical best
sampled value along the selected feasible subsequence of queried centers in the first `N + 1`
queries is at most `ε` above the canonical constrained optimum `problem.optimalValue`. The
positivity of the selected-feasible prefix now follows from the same accuracy budget after the
small-accuracy bridge `ε ≤ (M : ℝ) * R`, and is not kept as a separate public premise. -/
-- Proof sketch: first derive positivity of the selected feasible prefix count from the same
-- logarithmic threshold, then apply the chapter's selected-feasible best-value estimate to the
-- induced ellipsoid-method localization sequence, and finally identify the comparison value with
-- `problem.optimalValue` through the constrained argmin owner theorem.
theorem ellipsoid_method_oracle_complexity_of_interior_ball_bestFunctionValueUpTo
    {N : ℕ}
    (hN :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) ≤
        (N : ℝ)) :
    (bestFunctionValueUpTo
        (problem ∘ Y)
        (Nat.count
            (fun j ↦ y j ∈ problem.feasibleSet)
            (N + 1) - 1) : EReal) ≤
      problem.optimalValue + ε := by
  have hm :
      0 < Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) :=
    selected_feasible_count_pos_of_accuracy_budget
      (problem := problem) (initialCenter := initialCenter) (xStar := xStar) (M := M)
      (R := R) (ρ := ρ) (ε := ε)
      hε hε_le hfeasible_ball hfeasible_subset_ball hn hcut_nonzero hshape_pos hE0_cover hN
  have hfeasible_ball' : problem.feasibleSet.SatisfiesInteriorBallCondition ρ := hfeasible_ball
  rcases hfeasible_ball with ⟨hρ, _, _⟩
  have hxStar_feasible : xStar ∈ problem.feasibleSet := by
    exact (mem_constrainedArgmin_iff.mp hxStar).1
  have hdim : 0 < n := by linarith
  have hfinrank_pos : 0 < Module.finrank ℝ E := by
    simpa using hdim
  have hR_pos : 0 < R := by
    by_contra hR
    have hR_nonpos : R ≤ 0 := le_of_not_gt hR
    have hε_nonpos : ε ≤ 0 := by
      nlinarith [hε_le, M.2, hR_nonpos]
    linarith
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
  have hQ_lt_top : volume problem.feasibleSet < ⊤ := by
    exact
      lt_of_le_of_lt
        (measure_mono hfeasible_subset_ball)
        (by
          simpa using (measure_closedBall_lt_top : volume (Metric.closedBall xStar R) < ⊤))
  have hQ_pos_meas : 0 < volume problem.feasibleSet :=
    Measure.measure_pos_of_nonempty_interior volume
      (Set.SatisfiesInteriorBallCondition.interior_nonempty hfeasible_ball')
  have hQ_pos : 0 < volume.real problem.feasibleSet := by
    simpa [Measure.real] using ENNReal.toReal_pos hQ_pos_meas.ne' hQ_lt_top.ne
  have hEll_finite : volume (associatedEllipsoid problem initialCenter R (N + 1)) ≠ ⊤ := by
    exact
      (EllipsoidMethod.associatedEllipsoid_bounded
        (problem := problem) initialCenter R (N + 1) (hshape_pos (N + 1))).measure_lt_top.ne
  have hstage_subset :
      localizationSets
          problem.feasibleSet
          Y
          (problem.oracle ∘ Y)
          (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1)) ⊆
        associatedEllipsoid problem initialCenter R (N + 1) := by
    simpa [Y] using
      EllipsoidMethod.selectedLocalizationSets_subset_associatedEllipsoid
        (problem := problem) initialCenter R hn hcut_nonzero hE0_cover hshape_pos (N + 1)
  have hstage :
      volume
          (localizationSets
            problem.feasibleSet
            Y
            (problem.oracle ∘ Y)
            (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1))) ≤
        volume (associatedEllipsoid problem initialCenter R (N + 1)) := by
    exact measure_mono hstage_subset
  have hradius_bound :=
    selected_radius_bound_of_positive_index
      (Q := problem.feasibleSet)
      (xStar := xStar)
      (g := problem.oracle)
      (querySeq := y)
      (Ell := associatedEllipsoid problem initialCenter R)
      (D := R)
      (k := N + 1)
      hdim
      problem.feasibleSet_convex
      hxStar_feasible
      hQ_pos
      hfeasible_subset_ball
      hEll_finite
      hstage
      hm
  have hvol_ratio :=
    @volume_ratio_rpow_decay_under_interior_ball_condition
      (EuclideanSpace ℝ (Fin n)) _ _ _ _ _
      hfinrank_pos
      volume
      inferInstance
      problem.feasibleSet
      ρ
      hfeasible_ball'
      initialCenter
      R
      hR_nonneg
      (N + 1)
      (associatedEllipsoid problem initialCenter R (N + 1))
      (associated_ellipsoid_volume_decay_ennreal
        (problem := problem) (initialCenter := initialCenter) (R := R)
        hn hcut_nonzero hshape_pos hR_nonneg (N + 1))
  have hbudget :=
    accuracy_budget_implies_next_stage_log_threshold
      (problem := problem) (initialCenter := initialCenter) (xStar := xStar)
      (M := M) (R := R) (ρ := ρ) (ε := ε)
      hε hε_le hρ hN
  have houter_decay :
      R *
          Real.rpow
            (volume.real (associatedEllipsoid problem initialCenter R (N + 1)) /
              volume.real problem.feasibleSet)
            (1 / (n : ℝ)) ≤
        R *
          ((R / ρ) *
            Real.exp (-((N + 1 : ℝ) / (2 * (((n : ℝ) + 1) ^ (2 : ℕ)))))) := by
    exact mul_le_mul_of_nonneg_left hvol_ratio.2 hR_nonneg
  have hloc_lt :
      localization_radius xStar problem.oracle Y
          (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1) <
        ε / (M : ℝ) := by
    exact lt_of_le_of_lt (hradius_bound.1.trans (hradius_bound.2.trans houter_decay)) hbudget.2
  let ω : ℝ → WithTop ℝ := fun t ↦ (((M : ℝ) * max t 0 : ℝ) : WithTop ℝ)
  have hω_mono : Monotone ω := by
    intro a b hab
    change (((M : ℝ) * max a 0 : ℝ) : WithTop ℝ) ≤ (((M : ℝ) * max b 0 : ℝ) : WithTop ℝ)
    exact_mod_cast mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) M.2
  have hbound :
      ∀ i : Fin (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1)),
        problem (Y i) - problem xStar ≤
          ω (subgradientLocalizationMeasure problem.oracle xStar (Y i)) := by
    intro i
    have hYi_feasible : Y i ∈ problem.feasibleSet := by
      have hmem :
          y (Nat.nth (fun t ↦ y t ∈ problem.feasibleSet) i) ∈ problem.feasibleSet := by
        simpa using
          (Nat.nth_mem i fun hf ↦ i.2.trans_le (Nat.count_le_card hf (N + 1)))
      simpa [Y, feasibleSubsequence] using hmem
    have hsubgrad :
        IsSubgradientAt
            (fun x ↦ (problem x : WithTop ℝ))
            (Y i)
            (problem.oracle (Y i)) := by
      exact problem.oracle.subgradient_spec hYi_feasible
    have hmeasure_le :
        subgradientLocalizationMeasure problem.oracle xStar (Y i) ≤ R := by
      simpa using
        selected_point_localization_measure_le_outer_radius
          (problem := problem) (initialCenter := initialCenter) (xStar := xStar)
          (M := M) (R := R) (ρ := ρ) (ε := ε)
          hε hε_le hf_lipschitz hfeasible_ball hxStar hfeasible_subset_ball
          hn hcut_nonzero hshape_pos hE0_cover i
    -- The pointwise Lipschitz/subgradient gap estimate is the input for the best-radius owner.
    simpa [ω, Function.comp_apply] using
      (sub_le_lipschitz_mul_max_localizationMeasure
        (f := problem) (g := problem.oracle) (R := R) (M := M)
        xStar (Y i) hsubgrad hf_lipschitz hmeasure_le)
  have hgap :
      bestFunctionValueUpTo
          (problem ∘ Y)
          (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1) -
        problem xStar ≤
      (M : ℝ) *
        max
          (localization_radius xStar problem.oracle Y
            (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1))
          0 := by
    have hgapE :
        ((bestFunctionValueUpTo
              (problem ∘ Y)
              (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1) -
            problem xStar : ℝ) : WithTop ℝ) ≤
          ω
            (localization_radius xStar problem.oracle Y
              (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1)) := by
      simpa [ω, localization_radius, Nat.succ_pred_eq_of_pos hm, Function.comp_apply] using
        bestFunctionValueGapUpTo_le_modulusAtBestRadius
          problem
          ω
          hω_mono
          Y
          xStar
          (fun i ↦ subgradientLocalizationMeasure problem.oracle xStar (Y i))
          (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1)
          hbound
    exact_mod_cast hgapE
  have hM_pos : 0 < (M : ℝ) := by
    by_contra hM
    have hM_nonneg : 0 ≤ (M : ℝ) := M.2
    have hM_eq : (M : ℝ) = 0 := by linarith
    have hε_nonpos : ε ≤ 0 := by
      simpa [hM_eq] using hε_le
    linarith
  have hmax_lt :
      max
          (localization_radius xStar problem.oracle Y
            (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1))
          0 <
        ε / (M : ℝ) := by
    by_cases hloc_nonneg :
        0 ≤ localization_radius xStar problem.oracle Y
              (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1)
    · simpa [max_eq_left hloc_nonneg] using hloc_lt
    · have hdiv_pos : 0 < ε / (M : ℝ) := by positivity
      simpa [max_eq_right (le_of_not_ge hloc_nonneg)] using hdiv_pos
  have hmul_div :
      (M : ℝ) * (ε / (M : ℝ)) = ε := by
    field_simp [hM_pos.ne']
  have hω_le :
      (M : ℝ) *
          max
            (localization_radius xStar problem.oracle Y
              (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1))
            0 ≤
        ε := by
    have hω_lt :
        (M : ℝ) *
            max
              (localization_radius xStar problem.oracle Y
                (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1))
              0 <
          ε := by
      have hscaled := mul_lt_mul_of_pos_left hmax_lt hM_pos
      simpa [hmul_div] using hscaled
    exact hω_lt.le
  have hbest_le_xStar :
      bestFunctionValueUpTo
          (problem ∘ Y)
          (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1) ≤
        problem xStar + ε := by
    exact sub_le_iff_le_add'.mp (hgap.trans hω_le)
  -- The last step identifies the comparison value at the constrained minimizer with the owner
  -- optimal value from Chapter 1.
  rw [problem.optimalValue_eq_of_mem_argmin hxStar]
  exact_mod_cast hbest_le_xStar

/-- Proposition 3.47 in source-facing form: under the logarithmic oracle budget, one of the
queried ellipsoid centers is an `ε`-approximate minimizer of the constrained problem. -/
-- Proof sketch: first obtain the selected-feasible best-value bound, then turn the realizing
-- feasible selected sample back into a raw queried center via `Nat.nth`.
theorem ellipsoid_method_oracle_complexity_of_interior_ball
    {N : ℕ}
    (hN :
      2 * (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log ((M : ℝ) * R ^ (2 : ℕ) / (ρ * ε)) ≤
        (N : ℝ)) :
    ∃ k ≤ N, problem.IsApproximateMinimizer ε (y k) := by
  -- The remaining work is delegated to the selected-feasible best-value bound and the raw-index
  -- extraction lemma proved above.
  have hm :
      0 < Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) :=
    selected_feasible_count_pos_of_accuracy_budget
      (problem := problem) (initialCenter := initialCenter) (xStar := xStar) (M := M)
      (R := R) (ρ := ρ) (ε := ε)
      hε hε_le hfeasible_ball hfeasible_subset_ball hn hcut_nonzero hshape_pos hE0_cover hN
  have hbest :
      (bestFunctionValueUpTo
          (problem ∘ Y)
          (Nat.count (fun j ↦ y j ∈ problem.feasibleSet) (N + 1) - 1) : EReal) ≤
        problem.optimalValue + ε :=
    ellipsoid_method_oracle_complexity_of_interior_ball_bestFunctionValueUpTo
      (problem := problem) (initialCenter := initialCenter) (xStar := xStar) (M := M)
      (R := R) (ρ := ρ) (ε := ε)
      hε hε_le hf_lipschitz hfeasible_ball hxStar
      hfeasible_subset_ball hn hcut_nonzero hshape_pos hE0_cover hN
  exact selected_best_value_witness_is_approximate_minimizer
    (problem := problem) (initialCenter := initialCenter) (xStar := xStar) (M := M)
    (R := R) (ρ := ρ) (ε := ε)
    hε hε_le hf_lipschitz hfeasible_ball hxStar
    hfeasible_subset_ball hn hcut_nonzero hshape_pos hE0_cover hm hbest

end

end
