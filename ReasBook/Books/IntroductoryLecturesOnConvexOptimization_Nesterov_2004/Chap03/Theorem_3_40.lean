/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators DeltaN SubgradientLocalizationMeasure

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 3.40 lies in the chapter's projected normalized subgradient / finite-horizon stepsize
bound domain.

Sampled owner-style declarations:
- `FirstOrderConvexMinimizationProblem.normalizedSubgradientStep` in `Definition_3_40`, the owner
  projected normalized oracle step;
- `SimpleSetSubgradientMethod.iterates` in `Algorithm_3_2`, the recursive owner iterate sequence;
- `bestFunctionValueUpTo` in `Theorem_3_2_10`, the chapter owner of best sampled objective values;
- `deltaN` and `deltaN_apply` in `Definition_3_41`, the chapter owner and evaluation bridge for
  the finite stepsize scalar `Δ_N`.

Best owner abstraction:
- `source-facing`: the best sampled-value bound for a run
  `method : SimpleSetSubgradientMethod problem`;
- `core/canonical`: the scalar owner `deltaN`, surfaced as `Δ[k; R]`, for the finite
  stepsize prefix;
- `bridge/view`: the finite prefix `method.stepsizePrefix k`.

Primitive data:
- the owner first-order convex minimization problem `problem`;
- the owner simple-set subgradient run `method`;
- the reference minimizer `xStar`, radius `R`, Lipschitz constant `M`, and stage `k`.

Derived API:
- the owner projected normalized step and iterate recursion;
- the iterate sequence `method`;
- the sampled best value `bestFunctionValueUpTo (fun i ↦ problem (method i)) k`;
- the finite stepsize bound expressed canonically as `Δ[k; R]` of the method's prefix.

The previous version exposed a parallel selector-style API through raw parameters
`Q`, `projQ`, `f`, `xSeq`, `g`, and `h`. This refinement keeps the theorem source-facing,
retains the source's nonzero-subgradient side condition on nonoptimal iterates, and rewrites the
stepsize ratio through the chapter owner `deltaN`, leaving only the finite-prefix bridge
`method.stepsizePrefix k`.
-/

namespace SimpleSetSubgradientMethod

variable {problem : FirstOrderConvexMinimizationProblem E}

/-- Helper for Theorem 3.40: the best sampled objective gap is controlled by the method's best
localization radius. -/
lemma bestGap_le_lipschitz_mulLocalizationRadius
    (method : SimpleSetSubgradientMethod problem) (xStar : E) (R M : NNReal)
    (hxStar_min : IsMinOn problem problem.feasibleSet xStar)
    (hf_lipschitz : LipschitzOnWith M problem (Metric.closedBall xStar R))
    (hx0_ball : method.x0 ∈ Metric.closedBall xStar R)
    (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ problem (method i)) k - problem xStar ≤
      (M : ℝ) * localization_radius xStar problem.oracle.subgradient method k := by
  obtain ⟨j, hjradius⟩ :=
    bestFunctionValueUpTo_exists_eq
      (fun i ↦ v[problem.oracle.subgradient;xStar] (method i)) k
  have hbest_le_point :
      bestFunctionValueUpTo (fun i ↦ problem (method i)) k - problem xStar ≤
        problem (method j) - problem xStar := by
    exact sub_le_sub_right (bestFunctionValueUpTo_le j) _
  have hj_feasible : method j ∈ problem.feasibleSet :=
    method.iterates_mem j
  have hsubgrad :
      IsSubgradientAt (fun y ↦ (problem y : WithTop ℝ)) (method j)
        (problem.oracle.subgradient (method j)) :=
    problem.oracle.subgradient_spec (method j)
  have hmeasure_nonneg :
      0 ≤ v[problem.oracle.subgradient;xStar] (method j) := by
    -- The minimizing feasible point makes every sampled localization measure nonnegative.
    exact
      subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
        (f := problem) (g := problem.oracle.subgradient) hsubgrad
        ((isMinOn_iff.mp hxStar_min) _ hj_feasible)
  have hdist0 : ‖method 0 - xStar‖ ≤ (R : ℝ) := by
    -- The initial closed-ball hypothesis supplies the controlling radius.
    simpa [Metric.mem_closedBall, dist_eq_norm, method.iterates_zero] using hx0_ball
  have hmeasure0_le_R :
      v[problem.oracle.subgradient;xStar] (method 0) ≤ (R : ℝ) := by
    have hR_nonneg : 0 ≤ (R : ℝ) := le_trans (norm_nonneg _) hdist0
    by_cases hzero : problem.oracle.subgradient (method 0) = 0
    · simpa [subgradientLocalizationMeasure, hzero] using hR_nonneg
    · rw [subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero
        (g := problem.oracle.subgradient) (xBar := xStar) (x := method 0) hzero]
      have hinner_le :
          inner ℝ (problem.oracle.subgradient (method 0)) (method 0 - xStar) ≤
            ‖problem.oracle.subgradient (method 0)‖ * ‖method 0 - xStar‖ := by
        exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
      have hnorm_pos : 0 < ‖problem.oracle.subgradient (method 0)‖ :=
        norm_pos_iff.mpr hzero
      have hratio_le :
          inner ℝ (problem.oracle.subgradient (method 0)) (method 0 - xStar) /
              ‖problem.oracle.subgradient (method 0)‖ ≤
            ‖method 0 - xStar‖ := by
        exact (div_le_iff₀ hnorm_pos).2 <| by simpa [mul_comm] using hinner_le
      exact hratio_le.trans hdist0
  have hloc_le_R :
      localization_radius xStar problem.oracle.subgradient method k ≤ (R : ℝ) := by
    exact
      (localization_radius_le_measure
        (xStar := xStar) (g := problem.oracle.subgradient) (xSeq := method)
        (k := k) 0).trans hmeasure0_le_R
  have hjradius' :
      v[problem.oracle.subgradient;xStar] (method j) =
        localization_radius xStar problem.oracle.subgradient method k := by
    simpa [localization_radius, bestRadiusUpTo] using hjradius
  have hpoint_gap :
      problem (method j) - problem xStar ≤
        (M : ℝ) * max (v[problem.oracle.subgradient;xStar] (method j)) 0 := by
    -- Apply the one-point Lipschitz estimate at the iterate realizing the best radius.
    exact
      sub_le_lipschitz_mul_max_localizationMeasure
        (f := problem) (g := problem.oracle.subgradient) (R := R) (M := M)
        xStar (method j) hsubgrad hf_lipschitz (hjradius' ▸ hloc_le_R)
  -- The minimizing localization sample is nonnegative, so the `max` disappears.
  rw [max_eq_left hmeasure_nonneg, hjradius'] at hpoint_gap
  exact hbest_le_point.trans hpoint_gap

/-- Helper for Theorem 3.40: the normalized oracle direction rewrites the localization measure as
the corresponding inner product. -/
lemma inner_normalize_subgradient_eq_localizationMeasure
    (xStar x : E) :
    inner ℝ (NormedSpace.normalize (problem.oracle.subgradient x)) (x - xStar) =
      v[problem.oracle.subgradient;xStar] x := by
  by_cases hzero : problem.oracle.subgradient x = 0
  · -- In the zero branch both the normalized direction and the localization measure vanish.
    simp [hzero, NormedSpace.normalize, subgradientLocalizationMeasure_eq_zero_of_eq_zero
      (g := problem.oracle.subgradient) (xBar := xStar)]
  · -- Otherwise `normalize g` is exactly `g / ‖g‖`.
    rw [subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero
      (g := problem.oracle.subgradient) (xBar := xStar) (x := x) hzero]
    have hinner :
        inner ℝ (NormedSpace.normalize (problem.oracle.subgradient x)) (x - xStar) =
          ‖problem.oracle.subgradient x‖⁻¹ *
            inner ℝ (problem.oracle.subgradient x) (x - xStar) := by
      simp [NormedSpace.normalize, real_inner_smul_left]
    simpa [div_eq_mul_inv, mul_comm] using hinner

/-- Helper for Theorem 3.40: one projected normalized step satisfies the standard squared-distance
drop inequality with the localization measure. -/
lemma sqdist_succ_le_sqdist_sub_two_mulLocalization_add_sq
    (method : SimpleSetSubgradientMethod problem) (xStar : E)
    (hxStar_mem : xStar ∈ problem.feasibleSet)
    (i : ℕ) :
    ‖method (i + 1) - xStar‖ ^ (2 : ℕ) ≤
      ‖method i - xStar‖ ^ (2 : ℕ) -
        2 * method.stepsize i * v[problem.oracle.subgradient;xStar] (method i) +
        (method.stepsize i) ^ (2 : ℕ) := by
  let y : E :=
    method i - method.stepsize i • NormedSpace.normalize (problem.oracle.subgradient (method i))
  have hpre_sqdist :
      ‖method (i + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖y - xStar‖ ^ (2 : ℕ) := by
    have hpyth :
        ‖method (i + 1) - xStar‖ ^ (2 : ℕ) + ‖method (i + 1) - y‖ ^ (2 : ℕ) ≤
          ‖y - xStar‖ ^ (2 : ℕ) := by
      -- The next iterate is the projection of the explicit pre-projection point `y`.
      simpa [y, method.iterates_succ,
        FirstOrderConvexMinimizationProblem.normalizedSubgradientStep, norm_sub_rev, add_comm]
        using
        IsProjectionPointOn.pythagorean_ineq
          problem.feasibleSet_convex
          (problem.projection_spec y)
          hxStar_mem
    nlinarith
  have hnorm_normalize_sq_le_one :
      ‖NormedSpace.normalize (problem.oracle.subgradient (method i))‖ ^ (2 : ℕ) ≤ 1 := by
    by_cases hzero : problem.oracle.subgradient (method i) = 0
    · simp [hzero, NormedSpace.normalize]
    · rw [NormedSpace.norm_normalize hzero]
      norm_num
  have hpre_expand :
      ‖y - xStar‖ ^ (2 : ℕ) ≤
        ‖method i - xStar‖ ^ (2 : ℕ) -
          2 * method.stepsize i * v[problem.oracle.subgradient;xStar] (method i) +
          (method.stepsize i) ^ (2 : ℕ) := by
    have hnorm_term :
        ‖method.stepsize i • NormedSpace.normalize (problem.oracle.subgradient (method i))‖
            ^ (2 : ℕ) ≤
          (method.stepsize i) ^ (2 : ℕ) := by
      calc
        ‖method.stepsize i • NormedSpace.normalize (problem.oracle.subgradient (method i))‖
            ^ (2 : ℕ)
            = ‖method.stepsize i‖ ^ (2 : ℕ) *
                ‖NormedSpace.normalize (problem.oracle.subgradient (method i))‖ ^ (2 : ℕ) := by
                  rw [norm_smul]
                  ring
        _ ≤ ‖method.stepsize i‖ ^ (2 : ℕ) * 1 := by
              gcongr
        _ = (method.stepsize i) ^ (2 : ℕ) := by
              rw [mul_one, Real.norm_eq_abs, sq_abs]
    have hsq :
        ‖y - xStar‖ ^ (2 : ℕ) =
          ‖method i - xStar‖ ^ (2 : ℕ) -
            2 * method.stepsize i *
              inner ℝ (NormedSpace.normalize (problem.oracle.subgradient (method i)))
                (method i - xStar) +
            ‖method.stepsize i •
                NormedSpace.normalize (problem.oracle.subgradient (method i))‖ ^ (2 : ℕ) := by
      -- Expand the squared norm before replacing the inner product by the localization measure.
      calc
        ‖y - xStar‖ ^ (2 : ℕ)
            = ‖(method i - xStar) - method.stepsize i •
                NormedSpace.normalize (problem.oracle.subgradient (method i))‖ ^ (2 : ℕ) := by
                  simp [y, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        _ = ‖method i - xStar‖ ^ (2 : ℕ) -
              2 * inner ℝ (method i - xStar)
                (method.stepsize i •
                  NormedSpace.normalize (problem.oracle.subgradient (method i))) +
              ‖method.stepsize i •
                NormedSpace.normalize (problem.oracle.subgradient (method i))‖ ^ (2 : ℕ) := by
                rw [norm_sub_sq_real]
        _ = ‖method i - xStar‖ ^ (2 : ℕ) -
              2 * method.stepsize i *
                inner ℝ (NormedSpace.normalize (problem.oracle.subgradient (method i)))
                  (method i - xStar) +
              ‖method.stepsize i •
                NormedSpace.normalize (problem.oracle.subgradient (method i))‖ ^ (2 : ℕ) := by
                rw [real_inner_smul_right, real_inner_comm]
                ring
    rw [hsq]
    have hinner_rw :
        inner ℝ (NormedSpace.normalize (problem.oracle.subgradient (method i))) (method i - xStar) =
          v[problem.oracle.subgradient;xStar] (method i) :=
      inner_normalize_subgradient_eq_localizationMeasure (problem := problem) xStar (method i)
    rw [hinner_rw]
    nlinarith
  exact hpre_sqdist.trans hpre_expand

/-- Helper for Theorem 3.40: the best localization radius is bounded by the canonical finite
stepsize scalar `Δ[k; R]` attached to the method's prefix. -/
lemma localizationRadius_le_deltaN_stepsizePrefix
    (method : SimpleSetSubgradientMethod problem) (xStar : E) (R : NNReal)
    (hxStar_mem : xStar ∈ problem.feasibleSet)
    (hx0_ball : method.x0 ∈ Metric.closedBall xStar R)
    (hstepsize_pos : ∀ i : ℕ, 0 < method.stepsize i)
    (k : ℕ) :
    localization_radius xStar problem.oracle.subgradient method k ≤
      Δ[k; R] (method.stepsizePrefix k) := by
  have htelescoping :
      ∀ n : ℕ,
        2 * ∑ i : Fin n, method.stepsize i * v[problem.oracle.subgradient;xStar] (method i) ≤
          ‖method 0 - xStar‖ ^ (2 : ℕ) - ‖method n - xStar‖ ^ (2 : ℕ) +
            ∑ i : Fin n, (method.stepsize i) ^ (2 : ℕ) := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ihn =>
        have hstep :
            ‖method (n + 1) - xStar‖ ^ (2 : ℕ) ≤
              ‖method n - xStar‖ ^ (2 : ℕ) -
                2 * method.stepsize n * v[problem.oracle.subgradient;xStar] (method n) +
                (method.stepsize n) ^ (2 : ℕ) :=
          sqdist_succ_le_sqdist_sub_two_mulLocalization_add_sq
            (problem := problem) method xStar hxStar_mem n
        -- Split the finite sums into the previous prefix and the last step.
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
        have hcast_mul :
            (∑ i : Fin n, method.stepsize (Fin.castSucc i) *
                v[problem.oracle.subgradient;xStar] (method (Fin.castSucc i))) =
              ∑ i : Fin n, method.stepsize i *
                v[problem.oracle.subgradient;xStar] (method i) := by
          simp
        have hcast_sq :
            (∑ i : Fin n, (method.stepsize (Fin.castSucc i)) ^ (2 : ℕ)) =
              ∑ i : Fin n, (method.stepsize i) ^ (2 : ℕ) := by
          simp
        rw [hcast_mul, hcast_sq]
        simp only [Fin.last, Fin.val_mk] at *
        have hstep' :
            2 * method.stepsize n * v[problem.oracle.subgradient;xStar] (method n) ≤
              ‖method n - xStar‖ ^ (2 : ℕ) - ‖method (n + 1) - xStar‖ ^ (2 : ℕ) +
                (method.stepsize n) ^ (2 : ℕ) := by
          nlinarith [hstep]
        nlinarith
  have hdist0 : ‖method 0 - xStar‖ ≤ (R : ℝ) := by
    -- The initial point controls the initial squared distance term.
    simpa [Metric.mem_closedBall, dist_eq_norm, method.iterates_zero] using hx0_ball
  have hdist0_sq :
      ‖method 0 - xStar‖ ^ (2 : ℕ) ≤ (R : ℝ) ^ (2 : ℕ) := by
    have hR_nonneg : 0 ≤ (R : ℝ) := le_trans (norm_nonneg _) hdist0
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hR_nonneg] using hdist0)
  have hweighted :
      2 * ∑ i : Fin (k + 1), method.stepsize i *
        v[problem.oracle.subgradient;xStar] (method i) ≤
        (R : ℝ) ^ (2 : ℕ) + ∑ i : Fin (k + 1), (method.stepsize i) ^ (2 : ℕ) := by
    have hnonneg : 0 ≤ ‖method (k + 1) - xStar‖ ^ (2 : ℕ) := by positivity
    nlinarith [htelescoping (k + 1), hdist0_sq]
  have hsum_pos : 0 < ∑ i : Fin (k + 1), method.stepsize i := by
    have hle :
        method.stepsize (0 : Fin (k + 1)) ≤ ∑ i : Fin (k + 1), method.stepsize i := by
      simpa using
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin (k + 1))))
          (f := fun i : Fin (k + 1) ↦ method.stepsize i)
          (fun i _ ↦ le_of_lt (hstepsize_pos i))
          (by simp : (0 : Fin (k + 1)) ∈ (Finset.univ : Finset (Fin (k + 1))))
    exact lt_of_lt_of_le (hstepsize_pos (0 : Fin (k + 1))) hle
  have hloc_sum :
      2 * (∑ i : Fin (k + 1), method.stepsize i) *
          localization_radius xStar problem.oracle.subgradient method k ≤
        2 * ∑ i : Fin (k + 1), method.stepsize i *
          v[problem.oracle.subgradient;xStar] (method i) := by
    calc
      2 * (∑ i : Fin (k + 1), method.stepsize i) *
          localization_radius xStar problem.oracle.subgradient method k
          = (∑ i : Fin (k + 1), method.stepsize i) *
              (2 * localization_radius xStar problem.oracle.subgradient method k) := by
                ring
      _ = ∑ i : Fin (k + 1), method.stepsize i *
            (2 * localization_radius xStar problem.oracle.subgradient method k) := by
              rw [Finset.sum_mul]
      _ = ∑ i : Fin (k + 1), 2 * method.stepsize i *
            localization_radius xStar problem.oracle.subgradient method k := by
              simpa [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ ∑ i : Fin (k + 1), 2 * method.stepsize i *
            v[problem.oracle.subgradient;xStar] (method i) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hloc_i :
                  localization_radius xStar problem.oracle.subgradient method k ≤
                    v[problem.oracle.subgradient;xStar] (method i) :=
                localization_radius_le_measure
                  (xStar := xStar) (g := problem.oracle.subgradient)
                  (xSeq := method) (k := k) i
              nlinarith [hstepsize_pos i]
      _ = (∑ i : Fin (k + 1), method.stepsize i *
            v[problem.oracle.subgradient;xStar] (method i)) * 2 := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (Finset.sum_mul
                  (s := Finset.univ)
                  (f := fun i : Fin (k + 1) ↦
                    method.stepsize i * v[problem.oracle.subgradient;xStar] (method i))
                  2).symm
      _ = 2 * ∑ i : Fin (k + 1), method.stepsize i *
            v[problem.oracle.subgradient;xStar] (method i) := by
              ring
  have hloc_div :
      localization_radius xStar problem.oracle.subgradient method k ≤
        ((R : ℝ) ^ (2 : ℕ) + ∑ i : Fin (k + 1), (method.stepsize i) ^ (2 : ℕ)) /
          (2 * ∑ i : Fin (k + 1), method.stepsize i) := by
    refine (le_div_iff₀ (show 0 < 2 * ∑ i : Fin (k + 1), method.stepsize i by positivity)).2 ?_
    nlinarith [hloc_sum.trans hweighted]
  -- Rewrite the quotient through the canonical owner `Δ[k; R]`.
  simpa [deltaN_apply] using hloc_div

/-- Theorem 3.40: for a simple-set subgradient method on an owner first-order convex minimization
problem, the best objective value among the first `k + 1` iterates satisfies the standard
`M * Δ_k` error bound, written with the chapter owners
`bestFunctionValueUpTo (fun i ↦ problem (method i)) k` for the sampled minimum `f_k^*` and
`Δ[k; R] (method.stepsizePrefix k)` for the finite stepsize prefix; the chosen oracle
subgradient is assumed nonzero at every iterate different from `xStar`, as in the source. -/
theorem bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method
    (method : SimpleSetSubgradientMethod problem) (xStar : E) (R M : NNReal)
    (hxStar_min : IsMinOn problem problem.feasibleSet xStar)
    (hxStar_mem : xStar ∈ problem.feasibleSet)
    (hf_lipschitz : LipschitzOnWith M problem (Metric.closedBall xStar R))
    (hx0_ball : method.x0 ∈ Metric.closedBall xStar R)
    (hstepsize_pos : ∀ i : ℕ, 0 < method.stepsize i)
    (hsubgradient_nonzero :
      ∀ i : ℕ, method i ≠ xStar → problem.oracle.subgradient (method i) ≠ 0)
    (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ problem (method i)) k - problem xStar ≤
      (M : ℝ) * Δ[k; R] (method.stepsizePrefix k) := by
  let _ := hsubgradient_nonzero
  -- Route correction: the global-minimizer theorem from `Theorem_3_2_2` does not apply here,
  -- so the proof is split into a constrained best-gap bound and a projected-step radius estimate.
  have hbest :
      bestFunctionValueUpTo (fun i ↦ problem (method i)) k - problem xStar ≤
        (M : ℝ) * localization_radius xStar problem.oracle.subgradient method k :=
    bestGap_le_lipschitz_mulLocalizationRadius
      (problem := problem) method xStar R M hxStar_min hf_lipschitz hx0_ball k
  have hloc :
      localization_radius xStar problem.oracle.subgradient method k ≤
        Δ[k; R] (method.stepsizePrefix k) :=
    localizationRadius_le_deltaN_stepsizePrefix
      (problem := problem) method xStar R hxStar_mem hx0_ball hstepsize_pos k
  -- Compose the constrained gap estimate with the `Δ[k; R]` radius bound.
  exact hbest.trans <| mul_le_mul_of_nonneg_left hloc M.2

end SimpleSetSubgradientMethod

end
