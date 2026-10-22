/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_22
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Proposition 7.1: the interior-point hypothesis on `∂f(0)` contains a closed ball
around the origin. -/
lemma subdifferential_zero_contains_closedBall
    (problem : ConicUnconstrainedMinimizationProblem E) :
    ∃ ε > 0,
      Metric.closedBall (0 : E) ε ⊆ ∂ (fun y ↦ (problem y : WithTop ℝ))(0) := by
  -- Shrink the open neighborhood from the interior hypothesis to a closed ball.
  rcases Metric.mem_nhds_iff.1
      (isOpen_interior.mem_nhds problem.zero_mem_interior_subdifferential) with
    ⟨r, hr, hrsub⟩
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro g hg
  exact interior_subset (hrsub (Metric.closedBall_subset_ball (half_lt_self hr) hg))

/-- Helper for Proposition 7.1: the origin subdifferential interior gives a uniform linear lower
bound for the objective. -/
lemma objective_ge_radius_mul_norm
    (problem : ConicUnconstrainedMinimizationProblem E) :
    ∃ ε > 0, ∀ x : E, ε * ‖x‖ ≤ problem x := by
  rcases subdifferential_zero_contains_closedBall problem with ⟨ε, hε, hball⟩
  have hzero : problem (0 : E) = 0 := by
    -- Positive homogeneity at scale `0` forces the objective value at the origin to vanish.
    simpa using problem.map_nonneg_smul (x := (0 : E)) (t := (0 : ℝ)) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro x
  by_cases hx : x = 0
  · -- The zero vector contributes the trivial inequality `0 ≤ 0`.
    simp [hx, hzero]
  · have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let g : E := (ε / ‖x‖) • x
    have hg_mem_ball : g ∈ Metric.closedBall (0 : E) ε := by
      -- Normalize the test vector so its norm is exactly `ε`.
      have hgnorm : ‖g‖ = ε := by
        calc
          ‖g‖ = ‖ε / ‖x‖‖ * ‖x‖ := by
            simpa [g] using (norm_smul (ε / ‖x‖) x)
          _ = |ε / ‖x‖| * ‖x‖ := by
            rw [Real.norm_eq_abs]
          _ = (ε / ‖x‖) * ‖x‖ := by
            rw [abs_of_nonneg (div_nonneg hε.le hxnorm_pos.le)]
          _ = ε := by
            field_simp [hxnorm_pos.ne']
      simpa [Metric.mem_closedBall, g, dist_eq_norm] using hgnorm.le
    have hg_sub :
        g ∈ ∂ (fun y ↦ (problem y : WithTop ℝ))(0) :=
      hball hg_mem_ball
    have hsupport := (mem_subdifferential_coe_real_iff.mp hg_sub) x
    have hinner : inner ℝ g x = ε * ‖x‖ := by
      -- The normalized subgradient pairs with `x` exactly as `ε‖x‖`.
      calc
        inner ℝ g x = (ε / ‖x‖) * inner ℝ x x := by
          simpa [g] using (real_inner_smul_left x x (ε / ‖x‖))
        _ = (ε / ‖x‖) * (‖x‖ * ‖x‖) := by
          rw [real_inner_self_eq_norm_sq, pow_two]
        _ = ε * ‖x‖ := by
          field_simp [hxnorm_pos.ne']
    -- Apply the supporting inequality at the origin with the normalized subgradient.
    simpa [hzero, g, hinner] using hsupport

/-- Helper for Proposition 7.1: the closed feasible set stays a positive distance away from the
origin. -/
lemma feasibleSet_norm_away_from_zero
    (problem : ConicUnconstrainedMinimizationProblem E) :
    ∃ r > 0, ∀ ⦃x : E⦄, x ∈ problem.feasibleSet → r ≤ ‖x‖ := by
  have hzero_compl : (0 : E) ∈ problem.feasibleSetᶜ := problem.zero_not_mem_feasibleSet
  rcases Metric.mem_nhds_iff.1
      (problem.feasibleSet_isClosed.isOpen_compl.mem_nhds hzero_compl) with
    ⟨r, hr, hrball⟩
  refine ⟨r, hr, ?_⟩
  intro x hx
  by_contra hxr
  have hxn : ‖x‖ < r := lt_of_not_ge hxr
  have hxball : x ∈ Metric.ball (0 : E) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hxn
  have hxcompl : x ∈ problem.feasibleSetᶜ := hrball hxball
  exact hxcompl hx

/-- Helper for Proposition 7.1: every feasible constrained sublevel set is bounded because the
uniform linear lower bound controls the norm. -/
lemma bounded_objective_sublevels_on_feasibleSet
    (problem : ConicUnconstrainedMinimizationProblem E) :
    ∀ α : ℝ,
      Bornology.IsBounded
        (constrainedSublevelSet problem.feasibleSet
          (fun x ↦ (problem x : WithTop ℝ)) α) := by
  rcases objective_ge_radius_mul_norm problem with ⟨ε, hε, hbound⟩
  intro α
  by_cases hα : 0 ≤ α
  · -- A feasible point below level `α` must lie in the closed ball of radius `α / ε`.
    refine (Metric.isBounded_closedBall : Bornology.IsBounded
      (Metric.closedBall (0 : E) (α / ε))).subset ?_
    intro x hx
    rcases mem_constrainedSublevelSet_iff.mp hx with ⟨_, hxα⟩
    have hxα' : problem x ≤ α := by
      exact_mod_cast hxα
    have hnorm : ‖x‖ ≤ α / ε := by
      refine (le_div_iff₀ hε).2 ?_
      simpa [mul_comm] using le_trans (hbound x) hxα'
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  · -- Negative sublevels are empty because the objective is globally nonnegative.
    have hempty :
        constrainedSublevelSet problem.feasibleSet
            (fun x ↦ (problem x : WithTop ℝ)) α = ∅ := by
      ext x
      constructor
      · intro hx
        rcases mem_constrainedSublevelSet_iff.mp hx with ⟨_, hxα⟩
        have hxα' : problem x ≤ α := by
          exact_mod_cast hxα
        have hnonneg : 0 ≤ problem x := by
          exact le_trans (mul_nonneg hε.le (norm_nonneg x)) (hbound x)
        exact (not_le_of_gt (lt_of_not_ge hα)) (le_trans hnonneg hxα')
      · intro hx
        exact False.elim hx
    rw [hempty]
    exact Bornology.isBounded_empty

-- Proof sketch: combine the source-faithful lower bound `f(x) ≥ ε‖x‖` from the interior of
-- `∂f(0)` with the positive distance of the closed feasible set from the origin. The same lower
-- bound makes every feasible sublevel set bounded, so the Chapter 3 proper-space attainment theorem
-- yields a minimizer, and the distance estimate upgrades its value to a strict positive lower
-- bound.
/-
The attainment step below uses properness only to invoke the Chapter 3 compactness-based minimizer
theorem; the four geometric helper lemmas above are metric / convex and do not need it.
-/
variable [ProperSpace E]

/-- Proposition 7.1: for a conic unconstrained minimization problem, the optimal value
`min_{x ∈ Q₁} f(x)` is attained at a feasible point and that attained value is strictly positive.
-/
theorem positive_homogeneous_convex_minimizer_exists_and_pos
    (problem : ConicUnconstrainedMinimizationProblem E) :
    ∃ x ∈ problem.feasibleSet, IsMinOn problem problem.feasibleSet x ∧ 0 < problem x := by
  rcases objective_ge_radius_mul_norm problem with ⟨ε, hε, hbound⟩
  rcases feasibleSet_norm_away_from_zero problem with ⟨r, hr, hsep⟩
  letI : FiniteDimensional ℝ E :=
    FiniteDimensional.of_isCompact_closedBall ℝ zero_lt_one (by
      simpa using (isCompact_closedBall (x := (0 : E)) (r := (1 : ℝ))))
  have hcont : Continuous problem := by
    -- Convexity on the open whole space gives continuity of the real-valued objective.
    simpa [continuousOn_univ] using problem.objective_convex.continuousOn isOpen_univ
  let fTop : E → WithTop ℝ := fun x ↦ (problem x : WithTop ℝ)
  have hf_closed : ClosedConvexFunction fTop := by
    -- Package the continuous convex real-valued objective as a closed convex `WithTop` function.
    simpa [fTop] using
      (closedConvexFunction_coe_of_convexOn_continuous
        (f := problem) problem.objective_convex hcont)
  have hfeasible_dom : problem.feasibleSet ⊆ dom fTop := by
    intro x hx
    simp [fTop, withTopEffectiveDomain]
  have hf_feasible : ClosedConvexOn problem.feasibleSet fTop := by
    -- Restrict the global closed-convex owner to the closed convex feasible set.
    exact hf_closed.restrict
      problem.feasibleSet_isClosed
      problem.feasibleSet_convex
      hfeasible_dom
  obtain ⟨x, hx_feasible, hx_min⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      problem.feasibleSet_nonempty
      hf_feasible
      (bounded_objective_sublevels_on_feasibleSet problem)
  have hpositive_lb : 0 < ε * r := mul_pos hε hr
  have hvalue_lb : ε * r ≤ problem x := by
    -- Combine the feasible-set distance estimate with the global lower bound on `problem`.
    calc
      ε * r ≤ ε * ‖x‖ := by
        exact mul_le_mul_of_nonneg_left (hsep hx_feasible) hε.le
      _ ≤ problem x := hbound x
  exact ⟨x, hx_feasible, hx_min, lt_of_lt_of_le hpositive_lb hvalue_lb⟩
