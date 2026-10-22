/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_16
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_21
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_23

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {x : ℕ → E} {L : ℕ → PosReal}

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Source-faithful stepsize owner for Theorem 10.24: either the exact constant stepsize rule
`L_k = L_f`, or the genuine backtracking procedure B2 from Algorithm 10.3. Unlike the weaker
Remark 10.19 bridge `ConstantOrBacktrackingB2StepsizeRule`, the B2 branch records the actual
accepted-trial procedure rather than only the upper-model shadow it implies. -/
abbrev SourceConvergenceStepsizeRule
    {XStar : Set E} {FOpt : ℝ}
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  uses_proximal_gradient_Lf_stepsize_rule Lf L ∨
    ∃ s : PosReal, ∃ η : ProximalGradientBacktrackingGrowthFactor,
      uses_proximal_gradient_backtracking_B2_rule f g x L htraj s η

end IsConvexCompositeSmoothMinimizationProblem

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Helper for Theorem 10.24: enlarging the smoothness constant preserves `is_l_smooth_on` on the
same set. -/
private lemma isLSmoothOn_mono
    {h : E → ℝ} {S : Set E} {L₁ L₂ : NNReal}
    (hh : is_l_smooth_on h S L₁)
    (hL : (L₁ : ℝ) ≤ (L₂ : ℝ)) :
    is_l_smooth_on h S L₂ := by
  -- Rewrite the owner predicate to the pointwise Lipschitz-gradient bound and enlarge the final
  -- coefficient.
  rw [is_l_smooth_on_iff] at hh ⊢
  refine ⟨hh.1, ?_⟩
  intro x hx y hy
  exact le_trans (hh.2 x hx y hy) (by gcongr)

/-- Helper for Theorem 10.24: the composite objective `F = f + g` is lower semicontinuous. -/
private lemma compositeModelObjectiveLowerSemicontinuous
    {Lf : NNReal}
    (hprob : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    LowerSemicontinuous (composite_model_objective f g) := by
  have hf_closed : LowerSemicontinuous f := hprob.f_closed
  have hg_closed : LowerSemicontinuous g := hprob.g_closed
  have hg_ne_bot : ∀ y, g y ≠ ⊥ := hprob.g_proper.ne_bot
  have hf_ne_bot : ∀ y, f y ≠ ⊥ := hprob.f_ne_bot
  -- Lower semicontinuity is preserved under `EReal` addition because neither summand takes `⊥`.
  simpa [composite_model_objective_apply] using
    hf_closed.add' hg_closed fun y ↦
      EReal.continuousAt_add
        (Or.inr (hg_ne_bot y))
        (Or.inl (hf_ne_bot y))

/-- Helper for Theorem 10.24: lower semicontinuity bounds the value at the limit point by the
`liminf` along any convergent sequence. -/
private lemma lowerSemicontinuousValueLeLiminfAlongSequence
    {h : E → EReal} (hclosed : LowerSemicontinuous h) {z : ℕ → E} {xBar : E}
    (hz : Filter.Tendsto z Filter.atTop (nhds xBar)) :
    h xBar ≤ Filter.liminf (fun n ↦ h (z n)) Filter.atTop := by
  -- Compare the neighborhood-filter `liminf` at `xBar` with the mapped sequence filter.
  calc
    h xBar ≤ Filter.liminf h (nhds xBar) := hclosed.le_liminf xBar
    _ ≤ Filter.liminf h (Filter.map z Filter.atTop) := Filter.liminf_le_liminf_of_le hz
    _ = Filter.liminf (fun n ↦ h (z n)) Filter.atTop := by
      rw [← Filter.liminf_comp]
      rfl

/-- Helper for Theorem 10.24: every positive proximal-gradient iterate has a finite composite
objective value. -/
private lemma proximalGradientPositiveIterateObjectiveEqCoeToReal
    {Lf : NNReal}
    [hprob : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) :
    composite_model_objective f g (x (k + 1)) =
      ((((composite_model_objective f g (x (k + 1))).toReal : ℝ)) : EReal) := by
  letI : IsProperExtendedRealFunction g := hprob.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hprob.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hprob.g_convex⟩
  have hxsucc :
      x (k + 1) ∈ effective_domain g :=
    proximalGradientPositiveIterate_memEffectiveDomainG (hproblem := hprob) htraj k
  -- Rewrite the positive iterate objective through its finite real representative.
  rw [objectiveEqReal_of_memEffectiveDomainG (hproblem := hprob) hxsucc, EReal.toReal_coe]

/-- Helper for Theorem 10.24: every positive proximal-gradient iterate has a nonnegative real
objective gap. -/
private lemma proximalGradientPositiveIterateGapNonneg
    {Lf : NNReal}
    [hprob : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) :
    0 ≤ (composite_model_objective f g (x (k + 1))).toReal - FOpt := by
  letI : IsProperExtendedRealFunction g := hprob.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hprob.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hprob.g_convex⟩
  have hxsucc :
      x (k + 1) ∈ effective_domain g :=
    proximalGradientPositiveIterate_memEffectiveDomainG (hproblem := hprob) htraj k
  have hgapE :
      ((0 : ℝ) : EReal) ≤
        ((((composite_model_objective f g (x (k + 1))).toReal - FOpt : ℝ) : EReal)) := by
    rw [objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG (hproblem := hprob) hxsucc]
    have hgap_nonneg :
        (0 : EReal) ≤ composite_model_objective f g (x (k + 1)) - (FOpt : EReal) := by
      exact
        (EReal.sub_nonneg (Or.inr (by simp)) (Or.inr (by simp))).2
          (hprob.optimal_value_isGLB.1 ⟨x (k + 1), rfl⟩)
    simpa using hgap_nonneg
  exact EReal.coe_nonneg.mp hgapE

/-- Helper for Theorem 10.24: the source-facing constant/B2 owner forgets to Remark 10.19's
canonical constant/B2 owner. -/
private lemma sourceConvergenceRule_constantOrBacktrackingB2
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceConvergenceStepsizeRule x L htraj) :
    hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  rcases hrule with hLf_rule | ⟨s, η, hB2⟩
  · exact Or.inl hLf_rule
  · refine Or.inr ?_
    refine ⟨s, η, ?_⟩
    exact
      uses_proximal_gradient_backtracking_B2_rule_upperModel
        (f := f)
        (g := g)
        hproblem.f_ne_bot
        hB2

/-- Helper for Theorem 10.24: once `L_f` is known to be positive, the source-facing convergence
owner refines to Theorem 10.21's source-facing sublinear-rate owner. -/
private lemma sourceConvergenceRule_existsSourceSublinearRateRuleOf_posLf
    (hLf : 0 < (Lf : ℝ))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceConvergenceStepsizeRule x L htraj) :
    ∃ α, hproblem.SourceSublinearRateStepsizeRule x L htraj α := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  rcases hrule with hLf_rule | ⟨s, η, hB2⟩
  · -- In the constant-rule branch, Theorem 10.21 uses the textbook coefficient `α = 1`.
    exact ⟨1, Or.inl ⟨rfl, hLf_rule⟩⟩
  · -- In the B2 branch, package the stored `s, η` data with the supplied positivity witness.
    exact ⟨max (η : ℝ) ((s : ℝ) / (Lf : ℝ)), Or.inr ⟨hLf, s, η, rfl, hB2⟩⟩

/-- Helper for Theorem 10.24: if `(Lf : ℝ) = 0`, then the source-facing convergence owner forces
the realized stepsizes to be constant with value equal to the B2 seed `s`. -/
private lemma sourceConvergenceRule_zeroLf_constantStepsize
    (hLf0 : (Lf : ℝ) = 0)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceConvergenceStepsizeRule x L htraj) :
    ∃ s : PosReal, ∀ n, (L n : ℝ) = (s : ℝ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  rcases hrule with hLf_rule | ⟨s, η, hB2⟩
  · -- Route correction: the exact constant rule is impossible when `(Lf : ℝ) = 0`.
    exact False.elim ((uses_proximal_gradient_Lf_stepsize_rule_lf_pos hLf_rule).ne' hLf0)
  · refine ⟨s, ?_⟩
    intro n
    rcases
        proximal_gradient_backtracking_B2_stepsize_bounds
          (Lf := Lf)
          (f := f)
          (g := g)
          hproblem.f_ne_bot
          hproblem.f_effective_domain_convex
          hproblem.g_effective_domain_subset_interior_f_effective_domain
          hproblem.f_toReal_smooth_on_interior_effective_domain
          htraj
          s
          η
          hB2
          n with
      ⟨hs_lower, hL_upper⟩
    have hL_upper' : (L n : ℝ) ≤ (s : ℝ) := by
      have hL_upper_zero : (L n : ℝ) ≤ max (0 : ℝ) (s : ℝ) := by
        simpa [hLf0] using hL_upper
      rw [max_eq_right (le_of_lt (PosReal.coe_pos s))] at hL_upper_zero
      exact hL_upper_zero
    exact le_antisymm hL_upper' hs_lower

/-- Helper for Theorem 10.24: every sequential cluster point is optimal once Theorem 10.21's
source-facing sublinear-rate owner is available. -/
private lemma clusterPoint_mem_optimalSet_of_sourceSublinearRate
    {Lf : NNReal}
    [hprob : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
    {x : ℕ → E} {L : ℕ → PosReal} {α : ℝ} {xStar0 xBar : E}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hprob.SourceSublinearRateStepsizeRule x L htraj α)
    (hxStar0 : xStar0 ∈ XStar)
    (hxBar : MapClusterPt xBar Filter.atTop x) :
    xBar ∈ XStar := by
  letI : IsProperExtendedRealFunction g := hprob.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hprob.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hprob.g_convex⟩
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  have hshift_tendsto :
      Filter.Tendsto (fun n ↦ x (ψ (n + 1))) Filter.atTop (nhds xBar) := by
    -- Shift the subsequence so Theorem 10.21 can be applied at positive indices directly.
    exact
      hψtendsto.comp
        (Filter.tendsto_atTop_mono Nat.le_succ Filter.tendsto_id)
  let C : ℝ := α * (Lf : ℝ) * ‖x 0 - xStar0‖ ^ (2 : ℕ) / 2
  have hsubseq_gap :
      Filter.Tendsto
        (fun n ↦ (composite_model_objective f g (x (ψ (n + 1)))).toReal - FOpt)
        Filter.atTop
        (nhds 0) := by
    have hnonneg :
        ∀ n, 0 ≤ (composite_model_objective f g (x (ψ (n + 1)))).toReal - FOpt := by
      intro n
      have hψ_pos : 1 ≤ ψ (n + 1) := by
        exact le_trans (Nat.succ_le_succ (Nat.zero_le n)) (StrictMono.id_le hψmono (n + 1))
      rw [← Nat.sub_add_cancel hψ_pos]
      exact
        proximalGradientPositiveIterateGapNonneg
          (hprob := hprob)
          (htraj := htraj)
          (ψ (n + 1) - 1)
    have hupper :
        ∀ n,
          (composite_model_objective f g (x (ψ (n + 1)))).toReal - FOpt ≤
            C / (ψ (n + 1) : ℝ) := by
      intro n
      have hψ_pos : 1 ≤ ψ (n + 1) := by
        exact le_trans (Nat.succ_le_succ (Nat.zero_le n)) (StrictMono.id_le hψmono (n + 1))
      have hbound :=
        proximal_gradient_convex_objective_gap_le
          (hproblem := hprob)
          (htraj := htraj)
          (hrule := hrule)
          hxStar0
          (ψ (n + 1))
          hψ_pos
      have hobjval :
          composite_model_objective f g (x (ψ (n + 1))) =
            ((((composite_model_objective f g (x (ψ (n + 1)))).toReal : ℝ)) : EReal) := by
        rw [← Nat.sub_add_cancel hψ_pos]
        exact
          proximalGradientPositiveIterateObjectiveEqCoeToReal
            (hprob := hprob)
            (htraj := htraj)
            (ψ (n + 1) - 1)
      rw [hobjval] at hbound
      exact EReal.coe_le_coe_iff.mp (by
        simpa [C, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound)
    have hbound_tendsto :
        Filter.Tendsto (fun n ↦ C / (ψ (n + 1) : ℝ)) Filter.atTop (nhds 0) := by
      -- The shifted strictly monotone extraction still tends to infinity, so the reciprocal bound
      -- vanishes.
      exact
        (tendsto_const_div_atTop_nhds_zero_nat C).comp
          (hψmono.tendsto_atTop.comp
            (Filter.tendsto_atTop_mono Nat.le_succ Filter.tendsto_id))
    exact squeeze_zero hnonneg hupper hbound_tendsto
  have hsubseq_obj_real :
      Filter.Tendsto
        (fun n ↦ (composite_model_objective f g (x (ψ (n + 1)))).toReal)
        Filter.atTop
        (nhds FOpt) := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      hsubseq_gap.const_add FOpt
  have hsubseq_obj :
      Filter.Tendsto
        (fun n ↦ composite_model_objective f g (x (ψ (n + 1))))
        Filter.atTop
        (nhds (FOpt : EReal)) := by
    have hvals :
        (fun n ↦ composite_model_objective f g (x (ψ (n + 1)))) =
          fun n ↦ ((((composite_model_objective f g (x (ψ (n + 1)))).toReal : ℝ)) : EReal) := by
      ext n
      have hψ_pos : 1 ≤ ψ (n + 1) := by
        exact le_trans (Nat.succ_le_succ (Nat.zero_le n)) (StrictMono.id_le hψmono (n + 1))
      rw [← Nat.sub_add_cancel hψ_pos]
      exact
        proximalGradientPositiveIterateObjectiveEqCoeToReal
          (hprob := hprob)
          (htraj := htraj)
          (ψ (n + 1) - 1)
    have hcoe :
        Filter.Tendsto
          (fun n ↦
            ((((composite_model_objective f g (x (ψ (n + 1)))).toReal : ℝ)) : EReal))
          Filter.atTop
          (nhds (FOpt : EReal)) := by
      exact (continuous_coe_real_ereal.tendsto FOpt).comp hsubseq_obj_real
    rw [hvals]
    exact hcoe
  have hxBar_le_opt :
      composite_model_objective f g xBar ≤ (FOpt : EReal) := by
    have hxBar_le_liminf :
        composite_model_objective f g xBar ≤
          Filter.liminf (fun n ↦ composite_model_objective f g (x (ψ (n + 1)))) Filter.atTop :=
      lowerSemicontinuousValueLeLiminfAlongSequence
        (h := composite_model_objective f g)
        (compositeModelObjectiveLowerSemicontinuous hprob)
        hshift_tendsto
    rw [hsubseq_obj.liminf_eq] at hxBar_le_liminf
    exact hxBar_le_liminf
  -- Compare the cluster-point value with the global lower bound `FOpt`.
  rw [hprob.optimal_set_eq]
  refine (mem_unconstrained_problem_solutions_iff_forall_le).2 ?_
  intro z
  exact le_trans hxBar_le_opt (hprob.optimal_value_isGLB.1 ⟨z, rfl⟩)

/- Theorem 10.24 is `source-facing` in the convex proximal-gradient convergence API.

Domain sampling against the existing Chapter 10 development shows that the reusable owners are:
- `IsConvexCompositeSmoothMinimizationProblem` for Assumption 10.1 together with convexity of `f`;
- `is_proximal_gradient_trajectory` for the iterate sequence `x^k`;
- `hproblem.SourceConvergenceStepsizeRule` below as the source-faithful owner of the admissible
  exact-`L_f` or genuine-B2 regime from the theorem statement;
- `proximal_gradient_fejer_monotonicity` from Theorem 10.23,
  `proximal_gradient_convex_objective_gap_le` from Theorem 10.21, and
  `tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo` from Chapter 8 for the convergence
  route.

The public theorem therefore keeps the source-facing convergence conclusion while using a
same-file source-faithful stepsize owner. Any auxiliary `α` needed to call the objective-gap API
from Theorem 10.21 remains theorem-local bridge data, and the cluster-point optimality argument is
kept theorem-local rather than exposed as a separate public API. -/

-- Proof sketch: use Theorem 10.23 to obtain Fejér monotonicity, bound the trajectory in a closed
-- ball around a fixed optimizer, extract a cluster point by compactness, recover any auxiliary
-- sublinear-rate witness needed for Theorem 10.21 from the source-facing constant/B2 stepsize
-- regime locally, identify every cluster point as optimal by combining the objective-gap estimate
-- with lower semicontinuity of `F = f + g`, and then apply Theorem 8.16 to upgrade cluster-point
-- optimality to full convergence.
/-- Theorem 10.24: under Assumption 10.1, if `f` is convex and `x^k` is generated by the proximal
gradient method with either the exact `L_f` rule or backtracking procedure B2, then
the sequence converges to an optimal solution `xStar ∈ XStar = X^*`. -/
theorem proximal_gradient_tendsto_optimal_point
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceConvergenceStepsizeRule x L htraj) :
    ∃ xStar ∈ XStar, Filter.Tendsto x Filter.atTop (nhds xStar) := by
  obtain ⟨xStar0, hxStar0⟩ := hproblem.optimal_set_nonempty
  have hFejer :
      IsFejerMonotoneWithRespectTo x XStar :=
    proximal_gradient_fejer_monotonicity
      (htraj := htraj)
      (sourceConvergenceRule_constantOrBacktrackingB2 (hproblem := hproblem) htraj hrule)
  let r : ℝ := dist (x 0) xStar0
  have hball : ∀ n : ℕ, x n ∈ Metric.closedBall xStar0 r := by
    intro n
    have hdist : dist (x n) xStar0 ≤ dist (x 0) xStar0 := by
      induction n with
      | zero =>
          exact le_rfl
      | succ n ih =>
          exact le_trans (hFejer xStar0 hxStar0 n) ih
    simpa [r, Metric.mem_closedBall] using hdist
  have hfreq :
      ∃ᶠ n in Filter.atTop, x n ∈ Metric.closedBall xStar0 r :=
    (Filter.Eventually.of_forall hball).frequently
  rcases (isCompact_closedBall xStar0 r).exists_mapClusterPt_of_frequently hfreq with
    ⟨xBar, -, hxBar⟩
  have hlimitPoints_subset :
      {y : E | MapClusterPt y Filter.atTop x} ⊆ XStar := by
    intro y hy
    by_cases hLf : 0 < (Lf : ℝ)
    · -- The generic branch packages the source owner into Theorem 10.21's source-facing owner.
      obtain ⟨α, hsub⟩ :=
        sourceConvergenceRule_existsSourceSublinearRateRuleOf_posLf
          (hproblem := hproblem)
          hLf
          htraj
          hrule
      exact
        clusterPoint_mem_optimalSet_of_sourceSublinearRate
          (hprob := hproblem)
          (htraj := htraj)
          (hrule := hsub)
          hxStar0
          hy
    · -- Route correction: when `(Lf : ℝ) = 0`, repackage the problem with the positive constant
      -- B2 seed `s`, for which the realized stepsizes become exactly constant.
      have hLf0 : (Lf : ℝ) = 0 := le_antisymm (le_of_not_gt hLf) Lf.2
      obtain ⟨s, hsconst⟩ :=
        sourceConvergenceRule_zeroLf_constantStepsize
          (hproblem := hproblem)
          hLf0
          htraj
          hrule
      have hsmoothSurrogate :
          is_l_smooth_on
            (fun z ↦ (f z).toReal)
            (interior (effective_domain f))
            (PosReal.toNNReal s) := by
        have hLsurrogate : (Lf : ℝ) ≤ ((PosReal.toNNReal s : NNReal) : ℝ) := by
          simpa [hLf0, PosReal.coe_toNNReal] using (le_of_lt (PosReal.coe_pos s))
        exact
          isLSmoothOn_mono
            hproblem.f_toReal_smooth_on_interior_effective_domain
            hLsurrogate
      have hproblemSurrogate :
          IsConvexCompositeSmoothMinimizationProblem
            f
            g
            XStar
            FOpt
            (PosReal.toNNReal s) := by
        refine
          { f_ne_bot := hproblem.f_ne_bot
            g_proper := hproblem.g_proper
            f_closed := hproblem.f_closed
            g_closed := hproblem.g_closed
            f_convex := hproblem.f_convex
            g_convex := hproblem.g_convex
            g_effective_domain_subset_interior_f_effective_domain :=
              hproblem.g_effective_domain_subset_interior_f_effective_domain
            f_toReal_smooth_on_interior_effective_domain := hsmoothSurrogate
            optimal_set_eq := hproblem.optimal_set_eq
            optimal_set_nonempty := hproblem.optimal_set_nonempty
            optimal_value_isGLB := hproblem.optimal_value_isGLB }
      have hsubSurrogate :
          hproblemSurrogate.SourceSublinearRateStepsizeRule x L htraj 1 := by
        -- The zero-`Lf` branch has already collapsed the realized stepsizes to the constant seed.
        exact Or.inl ⟨rfl, fun n ↦ by simpa [PosReal.coe_toNNReal] using hsconst n⟩
      exact
        clusterPoint_mem_optimalSet_of_sourceSublinearRate
          (Lf := PosReal.toNNReal s)
          (hprob := hproblemSurrogate)
          (htraj := htraj)
          (hrule := hsubSurrogate)
          hxStar0
          hy
  have hlimitPoint : ∃ y : E, MapClusterPt y Filter.atTop x := ⟨xBar, hxBar⟩
  obtain ⟨xStar, hxStarCluster, hxTendsto⟩ :=
    tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo hFejer hlimitPoints_subset hlimitPoint
  exact ⟨xStar, hlimitPoints_subset hxStarCluster, hxTendsto⟩

end IsConvexCompositeSmoothMinimizationProblem

end
