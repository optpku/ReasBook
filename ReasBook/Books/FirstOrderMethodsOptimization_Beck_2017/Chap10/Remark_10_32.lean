/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/- Remark 10.32 is `source-facing`: it bounds the accepted B3 curvature parameters uniformly.

Layer triage:
- `source-facing`: `uses_backtracking_procedure_B3_rule_stepsize_bounds`;
- `core/canonical`: `uses_backtracking_procedure_B3_rule`,
  `proximal_gradient_backtracking_B2_previous_stepsize`, and `is_l_smooth_on`;
- `bridge/view`: the Assumption 10.31 specialization in the namespace
  `IsFastProximalGradientProblem` below.

Domain sampling:
- `uses_backtracking_procedure_B3_rule` from Algorithm 10.6 is already the canonical owner for the
  statement that the accepted curvature parameters `L_k` are produced by backtracking procedure
  B3 from the initial value `L_(-1) = s`;
- `proximal_gradient_backtracking_B2_previous_stepsize` from Algorithm 10.3 is the reused chapter
  owner for the recursion recording the previous accepted curvature estimate;
- `uses_backtracking_procedure_B3_rule_accepts` from Algorithm 10.6 is the owner-level acceptance
  theorem for the chosen B3 trial;
- `IsFastProximalGradientProblem.f_smooth` is the canonical owner field for the global
  `L_f`-smoothness of the smooth term `f`.

Primitive data:
- the global smoothness hypothesis `hf_smooth`;
- the B3 rule witness `hrule`.

Derived API:
- the Assumption 10.31 field `hproblem.f_smooth`.

The remark therefore belongs at the B3-owner layer, with Assumption 10.31 used only as a bridge
that supplies the smoothness hypothesis canonically. -/

-- Proof sketch: specialize `hrule k` to obtain the accepted trial index `i` with
-- `L k = LPrev * η^i`, where `LPrev` is `s` at `k = 0` and `L (k - 1)` later on. The lower bound
-- follows because `η > 1` implies every trial `LPrev * η^i` is at least `LPrev`, and induction on
-- `k` gives `LPrev ≥ s`. For the upper bound, either `i = 0`, so `L k = LPrev`, or `i > 0`, in
-- which case the previous trial is rejected by minimality. Global `L_f`-smoothness makes every
-- trial with curvature at least `L_f` automatically acceptable, so that rejected predecessor must
-- lie below `L_f`; multiplying by `η` gives `L k < η L_f`. Combining the two cases with the
-- inductive bound on `LPrev` yields `L k ≤ max {η L_f, s}`.
/-- Helper for Remark 10.32: any B3 trial curvature at least `L_f` satisfies the upper-model
acceptance predicate at the extrapolated point `y^k`. -/
lemma backtracking_B3_accepts_of_stepsize_ge_Lf
    (hf_smooth : is_l_smooth_on f Set.univ Lf)
    {y : ℕ → E} (k : ℕ) {Lbar : PosReal}
    (hLbar : (Lf : ℝ) ≤ (Lbar : ℝ)) :
    proximal_gradient_backtracking_B2_accepts
      f.toEReal g Lbar (interior_effective_domain_point_of_real f (y k)) := by
  let xNext : E := T[Lbar; f, g] (y k)
  have hdescentLf :
      f xNext ≤
        f (y k) +
          inner ℝ (∇ f (y k)) (xNext - y k) +
          ((Lf : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
    -- Global smoothness gives the quadratic upper model at the extrapolated point `y^k`.
    simpa [xNext, norm_sub_rev] using
      (is_l_smooth_on_univ_descent_lemma hf_smooth (y k) (T[Lbar; f, g] (y k)))
  have hdescentLbar :
      f xNext ≤
        f (y k) +
          inner ℝ (∇ f (y k)) (xNext - y k) +
          ((Lbar : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
    -- Enlarging the curvature coefficient from `L_f` to `Lbar` preserves the bound.
    have hnorm_nonneg : 0 ≤ ‖xNext - y k‖ ^ (2 : ℕ) := by
      positivity
    nlinarith
  -- Repackage the displayed real inequality as the canonical B3 acceptance predicate.
  exact
    (proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model f g Lbar (y k)).2
      hdescentLbar

/-- Helper for Remark 10.32: the accepted B3 curvature is at least the previous trial curvature
and at most `max {η L_f, L_prev}`. -/
lemma backtracking_B3_local_stepsize_bounds
    (hf_smooth : is_l_smooth_on f Set.univ Lf)
    {y : ℕ → E} {L : ℕ → PosReal} {s : PosReal}
    {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : uses_backtracking_procedure_B3_rule f g y L s η)
    (k : ℕ) :
    let LPrev := proximal_gradient_backtracking_B2_previous_stepsize s L k
    (LPrev : ℝ) ≤ (L k : ℝ) ∧
      (L k : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (LPrev : ℝ) := by
  rcases hrule k with ⟨i, hi, hLk⟩
  dsimp
  constructor
  · -- Every accepted B3 trial is `L_prev * η^i`, so it is at least `L_prev`.
    rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
    have hηge1 : (1 : ℝ) ≤ (η : ℝ) := le_of_lt η.2
    have hLPrev_nonneg :
        0 ≤ (proximal_gradient_backtracking_B2_previous_stepsize s L k : ℝ) := by
      exact le_of_lt (proximal_gradient_backtracking_B2_previous_stepsize s L k).2
    exact le_mul_of_one_le_right hLPrev_nonneg (one_le_pow₀ hηge1)
  · cases i with
    | zero =>
        -- If the first trial is already accepted, then the chosen curvature is exactly `L_prev`.
        rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
        simp
    | succ m =>
        let LPrev : PosReal := proximal_gradient_backtracking_B2_previous_stepsize s L k
        let Ltrial : PosReal := proximal_gradient_backtracking_trial_stepsize LPrev η m
        have hreject :
            ¬ proximal_gradient_backtracking_B2_accepts
                f.toEReal g Ltrial (interior_effective_domain_point_of_real f (y k)) := by
          exact is_backtracking_procedure_B2_index_minimal hi (Nat.lt_succ_self m)
        have htrial_lt_lf : (Ltrial : ℝ) < (Lf : ℝ) := by
          -- The rejected predecessor cannot be at least `L_f`, because such trials always accept.
          refine lt_of_not_ge fun hnot ↦ ?_
          exact hreject <| backtracking_B3_accepts_of_stepsize_ge_Lf hf_smooth k hnot
        have haccepted_eq :
            (L k : ℝ) = (Ltrial : ℝ) * (η : ℝ) := by
          simp [hLk, Ltrial, LPrev, proximal_gradient_backtracking_trial_stepsize_coe,
            pow_succ, mul_assoc]
        have haccepted_lt :
            (L k : ℝ) < (η : ℝ) * (Lf : ℝ) := by
          -- The accepted trial is one extra factor of `η` above the rejected predecessor.
          have hη_pos : 0 < (η : ℝ) := lt_trans zero_lt_one η.2
          rw [haccepted_eq]
          nlinarith
        exact le_trans (le_of_lt haccepted_lt) (le_max_left _ _)

/-- Remark 10.32: if the curvature estimates are generated by backtracking procedure B3 with
initial value `L_(-1) = s`, multiplier `η > 1`, and a globally `L_f`-smooth convex term `f`,
then for every iteration `k` the accepted stepsize satisfies `s ≤ L_k ≤ max {η L_f, s}`.
Equivalently, when `L_f > 0`, this is the textbook bound `β L_f ≤ L_k ≤ α L_f` with
`α = max {η, s / L_f}` and `β = s / L_f`. -/
theorem uses_backtracking_procedure_B3_rule_stepsize_bounds
    (hf_smooth : is_l_smooth_on f Set.univ Lf)
    (hf_convex : ConvexOn ℝ Set.univ f)
    {y : ℕ → E} {L : ℕ → PosReal}
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor)
    (hrule : uses_backtracking_procedure_B3_rule f g y L s η)
    (k : ℕ) :
    (s : ℝ) ≤ (L k : ℝ) ∧
      (L k : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) := by
  have _ := hf_convex
  induction k with
  | zero =>
      -- The initial comparison uses the seed curvature `s` as the previous trial.
      have hlocal :=
        backtracking_B3_local_stepsize_bounds hf_smooth hrule 0
      simpa [proximal_gradient_backtracking_B2_previous_stepsize_zero] using hlocal
  | succ k ih =>
      have hlocal :=
        backtracking_B3_local_stepsize_bounds hf_smooth hrule (k + 1)
      have hmono : (L k : ℝ) ≤ (L (k + 1) : ℝ) := by
        -- The local lower bound identifies the previous trial with `L k`.
        simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using hlocal.1
      have hstep :
          (L (k + 1) : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (L k : ℝ) := by
        -- The local upper bound is the one-step overshoot cap.
        simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using hlocal.2
      constructor
      · -- Monotonicity propagates the lower bound `s ≤ L_k`.
        exact le_trans ih.1 hmono
      · -- The upper bound propagates through the monotonicity of `max` in the second slot.
        have hmax_le :
            max ((η : ℝ) * (Lf : ℝ)) (L k : ℝ) ≤
              max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) := by
          exact max_le (le_max_left _ _) ih.2
        exact le_trans hstep hmax_le

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}

namespace IsFastProximalGradientProblem

/-- Under Assumption 10.31, Remark 10.32 is the specialization of the owner-level B3 stepsize
bound using the canonical smoothness field `hproblem.f_smooth` and the `g`-regularity fields
stored in `hproblem`. -/
theorem uses_backtracking_procedure_B3_rule_stepsize_bounds
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {y : ℕ → E} {L : ℕ → PosReal}
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor)
    (hrule :
      @uses_backtracking_procedure_B3_rule E _ _ _ f g
        (instIsProperExtendedRealFunctionRightOfIsFastProximalGradientProblem hproblem)
        (instFactLowerSemicontinuousRightOfIsFastProximalGradientProblem hproblem)
        (instFactIsConvexFunctionRightOfIsFastProximalGradientProblem hproblem)
        y L s η)
    (k : ℕ) :
    (s : ℝ) ≤ (L k : ℝ) ∧
      (L k : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) := by
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the properness instance needed by the owner theorem.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the lower-semicontinuity witness needed by the owner theorem.
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the convexity witness needed by the owner theorem.
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- Reuse the owner theorem with the canonical smoothness and convexity data.
  simpa using
    (_root_.uses_backtracking_procedure_B3_rule_stepsize_bounds
      hproblem.f_smooth hproblem.f_convex s η hrule k)

end IsFastProximalGradientProblem

end

end
