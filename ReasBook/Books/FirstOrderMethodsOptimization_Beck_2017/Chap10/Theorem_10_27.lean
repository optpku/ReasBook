/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_12
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_19
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]

variable {f : E → ℝ} {g : E → EReal} {Lf : NNReal}
variable {x : ℕ → E} {L : ℕ → PosReal}

/- Theorem 10.27 is `source-facing` in the Chapter 10 proximal-gradient rate API.

Domain sampling in the surrounding chapter identifies:
- `G[L; f, g]` from Definition 10.5 as the source-facing notation for the canonical owner
  `gradient_mapping` for a real-valued smooth term;
- `uses_proximal_gradient_Lf_stepsize_rule` from Remark 10.19 as the source-facing owner of the
  exact constant stepsize regime `L_k = L_f`;
- `prox_grad_step_gradient_mapping_norm_monotone` from Lemma 10.12 as the one-step monotonicity
  bridge;
- `IsConvexCompositeSmoothMinimizationProblem.gradientMapping` from Definition 10.67 as the
  bridge/view abbreviation showing that the convex-problem owner supplies the same residual as the
  canonical Chapter 10 notation;
- `proximal_gradient_best_gradient_mapping_norm_le_sublinear_rate` from Theorem 10.26 as the
  running-minimum rate bridge used in the convex constant-stepsize branch.

Triage for this file:
- `source-facing`: the two residual-rate clauses of Theorem 10.27;
- `core/canonical`: `gradient_mapping` for the residual itself, together with the convex composite
  Chapter 10 owner only where optimizer data is genuinely needed;
- `bridge/view`: the positive constant stepsize parameter `hLconst.stepsize` derived from the
  exact rule `L_k = L_f`.

Primitive data for clause (a) are the convexity and global `L_f`-smoothness of `f`, the
proper/closed/convex regularity of `g`, the trajectory, and the exact constant-rule owner from
Remark 10.19; optimizer-set data are irrelevant there and should not survive on the public API.
Clause (b) is different: it reuses Theorem 10.26 through the convex-problem owner, so the
optimizer set and value remain part of that clause through
`IsConvexCompositeSmoothMinimizationProblem`. The residual surface itself should still be stated
through the source-facing notation `G[hLconst.stepsize; f, g]`; the convex-problem owner is only
used to infer the regularity data and to access the Theorem 10.26 stepsize bridge. -/

-- Proof sketch: apply Lemma 10.12 at the iterate `x^k` using the primitive convexity and global
-- `L_f`-smoothness hypotheses on `f` together with the ambient proper/closed/convex regularity of
-- `g`. The trajectory rule together with
-- `uses_proximal_gradient_Lf_stepsize_rule Lf L` identifies the prox-gradient step
-- `T_(L_f)(x^k)` with the next iterate `x^(k+1)`. The public source-facing parameter
-- `hLconst.stepsize` upgrades `L_f` to the positive parameter required by `G[L; f, g]`.
/-- Theorem 10.27 (1): clause (a). If `g` is proper, closed, and convex, `f` is convex and
globally `L_f`-smooth, and the proximal-gradient trajectory uses the constant stepsize rule
`L_k = L_f`, then the gradient-mapping norms are nonincreasing:
`‖G_(L_f)(x^(k+1))‖ ≤ ‖G_(L_f)(x^k)‖`. -/
theorem proximal_gradient_mapping_norm_nonincreasing_of_constant_stepsize
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ Lf)
    (htraj : is_proximal_gradient_trajectory f.toEReal g x L)
    (hLconst : uses_proximal_gradient_Lf_stepsize_rule Lf L) (k : ℕ) :
    ‖G[hLconst.stepsize; f, g] (x (k + 1))‖ ≤ ‖G[hLconst.stepsize; f, g] (x k)‖ := by
  have hsmooth_stepsize : is_l_smooth_on f Set.univ (PosReal.toNNReal hLconst.stepsize) := by
    -- The constant-rule owner upgrades `L_f` to the positive stepsize
    -- parameter used by Lemma 10.12.
    simpa [uses_proximal_gradient_Lf_stepsize_rule.coe_stepsize] using hf_smooth
  have hk_stepsize : L k = hLconst.stepsize := by
    -- The exact constant-rule owner identifies the realized parameter `L_k` with `L_f`.
    ext
    simp [hLconst k]
  have hsmooth_k : is_l_smooth_on f Set.univ (PosReal.toNNReal (L k)) := by
    -- Re-express the global `L_f`-smoothness hypothesis at the realized parameter `L_k`.
    rw [hk_stepsize]
    simpa using hsmooth_stepsize
  have hmono :
      ‖G[L k; f, g] (T[L k; f, g] (x k))‖ ≤ ‖G[L k; f, g] (x k)‖ := by
    -- Apply Lemma 10.12 at the current iterate with the constant stepsize `L_f`.
    exact
      prox_grad_step_gradient_mapping_norm_monotone
        f g (L k) hf_convex hsmooth_k (x k)
  have hsucc : x (k + 1) = T[L k; f, g] (x k) := by
    simpa [proximal_gradient_trajectory_iterate, hLconst k] using
      proximal_gradient_trajectory_succ_eq_operator htraj k
  have hsucc' : x (k + 1) = T[hLconst.stepsize; f, g] (x k) := by
    simpa [hk_stepsize] using hsucc
  rw [hk_stepsize] at hmono
  -- Rewrite the realized successor iterate as the prox-gradient operator at `x^k`.
  simpa [hsucc'] using hmono

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- Helper for Theorem 10 27: an antitone sequence along `x` is bounded above by its running
minimum owner `best_achieved_function_value` at every prefix. -/
lemma antitone_le_bestAchievedFunctionValue
    {φ : E → ℝ} (hanti : Antitone (fun n ↦ φ (x n))) (k : ℕ) :
    φ (x k) ≤ best_achieved_function_value φ x k := by
  -- Unfold the prefix minimum and compare the terminal value to each earlier prefix value.
  unfold best_achieved_function_value
  apply Finset.le_min'
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
  exact hanti (by simpa using hn)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- Helper for Theorem 10 27: an antitone sequence coincides with its running minimum at every
prefix. -/
lemma antitone_eq_bestAchievedFunctionValue
    {φ : E → ℝ} (hanti : Antitone (fun n ↦ φ (x n))) (k : ℕ) :
    φ (x k) = best_achieved_function_value φ x k := by
  -- Compare the terminal value with the running minimum in both directions.
  apply le_antisymm
  · -- Antitonicity makes the terminal value a lower bound for the whole prefix.
    exact antitone_le_bestAchievedFunctionValue hanti k
  · -- The running minimum is always below the value attained at the terminal index.
    exact
      best_achieved_function_value_le_objective_value
        φ x k k (by simp)

section

variable {XStar : Set E} {FOpt : ℝ}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f.toEReal g XStar FOpt Lf]

local notation "G[" d "; " _f ", " _g "]" => hproblem.gradientMapping d

/-- Helper for Theorem 10 27: clause (a) packages the constant-stepsize residual sequence as an
antitone sequence on `ℕ`. -/
lemma constantStepsizeResidualAntitone
    (htraj : is_proximal_gradient_trajectory f.toEReal g x L)
    (hLconst : uses_proximal_gradient_Lf_stepsize_rule Lf L) :
    Antitone (fun n ↦ ‖G[hLconst.stepsize; f, g] (x n)‖) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hf_convex_raw :
      ConvexOn ℝ (effective_domain (f.toEReal)) (fun z ↦ ((f.toEReal z).toReal)) := by
    exact convexOn_toReal_of_is_convex_function hproblem.f_convex (fun z _ ↦ by simp)
  have hf_convex : ConvexOn ℝ Set.univ f := by
    -- Real-valued convexity is the `toReal` specialization of the convex problem owner.
    simpa [effective_domain] using hf_convex_raw
  have hf_smooth : is_l_smooth_on f Set.univ Lf := by
    -- For a real-valued smooth term, the interior-domain smoothness owner
    -- is exactly global smoothness.
    simpa [effective_domain] using hproblem.f_toReal_smooth_on_interior_effective_domain
  refine antitone_nat_of_succ_le ?_
  intro n
  -- Clause (a) gives the one-step decay needed by the order-theoretic antitone bridge.
  exact
    proximal_gradient_mapping_norm_nonincreasing_of_constant_stepsize
      hf_convex hf_smooth htraj hLconst n

/-- Helper for Theorem 10 27: in the constant-rule branch `α = 1`, the residual parameter from
Theorem 10.26 is exactly the source-facing constant stepsize `hLconst.stepsize`. -/
lemma constantRuleSublinearRateResidualStepsize_eq_stepsize
    (htraj : is_proximal_gradient_trajectory f.toEReal g x L)
    (hLconst : uses_proximal_gradient_Lf_stepsize_rule Lf L)
    (hruleConst : hproblem.SublinearRateStepsizeRule x L htraj 1) :
    hproblem.sublinearRateResidualStepsize htraj 1 hruleConst = hLconst.stepsize := by
  -- Both positive parameters have the same underlying real value `L_f`.
  ext
  simp [IsConvexCompositeSmoothMinimizationProblem.sublinearRateResidualStepsize]

/-- Helper for Theorem 10 27: Theorem 10.26 specialized to the constant-stepsize branch gives the
running-minimum gradient-mapping estimate on the source-facing residual surface
`G[hLconst.stepsize; f, g]`. -/
lemma constantStepsizeBestAchievedGradientMappingNorm_le_sublinearRate
    (htraj : is_proximal_gradient_trajectory f.toEReal g x L)
    (hLconst : uses_proximal_gradient_Lf_stepsize_rule Lf L)
    (xStar : E) (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 1 ≤ k) :
    best_achieved_function_value
      (fun y ↦ ‖G[hLconst.stepsize; f, g] y‖) x k ≤
        Real.sqrt ((Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (k : ℝ)) := by
  let β : PosReal := 1
  have hruleConst :
      hproblem.SourceSublinearRateStepsizeRule x L htraj 1 := by
    -- The constant branch of Theorem 10.21 is exactly the `α = 1` source owner.
    simp [IsConvexCompositeSmoothMinimizationProblem.SourceSublinearRateStepsizeRule, hLconst]
  have hsub :
      hproblem.SublinearRateStepsizeRule x L htraj 1 :=
    sourceSublinearRateRule_sublinearRateStepsizeRule htraj hruleConst
  have hLlower : ∀ ⦃n : ℕ⦄, n ≤ k → (β : ℝ) * (Lf : ℝ) ≤ (L n : ℝ) := by
    intro n hn
    -- The constant-rule owner rewrites each `L_n` to `L_f`.
    simp [β, hLconst n]
  have hrate :=
    proximal_gradient_best_gradient_mapping_norm_le_sublinear_rate
      htraj hruleConst hxStar k hk hLlower
  simpa [β, constantRuleSublinearRateResidualStepsize_eq_stepsize htraj hLconst hsub] using hrate

-- Proof sketch: combine clause (a) with the Theorem 10.26 owner-level running-minimum bridge in
-- the constant-stepsize regime. The canonical upstream rate is on the residual norm itself and is
-- only `O(1 / sqrt k)`, so the pointwise `O(1 / k)` statement here must live on the squared norm.
-- Antitonicity identifies the current residual at `x^(k+1)` with the running minimum on the
-- prefix `0, ..., k + 1`, and squaring the resulting `sqrt` bound yields the displayed estimate.
-- In this convex-composite section the ambient problem owner is used only to supply the regularity
-- instances and Theorem 10.26 bridge; the public residual surface remains the source-facing
-- notation `G[hLconst.stepsize; f, g]`.
/-- Theorem 10.27 (2): clause (b). Under the convex composite problem hypotheses used by
Theorem 10.26 and the same constant stepsize rule, every optimizer `xStar ∈ X^*` gives the
pointwise `O(1 / k)` estimate on the squared residual norm
`‖G_(L_f)(x^(k+1))‖² ≤ L_f² ‖x^0 - xStar‖² / (k + 1)`, stated on the source-facing residual
notation `G[hLconst.stepsize; f, g]`. -/
theorem proximal_gradient_mapping_norm_sq_le_one_div_k_of_constant_stepsize
    (htraj : is_proximal_gradient_trajectory f.toEReal g x L)
    (hLconst : uses_proximal_gradient_Lf_stepsize_rule Lf L)
    (xStar : E) (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖G[hLconst.stepsize; f, g] (x (k + 1))‖ ^ (2 : ℕ) ≤
      (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (k + 1 : ℝ) := by
  have hanti : Antitone (fun n ↦ ‖G[hLconst.stepsize; f, g] (x n)‖) :=
    constantStepsizeResidualAntitone htraj hLconst
  have hcurrent_eq_best :
      ‖G[hLconst.stepsize; f, g] (x (k + 1))‖ =
        best_achieved_function_value
          (fun y ↦ ‖G[hLconst.stepsize; f, g] y‖) x (k + 1) := by
    -- Antitonicity identifies the current residual with the exact prefix minimum.
    simpa using antitone_eq_bestAchievedFunctionValue hanti (k + 1)
  have hk_succ : 1 ≤ k + 1 := by
    exact Nat.succ_le_succ (Nat.zero_le k)
  have hbest_rate_succ :
      best_achieved_function_value
          (fun y ↦ ‖G[hLconst.stepsize; f, g] y‖) x (k + 1) ≤
        Real.sqrt ((Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (k + 1 : ℝ)) := by
    simpa [Nat.cast_add] using
      constantStepsizeBestAchievedGradientMappingNorm_le_sublinearRate
        htraj hLconst xStar hxStar hk_succ
  have hcurrent_rate :
      ‖G[hLconst.stepsize; f, g] (x (k + 1))‖ ≤
        Real.sqrt ((Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (k + 1 : ℝ)) :=
    hcurrent_eq_best.le.trans hbest_rate_succ
  have hbound_nonneg :
      0 ≤ (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (k + 1 : ℝ) := by
    have hk_pos : 0 < (k + 1 : ℝ) := by positivity
    exact
      div_nonneg
        (mul_nonneg (pow_two_nonneg (Lf : ℝ)) (pow_two_nonneg ‖x 0 - xStar‖))
        (le_of_lt hk_pos)
  nlinarith [hcurrent_rate,
    norm_nonneg (G[hLconst.stepsize; f, g] (x (k + 1))),
    Real.sq_sqrt hbound_nonneg]

end

end
