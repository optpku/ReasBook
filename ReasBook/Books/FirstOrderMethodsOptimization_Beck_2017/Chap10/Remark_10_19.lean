/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_67
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {f g : E → EReal} {Lf : NNReal}

/- Remark 10.19 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling in the existing project identifies:
- `IsCompositeSmoothMinimizationProblem` as the chapter owner for Assumption 10.1, but Remark
  10.19 only uses its primitive smoothness/domain-compatibility data together with the ambient
  proper, closed, convex owner data for `g`, rather than a second wrapper around those instances;
- `uses_proximal_gradient_backtracking_B2_rule` from Algorithm 10.3 as the stronger
  operator-based owner of the recursive B2 stepsize rule available once proximal points are
  single-valued;
- `uses_proximal_gradient_backtracking_B2_upper_model_rule` below as the source-facing
  trajectory-level B2 bridge for Remark 10.19 (1), which records the same geometric trial family
  together with the accepted upper-model inequality at the realized iterate `x^(k+1)`;
- `uses_proximal_gradient_Lf_stepsize_rule` below as the source-facing owner for the exact
  constant rule `L_k = L_f` used in this remark, rather than Theorem 10.15's more restrictive
  constant-stepsize owner
  `uses_proximal_gradient_constant_stepsize_rule`, whose parameter also encodes the lower bound
  `L_f / 2 < barL`;
- `is_proximal_gradient_trajectory` as the owner for the iterate sequence `x^k`;
- `proximal_gradient_backtracking_B2_accepts` as the stronger canonical sufficient-decrease
  predicate behind the single-valued B2 rule.

Primitive data for the source-facing bridge in Remark 10.19 (1) are therefore the
smoothness/domain-compatibility hypotheses, the trajectory, the exact constant rule, and the B2
geometric trial family together with the accepted upper-model inequality at the realized next
iterate. The stronger operator-based B2 owner from Algorithm 10.3 is a `bridge/view` available
under stronger ambient assumptions and should feed this source-facing layer rather than forcing
properness into every downstream statement. The stronger acceptance predicate
`proximal_gradient_backtracking_B2_accepts` remains a derived bridge once proximal points are
single-valued. The remark has two independent conclusions, so it is split into atomic theorem
skeletons. -/

/-- The constant branch in Remark 10.19 is the exact source-facing rule `L_k = L_f` for every
iteration `k`. -/
def uses_proximal_gradient_Lf_stepsize_rule (Lf : NNReal) (L : ℕ → PosReal) : Prop :=
  ∀ k : ℕ, (L k : ℝ) = (Lf : ℝ)

-- Proof sketch: evaluate the constant-rule owner at `k = 0`; since `L 0` is a `PosReal`, the
-- identity `L_0 = L_f` transfers positivity to `L_f`.
/-- The exact constant stepsize rule `L_k = L_f` forces the smoothness constant `L_f` to be
positive. -/
theorem uses_proximal_gradient_Lf_stepsize_rule_lf_pos
    {Lf : NNReal} {L : ℕ → PosReal}
    (hL_rule : uses_proximal_gradient_Lf_stepsize_rule Lf L) :
    0 < (Lf : ℝ) := by
  have hL0 := hL_rule 0
  simpa [hL0] using (L 0).prop

namespace uses_proximal_gradient_Lf_stepsize_rule

/-- Bridge/view layer: the exact constant rule `L_k = L_f` canonically upgrades the smoothness
constant `L_f` to the positive stepsize parameter used by the source-facing residual notation
`G[L; f, g]`. -/
abbrev stepsize
    {Lf : NNReal} {L : ℕ → PosReal}
    (hL_rule : uses_proximal_gradient_Lf_stepsize_rule Lf L) : PosReal :=
  ⟨Lf, uses_proximal_gradient_Lf_stepsize_rule_lf_pos hL_rule⟩

@[simp] theorem coe_stepsize
    {Lf : NNReal} {L : ℕ → PosReal}
    (hL_rule : uses_proximal_gradient_Lf_stepsize_rule Lf L) :
    ((hL_rule.stepsize : PosReal) : ℝ) = (Lf : ℝ) :=
  rfl

end uses_proximal_gradient_Lf_stepsize_rule

/-- Bridge/view layer: a trajectory follows the B2 geometric trial pattern from Remark 10.19 (1)
when each chosen stepsize `L_k` is one of the geometric trials based on `s` and `η`, and the
realized successor iterate `x^(k+1)` satisfies the accepted quadratic upper-model inequality for
that chosen `L_k`. This is the trajectory-level source-facing content needed later in the convex
analysis, before upgrading to the stronger single-valued B2 owner from Algorithm 10.3. -/
def uses_proximal_gradient_backtracking_B2_upper_model_rule
    (f g : E → EReal) (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ,
    L k =
      proximal_gradient_backtracking_trial_stepsize
        (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i ∧
    let xk : E := proximal_gradient_trajectory_iterate htraj k
    f (x (k + 1)) ≤
      (((f xk).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x (k + 1) - xk) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - xk‖ ^ (2 : ℕ) : ℝ) : EReal)

/-- The primitive stepsize regime in Remark 10.19: either every `L_k = L_f`, or the schedule is
follows the B2 geometric trial pattern from Remark 10.19 (1) along the realized
proximal-gradient trajectory. -/
def proximal_gradient_constant_or_backtracking_B2_stepsize_rule
    (f g : E → EReal) (Lf : NNReal)
    [hg_proper : IsProperExtendedRealFunction g]
    [hg_closed : Fact (LowerSemicontinuous g)]
    [hg_convex : Fact (is_convex_function g)]
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L) : Prop :=
  letI : IsProperExtendedRealFunction g := hg_proper
  letI : Fact (LowerSemicontinuous g) := hg_closed
  letI : Fact (is_convex_function g) := hg_convex
  uses_proximal_gradient_Lf_stepsize_rule Lf L ∨
    ∃ s : PosReal, ∃ η : ProximalGradientBacktrackingGrowthFactor,
      uses_proximal_gradient_backtracking_B2_upper_model_rule f g x L htraj s η

/-- The constant/B2 stepsize rule in the proximal-gradient sublinear-rate analysis: either every
`L_k = L_f`, giving `α = 1`, or the same B2 geometric trial pattern is used together with
`α = max {η, s / L_f}`. The B2 branch records `0 < L_f` explicitly so the quotient `s / L_f`
matches the textbook constant rather than Lean's default value at `L_f = 0`. -/
def proximal_gradient_sublinear_rate_stepsize_rule
    (f g : E → EReal) (Lf : NNReal)
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_closed : LowerSemicontinuous g) (hg_convex : is_convex_function g)
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (α : ℝ) : Prop :=
  letI : IsProperExtendedRealFunction g := hg_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hg_closed⟩
  letI : Fact (is_convex_function g) := ⟨hg_convex⟩
  (α = 1 ∧ uses_proximal_gradient_Lf_stepsize_rule Lf L) ∨
    ∃ _hLf : 0 < (Lf : ℝ), ∃ s : PosReal, ∃ η : ProximalGradientBacktrackingGrowthFactor,
      α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ)) ∧
        uses_proximal_gradient_backtracking_B2_upper_model_rule f g x L htraj s η

-- Proof sketch: in the constant branch, `L_0 = L_f` and `L_0` is positive because it is a
-- `PosReal`. In the B2 branch, the required positivity witness is already stored in the owner.
/-- The shared proximal-gradient sublinear-rate stepsize owner forces the smoothness constant
`L_f` to be positive. -/
theorem proximal_gradient_sublinear_rate_stepsize_rule_lf_pos
    (f g : E → EReal) (Lf : NNReal)
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_closed : LowerSemicontinuous g) (hg_convex : is_convex_function g)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    {α : ℝ}
    (hrule :
      proximal_gradient_sublinear_rate_stepsize_rule
        f g Lf hg_proper hg_closed hg_convex x L htraj α) :
    0 < (Lf : ℝ) := by
  rcases hrule with ⟨_, hLf_rule⟩ | ⟨hLf, _, _, _, _⟩
  · exact uses_proximal_gradient_Lf_stepsize_rule_lf_pos hLf_rule
  · exact hLf

/-- The shared proximal-gradient sublinear-rate stepsize owner also forces the rate constant
`α` to be positive. -/
theorem proximal_gradient_sublinear_rate_stepsize_rule_alpha_pos
    (f g : E → EReal) (Lf : NNReal)
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_closed : LowerSemicontinuous g) (hg_convex : is_convex_function g)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    {α : ℝ}
    (hrule :
      proximal_gradient_sublinear_rate_stepsize_rule
        f g Lf hg_proper hg_closed hg_convex x L htraj α) :
    0 < α := by
  rcases hrule with ⟨hα, _⟩ | ⟨hLf, s, η, hα, _⟩
  · simpa [hα]
  · rw [hα]
    exact lt_of_lt_of_le (div_pos s.prop hLf) (le_max_right _ _)

/-- Forgetting the auxiliary rate constant `α` from the proximal-gradient sublinear-rate
stepsize owner recovers the primitive constant/B2 stepsize regime from Remark 10.19. -/
theorem proximal_gradient_sublinear_rate_stepsize_rule_constant_or_backtracking_B2
    (f g : E → EReal) (Lf : NNReal)
    (hg_proper : IsProperExtendedRealFunction g)
    (hg_closed : LowerSemicontinuous g) (hg_convex : is_convex_function g)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    {α : ℝ}
    (hrule :
      proximal_gradient_sublinear_rate_stepsize_rule
        f g Lf hg_proper hg_closed hg_convex x L htraj α) :
    letI : IsProperExtendedRealFunction g := hg_proper
    letI : Fact (LowerSemicontinuous g) := ⟨hg_closed⟩
    letI : Fact (is_convex_function g) := ⟨hg_convex⟩
    proximal_gradient_constant_or_backtracking_B2_stepsize_rule f g Lf x L htraj := by
  rcases hrule with ⟨_, hLf_rule⟩ | ⟨_, s, η, _, hB2⟩
  · exact Or.inl hLf_rule
  · exact Or.inr ⟨s, η, hB2⟩

namespace IsCompositeSmoothMinimizationProblem

/-- Bridge/view layer: Assumption 10.1 canonically supplies the regularity data required by the
primitive constant/B2 stepsize regime from Remark 10.19. -/
abbrev ConstantOrBacktrackingB2StepsizeRule
    {XStar : Set E} {FOpt : ℝ}
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  proximal_gradient_constant_or_backtracking_B2_stepsize_rule f g Lf x L htraj

/-- Bridge/view layer: Assumption 10.1 canonically supplies the regularity data required by the
shared constant/B2 stepsize-rule owner. -/
abbrev SublinearRateStepsizeRule
    {XStar : Set E} {FOpt : ℝ}
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (α : ℝ) : Prop :=
  proximal_gradient_sublinear_rate_stepsize_rule
    f g Lf hproblem.g_proper hproblem.g_closed hproblem.g_convex x L htraj α

/-- Forgetting the auxiliary rate constant `α` from the shared sublinear-rate owner recovers the
primitive constant/B2 stepsize regime. -/
theorem sublinearRateStepsizeRule_constantOrBacktrackingB2
    {XStar : Set E} {FOpt : ℝ}
    {hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) :
    hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj := by
  have hraw :
      proximal_gradient_sublinear_rate_stepsize_rule
        f g Lf hproblem.g_proper hproblem.g_closed hproblem.g_convex x L htraj α := by
    simpa [SublinearRateStepsizeRule] using hrule
  simpa [SublinearRateStepsizeRule, ConstantOrBacktrackingB2StepsizeRule] using
    proximal_gradient_sublinear_rate_stepsize_rule_constant_or_backtracking_B2
      f g Lf hproblem.g_proper hproblem.g_closed hproblem.g_convex htraj hraw

/-- The canonical Chapter 10 owner `SublinearRateStepsizeRule` already includes positivity of the
smoothness constant `L_f`. -/
theorem sublinearRateStepsizeRule_lf_pos
    {XStar : Set E} {FOpt : ℝ}
    {hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) :
    0 < (Lf : ℝ) := by
  simpa [SublinearRateStepsizeRule] using
    proximal_gradient_sublinear_rate_stepsize_rule_lf_pos
      f g Lf hproblem.g_proper hproblem.g_closed hproblem.g_convex htraj hrule

/-- The canonical Chapter 10 owner `SublinearRateStepsizeRule` already includes positivity of the
rate constant `α`. -/
theorem sublinearRateStepsizeRule_alpha_pos
    {XStar : Set E} {FOpt : ℝ}
    {hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) :
    0 < α := by
  simpa [SublinearRateStepsizeRule] using
    proximal_gradient_sublinear_rate_stepsize_rule_alpha_pos
      f g Lf hproblem.g_proper hproblem.g_closed hproblem.g_convex htraj hrule

end IsCompositeSmoothMinimizationProblem

section ProblemBridge

variable {XStar : Set E} {FOpt : ℝ}

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Bridge/view layer: Assumption 10.77 refines Assumption 10.1 by adding convexity of `f`, so it
reuses the same constant/B2 stepsize owner without introducing new primitive stepsize data. -/
abbrev ConstantOrBacktrackingB2StepsizeRule
    {XStar : Set E} {FOpt : ℝ}
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L) : Prop :=
  hproblem.toIsCompositeSmoothMinimizationProblem.ConstantOrBacktrackingB2StepsizeRule x L htraj

/-- Bridge/view layer: the convex composite problem owner reuses the shared Remark 10.19
sublinear-rate stepsize owner directly. -/
abbrev SublinearRateStepsizeRule
    {XStar : Set E} {FOpt : ℝ}
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (α : ℝ) : Prop :=
  hproblem.toIsCompositeSmoothMinimizationProblem.SublinearRateStepsizeRule x L htraj α

/-- Forgetting the auxiliary rate constant `α` from the convex-problem sublinear-rate owner
recovers the constant/B2 stepsize regime. -/
theorem sublinearRateStepsizeRule_constantOrBacktrackingB2
    {XStar : Set E} {FOpt : ℝ}
    {hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) :
    hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj := by
  let hbase := hproblem.toIsCompositeSmoothMinimizationProblem
  have hbase_rule : hbase.SublinearRateStepsizeRule x L htraj α := by
    simpa [SublinearRateStepsizeRule] using hrule
  simpa [SublinearRateStepsizeRule, ConstantOrBacktrackingB2StepsizeRule] using
    (IsCompositeSmoothMinimizationProblem.sublinearRateStepsizeRule_constantOrBacktrackingB2
      hbase_rule)

/-- The convex-problem bridge inherits positivity of `L_f` from the shared Remark 10.19
sublinear-rate owner. -/
theorem sublinearRateStepsizeRule_lf_pos
    {XStar : Set E} {FOpt : ℝ}
    {hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) :
    0 < (Lf : ℝ) := by
  let hbase := hproblem.toIsCompositeSmoothMinimizationProblem
  have hbase_rule : hbase.SublinearRateStepsizeRule x L htraj α := by
    simpa [SublinearRateStepsizeRule] using hrule
  simpa [SublinearRateStepsizeRule] using
    (IsCompositeSmoothMinimizationProblem.sublinearRateStepsizeRule_lf_pos hbase_rule)

/-- The convex-problem bridge inherits positivity of `α` from the shared Remark 10.19
sublinear-rate owner. -/
theorem sublinearRateStepsizeRule_alpha_pos
    {XStar : Set E} {FOpt : ℝ}
    {hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) :
    0 < α := by
  let hbase := hproblem.toIsCompositeSmoothMinimizationProblem
  have hbase_rule : hbase.SublinearRateStepsizeRule x L htraj α := by
    simpa [SublinearRateStepsizeRule] using hrule
  simpa [SublinearRateStepsizeRule] using
    (IsCompositeSmoothMinimizationProblem.sublinearRateStepsizeRule_alpha_pos hbase_rule)

/-- Bridge/view layer: the convex-problem sublinear-rate owner canonically packages the positive
gradient-mapping parameter `α L_f` used in the residual-rate bounds. -/
def sublinearRateResidualStepsize
    {XStar : Set E} {FOpt : ℝ}
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (α : ℝ)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) : PosReal :=
  ⟨α * (Lf : ℝ),
    mul_pos
      (hproblem.sublinearRateStepsizeRule_alpha_pos hrule)
      (hproblem.sublinearRateStepsizeRule_lf_pos hrule)⟩

@[simp] theorem coe_sublinearRateResidualStepsize
    {XStar : Set E} {FOpt : ℝ}
    {hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) :
    ((hproblem.sublinearRateResidualStepsize htraj α hrule : PosReal) : ℝ) =
      α * (Lf : ℝ) :=
  rfl

end IsConvexCompositeSmoothMinimizationProblem

end ProblemBridge

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {f g : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]
variable (hf_effective_domain_convex : Convex ℝ (effective_domain f))
variable (hg_effective_domain_subset_interior_f_effective_domain :
  effective_domain g ⊆ interior (effective_domain f))
variable (hf_toReal_smooth_on_interior_effective_domain :
  is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)

/-- Helper for Remark 10.19: a real-valued descent estimate lifts to the displayed source-facing
`EReal` upper-model inequality once the next iterate stays in `interior (effective_domain f)`. -/
lemma proximal_gradient_upper_model_of_toReal_le
    {xk xNext : E} {Lk : PosReal}
    (hxNext : xNext ∈ interior (effective_domain f))
    (hdescent :
      (f xNext).toReal ≤
        (f xk).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ)) :
    f xNext ≤
      (((f xk).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  by_cases hxNext_bot : f xNext = ⊥
  · -- If the next iterate has value `⊥`, the target inequality is automatic.
    simp [hxNext_bot]
  · -- Otherwise the left-hand side is a finite real value, so the real descent estimate lifts.
    have hxNext_eff : xNext ∈ effective_domain f := interior_subset hxNext
    have hxNext_val : f xNext = (((f xNext).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxNext_eff).ne hxNext_bot).symm
    rw [hxNext_val]
    exact_mod_cast hdescent

-- Proof sketch: in the constant-rule case, `L k = L_f`, so apply the descent lemma from the
-- smoothness field in Assumption 10.1 to the two consecutive iterates of the proximal-gradient
-- trajectory. In the B2 branch, the trajectory-level owner already stores exactly the displayed
-- upper-model inequality at iteration `k`.
/-- Remark 10.19 (1): under the same hypotheses, the accepted stepsize inequality can be written
in the displayed source-facing form
`f(x^(k+1)) ≤ f(x^k) + ⟪∇ f(x^k), x^(k+1) - x^k⟫ + (L_k / 2) ‖x^(k+1) - x^k‖²`. -/
theorem proximal_gradient_upper_model_of_constant_or_backtracking_B2_rule
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : proximal_gradient_constant_or_backtracking_B2_stepsize_rule f g Lf x L htraj)
    (k : ℕ) :
    f (x (k + 1)) ≤
      (((f (x k)).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  rcases hrule with hLf_rule | ⟨s, η, hB2⟩
  · -- In the constant-rule branch, Lemma 5.7 applies directly to two consecutive iterates.
    have hxk_int :
        x k ∈ interior (effective_domain f) :=
      proximal_gradient_trajectory_mem_interior_effective_domain htraj k
    have hxk1_int :
        x (k + 1) ∈ interior (effective_domain f) :=
      proximal_gradient_trajectory_mem_interior_effective_domain htraj (k + 1)
    have hdescent :
        (f (x (k + 1))).toReal ≤
          (f (x k)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
            ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
      -- The smooth upper model on `interior (effective_domain f)` gives the textbook inequality.
      simpa [hLf_rule k, norm_sub_rev] using
        (is_l_smooth_on_descent_lemma
          hf_effective_domain_convex.interior
          hf_toReal_smooth_on_interior_effective_domain
          hxk_int
          hxk1_int)
    -- Lift the real descent estimate to the source-facing `EReal` inequality.
    exact proximal_gradient_upper_model_of_toReal_le hxk1_int hdescent
  · -- In the B2 branch, the source-facing owner already stores the desired inequality.
    rcases hB2 k with ⟨i, _, hmodel⟩
    simpa [proximal_gradient_trajectory_iterate] using hmodel

namespace IsConvexCompositeSmoothMinimizationProblem

/- Bridge/view layer: Assumption 10.77 specializes Remark 10.19 (1) to the canonical Chapter 10
constant-or-B2 stepsize owner without importing stronger compactness hypotheses. -/
theorem upper_model_of_constantOrBacktrackingB2Rule
    {XStar : Set E} {FOpt : ℝ}
    [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj)
    (k : ℕ) :
    f (x (k + 1)) ≤
      (((f (x k)).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [ConstantOrBacktrackingB2StepsizeRule] using
    proximal_gradient_upper_model_of_constant_or_backtracking_B2_rule
      hproblem.f_effective_domain_convex
      hproblem.g_effective_domain_subset_interior_f_effective_domain
      hproblem.f_toReal_smooth_on_interior_effective_domain
      htraj hrule k

end IsConvexCompositeSmoothMinimizationProblem

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]
variable {f g : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]
variable (hf_effective_domain_convex : Convex ℝ (effective_domain f))
variable (hg_effective_domain_subset_interior_f_effective_domain :
  effective_domain g ⊆ interior (effective_domain f))
variable (hf_toReal_smooth_on_interior_effective_domain :
  is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)

/-- Helper for Remark 10.19: in the proper-space setting, the successor of a proximal-gradient
trajectory is the canonical prox-gradient operator applied to the current iterate. -/
lemma proximal_gradient_trajectory_succ_eq_operator
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L) (k : ℕ) :
    x (k + 1) = T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) := by
  have hstep :
      x (k + 1) ∈
        proximal_gradient_step f g (proximal_gradient_trajectory_iterate htraj k : E) (L k) := by
    simpa [proximal_gradient_trajectory_iterate] using
      (is_proximal_gradient_trajectory_step htraj k).2
  rw
    [prox_grad_operator_eq_singleton
      f
      g
      (L k)
      (proximal_gradient_trajectory_iterate htraj k)] at hstep
  simpa using hstep

-- Proof sketch: `uses_proximal_gradient_backtracking_B2_rule_accepts` gives the canonical
-- acceptance owner at the iterate `x^k`. The prox-gradient trajectory step and
-- `prox_grad_operator_eq_singleton` identify the realized successor `x^(k+1)` with the
-- single-valued prox-gradient operator used in that acceptance predicate, so the stored operator
-- inequality rewrites to the trajectory-level upper-model inequality.
/-- The stronger single-valued B2 owner from Algorithm 10.3 canonically supplies the
trajectory-level upper-model owner used in Remark 10.19 (1). -/
theorem uses_proximal_gradient_backtracking_B2_rule_upperModel
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : uses_proximal_gradient_backtracking_B2_rule f g x L htraj s η) :
    uses_proximal_gradient_backtracking_B2_upper_model_rule f g x L htraj s η := by
  intro k
  rcases hrule k with ⟨i, hi, hLk⟩
  refine ⟨i, hLk, ?_⟩
  let xk := proximal_gradient_trajectory_iterate htraj k
  have hfxk_val : f (xk : E) = (((f (xk : E)).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset xk.2)).ne (hf_ne_bot _)).symm
  have haccepts :
      proximal_gradient_backtracking_B2_accepts f g (L k) xk := by
    -- The stronger B2 owner already certifies acceptance of the chosen trial curvature.
    simpa [xk] using uses_proximal_gradient_backtracking_B2_rule_accepts hrule k
  have hmodel :
      f (T[L k, f, g] xk) ≤
        (((f (xk : E)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (xk : E)) (T[L k, f, g] xk - (xk : E)) +
            ((L k : ℝ) / 2) * ‖T[L k, f, g] xk - (xk : E)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    have haccepts' := (proximal_gradient_backtracking_B2_accepts_iff f g (L k) xk).1 haccepts
    rw [hfxk_val] at haccepts'
    simpa [EReal.coe_add, add_assoc] using haccepts'
  -- Rewrite the accepted operator point as the realized successor iterate.
  simpa [xk, proximal_gradient_trajectory_succ_eq_operator htraj k] using hmodel

-- Proof sketch: in the constant-rule case, `L k = L_f`, so apply the descent lemma from the
-- smoothness field in Assumption 10.1 to the two consecutive iterates of the proximal-gradient
-- trajectory. In the B2 branch, rewrite the stored trajectory-level upper-model inequality using
-- the single-valued prox-gradient operator at the iterate `x^k`.
/-- Under the standing proper-space hypotheses, the admissible constant-or-B2 stepsize regime from
Remark 10.19 implies the canonical B2 acceptance predicate at every iteration. -/
theorem proximal_gradient_constant_or_backtracking_B2_stepsize_accepts
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : proximal_gradient_constant_or_backtracking_B2_stepsize_rule f g Lf x L htraj)
    (k : ℕ) :
    proximal_gradient_backtracking_B2_accepts
      f g (L k) (proximal_gradient_trajectory_iterate htraj k) := by
  let xk := proximal_gradient_trajectory_iterate htraj k
  have hfxk_val : f (xk : E) = (((f (xk : E)).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset xk.2)).ne (hf_ne_bot _)).symm
  have hmodel :=
    proximal_gradient_upper_model_of_constant_or_backtracking_B2_rule
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      htraj hrule k
  refine (proximal_gradient_backtracking_B2_accepts_iff f g (L k) xk).2 ?_
  -- Rewrite the base value through `toReal` and identify the realized successor iterate.
  rw [hfxk_val]
  simpa [xk, proximal_gradient_trajectory_succ_eq_operator htraj k, EReal.coe_add, add_assoc] using
    hmodel

/-- Helper for Remark 10.19: under the omitted `f_ne_bot` clause from Assumption 10.1, any trial
curvature `Lbar ≥ L_f` satisfies the canonical B2 acceptance predicate at the current iterate. -/
lemma backtracking_B2_accepts_of_stepsize_ge_Lf
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    {y : interior (effective_domain f)} {Lbar : PosReal}
    (hLbar : (Lf : ℝ) ≤ (Lbar : ℝ)) :
    proximal_gradient_backtracking_B2_accepts f g Lbar y := by
  let xNext : E := T[Lbar, f, g] y
  have hxNext_int : xNext ∈ interior (effective_domain f) := by
    -- Lemma 10.4 keeps the prox-gradient image inside `interior (effective_domain f)`.
    simpa [xNext] using
      prox_grad_operator_mem_interior_effective_domain_f
        f
        g
        Lf
        hf_ne_bot
        hf_effective_domain_convex
        hg_effective_domain_subset_interior_f_effective_domain
        hf_toReal_smooth_on_interior_effective_domain
        Lbar y
  have hdescentLf :
      (f xNext).toReal ≤
        (f (y : E)).toReal +
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xNext - (y : E)) +
          ((Lf : ℝ) / 2) * ‖xNext - (y : E)‖ ^ (2 : ℕ) := by
    -- Lemma 5.7 supplies the source upper model at the base point `y` and prox point `xNext`.
    simpa [xNext, norm_sub_rev] using
      (is_l_smooth_on_descent_lemma
        hf_effective_domain_convex.interior
        hf_toReal_smooth_on_interior_effective_domain
        y.2
        hxNext_int)
  have hdescentLbar :
      (f xNext).toReal ≤
        (f (y : E)).toReal +
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xNext - (y : E)) +
          ((Lbar : ℝ) / 2) * ‖xNext - (y : E)‖ ^ (2 : ℕ) := by
    -- Enlarging the curvature coefficient from `L_f` to `Lbar` preserves the inequality.
    have hnorm_nonneg : 0 ≤ ‖xNext - (y : E)‖ ^ (2 : ℕ) := by
      positivity
    nlinarith
  have hy_val : f (y : E) = (((f (y : E)).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset y.2)).ne (hf_ne_bot _)).symm
  have hmodel :
      f xNext ≤
        (((f (y : E)).toReal +
            inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xNext - (y : E)) +
            ((Lbar : ℝ) / 2) * ‖xNext - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    exact proximal_gradient_upper_model_of_toReal_le hxNext_int hdescentLbar
  refine (proximal_gradient_backtracking_B2_accepts_iff f g Lbar y).2 ?_
  -- Convert the source-facing real right-hand side into the canonical acceptance predicate.
  rw [hy_val]
  simpa [xNext, EReal.coe_add, add_assoc] using hmodel

/-- Helper for Remark 10.19: under the omitted `f_ne_bot` clause from Assumption 10.1, each
accepted B2 curvature lies between the previous trial curvature and `max {η L_f, L_prev}`. -/
lemma backtracking_B2_local_stepsize_bounds
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    {x : ℕ → E} {L : ℕ → PosReal} {s : PosReal}
    {η : ProximalGradientBacktrackingGrowthFactor}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hB2 : uses_proximal_gradient_backtracking_B2_rule f g x L htraj s η)
    (k : ℕ) :
    let LPrev := proximal_gradient_backtracking_B2_previous_stepsize s L k
    (LPrev : ℝ) ≤ (L k : ℝ) ∧
      (L k : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (LPrev : ℝ) := by
  rcases hB2 k with ⟨i, hi, hLk⟩
  dsimp
  constructor
  · -- Every accepted B2 trial has the form `L_prev * η^i`, so it is at least `L_prev`.
    rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
    have hηge1 : (1 : ℝ) ≤ (η : ℝ) := le_of_lt η.2
    have hLPrev_nonneg :
        0 ≤ (proximal_gradient_backtracking_B2_previous_stepsize s L k : ℝ) := by
      exact le_of_lt (proximal_gradient_backtracking_B2_previous_stepsize s L k).2
    exact le_mul_of_one_le_right hLPrev_nonneg (one_le_pow₀ hηge1)
  · cases i with
    | zero =>
        -- If the first geometric trial is accepted, then the chosen curvature is exactly `L_prev`.
        rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
        simp
    | succ m =>
        let LPrev : PosReal := proximal_gradient_backtracking_B2_previous_stepsize s L k
        let Ltrial : PosReal := proximal_gradient_backtracking_trial_stepsize LPrev η m
        have hreject :
            ¬ proximal_gradient_backtracking_B2_accepts
                f g Ltrial (proximal_gradient_trajectory_iterate htraj k) := by
          exact is_backtracking_procedure_B2_index_minimal hi (Nat.lt_succ_self m)
        have htrial_lt_lf : (Ltrial : ℝ) < (Lf : ℝ) := by
          refine lt_of_not_ge fun hnot ↦ ?_
          exact hreject <|
            backtracking_B2_accepts_of_stepsize_ge_Lf
              hf_effective_domain_convex
              hg_effective_domain_subset_interior_f_effective_domain
              hf_toReal_smooth_on_interior_effective_domain
              hf_ne_bot
              hnot
        have haccepted_eq :
            (L k : ℝ) = (Ltrial : ℝ) * (η : ℝ) := by
          simp [hLk, Ltrial, LPrev, proximal_gradient_backtracking_trial_stepsize_coe,
            pow_succ, mul_assoc]
        have haccepted_lt :
            (L k : ℝ) < (η : ℝ) * (Lf : ℝ) := by
          have hη_pos : 0 < (η : ℝ) := lt_trans zero_lt_one η.2
          rw [haccepted_eq]
          nlinarith
        exact le_trans (le_of_lt haccepted_lt) (le_max_left _ _)

/-- Helper for Remark 10.19: with the omitted `f_ne_bot` clause from Assumption 10.1 restored,
the B2 backtracking curvatures satisfy the textbook global bounds `s ≤ L_k ≤ max {η L_f, s}`. -/
theorem proximal_gradient_backtracking_B2_stepsize_bounds_of_ne_bot
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor)
    (hrule : uses_proximal_gradient_backtracking_B2_rule f g x L htraj s η)
    (k : ℕ) :
    (s : ℝ) ≤ (L k : ℝ) ∧
      (L k : ℝ) ≤ max (((η : ℝ) * (Lf : ℝ))) (s : ℝ) := by
  induction k with
  | zero =>
      -- The initial comparison uses the seed curvature `s` as the previous trial.
      have hlocal :=
        backtracking_B2_local_stepsize_bounds
          hf_effective_domain_convex
          hg_effective_domain_subset_interior_f_effective_domain
          hf_toReal_smooth_on_interior_effective_domain
          hf_ne_bot
          htraj hrule 0
      simpa [proximal_gradient_backtracking_B2_previous_stepsize_zero] using hlocal
  | succ k ih =>
      have hlocal :=
        backtracking_B2_local_stepsize_bounds
          hf_effective_domain_convex
          hg_effective_domain_subset_interior_f_effective_domain
          hf_toReal_smooth_on_interior_effective_domain
          hf_ne_bot
          htraj hrule (k + 1)
      have hmono : (L k : ℝ) ≤ (L (k + 1) : ℝ) := by
        simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using hlocal.1
      have hstep :
          (L (k + 1) : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (L k : ℝ) := by
        simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using hlocal.2
      constructor
      · -- Monotonicity from the local comparison propagates the lower bound `s ≤ L_k`.
        exact le_trans ih.1 hmono
      · -- The upper bound propagates through the monotone `max`.
        have hmax_le :
            max ((η : ℝ) * (Lf : ℝ)) (L k : ℝ) ≤
              max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) := by
          exact max_le (le_max_left _ _) ih.2
        exact le_trans hstep hmax_le

-- Proof sketch: the lower bound is immediate because each B2 trial is generated from the previous
-- positive stepsize by multiplication with a nonnegative power of `η`, so every accepted value is
-- at least `s`. For the upper bound, either `L k = s`, or the previous geometric trial was
-- rejected; combining that rejection with the descent lemma at smoothness constant `L_f` yields
-- `L k / η < L_f`, hence `L k ≤ max {η L_f, s}`.
/-- Remark 10.19 (2): under the same smoothness and domain-compatibility hypotheses, the stepsizes
`L_k` produced by backtracking
procedure B2 satisfy the bounds `s ≤ L_k ≤ max {η L_f, s}` for every `k ≥ 0`. -/
theorem proximal_gradient_backtracking_B2_stepsize_bounds
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor)
    (hrule : uses_proximal_gradient_backtracking_B2_rule f g x L htraj s η)
    (k : ℕ) :
    (s : ℝ) ≤ (L k : ℝ) ∧
      (L k : ℝ) ≤ max (((η : ℝ) * (Lf : ℝ))) (s : ℝ) := by
  exact
    proximal_gradient_backtracking_B2_stepsize_bounds_of_ne_bot
      (Lf := Lf)
      (f := f)
      (g := g)
      hf_ne_bot
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      htraj
      s
      η
      hrule
      k

end
