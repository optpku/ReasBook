/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_69
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_67
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/-- The primitive stepsize regime in Theorem 10.72: either every curvature estimate satisfies
`L_k = L_f`, or each `L_k` is produced by backtracking procedure B5 on the iterate sequence `x`. -/
def non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (x : ℕ → E) (L : ℕ → PosReal) : Prop :=
  letI : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ) := hω
  uses_proximal_gradient_Lf_stepsize_rule Lf L ∨
    ∃ s : PosReal, ∃ η : ProximalGradientBacktrackingGrowthFactor,
      UsesNonEuclideanProximalGradientBacktrackingB5Rule f g ω x L s η

/-- The constant/B5 sublinear-rate stepsize rule in Theorem 10.72 enriches the primitive
constant-or-B5 regime by recording the rate constant `α`: either every curvature estimate
satisfies `L_k = L_f`, giving `α = 1`, or each `L_k` is an accepted geometric B5 trial based on
the previous curvature estimate on the iterate sequence `x`, with
`α = max {η, s / L_f}`. The B5 branch records `0 < L_f` explicitly so the quotient `s / L_f`
matches the textbook constant rather than Lean's division-by-zero convention. -/
def non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (x : ℕ → E) (L : ℕ → PosReal)
    (α : ℝ) : Prop :=
  letI : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ) := hω
  (α = 1 ∧ uses_proximal_gradient_Lf_stepsize_rule Lf L) ∨
    ∃ _hLf : 0 < (Lf : ℝ), ∃ s : PosReal, ∃ η : ProximalGradientBacktrackingGrowthFactor,
      α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ)) ∧
        UsesNonEuclideanProximalGradientBacktrackingB5Rule f g ω x L s η

/-- Forgetting the auxiliary rate constant `α` from the sublinear-rate owner recovers the
primitive constant-or-B5 stepsize regime from Theorem 10.72. -/
theorem non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule_constant_or_backtracking_B5
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal} {α : ℝ}
    (hrule :
      non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule
        (f := f) (g := g) (ω := ω) (Lf := Lf) hω x L α) :
    non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule
      (f := f) (g := g) (ω := ω) (Lf := Lf) hω x L := by
  rcases hrule with ⟨_, hLf_rule⟩ | ⟨_, s, η, _, hB5⟩
  · exact Or.inl hLf_rule
  · exact Or.inr ⟨s, η, hB5⟩

/-- The shared non-Euclidean proximal-gradient sublinear-rate stepsize owner forces the smoothness
constant `L_f` to be positive. -/
theorem non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule_lf_pos
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal} {α : ℝ}
    (hrule :
      non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule
        (f := f) (g := g) (ω := ω) (Lf := Lf) hω x L α) :
    0 < (Lf : ℝ) := by
  rcases hrule with ⟨_, hLf_rule⟩ | ⟨hLf, _, _, _, _⟩
  · exact uses_proximal_gradient_Lf_stepsize_rule_lf_pos hLf_rule
  · exact hLf

end

section ProblemBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Bridge/view layer: Assumption 10.77 canonically supplies the `g`-regularity data required by
the primitive constant-or-B5 stepsize regime from Theorem 10.72, while the Bregman potential
hypothesis remains the explicit source-facing input `hω`. -/
abbrev ConstantOrBacktrackingB5StepsizeRule
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (x : ℕ → E) (L : ℕ → PosReal) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule
    (f := f) (g := g) (ω := ω) (Lf := Lf) hω x L

/-- Bridge/view layer: Assumption 10.77 canonically supplies the `g`-regularity data required by
the shared constant-or-B5 sublinear-rate stepsize owner from Theorem 10.72, with the Bregman
potential hypothesis kept explicit as `hω`. -/
abbrev NonEuclideanSublinearRateStepsizeRule
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (x : ℕ → E) (L : ℕ → PosReal)
    (α : ℝ) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule
    (f := f) (g := g) (ω := ω) (Lf := Lf) hω x L α

/-- Forgetting the auxiliary rate constant `α` from the shared non-Euclidean sublinear-rate
stepsize owner recovers the primitive constant-or-B5 stepsize regime from Theorem 10.72. -/
theorem sublinearRateStepsizeRule_constantOrBacktrackingB5
    {hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)}
    {x : ℕ → E} {L : ℕ → PosReal} {α : ℝ}
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α) :
    hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [NonEuclideanSublinearRateStepsizeRule, ConstantOrBacktrackingB5StepsizeRule] using
    non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule_constant_or_backtracking_B5
      (f := f) (g := g) (ω := ω) (Lf := Lf) hω hrule

/-- The canonical Chapter 10 non-Euclidean bridge owner `NonEuclideanSublinearRateStepsizeRule`
already includes positivity of the smoothness constant `L_f`. -/
theorem sublinearRateStepsizeRule_lf_pos_of_nonEuclidean
    {hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf}
    {hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)}
    {x : ℕ → E} {L : ℕ → PosReal} {α : ℝ}
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α) :
    0 < (Lf : ℝ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [NonEuclideanSublinearRateStepsizeRule] using
    non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule_lf_pos
      (f := f) (g := g) (ω := ω) (Lf := Lf) hω hrule

end IsConvexCompositeSmoothMinimizationProblem

end ProblemBridge
