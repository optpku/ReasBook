/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_4
import FirstOrderMethodsOptimization_Beck_2017.Chap10.ProxGradientLinearizationDefect
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

/- Remark 10.17 is `source-facing`: its genuinely new owner-level content is the first-order
residual `ℓ_f(x, y)`.

Layer triage:
- `source-facing`: the residual `ℓ_f(x, y)` itself, now owned by the small reusable support file
  `ProxGradientLinearizationDefect`;
- `core/canonical`: `fundamental_prox_grad_inequality` from Theorem 10.16 for the prox-gradient
  objective-gap estimate under a B2 upper model;
- `bridge/view`: the specialization at the smoothness constant `L_f` supplied by
  `IsCompositeSmoothMinimizationProblem` via its canonical smoothness/domain hypotheses and the
  B2 acceptance predicate.

This file therefore recalls the canonical residual owner and the downstream gap owner, and keeps
only the genuinely new smoothness-constant bridge as a public theorem. -/

/- Remark 10.17: the first-order residual
`ℓ_f(x, y) = f(x) - f(y) - ⟪∇ f(y), x - y⟫` is the Chapter 10 owner
`prox_gradient_linearization_defect`, with notation `ℓ[f, x, y]`. -/
recall prox_gradient_linearization_defect
recall prox_gradient_linearization_defect_eq

/- Remark 10.17 (1): the prox-gradient objective-gap estimate under the B2 upper-model hypothesis
is exactly the Chapter 10 owner `fundamental_prox_grad_inequality`. -/
recall fundamental_prox_grad_inequality

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : PosReal}

local notation "F" => composite_model_objective f g

namespace IsCompositeSmoothMinimizationProblem

section

/-- Bridge/view layer: Assumption 10.1 canonically supplies the regularity data needed to state
the B2 upper-model acceptance predicate at the smoothness constant `L_f`. -/
abbrev acceptsAtSmoothnessConstant
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt (PosReal.toNNReal Lf))
    (y : interior (effective_domain f)) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  proximal_gradient_backtracking_B2_accepts f g Lf y

/-- Bridge/view layer: the smoothness-constant specialization of Theorem 10.16 is packaged as a
source-faithful Chapter 10 bridge proposition with only the mathematical inputs exposed. -/
abbrev objectiveGapLowerBoundAtSmoothnessConstant
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt (PosReal.toNNReal Lf))
    (x : E) (y : interior (effective_domain f)) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let xPlus : E := T[Lf, f, g] y
  F x - F xPlus ≥
    ((((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
        ((Lf : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) +
      ℓ[f, x, y]

/-- Bridge/view layer: Assumption 10.1 supplies the B2 upper-model acceptance predicate at the
smoothness constant `L_f`. -/
theorem backtrackingB2AcceptsAtSmoothnessConstant
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt (PosReal.toNNReal Lf))
    (y : interior (effective_domain f)) :
    hproblem.acceptsAtSmoothnessConstant y := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let xPlus : E := T[Lf, f, g] y
  have hxPlus_int : xPlus ∈ interior (effective_domain f) := by
    simpa [xPlus] using
      prox_grad_operator_mem_interior_effective_domain_f
        f
        g
        (PosReal.toNNReal Lf)
        hproblem.f_ne_bot
        hproblem.f_effective_domain_convex
        hproblem.g_effective_domain_subset_interior_f_effective_domain
        hproblem.f_toReal_smooth_on_interior_effective_domain
        Lf y
  have hdescent :
      (f xPlus).toReal ≤
        (f (y : E)).toReal +
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
          ((Lf : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) := by
    simpa [xPlus, norm_sub_rev] using
      (is_l_smooth_on_descent_lemma
        hproblem.f_effective_domain_convex.interior
        hproblem.f_toReal_smooth_on_interior_effective_domain
        y.2
        hxPlus_int)
  have hy_val : f (y : E) = (((f (y : E)).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset y.2)).ne
        (hproblem.f_ne_bot _)).symm
  have hmodel :
      f xPlus ≤
        (((f (y : E)).toReal +
            inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
            ((Lf : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    by_cases hxPlus_bot : f xPlus = ⊥
    · simp [hxPlus_bot]
    · have hxPlus_val : f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
        exact
          (EReal.coe_toReal (mem_effective_domain.mp (interior_subset hxPlus_int)).ne
            hxPlus_bot).symm
      rw [hxPlus_val]
      exact_mod_cast hdescent
  refine (proximal_gradient_backtracking_B2_accepts_iff f g Lf y).2 ?_
  rw [hy_val]
  simpa [xPlus, EReal.coe_add, add_assoc] using hmodel

/-- The smoothness-constant specialization of Theorem 10.16 is the canonical bridge provided by
`IsCompositeSmoothMinimizationProblem.fundamentalProxGradInequalityAtSmoothnessConstant`. -/
theorem fundamentalProxGradInequalityAtSmoothnessConstant
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt (PosReal.toNNReal Lf))
    (x : E) (y : interior (effective_domain f)) :
    hproblem.objectiveGapLowerBoundAtSmoothnessConstant x y := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have haccepts : proximal_gradient_backtracking_B2_accepts f g Lf y := by
    simpa [acceptsAtSmoothnessConstant] using
      hproblem.backtrackingB2AcceptsAtSmoothnessConstant y
  simpa [objectiveGapLowerBoundAtSmoothnessConstant] using
    (fundamental_prox_grad_inequality x y Lf haccepts)

end

end IsCompositeSmoothMinimizationProblem

end

end
