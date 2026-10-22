/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}

/-- The optimal value of the generalized conditional-gradient model is the infimum of the attained
composite objective values. -/
noncomputable def generalized_conditional_gradient_optimal_value (f g : E → EReal) : EReal :=
  sInf (Set.range (composite_model_objective f g))

-- Proof sketch: unfold `generalized_conditional_gradient_optimal_value`; the statement is the
-- defining `sInf` formula for the composite objective values.
/-- Expanding the generalized conditional-gradient optimal value gives the `sInf` of the range of
the composite objective. -/
theorem generalized_conditional_gradient_optimal_value_eq_sInf
    (f g : E → EReal) :
    generalized_conditional_gradient_optimal_value f g =
      sInf (Set.range (composite_model_objective f g)) := rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Assumption 13.1 is `source-facing`: it fixes the standing hypotheses for the generalized
conditional-gradient model `min_x (f x + g x)`. Domain sampling identifies the relevant
`core/canonical` owners already present in the project:
- `composite_model_objective` and `unconstrained_problem_solutions` for the optimization object;
- `IsProperExtendedRealFunction`, `LowerSemicontinuous`, and `is_convex_function` for the
  extended-real regularity data;
- `effective_domain` and `is_l_smooth_on` for the domain-compatibility and smoothness clauses.

Primitive data are exactly the regularity and domain-compatibility clauses `(A)` and `(B)`.
Text 13.1 proves optimizer existence from those clauses, so optimal-set nonemptiness is derived
API and should not be stored as an extra primitive field in a second wrapper owner. -/

/-- Assumption 13.1: clauses `(A)` and `(B)` for the generalized conditional-gradient method mean
that `g : E → (-∞, ∞]` is proper, closed, and convex with compact effective domain, while
`f : E → (-∞, ∞]` never takes the value `-∞`, has open convex effective domain containing
`effective_domain g`, and `(fun x ↦ (f x).toReal)` is `L_f`-smooth on `effective_domain f` with
`L_f > 0`. Text 13.1 later derives the nonemptiness of the optimal set `X^*` from these
primitive assumptions. -/
class IsGeneralizedConditionalGradientProblem
    (f g : E → EReal) (Lf : NNReal) : Prop extends IsProperExtendedRealFunction g where
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  g_effective_domain_compact : IsCompact (effective_domain g)
  f_ne_bot : ∀ x, f x ≠ ⊥
  f_effective_domain_open : IsOpen (effective_domain f)
  f_effective_domain_convex : Convex ℝ (effective_domain f)
  g_effective_domain_subset_f_effective_domain :
    effective_domain g ⊆ effective_domain f
  f_toReal_smooth_on_effective_domain :
    is_l_smooth_on (fun x ↦ (f x).toReal) (effective_domain f) Lf
  Lf_pos : 0 < (Lf : ℝ)

/-- The domain compatibility hypothesis and properness of `g` force `effective_domain f` to be
nonempty. -/
theorem IsGeneralizedConditionalGradientProblem.f_effective_domain_nonempty
    {f g : E → EReal} {Lf : NNReal}
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    (effective_domain f).Nonempty := by
  rcases h.toIsProperExtendedRealFunction.effective_domain_nonempty with ⟨x, hx⟩
  exact ⟨x, h.g_effective_domain_subset_f_effective_domain hx⟩

/-- A generalized conditional-gradient problem canonically makes the smooth term `f` a proper
extended-real-valued function. -/
theorem IsGeneralizedConditionalGradientProblem.f_proper
    {f g : E → EReal} {Lf : NNReal}
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    IsProperExtendedRealFunction f where
  ne_bot := h.f_ne_bot
  effective_domain_nonempty := h.f_effective_domain_nonempty

-- Proof sketch: `g` is proper, so some `x₀` lies in `effective_domain g`; the domain inclusion
-- puts `x₀` in `effective_domain f`, giving a nonempty effective domain for `f`. The no-`⊥`
-- field supplies the remaining properness clause.
/-- A generalized conditional-gradient problem canonically makes the smooth term `f` a proper
extended-real-valued function. -/
instance {f g : E → EReal} {Lf : NNReal}
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    IsProperExtendedRealFunction f :=
  h.f_proper

-- Proof sketch: `effective_domain f` is open, so each `x ∈ effective_domain f` lies in its
-- interior; then apply the Chapter 10 interior-domain differentiability bridge to the smoothness
-- field of `h`.
/-- Under Assumption 13.1, every point of `effective_domain f` is a Chapter 3 differentiability
point of `f`. -/
theorem IsGeneralizedConditionalGradientProblem.is_differentiable_at
    {f g : E → EReal} {Lf : NNReal}
    (h : IsGeneralizedConditionalGradientProblem f g Lf) (x : effective_domain f) :
    is_differentiable_at f x := by
  have hx_int : (x : E) ∈ interior (effective_domain f) := by
    simp [h.f_effective_domain_open.interior_eq, x.property]
  have hx_finite : (x : E) ∈ interior (finite_domain f) := by
    simpa [finite_domain_eq_effective_domain h.f_ne_bot] using hx_int
  exact ⟨hx_finite, h.f_toReal_smooth_on_effective_domain.1 x x.property⟩

end
