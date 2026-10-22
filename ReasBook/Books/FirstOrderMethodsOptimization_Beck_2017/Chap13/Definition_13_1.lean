/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 13.1 is `source-facing`: it fixes the standing assumptions for the constrained
convex minimization problem used by the Frank-Wolfe / conditional-gradient method. The relevant
owner abstractions already present in the project are `IsProperExtendedRealFunction`,
`is_convex_function`, `effective_domain`, `IsCompact`, `Convex`, and `DifferentiableOn`, so the
clean public interface is a small `Prop`-valued class on the objective `f` and feasible set `C`
rather than a surrogate packaged optimization object. The primitive data are the no-`⊥` clause
for `f`, the feasible-set hypotheses on `C`, and the domain/differentiability clauses; properness
of `f` is derived from `constraint_nonempty` together with `C ⊆ effective_domain f`. -/

/-- Definition 13.1: the conditional-gradient problem `min {f x | x ∈ C}` has a nonempty convex
compact feasible set `C` in a normed real vector space `E`, an extended-real-valued convex objective
`f : E → (-∞, ∞]`, the feasibility condition `C ⊆ dom f`, an open effective domain `dom f`, and
differentiability of `f.toReal` on `dom f`. -/
class IsConditionalGradientProblem (f : E → EReal) (C : Set E) : Prop where
  f_ne_bot (x : E) : f x ≠ ⊥
  constraint_nonempty : C.Nonempty
  constraint_convex : Convex ℝ C
  constraint_compact : IsCompact C
  f_convex : is_convex_function f
  feasible_subset_effective_domain : C ⊆ effective_domain f
  f_effective_domain_open : IsOpen (effective_domain f)
  f_toReal_differentiableOn_effective_domain :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (effective_domain f)

/-- A conditional-gradient problem canonically makes the objective `f` a proper
extended-real-valued function. -/
instance {f : E → EReal} {C : Set E} (h : IsConditionalGradientProblem f C) :
    IsProperExtendedRealFunction f where
  ne_bot := h.f_ne_bot
  effective_domain_nonempty := by
    rcases h.constraint_nonempty with ⟨x, hx⟩
    exact ⟨x, h.feasible_subset_effective_domain hx⟩

-- Proof sketch: an open set equals its interior, so `effective_domain f = interior
-- (effective_domain f)`. Combine this with the feasibility inclusion `C ⊆ effective_domain f`.
/-- A conditional-gradient problem places every feasible point in the interior of the effective
domain of the objective. -/
theorem IsConditionalGradientProblem.feasible_subset_interior_effective_domain
    {f : E → EReal} {C : Set E} (h : IsConditionalGradientProblem f C) :
    C ⊆ interior (effective_domain f) := by
  simpa [h.f_effective_domain_open.interior_eq] using h.feasible_subset_effective_domain

end
