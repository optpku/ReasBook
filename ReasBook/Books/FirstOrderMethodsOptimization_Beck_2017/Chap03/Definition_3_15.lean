/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

noncomputable section

/- Definition 3.15 is `source-facing`: it defines the constrained extended-real objective attached
to `f` and `C`. The owner abstractions in this domain are the chapter declarations
`extendedIndicator` for the set term, `realEpigraph` for the geometric owner view, and
`is_convex_function` for the convexity predicate. Primitive data are only the original objective
`f`, the feasible set `C`, and the source-facing rule "equal to `f` on `C`, equal to `⊤` off
`C`". The identification with the canonical owner expression `f + δ_C` is derived `bridge/view`
API only: it needs the extra hypothesis that `f` never takes the value `⊥` on `Cᶜ`, because
`x + ⊤ = ⊤` in `EReal` fails exactly at `x = ⊥`. -/
recall extendedIndicator
recall realEpigraph
recall is_convex_function

section

variable {E : Type u}

/-- Definition 3.15: the constrained problem `min {f x : x ∈ C}` is represented by the
extended-real objective that agrees with `f` on `C` and takes the value `⊤` outside `C`. -/
def constrained_problem_objective (f : E → EReal) (C : Set E) : E → EReal :=
  open scoped Classical in
  C.piecewise f fun _ ↦ (⊤ : EReal)

-- Bridge/view layer: when `f` never takes the value `⊥` outside `C`, the source-facing
-- constrained objective agrees with the canonical indicator expression `f + δ_C`.
/-- If `f` never takes the value `⊥` outside `C`, then the constrained objective is `f + δ_C`. -/
theorem constrained_problem_objective_eq_add_extendedIndicator
    (f : E → EReal) (C : Set E) (h_ne_bot : ∀ x ∉ C, f x ≠ ⊥) :
    constrained_problem_objective f C = f + extendedIndicator C := by
  ext x
  by_cases hx : x ∈ C
  · simp [constrained_problem_objective, extendedIndicator, hx]
  · simp [constrained_problem_objective, extendedIndicator, hx,
      EReal.add_top_of_ne_bot (h_ne_bot x hx)]

-- Proof sketch: unfold `constrained_problem_objective`; when `x ∈ C`, the `piecewise` definition
-- selects the branch `f x`.
/-- On the feasible set, the constrained problem objective agrees with the original objective. -/
@[simp] theorem constrained_problem_objective_of_mem
    (f : E → EReal) {C : Set E} {x : E} (hx : x ∈ C) :
    constrained_problem_objective f C x = f x := by
  simp [constrained_problem_objective, hx]

-- Proof sketch: unfold `constrained_problem_objective`; when `x ∉ C`, the `piecewise` definition
-- selects the infeasible-value branch `⊤`.
/-- Outside the feasible set, the constrained problem objective takes the value `⊤`. -/
@[simp] theorem constrained_problem_objective_of_not_mem
    (f : E → EReal) {C : Set E} {x : E} (hx : x ∉ C) :
    constrained_problem_objective f C x = ⊤ := by
  simp [constrained_problem_objective, hx]

/-- A point lies in the effective domain of the constrained objective exactly when it is feasible
and the original objective is finite there. -/
@[simp] theorem mem_effective_domain_constrained_problem_objective
    (f : E → EReal) (C : Set E) (x : E) :
    x ∈ effective_domain (constrained_problem_objective f C) ↔
      x ∈ C ∧ x ∈ effective_domain f := by
  by_cases hx : x ∈ C
  · simp [effective_domain, constrained_problem_objective, hx]
  · simp [effective_domain, constrained_problem_objective, hx]

/-- The effective domain of the constrained objective is the feasible set intersected with the
effective domain of the original objective. -/
theorem effective_domain_constrained_problem_objective
    (f : E → EReal) (C : Set E) :
    effective_domain (constrained_problem_objective f C) = C ∩ effective_domain f := by
  ext x
  simpa using mem_effective_domain_constrained_problem_objective f C x

-- Proof sketch: in the real epigraph, the branch `⊤` outside `C` contributes no points because
-- `⊤ ≤ r` is false for every real `r`. Thus the epigraph is exactly the intersection of the
-- epigraph of `f` with the cylinder `C ×ˢ univ`.
/-- The real epigraph of the constrained objective is the epigraph of `f` restricted to the
feasible set. -/
theorem realEpigraph_constrained_problem_objective
    (f : E → EReal) (C : Set E) :
    realEpigraph (constrained_problem_objective f C) =
      (C ×ˢ (Set.univ : Set ℝ)) ∩ realEpigraph f := by
  ext p
  by_cases hp : p.1 ∈ C <;> simp [realEpigraph, constrained_problem_objective, hp]

end

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

-- Proof sketch: use `realEpigraph_constrained_problem_objective` to rewrite the real epigraph as
-- `(C ×ˢ univ) ∩ realEpigraph f`. Convexity of `C` gives convexity of the cylinder `C ×ˢ univ`,
-- while `hf` is convexity of `realEpigraph f`; their intersection is therefore convex.
/-- If `f` is convex and `C` is convex, then the extended-real objective associated to the
constrained problem is convex. -/
theorem is_convex_function_constrained_problem_objective
    {f : E → EReal} {C : Set E} (hf : is_convex_function f) (hC : Convex ℝ C) :
    is_convex_function (constrained_problem_objective f C) := by
  have hf_epi : Convex ℝ (realEpigraph f) := by
    simpa [is_convex_function, realEpigraph] using hf
  have hconstrained_epi : Convex ℝ (realEpigraph (constrained_problem_objective f C)) := by
    simpa [realEpigraph_constrained_problem_objective] using
      (hC.prod convex_univ).inter hf_epi
  simpa [is_convex_function, realEpigraph] using hconstrained_epi

end
