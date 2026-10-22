/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_18
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u

section
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- This item is `source-facing` in the chapter constrained convex-optimization API. The owner
abstractions are already upstream: `effective_domain` from Definition 2.5,
`IsProperExtendedRealFunction` and `is_convex_function` from Definition 2.6,
`subdifferential` from Definition 3.2, `normal_cone` from Definition 3.3, and mathlib's
`IsMinOn` for minimizers on a set. The theorem therefore stays as the textbook optimality
criterion itself, with no parallel local wrapper API. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall subdifferential
recall normal_cone
recall IsMinOn

/-- Helper for Theorem 3.31: minimizing `f` on `C` is equivalent to globally minimizing
`f + δ_ C`. -/
lemma isMinOn_add_extendedIndicator_univ_iff
    {f : E → EReal} (hf : IsProperExtendedRealFunction f)
    {C : Set E} {xStar : E} (hxStar : xStar ∈ C) :
    IsMinOn f C xStar ↔ IsMinOn (f + δ_ C) Set.univ xStar := by
  -- Rewrite both minimizer statements to pointwise comparison inequalities.
  rw [isMinOn_iff, isMinOn_univ_iff]
  constructor
  · intro hmin y
    by_cases hy : y ∈ C
    · -- On feasible points, the indicator vanishes and the objectives agree.
      simpa [extendedIndicator_of_mem hxStar, extendedIndicator_of_mem hy] using hmin y hy
    · -- Outside `C`, the constrained objective is `⊤`, so the inequality is automatic.
      have hxValue : (f + δ_ C) xStar = f xStar := by
        simp [Pi.add_apply, extendedIndicator_of_mem hxStar]
      have hyValue : (f + δ_ C) y = ⊤ := by
        simp [Pi.add_apply, extendedIndicator_of_not_mem hy, EReal.add_top_of_ne_bot (hf.ne_bot y)]
      rw [hxValue, hyValue]
      exact le_top
  · intro hmin y hy
    -- Restrict the global indicator objective back to feasible comparison points.
    simpa [extendedIndicator_of_mem hxStar, extendedIndicator_of_mem hy] using hmin y

/-- Helper for Theorem 3.31: the relative-interior qualification provides a finite point of
`effective_domain (f + δ_ C)`. -/
lemma effectiveDomain_add_extendedIndicator_nonempty_of_qualification
    {f : E → EReal} {C : Set E}
    (hri : (intrinsicInterior ℝ (effective_domain f) ∩ intrinsicInterior ℝ C).Nonempty) :
    (effective_domain (f + δ_ C)).Nonempty := by
  rcases hri with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hxDom : x ∈ effective_domain f :=
    intrinsicInterior_subset hx.1
  have hxC : x ∈ C :=
    intrinsicInterior_subset hx.2
  -- At a qualified feasible point the indicator is `0`, so the sum stays finite.
  simpa [effective_domain, extendedIndicator_of_mem hxC] using hxDom

/-- Helper for Theorem 3.31: the qualified sum rule rewrites `∂ (f + δ_ C)(xStar)` as the sum of
the subdifferential of `f` and the normal cone to `C`. -/
lemma subdifferential_add_extendedIndicator_eq_subdifferential_add_normalCone
    {f : E → EReal} (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f)
    {C : Set E} (hC : Convex ℝ C)
    (hri : (intrinsicInterior ℝ (effective_domain f) ∩ intrinsicInterior ℝ C).Nonempty)
    (xStar : E) :
    subdifferential (f + δ_ C) xStar = ∂ f(xStar) + N[C](xStar) := by
  let F : Fin 2 → E → EReal := ![f, δ_ C]
  have hneBot : ∀ i : Fin 2, ∀ y : E, F i y ≠ ⊥ := by
    intro i y
    fin_cases i
    · simpa [F] using hf.ne_bot y
    · by_cases hy : y ∈ C <;> simp [F, hy]
  have hconvF : ∀ i : Fin 2, is_convex_function (F i) := by
    intro i
    fin_cases i
    · simpa [F] using hconv
    · simpa [F] using extendedIndicator_isConvexFunction_of_convex C hC
  have hqual : (⋂ i : Fin 2, intrinsicInterior ℝ (effective_domain (F i))).Nonempty := by
    rcases hri with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro i
    fin_cases i
    · simpa [F] using hx.1
    · simpa [F, effective_domain_extendedIndicator] using hx.2
  -- Apply the finite-sum rule to the two-term family `f, δ_ C`.
  simpa [F, Fin.sum_univ_two, subdifferential_extended_indicator_eq_normal_cone] using
    subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
      F xStar hneBot hconvF hqual

/-- Helper for Theorem 3.31: stationarity in `∂ f(xStar) + N[C](xStar)` is equivalent to the
existence of a subgradient whose negation lies in the normal cone. -/
lemma zero_mem_subdifferential_add_normalCone_iff
    {f : E → EReal} {C : Set E} {xStar : E} :
    (0 : Module.Dual ℝ E) ∈ ∂ f(xStar) + N[C](xStar) ↔
      ∃ g : Module.Dual ℝ E, g ∈ ∂ f(xStar) ∧ -g ∈ N[C](xStar) := by
  constructor
  · intro hzero
    rw [Set.mem_add] at hzero
    rcases hzero with ⟨g, hg, n, hn, hsum⟩
    -- Normalize the additive witness `g + n = 0` to the cone condition `n = -g`.
    refine ⟨g, hg, ?_⟩
    have hnEq : n = -g := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hsum)
    simpa [hnEq] using hn
  · rintro ⟨g, hg, hcone⟩
    -- Use `g` and `-g` as the canonical witnesses in the pointwise set sum.
    rw [Set.mem_add]
    refine ⟨g, hg, -g, hcone, ?_⟩
    simp

-- Proof sketch: rewrite constrained optimality on `C` as unconstrained optimality of
-- `f + δ_C`, then apply Fermat's criterion to that extended-real objective. Use the
-- relative-interior qualification to invoke the convex sum rule
-- `∂ (f + δ_C) (xStar) = ∂ f xStar + ∂ δ_C xStar`, and identify
-- `∂ δ_C xStar` with `N[C](xStar)`; finally rewrite
-- `0 ∈ ∂ f xStar + N[C](xStar)` as the existence of
-- `g ∈ ∂ f xStar` with `-g ∈ N[C](xStar)`.
/-- Theorem 3.31: necessary and sufficient optimality conditions for convex constrained
optimization. If `f` is a proper convex extended-real-valued function, `C` is convex, and
`ri(dom f) ∩ ri(C) ≠ ∅`, then a feasible point `xStar ∈ C` minimizes `f` on `C` if and only if
there exists a subgradient `g ∈ ∂ f(xStar)` whose negation belongs to the normal cone
`N[C](xStar)`. -/
theorem isMinOn_iff_exists_subgradient_neg_mem_normal_cone
    {f : E → EReal} (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f)
    {C : Set E} (hC : Convex ℝ C)
    (hri : (intrinsicInterior ℝ (effective_domain f) ∩ intrinsicInterior ℝ C).Nonempty)
    {xStar : E} (hxStar : xStar ∈ C) :
    IsMinOn f C xStar ↔
      ∃ g : Module.Dual ℝ E, g ∈ ∂ f(xStar) ∧ -g ∈ N[C](xStar) := by
  -- Route correction: follow the source proof through the indicator objective, then rewrite the
  -- resulting Fermat stationarity condition with the qualified sum rule and the normal-cone API.
  rw [isMinOn_add_extendedIndicator_univ_iff (f := f) hf (C := C) hxStar]
  rw [isMinOn_univ_iff_zero_mem_subdifferential
    (f := f + δ_ C)
    (effectiveDomain_add_extendedIndicator_nonempty_of_qualification (f := f) (C := C) hri)]
  rw [subdifferential_add_extendedIndicator_eq_subdifferential_add_normalCone
    (f := f) hf hconv (C := C) hC hri xStar]
  exact zero_mem_subdifferential_add_normalCone_iff (f := f) (C := C) (xStar := xStar)

-- Downstream Chapter 3 files use this properness-exported companion name for the same
-- optimality criterion.
/-- Properness-exported companion: under the same convexity and relative-interior qualification
hypotheses, a feasible point `xStar ∈ C` minimizes `f` on `C` if and only if there exists a
subgradient `g ∈ ∂ f(xStar)` whose negation belongs to the normal cone `N[C](xStar)`. -/
theorem isMinOn_iff_exists_subgradient_neg_mem_normal_cone_of_proper
    {f : E → EReal} (hf : IsProperExtendedRealFunction f) (hconv : is_convex_function f)
    {C : Set E} (hC : Convex ℝ C)
    (hri : (intrinsicInterior ℝ (effective_domain f) ∩ intrinsicInterior ℝ C).Nonempty)
    {xStar : E} (hxStar : xStar ∈ C) :
    IsMinOn f C xStar ↔
      ∃ g : Module.Dual ℝ E, g ∈ ∂ f(xStar) ∧ -g ∈ N[C](xStar) := by
  -- Reuse the source-facing owner theorem verbatim; this name just exports properness explicitly.
  simpa using
    isMinOn_iff_exists_subgradient_neg_mem_normal_cone
      (f := f) hf hconv (C := C) hC hri (xStar := xStar) hxStar

end
