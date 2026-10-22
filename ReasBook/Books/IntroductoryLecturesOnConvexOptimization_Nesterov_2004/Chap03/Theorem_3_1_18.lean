/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.1.18 lies in the chapter's extended-valued convex-analysis / subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt` in `Definition_3_1_5`, the primitive owner predicate
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`, the set-valued view
- `IsSubgradientAt.mem_dom` in `Definition_3_1_5`, the owner finiteness lemma
- no matching mathlib owner for this exact `WithTop ℝ`-valued subgradient interface

Best owner abstraction:
- `IsSubgradientAt`, with `∂ f(x0)` as derived API

Primitive data:
- an extended-real-valued function `f`
- a base point `x0`, a vector `g`, and the owner hypothesis `IsSubgradientAt f x0 g`
- a comparison point `x` satisfying the sublevel inequality `f x ≤ f x0`

Derived API:
- the lower-sublevel pairing inequality `0 ≤ inner ℝ g (x0 - x)`
- its source-facing wrapper under the owner notation `g ∈ ∂ f(x0)`

Source/core/bridge triage:
- source-facing: Theorem 3.1.18's statement for a subgradient `g ∈ ∂ f(x0)`
- core/canonical: `IsSubgradientAt`
- bridge/view: `mem_subdifferential_iff`

The refined file therefore proves the inequality first at the owner level `IsSubgradientAt` and
keeps the textbook set-valued theorem as the thin bridge from `g ∈ ∂ f(x0)` to that owner
statement. -/
variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A subgradient supports every point whose value lies below the base value. -/
theorem IsSubgradientAt.nonneg_inner_sub_of_le
    {f : V → WithTop ℝ} {x0 g : V} (hg : IsSubgradientAt f x0 g)
    {x : V} (hx : f x ≤ f x0) :
    0 ≤ inner ℝ g (x0 - x) := by
  have hx0_dom : x0 ∈ dom f := hg.mem_dom
  have hx_dom : x ∈ dom f := lt_of_le_of_lt hx hx0_dom
  have hsupport : f x0 + (inner ℝ g (x - x0) : WithTop ℝ) ≤ f x0 :=
    le_trans (hg.2 hx_dom) hx
  have hreal : inner ℝ g (x - x0) ≤ 0 := by
    rw [← coe_withTopRealPart hx0_dom] at hsupport
    have hreal' : withTopRealPart f x0 + inner ℝ g (x - x0) ≤ withTopRealPart f x0 := by
      exact_mod_cast hsupport
    linarith
  simpa [inner_sub_right] using hreal

/-- Theorem 3.1.18: every subgradient `g ∈ ∂f(x₀)` supports the lower level set
`𝓛_f(f(x₀)) = {x ∈ dom f | f x ≤ f x₀}` in the sense that
`⟪g, x₀ - x⟫ ≥ 0` for every point of that set. -/
-- Proof sketch: unpack `g ∈ ∂ f(x₀)` into the defining affine lower-support
-- inequality. If `f x ≤ f x₀`, then applying the subgradient inequality at `x` gives
-- `f x₀ + ⟪g, x - x₀⟫ ≤ f x ≤ f x₀`; rearranging yields `⟪g, x₀ - x⟫ ≥ 0`.
theorem subgradient_nonneg_on_sublevelSet_of_mem_subdifferential
    {f : V → WithTop ℝ} {x0 g : V}
    (hg : g ∈ ∂ f(x0)) {x : V} (hx : f x ≤ f x0) :
    0 ≤ inner ℝ g (x0 - x) :=
  (show IsSubgradientAt f x0 g from hg).nonneg_inner_sub_of_le hx

end
