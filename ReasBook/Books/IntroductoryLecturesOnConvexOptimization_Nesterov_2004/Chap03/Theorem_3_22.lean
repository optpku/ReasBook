/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Theorem 3.22 lies in the chapter's extended-valued subgradient / supporting-nesterovHyperplane domain.

Relevant sampled declarations:
- `subdifferential` and the notation `∂ f(x0)` from `Definition_3_1_5`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential` from `Theorem_3_1_18`
- `AffineHyperplane.IsSupporting` and `IsSupportingHyperplane` from `Definition_3_1_4_1`

Best owner abstraction:
- the subdifferential owner hypothesis `g ∈ ∂ f(x0)` together with the earlier theorem
  `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`

Primitive data:
- an extended-valued function `f`, a base point `x0`, and a subgradient vector `g`
- the owner hypothesis `g ∈ ∂ f(x0)`
- the nonvanishing hypothesis `g ≠ 0` for the nesterovHyperplane conclusion

Derived API:
- the sign-reversed sublevel-set inequality `⟪g, x - x0⟫ ≤ 0`
- the owner-level supporting-affine-nesterovHyperplane conclusion for `{x | f x ≤ f x0}`
- its coordinate bridge `IsSupportingHyperplane`

Source/core/bridge triage:
- source-facing: Theorem 3.22's sign convention `⟪g, x - x0⟫ ≤ 0`
- core/canonical: `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- bridge/view: the equivalent sign change and the coordinate support predicate
  `IsSupportingHyperplane`

The earlier theorem `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential` already captures
the same mathematical support statement at the owner level, with the equivalent form
`0 ≤ ⟪g, x0 - x⟫`. This file keeps the source-facing sign convention, then packages the supporting
result first at the chapter owner `AffineHyperplane.IsSupporting` and only afterwards exposes the
textbook coordinate bridge `IsSupportingHyperplane`.
-/
/-- Theorem 3.22: every subgradient `g ∈ ∂f(x₀)` is a supporting vector to the level set
`{x | f x ≤ f x₀}` at `x₀`, in the sense that `⟪g, x - x₀⟫ ≤ 0` for every point of that
sublevel set. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the textbook statement on
`ℝⁿ`. -/
theorem subgradient_nonpos_on_sublevelSet_of_mem_subdifferential
    {f : E → WithTop ℝ} {x0 g : E} (hg : g ∈ ∂ f(x0)) {x : E} (hx : f x ≤ f x0) :
    inner ℝ g (x - x0) ≤ 0 := by
  simpa [inner_sub_right] using
    subgradient_nonneg_on_sublevelSet_of_mem_subdifferential hg hx

/-- A nonzero subgradient at `x₀` yields the supporting affine nesterovHyperplane with normal `g` and
offset `⟪g, x₀⟫` for the sublevel set `{x | f x ≤ f x₀}`. -/
-- Proof sketch: apply the main sublevel-set inequality to rewrite
-- `⟪g, x - x₀⟫ ≤ 0` as `⟪g, x⟫ ≤ ⟪g, x₀⟫` on `{x | f x ≤ f x₀}`, then combine this half-space
-- containment with `g ≠ 0` and the contact point
-- `x₀ ∈ {x | f x ≤ f x₀} ∩ (⟨g, hg0, ⟪g, x₀⟫⟩ : AffineHyperplane E)`.
theorem subgradient_affineHyperplane_isSupporting_sublevelSet_of_mem_subdifferential
    {f : E → WithTop ℝ} {x0 g : E} (hg : g ∈ ∂ f(x0)) (hg0 : g ≠ 0) :
    (⟨g, hg0, inner ℝ g x0⟩ : AffineHyperplane E).IsSupporting {x : E | f x ≤ f x0} := by
  constructor
  · intro x hx
    change inner ℝ g x ≤ inner ℝ g x0
    have hx' : inner ℝ g (x - x0) ≤ 0 :=
      subgradient_nonpos_on_sublevelSet_of_mem_subdifferential hg hx
    simpa [inner_sub_right] using hx'
  · refine ⟨x0, ?_⟩
    constructor
    · exact (le_rfl : f x0 ≤ f x0)
    · simp [AffineHyperplane.carrier]

/-- A nonzero subgradient at `x₀` yields a supporting nesterovHyperplane to the sublevel set
`{x | f x ≤ f x₀}`. -/
theorem subgradient_isSupportingHyperplane_sublevelSet_of_mem_subdifferential
    {f : E → WithTop ℝ} {x0 g : E} (hg : g ∈ ∂ f(x0)) (hg0 : g ≠ 0) :
    IsSupportingHyperplane {x : E | f x ≤ f x0} g (inner ℝ g x0) := by
  exact ⟨hg0,
    subgradient_affineHyperplane_isSupporting_sublevelSet_of_mem_subdifferential hg hg0⟩

end
