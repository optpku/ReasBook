/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section SubdifferentialOfScalarComposition

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: view the real-valued convex map `f` through `f.toEReal`, use the
-- composition result of Proposition 8.21 to place `φ ∘ f` in the convex lsc setting, then apply
-- the infimal-projection chain rule from Theorem 16.71 to the epigraphical operator
-- `x ↦ {y : ℝ | f x ≤ y}`. Proposition 16.69 identifies the resulting coderivative slice with the
-- scaled set `α • (∂ f.toEReal) xbar`.
/-- Corollary 16.72: if `f : H → ℝ` is continuous and convex, `φ ∈ Γ₀(ℝ)` is increasing on
`range f`, and the regularity condition
`(ri (range f) + ℝ_{++}) ∩ ri (dom φ) ≠ ∅` holds, then the subdifferential of the scalar
composition `φ ∘ f` at `xbar` is exactly the union of the scaled subdifferentials
`α • (∂ f.toEReal) xbar` over `α ∈ (∂ φ) (f xbar)`. -/
theorem subdifferential_comp_eq_iUnion_smul_of_continuous_convexOn_univ_of_monotoneOn_range
    (f : H → ℝ) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) (hφ : φ ∈ Γ₀(ℝ))
    (hmono : MonotoneOn φ (range f))
    (hregular :
      ((ri (range f) + Ioi (0 : ℝ)) ∩ ri (effectiveDomain φ)).Nonempty)
    (xbar : H) (hxbar : f xbar ∈ effectiveDomain φ) :
    (∂ (φ ∘ f)) xbar = ⋃ α ∈ (∂ φ) (f xbar), α • ((∂ f.toEReal) xbar) := sorry

end SubdifferentialOfScalarComposition

end ERealFunction
