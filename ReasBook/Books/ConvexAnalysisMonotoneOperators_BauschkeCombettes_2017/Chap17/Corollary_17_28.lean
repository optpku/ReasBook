/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_27

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
  [Module ℝ H] [ContinuousSMul ℝ H]

-- Proof sketch: if every directional derivative of `f` along `x₁ - x₀` on `[x₀,x₁[` were
-- nonpositive, Proposition 17.27 would force `f x₁ ≤ f x₀`, contradicting the strict increase.
-- Hence some point of the half-open segment has directional derivative strictly positive in the
-- direction `x₁ - x₀`.
/-- Corollary 17.28: if `f` strictly increases from `x₀` to `x₁`, if `f` is lower semicontinuous
on the segment `[x₀,x₁]`, and if every point of `[x₀,x₁[` admits a directional derivative along
`x₁ - x₀`, then some point of that half-open segment has strictly positive directional derivative
in the direction `x₁ - x₀`. -/
theorem exists_positive_directional_derivative_on_half_open_segment
    (f : H → Set.Ioi (⊥ : EReal)) (x0 x1 : H)
    (hvalue : f.asEReal x0 < f.asEReal x1)
    (hlsc : LowerSemicontinuousOn f.asEReal (segment ℝ x0 x1))
    (hderiv : ∀ x ∈ closedOpenSegment x0 x1,
      ∃ ξ : EReal, HasDirectionalDerivativeAt f x (x1 - x0) ξ) :
    ∃ x ∈ closedOpenSegment x0 x1, ∃ ξ : EReal,
      HasDirectionalDerivativeAt f x (x1 - x0) ξ ∧ 0 < ξ := by
  by_contra hpositive
  have hnonpos :
      ∀ x ∈ closedOpenSegment x0 x1,
        ∃ ξ : EReal, HasDirectionalDerivativeAt f x (x1 - x0) ξ ∧ ξ ≤ 0 := by
    intro x hx
    obtain ⟨ξ, hξ⟩ := hderiv x hx
    refine ⟨ξ, hξ, ?_⟩
    by_contra hξ_pos
    exact hpositive ⟨x, hx, ξ, hξ, lt_of_not_ge hξ_pos⟩
  exact hvalue.not_ge <|
    apply_right_le_left_of_nonpos_directionalDerivativeOn_segment f hlsc hnonpos

end ERealFunction
