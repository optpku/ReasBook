/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34

-- Declarations for this item will be appended below by the statement pipeline.

open Set

noncomputable section

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}

/-- Proposition 12.36 (1): the effective domain of the infimal postcomposition is the image under
`L` of the effective domain of `f`. -/
theorem dom_infimalPostcomposition (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) :
    dom (L ▷ f) = L '' effectiveDomain f := by
  ext y
  rw [mem_dom_iff, Set.mem_image]
  change sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' {y})) < ⊤ ↔
      ∃ x, ((f x : EReal) < ⊤) ∧ L x = y
  constructor
  · intro hy
    obtain ⟨z, hzmem, hzlt⟩ := (sInf_lt_iff).1 hy
    rcases hzmem with ⟨x, hxLy, rfl⟩
    exact ⟨x, hzlt, by simpa using hxLy⟩
  · rintro ⟨x, hxdom, hxLy⟩
    refine lt_of_le_of_lt (sInf_le ?_) hxdom
    exact ⟨x, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hxLy, rfl⟩

section RealVectorSpace

variable [AddCommGroup H] [Module ℝ H]
variable [AddCommGroup K] [Module ℝ K]

-- Proof sketch: treat the source hypothesis “`f` is convex” through the project owner
-- `Convex ℝ (epigraph f.asEReal)`. Then consider the jointly convex function on `K × H` obtained
-- by adding `f.asEReal` to the indicator of the graph of `L`. Proposition 8.35 gives convexity
-- of its marginal, which is exactly `L ▷ f`.
/-- Proposition 12.36 (2): if `f` has convex real-height epigraph and `L` is affine, then the
real-height epigraph of `L ▷ f` is convex. -/
theorem convex_epigraph_infimalPostcomposition (f : H → Set.Ioi (⊥ : EReal))
    (L : H →ᵃ[ℝ] K) (hf : Convex ℝ (epigraph f.asEReal)) :
    Convex ℝ (epigraph (L ▷ f)) := sorry

end RealVectorSpace

end ERealFunction
