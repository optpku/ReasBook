/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

variable {H : Type u} [AddGroup H]
variable (f g : H → Set.Ioi (⊥ : EReal))

-- Proof sketch: unpack membership in the pointwise sum of the two epigraphs, rewrite each
-- epigraph condition with `mem_epigraph_iff`, and compare the defining infimum of `f □ g` with the
-- single decomposition coming from the chosen summands.
/-- Proposition 12.8 (1): the pointwise sum of the real-height epigraphs of `f` and `g` is
contained in the real-height epigraph of their infimal convolution. -/
theorem add_epigraph_subset_epigraph_infimalConvolution :
    epigraph f.asEReal + epigraph g.asEReal ⊆
      epigraph (f □ g) := sorry

-- Proof sketch: one inclusion is Proposition 12.8 (1). For the reverse inclusion, take a point
-- of `epigraph (f □ g)`, use exactness to choose a minimizing decomposition `x = y + (x - y)`,
-- and place the two resulting summands in the epigraphs of `f` and `g`.
/-- Proposition 12.8 (2): if the infimal convolution is exact, then its real-height epigraph is
exactly the pointwise sum of the real-height epigraphs of `f` and `g`. -/
theorem epigraph_infimalConvolution_eq_add_epigraph_of_exact
    (hExact : infimalConvolution.Exact f g) :
    epigraph (f □ g) =
      epigraph f.asEReal + epigraph g.asEReal := sorry

end ERealFunction
