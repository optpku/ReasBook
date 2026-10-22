/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: if `(dom f∗).Nonempty`, then Proposition 13.12 supplies a continuous affine
-- minorant of `f`, which makes `lowerSemicontinuousConvexEnvelope f` proper because it lies
-- between that affine minorant and `f`. Proposition 13.16(iv) gives
-- `conjugate (lowerSemicontinuousConvexEnvelope f) = conjugate f`, so taking conjugates again and
-- applying Theorem 13.37 to the proper function `lowerSemicontinuousConvexEnvelope f` yields
-- `f∗∗ = lowerSemicontinuousConvexEnvelope f`.
section CompleteSpace

variable [CompleteSpace H]

/-- If the domain of `f*` is nonempty, equivalently if `f` admits a continuous affine minorant,
then the Fenchel biconjugate of `f` is its lower semicontinuous convex envelope `\breve f`. -/
theorem biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty
    (f : H → EReal)
    (hdom : (dom f∗).Nonempty) :
    f∗∗ = lowerSemicontinuousConvexEnvelope f := sorry

end CompleteSpace

-- Proof sketch: by Proposition 13.12's pointwise bridge together with Proposition 13.12(ii),
-- `dom f∗ = ∅` means
-- `conjugate f = ⊤`. Therefore
-- `f∗∗ = conjugate (conjugate f)` is the conjugate of the
-- constant `⊤` function, which is identically `⊥` by Proposition 13.10(ii).
/-- If the domain of `f*` is empty, then the Fenchel biconjugate of `f` is identically `-∞`. -/
theorem biconjugate_eq_bot_of_dom_conjugate_eq_empty
    (f : H → EReal)
    (hdom : dom f∗ = ∅) :
    f∗∗ = ⊥ := sorry

section CompleteSpace

variable [CompleteSpace H]

attribute [local instance] Classical.propDecidable

-- Proof sketch: combine the previous two branch theorems by splitting on whether `(dom f∗)` is
-- nonempty; the affine-minorant reformulation comes directly from Proposition 13.12.
/-- Proposition 13.45: if the domain of the Fenchel conjugate `f*` is nonempty, equivalently if
`f` admits a continuous affine minorant, then `f** = \breve f`; otherwise `f**` is identically
`-∞`. -/
theorem biconjugate_eq_lowerSemicontinuousConvexEnvelope_or_bot
    (f : H → EReal) :
    f∗∗ =
      if (dom f∗).Nonempty then
        lowerSemicontinuousConvexEnvelope f
      else
        ⊥ := sorry

end CompleteSpace

end Conjugation

end ERealFunction
