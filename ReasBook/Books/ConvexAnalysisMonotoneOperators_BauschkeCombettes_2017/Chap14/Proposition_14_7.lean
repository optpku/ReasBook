/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Definition_14_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

noncomputable section

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [Module ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 14.7 records the symmetry, domain formula, and convex/properness
  properties of the proximal average.
- `core/canonical`: the owner abstraction is `proximalAverage`, with primitive data
  `proximalAverageMidpointMap` and `proximalAverageKernel`.
- `bridge/view`: Proposition 12.36 supplies the infimal-postcomposition domain and epigraph API
  used to derive the specialized proximal-average clauses below. -/

-- Proof sketch: unfold `proximalAverage`; swap the roles of `f` and `g`, then reindex the
-- defining infimum by `y ↦ 2 • x - y`.
/-- Proposition 14.7 (1): the proximal average is symmetric in its two arguments. -/
theorem proximalAverage_comm (f g : H → Set.Ioi (⊥ : EReal)) :
    pav(f, g) = pav(g, f) := sorry

/- Proposition 14.7 (2): by Definition 14.6, the proximal average is exactly the infimal
postcomposition of the proximal-average kernel along the midpoint map. This is the canonical owner
declaration `proximalAverage`. -/
recall proximalAverage

-- Proof sketch: combine Definition 14.6 with `dom_infimalPostcomposition`.
-- Then compute the
-- domain of `proximalAverageKernel f g` and the image of that set under the midpoint map.
/-- Proposition 14.7 (3): the effective domain of the proximal average is
`(1 / 2) dom f + (1 / 2) dom g`. -/
theorem dom_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) :
    dom (pav(f, g)) =
      ((1 / 2 : ℝ) • effectiveDomain f) + ((1 / 2 : ℝ) • effectiveDomain g) := sorry

-- Proof sketch: use Definition 14.6 and Proposition 12.36.
-- This gives convexity of the epigraph from
-- convexity of the kernel under the linear midpoint map, and use clause (3) together with
-- `hf, hg ∈ Γ₀(H)` to get properness.
/-- Proposition 14.7 (4): if `f, g ∈ Γ₀(H)`, then the proximal average is a proper convex
extended-real-valued function. -/
theorem isProper_and_convex_epigraph_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    IsProper (pav(f, g)) ∧ Convex ℝ (epigraph (pav(f, g))) := sorry

/-- If `f, g ∈ Γ₀(H)`, then the proximal average is proper as an `EReal`-valued function. -/
theorem isProper_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    IsProper (pav(f, g)) :=
  (isProper_and_convex_epigraph_proximalAverage f g hf hg).1

end ERealFunction
