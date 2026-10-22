/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Definition_14_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Proposition 14.9 records the two-sided bounds for the proximal average.
- `core/canonical`: the owner abstraction is `proximalAverage`/`pav` from Definition 14.6; the
  lower bound additionally uses Fenchel conjugation `∗` from Definition 13.1.
- `bridge/view`: `Function.asEReal` is only the codomain bridge from `H → Set.Ioi (⊥ : EReal)` to
  the canonical `EReal`-valued function API, so the half-sum expressions below are derived
  pointwise function operations rather than primitive data. -/

section ProximalAverage

variable {H : Type u} [NormedAddCommGroup H] [Module ℝ H]

-- Proof sketch: evaluate the defining infimum of `pav(f, g)` at the diagonal choice `y = x`.
/-- Proposition 14.9: the proximal average is bounded above by the half-sum of `f` and `g`. -/
theorem proximalAverage_upper_bound
    (f g : H → Set.Ioi (⊥ : EReal)) :
    pav(f, g) ≤
      ((1 / 2 : ℝ) : EReal) • f.asEReal + ((1 / 2 : ℝ) : EReal) • g.asEReal := sorry

end ProximalAverage

section ProximalAverageConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use the Chapter 14 proximal-average formula together with the Chapter 13 Fenchel
-- conjugation calculus to the pointwise half-sum of `f*` and `g*`.
/-- Proposition 14.9: the proximal average dominates the conjugate of the half-sum of `f*` and
`g*`. -/
theorem proximalAverage_lower_bound
    (f g : H → Set.Ioi (⊥ : EReal)) :
    ((((1 / 2 : ℝ) : EReal) • f.asEReal∗) + ((1 / 2 : ℝ) : EReal) • g.asEReal∗)∗ ≤
      pav(f, g) := sorry

-- Proof sketch: combine the preceding lower and upper bounds.
/-- Proposition 14.9: equation `(14.18)` sandwiches `pav(f, g)` between the conjugate of the
half-sum of `f*` and `g*` and the half-sum of `f` and `g`. -/
theorem proximalAverage_bounds
    (f g : H → Set.Ioi (⊥ : EReal)) :
    ((((1 / 2 : ℝ) : EReal) • f.asEReal∗) + ((1 / 2 : ℝ) : EReal) • g.asEReal∗)∗ ≤
      pav(f, g) ∧
    pav(f, g) ≤
      ((1 / 2 : ℝ) : EReal) • f.asEReal + ((1 / 2 : ℝ) : EReal) • g.asEReal := by
  exact ⟨proximalAverage_lower_bound f g, proximalAverage_upper_bound f g⟩

end ProximalAverageConjugation

end ERealFunction
