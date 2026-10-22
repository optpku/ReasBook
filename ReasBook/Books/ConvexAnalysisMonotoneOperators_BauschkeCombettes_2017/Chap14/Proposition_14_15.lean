/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: for `(i) → (ii)`, combine supercoercive growth with the Fenchel conjugate formula
-- to get a uniform real upper bound on each bounded set. For `(ii) → (i)`, apply the bounded-set
-- hypothesis to large closed balls in the dual space and use the standard dual characterization of
-- supercoercivity for functions in `Γ₀(H)`.
/-- Proposition 14.15 (1): for `f ∈ Γ₀(H)`, supercoercivity of `f` is equivalent to the Fenchel
conjugate `f*` being bounded above on every bounded subset of `H`. -/
theorem supercoercive_iff_conjugate_boundedOnEveryBoundedSet
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Supercoercive f.asEReal ↔
      ∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u ≤ M := sorry

-- Proof sketch: apply the bounded-set hypothesis to each singleton `{u}`. Since a singleton is
-- bounded, `conjugate f u` is dominated by some real number, hence lies in the domain.
/-- Proposition 14.15 (2): if the Fenchel conjugate `f*` is bounded above on every bounded subset
of `H`, then `dom f* = H`. -/
theorem dom_conjugate_eq_univ_of_conjugate_boundedOnEveryBoundedSet
    (f : H → Set.Ioi (⊥ : EReal))
    (hbounded :
      ∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u ≤ M) :
    dom f.asEReal∗ = Set.univ := sorry

end Conjugation

end ERealFunction
