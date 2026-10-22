/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_3
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_4
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_4_10

universe u

set_option autoImplicit false

noncomputable section

open FreeGroupBasis GroupPresentation

section

variable {X : Type u}

local instance theorem_5_5_4_decidableEq : DecidableEq X := Classical.decEq X
local instance instDecidableProp_5_5_4 (p : Prop) : Decidable p := Classical.propDecidable p

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: the conjugacy problem for small-cancellation quotients of free groups.

Layer triage:
- `source-facing`: a relator set `R : Set (FreeGroup X)`, nontrivial cyclically `R`-reduced words
  `u` and `z` that are not conjugate in the free group, and the criterion that conjugacy in the
  quotient is witnessed by a short conjugator built from one or two relator subwords.
- `core/canonical`: `FreeGroup X` is the owner of the ambient free group,
  `PresentedGroup.mk R` is the canonical quotient map into `G = F / N`,
  `IsConj` is the owner predicate for conjugacy,
  `basis.is_cyclically_r_reduced R` is the chapter owner for cyclic `R`-reduction,
  `symmetrizedRelatorFamily R` is the owner of `R*`,
  `CyclicWord.HasPart` is the owner predicate for a cyclic subword of a relator,
  `C'((1 / 6 : ℝ))[basis, R]`, `C'((1 / 4 : ℝ))[basis, R]`, `C'((1 / 8 : ℝ))[basis, R]`, and
  `T(4)[basis, R]` are the chapter owners for the small-cancellation hypotheses, and
  `HasSolvableConjugacyProblem R` is the owner predicate for the algorithmic corollary.
- `bridge/view`: the source subwords `b₁` and `b₂` are represented by signed words
  `part₁`, `part₂ : List (X × Bool)` together with the equalities
  `FreeGroup.mk partᵢ = bᵢ`, while the relator-length bound is read on the supporting cyclic
  relators from `symmetrizedRelatorFamily R`.

Domain sampling:
1. `basis.is_cyclically_r_reduced R` from Definition `5-4-10` is the existing owner for the
   source hypothesis that `u` and `z` are cyclically `R`-reduced.
2. `symmetrizedRelatorFamily R` and `CyclicWord.HasPart` are the canonical owners for saying that
   a word is a subword of a relator from `R*`.
3. `PresentedGroup.mk R` and `IsConj` are the canonical owner interfaces for conjugacy in the
   quotient `G = F / N`.
4. `GroupPresentation.IsRecursive R` and `HasSolvableConjugacyProblem R` from Definitions
   `2-1-3` and `2-1-4` are the established owner predicates for the algorithmic corollary.

Primitive vs. derived:
- primitive public data: the relator set `R`, the elements `u`, `z`, the small-cancellation case,
  the nontriviality and cyclic `R`-reduction hypotheses, and the free-group nonconjugacy
  hypothesis;
- derived API: the quotient conjugacy criterion and the solvable-conjugacy corollary, whose
  short-conjugator clause is stated directly with `symmetrizedRelatorFamily R`,
  `CyclicWord.HasPart`, and `FreeGroup.mk`.
-/

namespace FreeGroup

-- Proof sketch: for the forward implication, start from a reduced annular `R`-diagram for the
-- quotient conjugacy class and apply the annular small-cancellation analysis to a region meeting
-- both boundary components. Reading the corresponding boundary arc yields a conjugator that is one
-- or two relator subwords, with relator lengths bounded by `2q max(|u|, |z|)` and with the
-- `C'(1 / 8)` improvement forcing the one-subword case. The reverse implication is immediate from
-- the displayed quotient equality `u = h⁻¹ z h`.
/-- Theorem 5-5-4 (1): if `R` satisfies either `C'(1 / 6)` or `C'(1 / 4)` together with `T(4)`,
and `u`, `z` are nontrivial cyclically `R`-reduced free-group elements that are not conjugate in
the free group itself, then their images in the quotient `G = F / N` are conjugate if and only if
there exists a conjugator `h` such that the outer small-cancellation hypothesis determines the
relator-length bound `2q max(|u|, |z|)` with `q = 3` in the `C'(1 / 6)` case and `q = 4`
otherwise, the quotient equality `u = h⁻¹ z h` holds, and `h` has the source short factorization
by one or two relator subwords. Because `u` and `z` are already cyclically `R`-reduced, the
criterion is stated directly for `u` and `z` rather than introducing extra witnesses `u*` and
`z*`. -/
theorem quotient_conjugacy_iff_exists_short_smallCancellation_conjugator
    (R : Set (FreeGroup X)) {u z : FreeGroup X}
    (hcase : C'((1 / 6 : ℝ))[basis, R] ∨ (C'((1 / 4 : ℝ))[basis, R] ∧ T(4)[basis, R]))
    (hu_ne : u ≠ 1) (hz_ne : z ≠ 1)
    (hu_cyclic : (basis).is_cyclically_r_reduced R u.toWord)
    (hz_cyclic : (basis).is_cyclically_r_reduced R z.toWord)
    (hnotconj : ¬ IsConj u z) :
    IsConj (PresentedGroup.mk R u) (PresentedGroup.mk R z) ↔
      ∃ h : FreeGroup X,
        let qBound := if C'((1 / 6 : ℝ))[basis, R] then 3 else 4;
        let bound := 2 * qBound * max u.toWord.length z.toWord.length;
        let hasShortRelatorPart : List (X × Bool) → Prop := fun part ↦
          ∃ q ∈ symmetrizedRelatorFamily R, q.HasPart part ∧ q.length < bound;
        PresentedGroup.mk R u = PresentedGroup.mk R (h⁻¹ * z * h) ∧
          (((∃ part₁ : List (X × Bool),
              h = FreeGroup.mk part₁ ∧ hasShortRelatorPart part₁) ∨
            ∃ part₁ part₂ : List (X × Bool),
              h = FreeGroup.mk part₁ * FreeGroup.mk part₂ ∧
                hasShortRelatorPart part₁ ∧ hasShortRelatorPart part₂) ∧
            (C'((1 / 8 : ℝ))[basis, R] →
              ∃ part₁ : List (X × Bool),
                h = FreeGroup.mk part₁ ∧ hasShortRelatorPart part₁)) := sorry

end FreeGroup

namespace GroupPresentation

-- Proof sketch: reduce conjugacy in the quotient to cyclically `R`-reduced representatives, apply
-- clause (1) to bound the search to one or two relator parts whose supporting relators have
-- length `< 2q max(|u|, |z|)`, and use the recursive relator predicate together with the finite
-- generator type to enumerate all such candidates effectively. Deciding whether one candidate
-- works yields a decision procedure for quotient conjugacy.
/-- Theorem 5-5-4 (2): if the free group on the finite generator type `X` has recursive relator
set `R` satisfying either `C'(1 / 6)` or `C'(1 / 4)` together with `T(4)`, then the presented
quotient `G = F / N` has solvable conjugacy problem. Here finite generation is recorded by
`[Finite X]`, and recursive presentation is recorded by
`GroupPresentation.IsRecursive R`. -/
theorem hasSolvableConjugacyProblem_of_recursive_smallCancellation
    (R : Set (FreeGroup X)) [Finite X] [Primcodable X]
    (hcase : C'((1 / 6 : ℝ))[basis, R] ∨ (C'((1 / 4 : ℝ))[basis, R] ∧ T(4)[basis, R]))
    (hrecursive : IsRecursive R) :
    HasSolvableConjugacyProblem R := sorry

end GroupPresentation

end
