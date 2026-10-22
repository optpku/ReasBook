/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_4
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_3

universe u

set_option autoImplicit false

noncomputable section

open FreeGroupBasis

section

variable {X : Type u}

local instance instDecidableEqX_5_6_3 : DecidableEq X := Classical.decEq X

private abbrev basis : FreeGroupBasis X (FreeGroup X) := FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: algorithmic solvability of the word problem for small-cancellation quotients of
finitely generated free groups.

Layer triage:
- `source-facing`: a finitely generated free group `F`, a finite relator set `R`, its normal
  closure `N`, one of the small-cancellation hypotheses `C(6)`, `C(4)` together with `T(4)`, or
  `C(3)` together with `T(6)`, and the conclusion that the quotient `F / N` has solvable word
  problem.
- `core/canonical`: `FreeGroup X` with `[Finite X]` is the project's canonical model of a
  finitely generated free group, `HasSolvableWordProblem R` is the established presentation-level
  owner predicate for solvability of the word problem, and `PresentedGroup R` is the canonical
  quotient by the normal closure of `R`.
- `bridge/view`: `basis = FreeGroupBasis.ofFreeGroup X` is the canonical chosen basis used by the
  Chapter `5` small-cancellation owners `C(p)[basis, R]` and `T(q)[basis, R]`.

Domain sampling:
1. `GroupPresentation.HasSolvableWordProblem R` from Definition `2-1-4` is the owner predicate
   for the conclusion.
2. `FreeGroupBasis.condition_c` from Definition `5-2-2`, with notation `C(p)[basis, R]`, is the
   owner predicate for the `C(p)` hypotheses.
3. `FreeGroupBasis.condition_t` from Definition `5-2-3`, with notation `T(q)[basis, R]`, is the
   owner predicate for the `T(q)` hypotheses.
4. `FreeGroupBasis.ofFreeGroup X` is the canonical basis on the free group `FreeGroup X`, so the
   theorem should use that basis directly rather than introduce a parallel free-group wrapper.

Primitive vs. derived:
- primitive public data: the relator set `R`, finiteness of the generator type and of `R`, and
  the small-cancellation alternative;
- derived API: the presentation-level solvable-word-problem conclusion for the quotient by the
  normal closure of `R`.
- API refinement note: the three source alternatives already live directly in the owner predicates
  `C(p)[basis, R]` and `T(q)[basis, R]`, so this file should state their disjunction directly
  instead of introducing a parallel wrapper proposition.
-/

namespace GroupPresentation

-- Proof sketch: use the small-cancellation hypotheses to derive the Dehn-type reduction or
-- maximum-principle criterion for null-homotopic loops in the Cayley complex of the presentation.
-- Because `X` and `R` are finite, that criterion yields an effective procedure deciding whether a
-- signed word lies in the normal closure of `R`, which is exactly `HasSolvableWordProblem R`.
/-- Theorem 5-6-3: if `R` is a finite relator set in the finitely generated free group
`FreeGroup X` and `R` satisfies `C(6)`, or `C(4)` together with `T(4)`, or `C(3)` together with
`T(6)`, then the quotient by the normal closure of `R` has solvable word problem. This is stated
through the canonical presentation owner `HasSolvableWordProblem R`, and its hypotheses are stated
directly in the chapter owner predicates `C(p)[basis, R]` and `T(q)[basis, R]`. The source
assumption that `R` is symmetrized is absorbed by these owners: `C(p)` is stated on the
symmetrized relator family, while `T(q)` is stated on the corresponding symmetrized relator set
transported back to actual relators through the canonical basis `basis`. -/
theorem hasSolvableWordProblem_of_finite_smallCancellation
    (R : Set (FreeGroup X)) [Finite X] [Primcodable X] (hR : R.Finite)
    (hcase :
      C(6)[basis, R] ∨
        (C(4)[basis, R] ∧ T(4)[basis, R]) ∨
          (C(3)[basis, R] ∧ T(6)[basis, R])) :
    HasSolvableWordProblem R := sorry

end GroupPresentation

end
