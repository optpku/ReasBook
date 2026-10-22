/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_6_3
import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_7_6

universe u

set_option autoImplicit false

noncomputable section

open FreeGroupBasis

section

variable {X : Type u}

local instance instDecidableEqX_5_8_4 : DecidableEq X := Classical.decEq X

private abbrev basis : FreeGroupBasis X (FreeGroup X) := FreeGroupBasis.ofFreeGroup X

namespace GroupPresentation

/-!
Primary domain: decision problems for small-cancellation quotients of finitely generated free
groups.

Layer triage:
- `source-facing`: a finite relator set `R` in a free group, together with the Chapter `5`
  small-cancellation hypotheses `C(4)` and `T(4)`.
- `core/canonical`: `hasSolvableWordProblem_of_finite_smallCancellation` and
  `hasSolvableConjugacyProblem_of_finite_smallCancellation` are the existing Chapter `5` owner
  theorems for the word and conjugacy conclusions, while `HasSolvableWordProblem R`,
  `HasSolvableConjugacyProblem R`, `C(4)[basis, R]`, and `T(4)[basis, R]` are the underlying
  owner predicates.
- `bridge/view`: this file is only the `(C(4), T(4))` specialization of those upstream
  small-cancellation theorems, expressed using the canonical basis
  `basis = FreeGroupBasis.ofFreeGroup X`.

Domain sampling:
1. `GroupPresentation.hasSolvableWordProblem_of_finite_smallCancellation` from Theorem `5-6-3`
   is the canonical Chapter `5` theorem for solvable word problem under the three standard
   small-cancellation alternatives.
2. `GroupPresentation.hasSolvableConjugacyProblem_of_finite_smallCancellation` from Theorem
   `5-7-6` is the matching canonical theorem for solvable conjugacy problem.
3. `FreeGroupBasis.condition_c`, written `C(4)[basis, R]`, is the owner predicate for the `C(4)`
   hypothesis.
4. `FreeGroupBasis.condition_t`, written `T(4)[basis, R]`, is the owner predicate for the `T(4)`
   hypothesis.

Primitive vs. derived:
- primitive public data: the relator set `R`, finiteness of the generator type and relator set,
  and the Chapter `5` small-cancellation hypotheses;
- derived API: the two `(C(4), T(4))` corollaries, obtained by specializing the canonical
  small-cancellation owner theorems to the middle disjunct.
-/

variable (R : Set (FreeGroup X)) [Finite X] [Primcodable X]

-- Proof sketch: specialize the Chapter `5` small-cancellation word-problem theorem to the
-- `(C(4), T(4))` case. The source knot-group assumptions that `R` is symmetrized and all relators
-- have length four are bookkeeping for this application, while the decision-problem conclusion is
-- expressed directly through the canonical owner predicates `C(4)[basis, R]` and `T(4)[basis, R]`.
/-- Lemma 5-8-4 (1): if `R` is a finite relator set in the finitely generated free group
`FreeGroup X` and `R` satisfies `C(4)` and `T(4)`, then the quotient by the normal closure of `R`
has solvable word problem. The source phrase “`T(4)` for minimal sequences” is recorded here
through the Chapter `5` owner predicate `T(4)[basis, R]`. -/
theorem hasSolvableWordProblem_of_finite_C4_T4
    (hR : R.Finite) (hC4 : C(4)[basis, R]) (hT4 : T(4)[basis, R]) :
    HasSolvableWordProblem R := by
  simpa using
    hasSolvableWordProblem_of_finite_smallCancellation R hR <| Or.inr <| Or.inl ⟨hC4, hT4⟩

-- Proof sketch: specialize the Chapter `5` small-cancellation conjugacy theorem to the
-- `(C(4), T(4))` case. The textbook length-four and symmetrized hypotheses belong to the
-- surrounding knot-group setup, while the canonical owner conclusion is the predicate
-- `HasSolvableConjugacyProblem R`.
/-- Lemma 5-8-4 (2): under the same finite `C(4)` and `T(4)` small-cancellation hypotheses, the
quotient by the normal closure of `R` has solvable conjugacy problem. -/
theorem hasSolvableConjugacyProblem_of_finite_C4_T4
    (hR : R.Finite) (hC4 : C(4)[basis, R]) (hT4 : T(4)[basis, R]) :
    HasSolvableConjugacyProblem R := by
  exact hasSolvableConjugacyProblem_of_finite_smallCancellation R hR <|
    Or.inr <| Or.inl ⟨hC4, hT4⟩

end GroupPresentation

end
