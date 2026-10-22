/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_4_8
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_7_1

universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: algorithmic group theory in the Higman embedding section.

Layer triage:
- `source-facing`: the existence of a finitely presented group with unsolvable word problem.
- `core/canonical`: `Group.IsFinitelyPresented` is the abstract owner for finite presentability,
  and `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the chapter owner for solvability of
  the word problem.
- `bridge/view`: `Group.IsRecursivelyPresented` and its owner-side corollary
  `Group.IsRecursivelyPresented.exists_finitelyPresented_embedding` from Theorem `4-7-1` package
  Higman's embedding theorem, so the recursive-presentation construction in the textbook stays
  proof-level bridge data rather than becoming a second public wrapper here.

Domain sampling:
1. `Group.IsFinitelyPresented` is mathlib's owner predicate for finite presentability.
2. `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the chapter's abstract owner predicate
   for solvable word problem.
3. `Group.IsRecursivelyPresented` from Theorem `4-7-1` is the chapter owner abstraction for the
   recursive-presentation hypothesis used in Higman's theorem.
4. `Group.IsRecursivelyPresented.exists_finitelyPresented_embedding` from Theorem `4-7-1` is the
   owner-side bridge from recursive presentability to embedding in a finitely presented group.

Primitive vs. derived:
- primitive public data: only the ambient witness group `H`;
- derived owner-side properties: finite presentability of `H` and failure of
  `Group.HasSolvableWordProblem H`.
-/

/-- Theorem 4-7-2: there exists a finitely presented group with unsolvable word problem. -/
-- Proof sketch: choose a recursively enumerable nonrecursive set `S ⊆ ℕ+` and form the standard
-- recursively presented group whose relators force `a⁻ⁿ * b * aⁿ = c⁻ⁿ * d * cⁿ` exactly for
-- `n ∈ S`. Membership in `S` reduces to the word problem in that group, so the word problem is
-- unsolvable. Applying
-- `Group.IsRecursivelyPresented.exists_finitelyPresented_embedding` from Theorem `4-7-1` embeds
-- this finitely generated recursively presented group in a finitely presented group, and
-- solvability of the ambient word problem would restrict to the embedded subgroup, contradiction.
theorem exists_finitelyPresented_not_hasSolvableWordProblem :
    ∃ (H : Type u) (_ : Group H),
      IsFinitelyPresented H ∧ ¬ HasSolvableWordProblem H := sorry

end Group
