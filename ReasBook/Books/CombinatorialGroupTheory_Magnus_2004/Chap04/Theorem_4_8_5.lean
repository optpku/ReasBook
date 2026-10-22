/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_8_4

universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: algebraically closed groups and algorithmic group theory.

Layer triage:
- `source-facing`: a finitely generated group `G` together with the hypothesis that `G` embeds in
  every algebraically closed group and the conclusion that `G` has solvable word problem.
- `core/canonical`: `EmbedsInAllAlgebraicallyClosedGroups` from Theorem `4-8-4` is the chapter
  owner for the embedding hypothesis, and `Group.HasSolvableWordProblem` from Theorem `4-4-8` is
  the abstract owner for the conclusion.
- `bridge/view`: the owner predicate `EmbedsInAllAlgebraicallyClosedGroups G` expands to the
  canonical homomorphism-and-injectivity embedding datum for each ambient algebraically closed
  group `A`.

Domain sampling:
1. `EmbedsInAllAlgebraicallyClosedGroups` from Theorem `4-8-4` is the chapter owner for the
   hypothesis that `G` embeds in every algebraically closed group.
2. `IsAlgebraicallyClosedGroup` from Theorem `4-8-1` remains the underlying owner for algebraic
   closedness of the ambient target.
3. `Group.FG G` is mathlib's owner predicate for finite generation.
4. `Group.HasSolvableWordProblem` from Theorem `4-4-8` is the abstract group-level owner for the
   conclusion.

Primitive vs. derived:
- primitive public data: the ambient group `G` and the imported owner hypothesis
  `EmbedsInAllAlgebraicallyClosedGroups G`;
- derived API: `Group.HasSolvableWordProblem G` as the abstract owner for the conclusion, together
  with the thin `↔` companion theorem pairing this converse with Theorem `4-8-4`.
-/

variable {G : Type u} [Group G]

namespace EmbedsInAllAlgebraicallyClosedGroups

-- Proof sketch: this file introduces no new owner abstraction. It records the converse half of
-- the embedding criterion whose forward direction is Theorem `4-8-4`; the companion `↔` theorem
-- below is then just the direct pairing of those two owner-level implications.
/-- Theorem 4-8-5: if a finitely generated group embeds in every algebraically closed group, then
it has solvable word problem. -/
theorem hasSolvableWordProblem [FG G] (hG : EmbedsInAllAlgebraicallyClosedGroups G) :
    HasSolvableWordProblem G := sorry

end EmbedsInAllAlgebraicallyClosedGroups

/-- A finitely generated group has solvable word problem exactly when it embeds in every
algebraically closed group. -/
theorem hasSolvableWordProblem_iff_embedsInAllAlgebraicallyClosedGroups [FG G] :
    HasSolvableWordProblem G ↔ EmbedsInAllAlgebraicallyClosedGroups G :=
  ⟨HasSolvableWordProblem.embedsInAllAlgebraicallyClosedGroups,
    EmbedsInAllAlgebraicallyClosedGroups.hasSolvableWordProblem⟩

end Group
