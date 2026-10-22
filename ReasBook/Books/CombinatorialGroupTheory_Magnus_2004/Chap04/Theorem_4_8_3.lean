/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_3
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_8_1

universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: algebraically closed groups and recursive presentations on countably many
generators.

Layer triage:
- `source-facing`: an algebraically closed group `G` together with the source claim that `G`
  cannot admit an infinite recursive presentation
  `⟨x_i, i ∈ ℕ ; r₁, r₂, ...⟩`.
- `core/canonical`: `PresentedGroup R` is the owner object attached to a relator set
  `R : Set (FreeGroup ℕ)`, `GroupPresentation.IsRecursive R` is the owner predicate for recursive
  enumerability of the relators, and `IsAlgebraicallyClosedGroup G` imported from Theorem
  `4-8-1` records the chapter's finite-system extension property for `G`.
- `bridge/view`: the source phrase “`G` admits an infinite recursive presentation” is expressed
  directly by a chosen equivalence `PresentedGroup R ≃* G` for some recursive relator set on
  generators indexed by `ℕ`.

Domain sampling:
1. `GroupPresentation.IsRecursive R` from Definition `2-1-3` is the chapter owner predicate for
   recursive relator sets.
2. `PresentedGroup R ≃* G` is the project's canonical presentation bridge from Chapter II.
3. `Group.IsRecursivelyPresented` from Theorem `4-7-1` is the earlier chapter owner for the
   finite-generator variant, so the present `ℕ`-indexed notion should remain only the countable
   source-facing companion.
4. `IsAlgebraicallyClosedGroup` from Theorem `4-8-1` is the chapter owner for algebraic
   closedness.

Primitive vs. derived:
- primitive public data for algebraic closedness: the imported owner predicate
  `IsAlgebraicallyClosedGroup G`;
- primitive public data for an infinite recursive presentation: a relator set
  `R : Set (FreeGroup ℕ)` and a presentation equivalence `PresentedGroup R ≃* G`;
- derived API is unnecessary here: the theorem can be stated directly on the canonical
  presentation data, so no extra group-level wrapper around the existential presentation data is
  introduced.
-/

variable (G : Type u) [Group G]

/-- Theorem 4-8-3: if `PresentedGroup R ≃* G` presents an algebraically closed group `G` on
generators indexed by `ℕ`, then the relator set `R` is not recursive. Equivalently, no
algebraically closed group admits an infinite recursive presentation. -/
-- Proof sketch: assume `G` has a recursive presentation `PresentedGroup R ≃* G` on generators
-- `ℕ`. The algebraic-closedness hypothesis implies the simplicity reduction used in the preceding
-- item, so Theorem `4-3-7` gives a solvable word problem for that recursive presentation. The
-- textbook diagonal argument then uses this decision procedure to solve the word problem for a
-- finitely presented group known to have unsolvable word problem, contradiction.
theorem not_isRecursive_of_presentation_of_algebraicallyClosedGroup
    (hG : IsAlgebraicallyClosedGroup G) {R : Set (FreeGroup ℕ)} (P : PresentedGroup R ≃* G) :
    ¬ GroupPresentation.IsRecursive R := sorry

end Group
