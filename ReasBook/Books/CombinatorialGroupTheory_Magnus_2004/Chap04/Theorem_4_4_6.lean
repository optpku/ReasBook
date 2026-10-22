/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

namespace FreeGroupProduct

/-!
Primary domain: algorithmic group theory for direct products of finite-rank free groups.

Layer triage:
- `source-facing`: the generating problem of Definition `4-4-5` for `F_n × F_n`.
- `core/canonical`: the owner predicate `HasSolvableGeneratingProblem` together with the canonical
  underlying free-group and subgroup constructions used in that definition.
- `bridge/view`: Mihailova's construction reduces an unsolvable subgroup-membership problem to the
  failure of this source-facing computable predicate.

Domain sampling:
1. `FreeGroupProduct.HasSolvableGeneratingProblem` in Definition `4-4-5` is the source-facing
   owner for the theorem's conclusion.
2. `FreeGroup (Fin n)` is the canonical owner for the textbook free group `F_n`.
3. `FreeGroup.mk` is the canonical evaluation map from finite signed words to free-group
   elements.
4. `Subgroup.closure` is the owner construction behind the generating predicate.

Primitive vs. derived:
- primitive public data: the rank `n`;
- derived owner-side API: the source-facing predicate `HasSolvableGeneratingProblem n`.
-/

-- Proof sketch: encode finitely generated subgroups of `F_n × F_n` by finite lists of pairs of
-- words in the standard free bases. Mihailova's construction embeds an unsolvable subgroup
-- membership problem into the question whether such a finite family generates the whole direct
-- product. For `n ≥ 6`, the required finitely presented group with unsolvable word problem exists
-- by the preceding Higman-Rabin results, so no algorithm can solve the generating problem.
/-- Theorem 4-4-6: if `n ≥ 6`, then the generating problem for `F_n × F_n` is unsolvable. -/
theorem not_hasSolvableGeneratingProblem (n : ℕ) (hn : 6 ≤ n) :
    ¬ HasSolvableGeneratingProblem n := sorry

end FreeGroupProduct
