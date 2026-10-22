/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

variable (G : Type u) [Group G]

/-!
Primary domain: divisible groups and `n`th roots in multiplicative form.

Layer triage:
- `source-facing`: the textbook property that every element of a group admits an `n`th root for
  every positive integer `n`.
- `core/canonical`: the chapter-facing owner for this notion is `RootableBy G ℕ`.
- `bridge/view`: for groups, mathlib also provides the equivalent integer-indexed bridge
  `rootableByIntOfRootableByNat`, while the companion theorem below recovers the textbook
  existential formulation with `0 < n`.

Domain sampling:
1. `RootableBy A α` in `Mathlib/GroupTheory/Divisible` is the canonical multiplicative notion of
   divisibility/rootability.
2. `RootableBy.surjective_pow` exposes the textbook existence statement as surjectivity of the
   `n`th-power map.
3. `rootableByOfPowLeftSurj` converts surjectivity of the `n`th-power maps back to the canonical
   owner.
4. `rootableByIntOfRootableByNat` shows that for groups the `ℕ`-indexed owner already carries the
   equivalent `ℤ`-indexed rootability structure, so using `ℕ` remains faithful to the textbook's
   positive-integer formulation without losing the richer group-level API.

Primitive vs. derived:
- primitive public owner: `RootableBy G ℕ`;
- derived bridge API: the textbook positive-integer root-existence theorem obtained from that
  owner.
-/

/- Definition 4-3-4: a group `G` is divisible when every element of `G` has an `n`th root for
every positive integer `n`.

Mathlib records the chapter-facing owner of this notion as `RootableBy G ℕ`. For groups this is
equivalent to the integer-indexed rootability structure, but the `ℕ`-indexed form matches the
textbook definition directly. The textbook existential wording is recovered by the companion
theorem below, so the main labeled entry is the direct recall of this canonical type expression
rather than a redundant local alias. -/
#check (RootableBy G ℕ)

end

section

variable (G : Type u) [Monoid G]

/-- A `RootableBy G ℕ` structure yields the textbook positive-natural root-existence statement. -/
theorem forall_exists_pos_nat_root_of_rootableBy_nat [RootableBy G ℕ]
    (g : G) (n : ℕ) (hn : 0 < n) : ∃ y : G, y ^ n = g :=
  RootableBy.surjective_pow G ℕ (Nat.ne_of_gt hn) g

end
