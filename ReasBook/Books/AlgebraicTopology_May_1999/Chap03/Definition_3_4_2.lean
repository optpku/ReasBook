/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 3.4.2: a free action of `G` on `S` is the canonical proposition
`IsCancelSMul G S`. -/
recall IsCancelSMul (G : Type u) (S : Type v) [SMul G S] : Prop

/- The canonical mathlib owner for the orbit condition in a transitive action is
`MulAction.IsPretransitive G S`. The source-facing transitivity notion additionally requires
`Nonempty S`; mathlib does not introduce a separate `MulAction.IsTransitive`. -/
recall MulAction.IsPretransitive (G : Type u) (S : Type v) [SMul G S] : Prop

namespace MulAction

/-- Definition 3.4.2: a transitive action of `G` on `S` is a nonempty pretransitive action,
equivalently `S` is a single orbit. -/
def IsTransitive (G : Type u) (S : Type v) [SMul G S] : Prop :=
  Nonempty S ∧ IsPretransitive G S

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/-- A `G`-action on `S` is transitive exactly when some orbit is all of `S`. -/
theorem isTransitive_iff_exists_orbit_eq_univ :
    IsTransitive G S ↔ ∃ s : S, orbit G s = Set.univ := by
  constructor
  · rintro ⟨hS, hG⟩
    letI : IsPretransitive G S := hG
    obtain ⟨s⟩ := hS
    exact ⟨s, orbit_eq_univ G s⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨s⟩, (isPretransitive_iff_orbit_eq_univ s).2 hs⟩

/-- The source-facing transitivity notion is equivalent to nonemptiness together with the
canonical mathlib owner for the orbit condition. -/
theorem isTransitive_iff_nonempty_pretransitive :
    IsTransitive G S ↔ Nonempty S ∧ IsPretransitive G S :=
  Iff.rfl

end MulAction

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/- For `s : S`, the isotropy group `G_s` is the canonical subgroup
`MulAction.stabilizer G s` of those elements `g : G` satisfying `g • s = s`. -/
recall MulAction.stabilizer (G : Type u) {S : Type v} [Group G] [MulAction G S] (s : S) :
    Subgroup G

/- Equivalently, a free action is one whose isotropy groups are all trivial. -/
recall isCancelSMul_iff_stabilizer_eq_bot :
    IsCancelSMul G S ↔ ∀ s : S, MulAction.stabilizer G s = ⊥

/- With a chosen basepoint `s`, the orbit condition underlying transitivity is equivalent to every
point of `S` being a translate of `s`. -/
recall MulAction.isPretransitive_iff_base (s : S) :
    MulAction.IsPretransitive G S ↔ ∀ t : S, ∃ g : G, g • s = t

/- With a chosen basepoint `s`, the orbit condition underlying transitivity is also equivalent to
the orbit of `s` being all of `S`. -/
recall MulAction.isPretransitive_iff_orbit_eq_univ (s : S) :
    MulAction.IsPretransitive G S ↔ MulAction.orbit G s = Set.univ
