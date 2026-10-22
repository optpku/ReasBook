/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Data.PNat.Notation
import Mathlib.GroupTheory.PushoutI

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {G : Type u} [Group G] {ι : Type v}

/- Layer triage:
- `source-facing`: an indexed family `g : ι → G` with positive exponents `m : ι → ℕ+`, together
  with the existence of an overgroup in which each `g i` has an `m i`th root.
- `core/canonical`: `zpowersHom` and `Monoid.PushoutI`.
- `bridge/view`: adjoin one prescribed root by one `Monoid.PushoutI` step using the canonical
  maps from `Multiplicative ℤ`, then iterate over the family `ι`.

Domain sampling:
1. `zpowersHom G (g i) : Multiplicative ℤ →* G` is the canonical owner morphism from the infinite
   cyclic group determined by the target element `g i`.
2. `zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd (m i : ℤ))` is the canonical `m i`-power
   endomorphism of the infinite cyclic root carrier.
3. `Monoid.PushoutI`, with `of`, `base`, and `of_injective`, is the canonical owner for the
   one-step amalgam used to force the relation `x ^ (m i : ℕ) = g i`.
4. No existing chapter/mathlib declaration already packages this simultaneous root-adjunction
   statement, so the proposition should remain source-facing rather than being replaced by a
   recall-only alias.

Primitive vs. derived:
the primitive source data are only `g` and `m`; the canonical cyclic maps, one-step amalgams,
ambient overgroup, embedding, and root family are derived from those owner constructions.
-/
/-- Proposition 1-6-1: every family of elements of a group admits simultaneous prescribed positive
roots after embedding the group into a larger group. -/
-- Proof sketch: adjoin one equation `x ^ m = g` at a time. For one step, identify the source
-- and root cyclic groups through the canonical maps `zpowersHom G g` and
-- `zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd (m : ℤ))`, and glue them by
-- `Monoid.PushoutI`. Iterating that owner construction over `ι` yields the required overgroup in
-- `Type (max u v)`.
theorem exists_embedding_with_prescribed_roots (g : ι → G) (m : ι → ℕ+) :
    ∃ (H : Type (max u v)) (_ : Group H) (f : G →* H),
      Function.Injective f ∧ ∃ roots : ι → H, ∀ i, roots i ^ (m i : ℕ) = f (g i) := sorry

end
