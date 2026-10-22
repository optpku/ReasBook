/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-!
Primary domain: torsion-freeness of free groups.

Layer triage:
- `source-facing`: an abstract free group `F`, an element `w : F`, and the textbook consequence
  that `w ^ n = 1` with `n ≠ 0` forces `w = 1`.
- `core/canonical`: `IsMulTorsionFree` and its owner lemma
  `IsMulTorsionFree.zpow_eq_one_iff_left`.
- `bridge/view`: `IsFreeGroup.toFreeGroup` transports the source statement to the canonical free
  group model `FreeGroup (IsFreeGroup.Generators F)`.

Domain sampling:
1. `IsFreeGroup.toFreeGroup` is mathlib's canonical bridge from an abstract free group to the
   owner model `FreeGroup _`.
2. `Function.Injective.isMulTorsionFree` transports torsion-freeness back along that embedding.
3. The instance `IsMulTorsionFree (FreeGroup α)` is the owner torsion-free result for free groups.
4. `IsMulTorsionFree.zpow_eq_one_iff_left` is the canonical theorem behind the present
   source-facing proposition.

Primitive vs. derived:
- primitive public data: the group `F`, the free-group structure `[IsFreeGroup F]`, the element
  `w`, the integer `n`, and the relation `w ^ n = 1`;
- derived API: torsion-freeness of `F`, obtained internally from the canonical free-group model.
-/

/-- Proposition 1-2-18: a free group is torsion free. -/
instance : IsMulTorsionFree F := by
  let e := IsFreeGroup.toFreeGroup F
  exact Function.Injective.isMulTorsionFree e.toMonoidHom e.injective

/-- Proposition 1-2-18: in a free group, if `w ^ n = 1` for an integer `n ≠ 0`, then `w = 1`. -/
theorem eq_one_of_zpow_eq_one (w : F) (n : ℤ) (hn : n ≠ 0) (hpow : w ^ n = 1) : w = 1 := by
  exact (IsMulTorsionFree.zpow_eq_one_iff_left hn).mp hpow

end
