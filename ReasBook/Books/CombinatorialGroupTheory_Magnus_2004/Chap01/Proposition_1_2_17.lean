/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open FreeGroup

/-!
Primary domain: reduced-word powers in free groups.

Layer triage:
- `source-facing`: powers of an element of a free group, measured relative to a chosen basis.
- `core/canonical`: `FreeGroup.IsCyclicallyReduced`, `FreeGroup.toWord`, and `FreeGroup.norm`.
- `bridge/view`: `FreeGroupBasis.repr` transports the source-facing statement to the canonical
  free-group model.

Domain sampling:
1. `FreeGroup.IsCyclicallyReduced.flatten_replicate` is the owner theorem controlling powers of a
   cyclically reduced reduced word.
2. `FreeGroup.toWord_pow` is the owner evaluation theorem for reduced words of powers.
3. `FreeGroup.norm` is the owner reduced-word length function.
4. `FreeGroupBasis.repr` is the chapter's canonical bridge from an abstract free group with chosen
   basis to the concrete `FreeGroup` model.

Primitive vs. derived:
- primitive public data: an element `w : FreeGroup α` and the proof that `w.toWord` is cyclically
  reduced;
- derived API: the exact reduced word of `w ^ n`, its linear norm growth, and the basis-level
  transport statement.
-/

namespace FreeGroup

section

variable {α : Type u}

local instance proposition_1_2_17_decidableEq_alpha : DecidableEq α := Classical.decEq α

/-- Proposition 1-2-17 on the canonical free-group model: if the reduced word of `w` is
cyclically reduced, then every power is represented by the concatenation of the expected number of
copies of that reduced word. -/
theorem toWord_pow_of_isCyclicallyReduced (w : FreeGroup α)
    (hw : IsCyclicallyReduced w.toWord) (n : ℕ) :
    toWord (w ^ n) = (List.replicate n w.toWord).flatten := by
  rw [toWord_pow, (hw.flatten_replicate n).isReduced.reduce_eq]

/-- Proposition 1-2-17 on the canonical free-group model: powers of a cyclically reduced element
have exactly linear reduced-word length growth. -/
theorem norm_pow_of_isCyclicallyReduced (w : FreeGroup α)
    (hw : IsCyclicallyReduced w.toWord) (n : ℕ) :
    norm (w ^ n) = n * norm w := by
  simpa [norm] using congrArg List.length (toWord_pow_of_isCyclicallyReduced w hw n)

end

end FreeGroup

namespace FreeGroupBasis

variable {ι : Type v} {F : Type u} [Group F]

local instance proposition_1_2_17_decidableEq_iota : DecidableEq ι := Classical.decEq ι

/-- Proposition 1-2-17: relative to a chosen free basis, powers of an element whose reduced word
is cyclically reduced have exactly linear reduced-word length growth. -/
theorem norm_repr_pow_of_isCyclicallyReduced (b : FreeGroupBasis ι F) (w : F)
    (hw : IsCyclicallyReduced (b.repr w).toWord) (n : ℕ) :
    norm (b.repr (w ^ n)) = n * norm (b.repr w) := by
  simpa [map_pow] using norm_pow_of_isCyclicallyReduced (b.repr w) hw n

end FreeGroupBasis
