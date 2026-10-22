/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_9
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_2_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open Monoid.CoprodI Monoid.PushoutI
open Subgroup.amalgamatedProductAlong

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Subgroup.amalgamatedProductAlong

/-!
Primary domain: cyclic reduction for normal-form words in a free product with amalgamation.

Layer triage:
- `source-facing`: a reduced two-factor word `w = y₁ ⋯ yₙ` in amalgam normal form, together with
  the textbook predicate “weakly cyclically reduced”, and the specialization of the already owned
  cyclic-reduction predicate to normal-form words.
- `core/canonical`: `Monoid.CoprodI.Word` is the owner for reduced alternating words in the two
  factors, specialized here through `Monoid.CoprodI.twoFactorFamily G H`.
- `bridge/view`: the first and last letters of a nonempty word are boundary data in one of the two
  factors, viewed in the ambient amalgamated product through `Monoid.PushoutI.of`; weak cyclic
  reduction compares their product with the canonical base subgroup `(base e).range`.

Domain sampling:
1. `Monoid.CoprodI.Word.IsCyclicallyReduced` from Theorem `4-2-12` is the chapter owner for
   cyclic reduction of a reduced alternating two-factor word.
2. `Monoid.CoprodI.NeWord.head` and `Monoid.CoprodI.NeWord.last` show that first and last letters
   are canonical boundary data of a nonempty reduced word.
3. `Subgroup.amalgamatedProductAlong.Reduced` is the chapter-facing owner for “normal form” in the
   two-factor amalgamated product.
4. `Monoid.PushoutI.of` and `Subgroup.amalgamatedProductAlong.base` are the canonical factor and
   base embeddings into the ambient amalgamated product.

Primitive vs. derived:
primitive public data: a source word `w : Word Family`, together with the owner-side reducedness
proof `Reduced e w` from Definition `4-2-9`, and its first and last boundary letters;
- derived API: the recalled cyclic-reduction owner predicate and the source weak cyclic-reduction
  predicate.
-/

section

variable {G H : Type u} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H}
variable (e : A ≃* B)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "P" => amalgamatedProductAlong e
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom

/- Definition 5-11-2 (1): for a normal-form word, “cyclically reduced” is the existing chapter
owner predicate `Monoid.CoprodI.Word.IsCyclicallyReduced`, specialized to the amalgamating maps
`ιA` and `ιB`. -/
#check (Word.IsCyclicallyReduced ιA ιB)

-- Proof sketch: this is the length-`0`/length-`1` branch built directly into the definition.
/-- Words of syllable length at most one are cyclically reduced. -/
theorem isCyclicallyReduced_of_length_le_one
    {w : Word Family} (hwred : Reduced e w) (hw : w.toList.length ≤ 1) :
    w.IsCyclicallyReduced ιA ιB := by
  exact ⟨hwred, fun _ _ _ ↦ hw⟩

/-- Definition 5-11-2 (2): a normal-form word is weakly cyclically reduced when a boundary pinch
through the amalgamated subgroup can occur only in syllable length at most one. Equivalently, for
words of length greater than one, if the last and first syllables lie in the same factor, then
their product does not lie in the amalgamated subgroup. -/
def IsWeaklyCyclicallyReduced
    (w : Word Family) : Prop :=
  Reduced e w ∧
    ∀ {b} {yLast yFirst : Family b},
      w.toList.getLast? = some ⟨b, yLast⟩ →
        w.toList.head? = some ⟨b, yFirst⟩ →
          ((Monoid.PushoutI.of b yLast : P) * Monoid.PushoutI.of b yFirst) ∈ (base e).range →
            w.toList.length ≤ 1

-- Proof sketch: this is again the length-`0`/length-`1` branch built directly into the
-- definition.
/-- Words of syllable length at most one are weakly cyclically reduced. -/
theorem isWeaklyCyclicallyReduced_of_length_le_one
    {w : Word Family} (hwred : Reduced e w) (hw : w.toList.length ≤ 1) :
    IsWeaklyCyclicallyReduced e w := by
  refine ⟨hwred, ?_⟩
  intro _ _ _ _ _ _
  exact hw

end

end Subgroup.amalgamatedProductAlong
