/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.GroupTheory.PushoutI
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

set_option autoImplicit false

open Monoid
open Monoid.CoprodI Monoid.PushoutI
open MulEquiv

attribute [-instance] Monoid.CoprodI.twoFactorFamilyMonoid

namespace Monoid.CoprodI

/-- The canonical `Bool`-indexed pushout diagram for a two-factor amalgamated product with
amalgamating maps `φG : A →* G` and `φH : A →* H`. -/
abbrev twoFactorAmalgamatingMaps
    {A : Type u} {G : Type v} {H : Type w}
    [Group A] [Group G] [Group H]
    (φG : A →* G)
    (φH : A →* H) :
    (b : Bool) → A →* twoFactorFamily G H b
  | false => (ulift.symm.toMonoidHom : G →* twoFactorFamily G H false).comp φG
  | true => (ulift.symm.toMonoidHom : H →* twoFactorFamily G H true).comp φH

end Monoid.CoprodI

namespace Monoid.PushoutI

section

variable {A : Type u} {G : Type v} {H : Type w}
variable [Group A] [Group G] [Group H]
variable (φG : A →* G) (φH : A →* H)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "Maps" => twoFactorAmalgamatingMaps φG φH

/-- Bridge predicate for the two-factor pushout diagram determined by `φG` and `φH`.

This is not the chapter's main source-facing owner for Definition `4-2-9`; it is the generic
`Bool`-indexed helper that the subgroup specialization reuses. -/
abbrev TwoFactorReduced (w : Word Family) : Prop :=
  w.toList.length ≤ 1 ∨ Reduced Maps w

/-- For words of length greater than one, `TwoFactorReduced` is exactly the canonical condition
that no letter lies in the image of the base-group map. -/
theorem twoFactorReduced_iff_of_one_lt_length
    {w : Word Family}
    (hw : 1 < w.toList.length) :
    TwoFactorReduced φG φH w ↔ Reduced Maps w := by
  constructor
  · intro h
    rcases h with hlen | hred
    · omega
    · exact hred
  · intro h
    exact Or.inr h

end

end Monoid.PushoutI

namespace Subgroup

section

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {A : Subgroup G} {B : Subgroup H}

/-- The free product of `G` and `H` with the subgroups `A` and `B` amalgamated along `e`. -/
abbrev amalgamatedProductAlong (e : A ≃* B) : Type (max u v) :=
  PushoutI (twoFactorAmalgamatingMaps A.subtype (B.subtype.comp e.toMonoidHom))

namespace amalgamatedProductAlong

section

variable (e : A ≃* B)

local notation "Family" => Monoid.CoprodI.twoFactorFamily G H
local notation "P" => Subgroup.amalgamatedProductAlong e
local notation "ιA" => A.subtype
local notation "ιB" => B.subtype.comp e.toMonoidHom
local notation "Maps" => twoFactorAmalgamatingMaps ιA ιB

/-- Definition 4-2-9: a word in the free product of `G` and `H` with `A` and `B` amalgamated
along `e` is reduced when it is an alternating word in the two factors and either has length at
most one or, if it has length greater than one, every letter lies outside the amalgamated
subgroup in its factor.

The alternating nontrivial-word clauses are already carried by `Monoid.CoprodI.Word`; this
source-facing predicate only adds the textbook length-one exception on top of the canonical
owner-side predicate `Monoid.PushoutI.Reduced`. -/
abbrev Reduced (w : Word Family) : Prop :=
  TwoFactorReduced ιA ιB w

/-- For words of length greater than one, Definition `4-2-9` agrees with the canonical owner-side
predicate saying that no letter lies in the image of the amalgamated subgroup. -/
theorem reduced_iff_of_one_lt_length
    {w : Word Family}
    (hw : 1 < w.toList.length) :
    Reduced e w ↔ Monoid.PushoutI.Reduced Maps w := by
  simpa [Subgroup.amalgamatedProductAlong.Reduced] using
    Monoid.PushoutI.twoFactorReduced_iff_of_one_lt_length ιA ιB hw

/-- The canonical left embedding of `G` into `Subgroup.amalgamatedProductAlong e`. -/
abbrev left : G →* P :=
  (PushoutI.of false).comp (ulift.symm.toMonoidHom : G →* Family false)

/-- The canonical right embedding of `H` into `Subgroup.amalgamatedProductAlong e`. -/
abbrev right : H →* P :=
  (PushoutI.of true).comp (ulift.symm.toMonoidHom : H →* Family true)

/-- The canonical embedding of the amalgamated subgroup `A` into
`Subgroup.amalgamatedProductAlong e`. -/
abbrev base : A →* P :=
  PushoutI.base Maps

/-- Evaluate a reduced alternating word in the two-factor amalgamated product along `e`. -/
abbrev ofWord (w : Word Family) : P :=
  ofCoprodI w.prod

end

end amalgamatedProductAlong

end

end Subgroup
