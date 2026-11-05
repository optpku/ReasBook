/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_16.Blocker

public section

namespace Blocker

open Clutter

universe u

variable {α : Type u} [DecidableEq α]
variable (E : Finset α) (S : Set (Finset α)) {T : Finset α}

/- Definition 2.16 (1): the textbook notion of a transversal of a finite set family on the ground
set `E` is formalized by `Clutter.IsTransversal E S`. -/
#check (IsTransversal E S : Finset α → Prop)

/-- Unfolding `Clutter.IsTransversal E S` recovers the textbook condition: `T` lies in `E` and
meets every member `U ∈ S`. -/
theorem isTransversal_iff :
    IsTransversal E S T ↔ T ⊆ E ∧ ∀ U ∈ S, (T ∩ U).Nonempty := by
  simpa [Finset.inter_comm] using
    (Clutter.isTransversal_iff :
      IsTransversal E S T ↔ T ⊆ E ∧ ∀ U ∈ S, (U ∩ T).Nonempty)

/- Definition 2.16 (2): the blocker of `S` over `E` is the family `Clutter.blocker E S` of all
inclusionwise minimal transversals. -/
#check (blocker E S : Set (Finset α))

/- Membership in `Clutter.blocker E S` is exactly inclusionwise minimal transversality. -/
#check
  (mem_blocker_iff :
    T ∈ blocker E S ↔ Minimal (fun U ↦ IsTransversal E S U) T)

/- Definition 2.16 (3): the blocker of a finite set family is a clutter on the same ground set. -/
#check (blocker_isClutterOn E S : IsClutterOn E (blocker E S))

end Blocker
