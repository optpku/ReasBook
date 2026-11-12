/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_proposition_2_8.DoubleBlocker

public section

namespace Clutter

universe u

variable {α : Type u} [DecidableEq α]
variable (E : Finset α) (S : Set (Finset α))

/- Proposition 2.8: if `S` is a clutter on the finite ground set `E`, then the blocker of the
blocker of `S` is `S`; this is the blocker involution theorem `Clutter.blocker_blocker_eq`. -/
#check
  (blocker_blocker_eq E S :
    IsClutterOn E S → blocker E (blocker E S) = S)

end Clutter
