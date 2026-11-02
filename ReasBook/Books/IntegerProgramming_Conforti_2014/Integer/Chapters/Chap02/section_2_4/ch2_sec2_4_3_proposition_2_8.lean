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
