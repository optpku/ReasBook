/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

import Mathlib.Data.Set.Basic

/- Proposition 1.4 [Pruning by infeasibility]

If `S ⊆ P` and `P = ∅`, then `S = ∅`. This item is canonical reuse of
`Set.subset_eq_empty`.
-/
#check Set.subset_eq_empty
