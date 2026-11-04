/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

open scoped Pointwise

section Exercise_9_21

open MulAction

variable {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (S : Set (Fin n))

/- Exercise 9.21 is a `core/canonical` recall in the permutation-action domain.

The owner abstraction for the stabilizer of a subset is `MulAction.stabilizer`; the bundled
subgroup and its induced group structure are already provided upstream, with set-level supporting
API such as `mem_stabilizer_set` living in the pointwise stabilizer file. -/
recall MulAction.stabilizer
#check (stabilizer G S : Subgroup G)
#synth Group ↥(stabilizer G S)

end Exercise_9_21
