/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_9.ch2_sec2_9_definition_2_42.FeasibleSet

public section

open scoped MixingNotation

/-!
Mixing set.

Definition 2.42 is formalized by the source-facing owner `Mixing.feasibleSet`, its scoped source
notation `MIX[b]`, together with the tuple bridge `Mixing.point` and the canonical membership
companions in the item-local foundation module `ch2_sec2_9_definition_2_42.FeasibleSet`.
-/

/- The canonical source-facing declarations for Definition 2.42 are the mixing-set owners below. -/
#check Mixing.point
#check Mixing.feasibleSet
#check Mixing.mem_feasibleSet_iff

variable {n : ℕ} (b : Fin n → ℝ)

/- With demand vector `b` fixed, the source notation for the mixing set is `MIX[b]`. -/
#check MIX[b]

/- Definition 2.42 (Mixing set for a make-or-buy problem): for a demand vector `b`, the canonical
owner `Mixing.feasibleSet b`, written `MIX[b]`, is the set of mixed points `Mixing.point x y`
with nonnegative production amount `y`, componentwise-nonnegative integral purchase vector `x`,
and covering constraints `b i ≤ y + x i` for every scenario `i`. This source-form membership
criterion is exactly `Mixing.point_mem_feasibleSet_iff`. -/
#check Mixing.point_mem_feasibleSet_iff

end
