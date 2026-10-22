/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_10_6
import CombinatorialGroupTheory_Magnus_2004.Chap01.SignedLetter

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {X : Type u}

/- Definition 1-10-5 lies in Fox calculus for free groups.

Layer triage:
- `source-facing`: the coordinate Fox derivative with respect to a generator `x`.
- `core/canonical`: the chapter owner map `foxTriangularRepresentation X` and its coordinate
  `foxUniversalDifferential`.
- `bridge/view`: the explicit signed-letter formula `foxLetterDerivative` and the word-sum formula
  `foxDerivative_mk_eq_sum`.

Domain sampling:
1. `FreeGroup.lift` is mathlib's owner constructor for multiplicative maps out of a free group.
2. `FreeGroup.lift_mk` is the canonical word-level formula for such owner maps on displayed words.
3. `foxTriangularRepresentation` is the chapter owner Fox-calculus representation built from that
   constructor, and `foxUniversalDifferential` is its canonical differential coordinate.

Primitive vs. derived:
the primitive chapter owner data is `foxUniversalDifferential`; the source-facing coordinate is
its ordinary evaluation at `x`, while the explicit signed-letter and displayed-word formulas on
`SignedLetter X` and `List (SignedLetter X)` are derived API. This file should therefore avoid
owning a second public Fox-derivative owner parallel to that canonical differential.
-/

section

local notation "R" => FreeGroupRing X
local instance definition_1_10_5_decidableEq : DecidableEq X := Classical.decEq X

/-- The Fox derivative of a single signed letter with respect to the generator `x`. -/
def foxLetterDerivative (x : X) : SignedLetter X → R :=
  fun
  | (y, true) => if y = x then 1 else 0
  | (y, false) => if y = x then -MonoidAlgebra.of ℤ (FreeGroup X) ((FreeGroup.of y)⁻¹) else 0

/-- Definition 1-10-5: the Fox derivative of `w` with respect to the generator `x`, defined as the
`x`-coordinate of the universal Fox differential from Proposition `1-10-6`. -/
abbrev foxDerivative (x : X) (w : FreeGroup X) : R :=
  foxUniversalDifferential w x

/- Definition 1-10-5 is the coordinate Fox derivative `∂w / ∂x`. -/
#check foxDerivative

-- Proof sketch: induct on the list `word`; the empty word contributes `0`, and the inductive step
-- pulls out the first-letter term and multiplies the inductive sum for the suffix by the prefix
-- monomial represented by that first letter.
/-- The universal Fox differential of a displayed word is the sum of the derivatives of its
letters weighted by their preceding prefixes. -/
theorem foxUniversalDifferential_mk_eq_sum
    (word : List (SignedLetter X)) (x : X) :
    foxUniversalDifferential (FreeGroup.mk word) x =
      ∑ j : Fin word.length,
        MonoidAlgebra.of ℤ (FreeGroup X) (FreeGroup.mk (word.take j.val)) *
          foxLetterDerivative x (word.get j) := sorry

/-- The Fox derivative of a displayed word is the corresponding coordinate form of
`foxUniversalDifferential_mk_eq_sum`. -/
theorem foxDerivative_mk_eq_sum (word : List (SignedLetter X)) (x : X) :
    foxDerivative x (FreeGroup.mk word) =
      ∑ j : Fin word.length,
        MonoidAlgebra.of ℤ (FreeGroup X) (FreeGroup.mk (word.take j.val)) *
          foxLetterDerivative x (word.get j) := by
  simpa [foxDerivative] using foxUniversalDifferential_mk_eq_sum word x

end
