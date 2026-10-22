/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_10_5
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_10_6

universe u

noncomputable section

variable {X : Type u}

/- Definition 1-10-7 lies in Fox calculus for free groups.

Layer triage:
- `source-facing`: the Fox differential `dw` and the second Magnus representation of `FreeGroup X`.
- `core/canonical`: `foxDifferentialModule X`, `foxUniversalDifferential`,
  `foxTriangularRepresentationTarget X`, and `foxTriangularRepresentation`.
- `bridge/view`: the coordinate word formula from Definition `1-10-5`, expressing
  `foxUniversalDifferential (FreeGroup.mk word) x` as the signed-letter sum over the displayed
  word.

Domain sampling:
1. `foxDifferentialModule` is the owner module for Fox differentials.
2. `foxUniversalDifferential` is its canonical differential coordinate.
3. `foxTriangularRepresentation` is the canonical triangular owner map.
4. `foxTriangularRepresentation_eq_pair` and `foxTriangularRepresentation_injective` provide the
   textbook coordinate description and faithfulness.

Primitive vs. derived:
the primitive owner data is the semidirect-product representation `foxTriangularRepresentation`;
the coordinate descriptions of `dw` are derived API. -/

-- Proof sketch: `foxTriangularRepresentation 1 = 1`, so its left coordinate is the additive
-- identity of the Fox differential module.
/-- The universal Fox differential of the identity element is zero. -/
theorem foxUniversalDifferential_one :
    foxUniversalDifferential (1 : FreeGroup X) = 0 := by
  simp [foxUniversalDifferential]

-- Proof sketch: compare the left coordinates in the multiplicativity of
-- `foxTriangularRepresentation X`; semidirect-product multiplication gives the additive product
-- rule.
/-- The universal Fox differential satisfies the Fox product rule `d(uv) = du + u · dv`. -/
theorem foxUniversalDifferential_mul (u v : FreeGroup X) :
    foxUniversalDifferential (u * v) =
      foxUniversalDifferential u + u • foxUniversalDifferential v := by
  apply Additive.toMul.injective
  change (foxTriangularRepresentation X (u * v)).left =
    Additive.toMul (foxUniversalDifferential u + u • foxUniversalDifferential v)
  rw [map_mul, foxTriangularRepresentation_eq_pair u, foxTriangularRepresentation_eq_pair v]
  rfl

/- Definition 1-10-7: the second Magnus representation is the canonical Fox triangular
representation of the free group. -/
#check foxTriangularRepresentation

/- In source coordinates, the canonical triangular representation sends `w` to `(dw, w)`. -/
#check (foxTriangularRepresentation_eq_pair :
  ∀ w : FreeGroup X,
    foxTriangularRepresentation X w =
      (⟨Additive.toMul (foxUniversalDifferential w), w⟩ :
        foxTriangularRepresentationTarget X))

/- The second Magnus representation is faithful. -/
#check foxTriangularRepresentation_injective
