/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open CategoryTheory
open scoped FundamentalGroup

/-- Helper for Proposition 1.3.4: the isomorphism in the fundamental groupoid represented by the
reversed path is the inverse of the isomorphism represented by the original path. -/
lemma path_symm_iso_eq_inverse (a : Path x y) :
    ((Groupoid.isoEquivHom
      (FundamentalGroupoid.mk x)
      (FundamentalGroupoid.mk y)).symm ⟦a⟧).symm =
      (Groupoid.isoEquivHom
        (FundamentalGroupoid.mk y)
        (FundamentalGroupoid.mk x)).symm ⟦a.symm⟧ := by
  -- The quotient representatives are definitionally inverse after reversing the path.
  ext
  rfl

/-- Proposition 1.3.4: the inverse of the basepoint-change equivalence associated to a path
`a : Path x y` is the basepoint-change equivalence associated to the reversed path `a.symm`. -/
-- Proof sketch: `γ[a]` is conjugation by the isomorphism in the fundamental groupoid represented
-- by `a`. The inverse of that conjugation is conjugation by the inverse isomorphism, and the
-- inverse isomorphism is represented by the reversed path `a.symm`.
theorem fundamentalGroupMulEquivOfPath_symm (a : Path x y) :
    (γ[a]).symm = γ[a.symm] := by
  -- Replace conjugation by the inverse isomorphism with conjugation by the reversed path.
  simpa [FundamentalGroup.fundamentalGroupMulEquivOfPath] using
    congrArg Iso.conj (path_symm_iso_eq_inverse a)
