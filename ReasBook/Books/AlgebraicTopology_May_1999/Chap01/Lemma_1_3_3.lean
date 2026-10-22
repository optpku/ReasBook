/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x y z : X}

open CategoryTheory
open scoped FundamentalGroup

/-- Lemma 1.3.3: basepoint change along a composite path is the composite of the corresponding
basepoint-change equivalences, so `γ[b · a] = γ[b] ∘ γ[a]`. -/
-- Proof sketch: view `FundamentalGroup.fundamentalGroupMulEquivOfPath` as conjugation by the
-- corresponding morphism in the fundamental groupoid, identify the class of `a.trans b` with the
-- composite of the classes of `a` and `b`, and use functoriality of conjugation under
-- composition.
theorem fundamentalGroupMulEquivOfPath_trans (a : Path x y) (b : Path y z) :
    γ[a.trans b] = (γ[a]).trans (γ[b]) := by
  let α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk y :=
    (Groupoid.isoEquivHom _ _).symm ⟦a⟧
  let β : FundamentalGroupoid.mk y ≅ FundamentalGroupoid.mk z :=
    (Groupoid.isoEquivHom _ _).symm ⟦b⟧
  have hcomp : (Groupoid.isoEquivHom _ _).symm ⟦a.trans b⟧ = α ≪≫ β := by
    ext
    rfl
  ext f
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath, hcomp]
  change (α ≪≫ β).conj f = β.conj (α.conj f)
  exact Iso.trans_conj α β f
