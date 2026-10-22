/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open CategoryTheory FundamentalGroupoidFunctor
open scoped ContinuousMap
open scoped FundamentalGroup

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]

/-- Proposition 1.4.4: if `H : p.Homotopy q`, then the induced maps on fundamental groups commute
with basepoint change along the track `H.evalAt x`, so `γ[H.evalAt x] ∘ p_* = q_*`. -/
-- Proof sketch: use the natural isomorphism on fundamental groupoids induced by a homotopy,
-- evaluate its naturality square at the object `x`, and read the resulting equality on
-- endomorphism groups as conjugation by the path `H.evalAt x`.
theorem fundamental_group_map_homotopy_commutes (p q : C(X, Y)) (H : p.Homotopy q) (x : X) :
    ((γ[H.evalAt x]).toMonoidHom.comp (FundamentalGroup.map p x)) =
      FundamentalGroup.map q x := by
  let e : FundamentalGroupoid.mk (p x) ≅ FundamentalGroupoid.mk (q x) :=
    (Groupoid.isoEquivHom _ _).symm ⟦H.evalAt x⟧
  ext α
  change e.conj ((FundamentalGroupoid.map p).map α) = (FundamentalGroupoid.map q).map α
  have hnat :
      (FundamentalGroupoid.map p).map α ≫ e.hom =
        e.hom ≫ (FundamentalGroupoid.map q).map α := by
    simpa [e, FundamentalGroupoidFunctor.homotopicMapsNatIso] using
      NatTrans.naturality (homotopicMapsNatIso H) α
  have hconj :
      (FundamentalGroupoid.map q).map α =
        e.inv ≫ ((FundamentalGroupoid.map p).map α ≫ e.hom) :=
    (e.eq_inv_comp).2 hnat.symm
  simpa [Iso.conj_apply, Category.assoc] using hconj.symm
