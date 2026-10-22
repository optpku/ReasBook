/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_11
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable {p : E ⥤ B} {p' : E' ⥤ B} {e : E}
variable [IsConnected E]

/-- Corollary 3.5.7 (1): a connected universal covering functor over the base object `p.obj e`
maps uniquely to every covering functor over `B` once a point of the target fiber over `p.obj e`
is chosen. -/
-- Proof sketch: apply `existsUnique_map_iff_mapVertexGroup_range_le` with
-- `(Functor.mapVertexGroup p e).range = ⊥`; the needed subgroup inclusion is `⊥ ≤ H` for any
-- target subgroup `H`.
theorem universalCovering_existsUnique_map_to_covering
    (hp : Functor.IsUniversalCovering p e) (hp' : Functor.IsCovering p')
    (e' : p'.Fiber (p.obj e)) :
    ∃! h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom,
      let g : E ⥤ E' := h.left.toFunctor
      g.obj e = e'.1 := by
  simpa using
    (existsUnique_map_iff_mapVertexGroup_range_le
      hp' (p.obj e) ⟨e, rfl⟩ e').2 <|
      by
        rw [hp.mapVertexGroup_range_eq_bot]
        exact bot_le

/- Corollary 3.5.7 (2): if the target covering is also universal at the chosen fiber point, then
every point-preserving map of coverings over `B` is an isomorphism of coverings, provided the
target total groupoid is preconnected. -/
-- Proof sketch: if `p'` is also universal at `e'.1`, then both image subgroups in
-- `isIso_map_iff_mapVertexGroup_range_eq` are trivial, so the subgroup equality criterion
-- implies that any point-preserving map of coverings is an isomorphism.
theorem universalCovering_map_isIso_of_target_isUniversal
    [IsPreconnected E']
    (hp : Functor.IsUniversalCovering p e)
    (e' : p'.Fiber (p.obj e)) (hp'univ : Functor.IsUniversalCovering p' e'.1)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom)
    (hh : let g : E ⥤ E' := h.left.toFunctor
      g.obj e = e'.1) :
    IsIso h := by
  letI : Nonempty E' := ⟨e'.1⟩
  letI : IsConnected E' := { toIsPreconnected := inferInstance }
  obtain ⟨g, hg, _huniqg⟩ :=
    universalCovering_existsUnique_map_to_covering
      hp'univ hp.isCovering ⟨e, e'.2.symm⟩
  let hF : E ⥤ E' := h.left.toFunctor
  let gF : E' ⥤ E := g.left.toFunctor
  have hhF : hF.obj e = e'.1 := by
    simpa [hF] using hh
  have hgF : gF.obj e'.1 = e := by
    simpa [gF] using hg
  let hgFcomp : E ⥤ E := (h ≫ g).left.toFunctor
  have hhg : hgFcomp.obj e = e := by
    change gF.obj (hF.obj e) = e
    simpa [hhF] using hgF
  let ghFcomp : E' ⥤ E' := (g ≫ h).left.toFunctor
  have hgh : ghFcomp.obj e'.1 = e'.1 := by
    change hF.obj (gF.obj e'.1) = e'.1
    simpa [hgF] using hhF
  obtain ⟨_, _, huniqk⟩ :=
    universalCovering_existsUnique_map_to_covering hp hp.isCovering ⟨e, rfl⟩
  have h_comp_g : h ≫ g = 𝟙 _ :=
    (huniqk (h ≫ g) (by simpa [hgFcomp] using hhg)).trans (huniqk (𝟙 _) rfl).symm
  obtain ⟨_, _, huniqk'⟩ :=
    universalCovering_existsUnique_map_to_covering hp'univ hp'univ.isCovering ⟨e'.1, rfl⟩
  have g_comp_h : g ≫ h = 𝟙 _ :=
    (huniqk' (g ≫ h) (by simpa [ghFcomp] using hgh)).trans (huniqk' (𝟙 _) rfl).symm
  exact ⟨⟨g, h_comp_g, g_comp_h⟩⟩

end CategoryTheory.Functor.IsCovering
