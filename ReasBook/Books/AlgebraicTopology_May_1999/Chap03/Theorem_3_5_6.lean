/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_1
import AlgebraicTopology_May_1999.Chap03.Lemma_3_5_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable {p : E ⥤ B} {p' : E' ⥤ B}

/-- Theorem 3.5.6: for a connected groupoid `E`, a functor `p : E ⥤ B`, a covering functor
`p' : E' ⥤ B`, and chosen points `e` and `e'` of the fibers over the same base object `b`, there
exists a unique map of coverings
`h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom` with `h.left.toFunctor.obj e.1 = e'.1` exactly
when the image of the vertex group at `e.1` under `p` is contained in the image of the vertex
group at `e'.1` under `p'`, both viewed as subgroups of `π(B,b)`. -/
-- Proof sketch: specialize `existsUnique_lift_iff_mapVertexGroup_range_le` to the functor
-- `f := p` and the base object `e.1`, then package the resulting lift functor as a morphism in
-- `Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom`. The chosen point `e'` lies over `p.obj e.1 = b`,
-- so the subgroup condition is exactly the inclusion of `p(π(E,e.1))` into
-- `p'(π(E',e'.1))` inside `π(B,b)`.
theorem existsUnique_map_iff_mapVertexGroup_range_le
    [IsConnected E] (hp' : Functor.IsCovering p') (b : B)
    (e : p.Fiber b) (e' : p'.Fiber b) :
    (∃! h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom,
      let g : E ⥤ E' := h.left.toFunctor
      g.obj e.1 = e'.1) ↔
      e.2 ▸ (Functor.mapVertexGroup p e.1).range ≤
        e'.2 ▸ (Functor.mapVertexGroup p' e'.1).range := by
  rcases e with ⟨e, rfl⟩
  constructor
  · rintro ⟨h, hh, huniq⟩
    refine (existsUnique_lift_iff_mapVertexGroup_range_le hp' e e').mp ?_
    refine ⟨h.left.toFunctor, ?_, ?_⟩
    · refine ⟨?_, by simpa using hh⟩
      simpa using congrArg (fun F ↦ F.toFunctor) (Over.w h)
    · intro g hg
      have hhg :
          Over.homMk g.toCatHom (by simpa using congrArg Functor.toCatHom hg.1) = h :=
        huniq (Over.homMk g.toCatHom (by simpa using congrArg Functor.toCatHom hg.1))
          (by simpa using hg.2)
      simpa using congrArg (fun k ↦ k.left.toFunctor) hhg
  · intro hsub
    rcases (existsUnique_lift_iff_mapVertexGroup_range_le hp' e e').mpr hsub with
      ⟨g, hg, huniq⟩
    refine ⟨Over.homMk g.toCatHom (by simpa using congrArg Functor.toCatHom hg.1), ?_, ?_⟩
    · simpa using hg.2
    · intro h hh
      apply Over.OverMorphism.ext
      simpa using congrArg Functor.toCatHom <|
        huniq h.left.toFunctor
          ⟨by simpa using congrArg (fun F ↦ F.toFunctor) (Over.w h), by simpa using hh⟩

/-- Companion for Theorem 3.5.6: for connected total groupoids `E` and `E'`, a map of coverings
`h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom` over `B` sending `e` to `e'` is an isomorphism of
coverings exactly when the image subgroups `p(π(E,e.1))` and `p'(π(E',e'.1))` coincide inside
`π(B,b)`. -/
-- Proof sketch: if `h` is an isomorphism, use the induced inverse map of coverings and
-- part (1) in both directions to obtain the two subgroup inclusions. Conversely,
-- equality gives a reverse map of coverings from part (1). Here `E'` is connected
-- because it is preconnected and `e'.1` provides an object of `E'`.
-- Uniqueness of lifts then shows that the two composites are
-- identities, so `h` is an isomorphism in the over-category.
theorem isIso_map_iff_mapVertexGroup_range_eq
    [IsConnected E] [IsPreconnected E']
    (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p') (b : B)
    (e : p.Fiber b) (e' : p'.Fiber b)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom)
    (hh : let g : E ⥤ E' := h.left.toFunctor
      g.obj e.1 = e'.1) :
    IsIso h ↔
      e.2 ▸ (Functor.mapVertexGroup p e.1).range =
        e'.2 ▸ (Functor.mapVertexGroup p' e'.1).range := by
  rcases e with ⟨e, rfl⟩
  constructor
  · intro hIso
    letI := hIso
    letI : Nonempty E' := ⟨e'.1⟩
    letI : IsConnected E' := { toIsPreconnected := inferInstance }
    let hF : E ⥤ E' := h.left.toFunctor
    let gF : E' ⥤ E := (CategoryTheory.inv h).left.toFunctor
    have hhF : hF.obj e = e'.1 := by
      simpa [hF] using hh
    -- The inverse over-morphism sends the chosen target point back to the chosen source point.
    have hgF : gF.obj e'.1 = e := by
      have hcomp : h ≫ CategoryTheory.inv h = 𝟙 _ := by
        simp
      have hpoint : gF.obj (hF.obj e) = e := by
        exact congrArg
          (fun k : Over.mk p.toCatHom ⟶ Over.mk p.toCatHom ↦
            k.left.toFunctor.obj e) hcomp
      simpa [hF, gF, hhF] using hpoint
    -- Apply the lifting criterion to `h`.
    have hhOver : hF ⋙ p' = p := by
      simpa [hF] using congrArg (fun F ↦ F.toFunctor) (Over.w h)
    have hle :
        (Functor.mapVertexGroup p e).range ≤
          e'.2 ▸ (Functor.mapVertexGroup p' e'.1).range :=
      Functor.mapVertexGroup_range_le_of_lift
        (p := p') (f := p) (g := hF) e e' hhOver hhF
    -- Apply the same criterion to the inverse morphism.
    have hgOver : gF ⋙ p = p' := by
      simpa [gF] using congrArg (fun F ↦ F.toFunctor) (Over.w (CategoryTheory.inv h))
    have hle'₀ :
        (Functor.mapVertexGroup p' e'.1).range ≤
          e'.2.symm ▸ (Functor.mapVertexGroup p e).range :=
      Functor.mapVertexGroup_range_le_of_lift
        (p := p) (f := p') (g := gF) e'.1 ⟨e, e'.2.symm⟩ hgOver hgF
    have hle' :
        e'.2 ▸ (Functor.mapVertexGroup p' e'.1).range ≤
          (Functor.mapVertexGroup p e).range := by
      intro γ hγ
      have hγ' :
          eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm ∈
            (Functor.mapVertexGroup p' e'.1).range := by
        exact (mapVertexGroup_range_transport_iff e'.2 γ).1 hγ
      have hγ'' :
          eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm ∈
            e'.2.symm ▸ (Functor.mapVertexGroup p e).range :=
        hle'₀ hγ'
      have hγ''' :
          eqToHom e'.2.symm ≫
              (eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm) ≫
              eqToHom e'.2 ∈
            (Functor.mapVertexGroup p e).range := by
        exact
          (mapVertexGroup_range_transport_iff e'.2.symm
            (eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm)).1 hγ''
      simpa [Category.assoc] using hγ'''
    exact le_antisymm hle hle'
  · intro hEq
    letI : Nonempty E' := ⟨e'.1⟩
    letI : IsConnected E' := { toIsPreconnected := inferInstance }
    obtain ⟨g, hg, _huniqg⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p') (p' := p) hp (p.obj e) e' ⟨e, rfl⟩).2 hEq.symm.le
    let hF : E ⥤ E' := h.left.toFunctor
    let gF : E' ⥤ E := g.left.toFunctor
    have hhF : hF.obj e = e'.1 := by
      simpa [hF] using hh
    have hgF : gF.obj e'.1 = e := by
      simpa [gF] using hg
    -- The source-side composite fixes the chosen source point, so uniqueness forces identity.
    let hgFcomp : E ⥤ E := (h ≫ g).left.toFunctor
    have hhg : hgFcomp.obj e = e := by
      change gF.obj (hF.obj e) = e
      simpa [hhF] using hgF
    obtain ⟨_, _, huniqk⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p) (p' := p) hp (p.obj e) ⟨e, rfl⟩ ⟨e, rfl⟩).2 le_rfl
    have h_comp_g : h ≫ g = 𝟙 _ :=
      (huniqk (h ≫ g) (by simpa [hgFcomp] using hhg)).trans (huniqk (𝟙 _) rfl).symm
    -- The target-side composite fixes the chosen target point, so uniqueness gives the other identity.
    let ghFcomp : E' ⥤ E' := (g ≫ h).left.toFunctor
    have hgh : ghFcomp.obj e'.1 = e'.1 := by
      change hF.obj (gF.obj e'.1) = e'.1
      simpa [hgF] using hhF
    obtain ⟨_, _, huniqk'⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p') (p' := p') hp' (p.obj e) e' e').2 le_rfl
    have g_comp_h : g ≫ h = 𝟙 _ :=
      (huniqk' (g ≫ h) (by simpa [ghFcomp] using hgh)).trans (huniqk' (𝟙 _) rfl).symm
    exact ⟨⟨g, h_comp_g, g_comp_h⟩⟩

end CategoryTheory.Functor.IsCovering
