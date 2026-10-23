module

public import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

/- Domain-style sampling for Lemma 4.14.10:
- primary domain: categorical Fubini theorems for limits and colimits of bifunctors.
- sampled owner abstractions in `Mathlib.CategoryTheory.Limits.Fubini`:
  `DiagramOfCocones` / `DiagramOfCones`,
  `DiagramOfCocones.coconePoints` / `DiagramOfCones.conePoints`,
  `coconeOfCoconeUncurryIsColimit` / `coneOfConeUncurryIsLimit`,
  `DiagramOfCocones.mkOfHasColimits` / `DiagramOfCones.mkOfHasLimits`,
  `colimitIsoColimitCurryCompColim` / `limitIsoLimitCurryCompLim`.

Primitive-vs-derived split:
- primitive data: a chosen diagram `D : DiagramOfCocones (curry.obj M)` or
  `D : DiagramOfCones (curry.obj M)` together with the rowwise `IsColimit` / `IsLimit`
  witnesses `∀ i, IsColimit (D.obj i)` or `∀ i, IsLimit (D.obj i)`.
- derived API: the induced source-facing functors `D.coconePoints` and `D.conePoints`, the
  existence equivalences below, the rowwise coincidence isomorphisms for colimits and limits, and
  the canonical `⋙ colim` / `⋙ lim` specializations under stronger global assumptions.

Source/core/bridge triage:
- `source-facing`: a chosen rowwise colimit system for one bifunctor and the resulting functor of
  cocone points; dually, a chosen rowwise limit system and the resulting functor of cone points.
- `core/canonical`: the mathlib Fubini comparison isomorphisms and their cocone/cone
  constructions.
- `bridge/view`: the `curry.obj M ⋙ colim` and `curry.obj M ⋙ lim` specializations obtained from
  `DiagramOfCocones.mkOfHasColimits` and `DiagramOfCones.mkOfHasLimits`. -/

section

variable (M : I × J ⥤ C)

/-- Lemma 4.14.10: for a chosen diagram `D` of rowwise colimit cocones of a bifunctor `M`, the
resulting functor `D.coconePoints` has a colimit if and only if `M` has a colimit. -/
lemma hasColimit_coconePoints_iff_hasColimit (D : DiagramOfCocones (curry.obj M))
    (Q : ∀ i, IsColimit (D.obj i)) : HasColimit D.coconePoints ↔ HasColimit M := by
  constructor
  · intro h
    let _ := h
    let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
    let cM : Cocone M :=
      { pt := colimit D.coconePoints
        ι :=
          { app x := (D.obj x.1).ι.app x.2 ≫ colimit.ι D.coconePoints x.1
            naturality {x y} := fun ⟨f₁, f₂⟩ ↦ by
              have hrow := (D.obj y.1).w f₂
              have hmap := (D.map f₁).w x.2
              have hw := colimit.w D.coconePoints f₁
              dsimp [DiagramOfCocones.coconePoints] at hrow hmap hw ⊢
              simpa [DiagramOfCocones.coconePoints] using
                (calc
                  M.map (f₁, f₂) ≫ (D.obj y.1).ι.app y.2 ≫ colimit.ι D.coconePoints y.1
                      = M.map (Prod.mkHom f₁ (𝟙 x.2)) ≫
                          (M.map (Prod.mkHom (𝟙 y.1) f₂) ≫ (D.obj y.1).ι.app y.2) ≫
                            colimit.ι D.coconePoints y.1 := by
                          simp only [Prod.fac' (f₁, f₂), M.map_comp, Category.assoc]
                  _ = M.map (Prod.mkHom f₁ (𝟙 x.2)) ≫ (D.obj y.1).ι.app x.2 ≫
                        colimit.ι D.coconePoints y.1 := by
                          simpa [Category.assoc] using congrArg
                            (fun z ↦ M.map (Prod.mkHom f₁ (𝟙 x.2)) ≫ z ≫
                              colimit.ι D.coconePoints y.1)
                            hrow
                  _ = (D.obj x.1).ι.app x.2 ≫ (D.map f₁).hom ≫ colimit.ι D.coconePoints y.1 := by
                        simpa [Category.assoc] using congrArg
                          (fun z ↦ z ≫ colimit.ι D.coconePoints y.1)
                          hmap.symm
                  _ = (D.obj x.1).ι.app x.2 ≫ colimit.ι D.coconePoints x.1 ≫ 𝟙 _ := by
                        have hw' := congrArg ((D.obj x.1).ι.app x.2 ≫ ·) hw
                        simpa only [Category.comp_id, Category.assoc] using hw') } }
    let c : Cocone (uncurry.obj (curry.obj M)) :=
      (Cocone.precompose e.inv).obj cM
    let S : ∀ i, Cocone ((curry.obj M).obj i) := fun i ↦
      { pt := colimit D.coconePoints
        ι :=
          { app j := c.ι.app (i, j)
            naturality {j j'} f := by
              simpa using @NatTrans.naturality _ _ _ _ _ _ c.ι (i, j) (i, j') (𝟙 i, f) } }
    have hcocone : IsColimit (coconeOfCoconeUncurry Q c) := by
      let hico : coconeOfCoconeUncurry Q c ≅ colimit.cocone D.coconePoints :=
        Cocone.ext (Iso.refl (colimit D.coconePoints)) fun i ↦ by
          apply (Q i).hom_ext
          intro j
          simpa [S, c, cM, e, coconeOfCoconeUncurry] using
            (Q i).fac (S i) j
      exact IsColimit.ofIsoColimit (colimit.isColimit D.coconePoints) hico.symm
    have hc : IsColimit c := by
      apply IsColimit.ofCoconeUncurry Q
      exact hcocone
    let _ : HasColimit (uncurry.obj (curry.obj M)) := ⟨⟨c, hc⟩⟩
    exact hasColimit_of_iso e
  · intro h
    let _ := h
    let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
    let c : Cocone (uncurry.obj (curry.obj M)) := (Cocone.precompose e.inv).obj (colimit.cocone M)
    have hc : IsColimit c :=
      (IsColimit.precomposeInvEquiv e (colimit.cocone M)).symm (colimit.isColimit M)
    exact ⟨⟨coconeOfCoconeUncurry Q c, coconeOfCoconeUncurryIsColimit Q hc⟩⟩

/-- Under the hypotheses of Lemma 4.14.10, the colimit of the rowwise-colimit functor
`D.coconePoints` is canonically isomorphic to the colimit of `M`. -/
noncomputable def colimitCoconePointsIsoColimit (D : DiagramOfCocones (curry.obj M))
    (Q : ∀ i, IsColimit (D.obj i)) [HasColimit D.coconePoints] [HasColimit M] :
    colimit D.coconePoints ≅ colimit M :=
  let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
  let c : Cocone (uncurry.obj (curry.obj M)) := (Cocone.precompose e.inv).obj (colimit.cocone M)
  let hc : IsColimit c :=
    (IsColimit.precomposeInvEquiv e (colimit.cocone M)).symm (colimit.isColimit M)
  colimit.isoColimitCocone
    ⟨coconeOfCoconeUncurry Q c, coconeOfCoconeUncurryIsColimit Q hc⟩

/-- Bridge specialization of Lemma 4.14.10: when all `J`-indexed rowwise colimits exist in `C`,
the source-facing functor `D.coconePoints` is canonically `curry.obj M ⋙ colim`. -/
lemma hasColimit_curryCompColim_iff_hasColimit [HasColimitsOfShape J C] :
    HasColimit (curry.obj M ⋙ colim) ↔ HasColimit M := by
  simpa [DiagramOfCocones.mkOfHasColimits_coconePoints] using
    hasColimit_coconePoints_iff_hasColimit M (DiagramOfCocones.mkOfHasColimits (curry.obj M))
      fun i ↦ colimit.isColimit _

end

section

variable (M : I × J ⥤ C)

/-- Dual companion to Lemma 4.14.10: for a chosen diagram `D` of rowwise limit cones of a
bifunctor `M`, the resulting functor `D.conePoints` has a limit if and only if `M` has a
limit. -/
lemma hasLimit_conePoints_iff_hasLimit (D : DiagramOfCones (curry.obj M))
    (Q : ∀ i, IsLimit (D.obj i)) : HasLimit D.conePoints ↔ HasLimit M := by
  constructor
  · intro h
    let _ := h
    let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
    let cM : Cone M :=
      { pt := limit D.conePoints
        π :=
          { app x := limit.π D.conePoints x.1 ≫ (D.obj x.1).π.app x.2
            naturality {x y} := fun ⟨f₁, f₂⟩ ↦ by
              have hrow := (D.obj x.1).w f₂
              have hmap := (D.map f₁).w y.2
              have hw := limit.w D.conePoints f₁
              dsimp [DiagramOfCones.conePoints] at hrow hmap hw ⊢
              rw [← hw, Category.assoc, hmap, ← hrow]
              simp only [Category.id_comp, Category.assoc, Prod.fac (f₁, f₂), M.map_comp] } }
    let c : Cone (uncurry.obj (curry.obj M)) :=
      (Cone.postcompose e.hom).obj cM
    let S : ∀ i, Cone ((curry.obj M).obj i) := fun i ↦
      { pt := limit D.conePoints
        π :=
          { app j := c.π.app (i, j)
            naturality {j j'} f := by
              simpa using @NatTrans.naturality _ _ _ _ _ _ c.π (i, j) (i, j') (𝟙 i, f) } }
    have hcone : IsLimit (coneOfConeUncurry Q c) := by
      let hiso : coneOfConeUncurry Q c ≅ limit.cone D.conePoints :=
        Cone.ext (Iso.refl (limit D.conePoints)) fun i ↦ by
          apply (Q i).hom_ext
          intro j
          simpa [S, c, cM, e, coneOfConeUncurry] using (Q i).fac (S i) j
      exact IsLimit.ofIsoLimit (limit.isLimit D.conePoints) hiso.symm
    have hc : IsLimit c := by
      apply IsLimit.ofConeOfConeUncurry Q
      exact hcone
    let _ : HasLimit (uncurry.obj (curry.obj M)) := ⟨⟨c, hc⟩⟩
    exact hasLimit_of_iso e.symm
  · intro h
    let _ := h
    let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
    let c : Cone (uncurry.obj (curry.obj M)) := (Cone.postcompose e.hom).obj (limit.cone M)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv e (limit.cone M)).symm (limit.isLimit M)
    exact ⟨⟨coneOfConeUncurry Q c, coneOfConeUncurryIsLimit Q hc⟩⟩

/-- Dual bridge specialization of Lemma 4.14.10: when all `J`-indexed rowwise limits exist in `C`,
the source-facing functor `D.conePoints` is canonically `curry.obj M ⋙ lim`. -/
lemma hasLimit_curryCompLim_iff_hasLimit [HasLimitsOfShape J C] :
    HasLimit (curry.obj M ⋙ lim) ↔ HasLimit M := by
  simpa [DiagramOfCones.mkOfHasLimits_conePoints] using
    hasLimit_conePoints_iff_hasLimit M (DiagramOfCones.mkOfHasLimits (curry.obj M))
      fun i ↦ limit.isLimit _

/-- Under the hypotheses of Lemma 4.14.10, the limit of the rowwise-limit functor
`D.conePoints` is canonically isomorphic to the limit of `M`. -/
noncomputable def limitConePointsIsoLimit (D : DiagramOfCones (curry.obj M))
    (Q : ∀ i, IsLimit (D.obj i)) [HasLimit D.conePoints] [HasLimit M] :
    limit D.conePoints ≅ limit M :=
  let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
  let c : Cone (uncurry.obj (curry.obj M)) := (Cone.postcompose e.hom).obj (limit.cone M)
  let hc : IsLimit c := (IsLimit.postcomposeHomEquiv e (limit.cone M)).symm (limit.isLimit M)
  limit.isoLimitCone ⟨coneOfConeUncurry Q c, coneOfConeUncurryIsLimit Q hc⟩

end

/- Companion recall: when both colimits exist, the canonical comparison isomorphism identifying the
total colimit of `M` with the iterated colimit `colimit (curry.obj M ⋙ colim)` is
`colimitIsoColimitCurryCompColim`. -/
recall colimitIsoColimitCurryCompColim

/- Companion recall: when both iterated colimits exist, the canonical comparison isomorphism
`colimitCurrySwapCompColimIsoColimitCurryCompColim` identifies the two orders of iterated colimit,
corresponding to the textbook equality
`colim_i colim_j M_{i,j} = colim_j colim_i M_{i,j}` up to canonical isomorphism. -/
recall colimitCurrySwapCompColimIsoColimitCurryCompColim

/- Dual companion recall: the canonical limit comparison identifying the limit of `M` with the
iterated limit `limit (curry.obj M ⋙ lim)` is `limitIsoLimitCurryCompLim`. -/
recall limitIsoLimitCurryCompLim

/- Dual companion recall: the canonical comparison
`limitCurrySwapCompLimIsoLimitCurryCompLim` identifies the two orders of iterated limit. -/
recall limitCurrySwapCompLimIsoLimitCurryCompLim

end CategoryTheory.Limits
