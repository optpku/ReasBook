module

public import stacks_project.Chap04.Lemma_4_36_4.Strictification.Fiber

@[expose] public section

universe v₁ v₂ v₃ vS u₁ u₂ u₃ w

namespace CategoryTheory

open Bicategory
open BasedFunctor
open Functor
open Fiber
open Opposite
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/-- Helper for Lemma 4.36.4: reindexing along `g` defines a functor between the strict fibers. -/
noncomputable def pullbackStrictificationReindex
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (g : V ⟶ U) :
    PullbackStrictificationFiber p hc U ⥤ PullbackStrictificationFiber p hc V where
  obj := pullbackStrictificationReindexObj p hc g
  map := pullbackStrictificationReindexMap p hc g
  map_id := pullbackStrictificationReindexMap_id p hc g
  map_comp := pullbackStrictificationReindexMap_comp p hc g

/-- Helper for Lemma 4.36.4: reindexing along the identity in the strict model is the identity
functor on each strict fiber. -/
theorem pullback_strictification_functor_map_id
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (U : Cᵒᵖ) :
    (pullbackStrictificationReindex p hc (𝟙 (unop U))).toCatHom =
      𝟙 (Cat.of (PullbackStrictificationFiber p hc (unop U))) := by
  -- Route correction: identify the object transports explicitly, then use the naturality of the
  -- identity-pullback comparison to rewrite the map part into the `Functor.ext` target.
  apply CategoryTheory.Cat.ext
  refine CategoryTheory.Functor.ext
    (fun X ↦ pullback_strictification_reindex_obj_id p hc (unop U) X) ?_
  intro X Y φ
  change pullbackStrictificationReindexMap p hc (𝟙 (unop U)) φ =
    eqToHom
        (congrArg (pullbackStrictificationFiberForget p hc (unop U))
          (pullback_strictification_reindex_obj_id p hc (unop U) X)) ≫
      φ ≫
      eqToHom
        (congrArg (pullbackStrictificationFiberForget p hc (unop U))
          (pullback_strictification_reindex_obj_id p hc (unop U) Y)).symm
  -- After rewriting the transports, the only input is naturality of `hc.pullbackIdIso`.
  cases X with
  | mk targetX arrowX fiberObjX =>
      cases Y with
      | mk targetY arrowY fiberObjY =>
          change pullbackStrictificationReindexMap p hc (𝟙 (unop U)) φ =
            eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj fiberObjX)
                (Category.id_comp arrowX)) ≫
              φ ≫
              eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj fiberObjY)
                (Category.id_comp arrowY)).symm
          rw [pullback_strictification_id_eqToHom (p := p) (hc := hc) (f := arrowX) (x := fiberObjX)]
          dsimp [pullbackStrictificationReindexMap]
          let αX :=
            (hc.pullbackCompIso arrowX (𝟙 (unop U))).hom.app fiberObjX
          let βX :=
            (hc.pullbackIdIso (unop U)).inv.app ((hc.pullbackFunctor arrowX).obj fiberObjX)
          let βY :=
            (hc.pullbackIdIso (unop U)).inv.app ((hc.pullbackFunctor arrowY).obj fiberObjY)
          let γY :=
            (hc.pullbackIdIso (unop U)).hom.app ((hc.pullbackFunctor arrowY).obj fiberObjY)
          let δY :=
            (hc.pullbackCompIso arrowY (𝟙 (unop U))).inv.app fiberObjY
          have htarget :
              eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj fiberObjY)
                (Category.id_comp arrowY)).symm =
                γY ≫ δY := by
            simpa [γY, δY] using
              (pullback_strictification_id_eqToHom_symm
                (p := p) (hc := hc) (f := arrowY) (x := fiberObjY))
          have hcancel : βY ≫ γY ≫ δY = δY := by
            simpa [βY, γY, δY, Category.assoc] using
              Iso.inv_hom_id_assoc
                ((hc.pullbackIdIso (unop U)).app ((hc.pullbackFunctor arrowY).obj fiberObjY))
                ((hc.pullbackCompIso arrowY (𝟙 (unop U))).inv.app fiberObjY)
          have hnat :
              (hc.pullbackFunctor (𝟙 (unop U))).map φ ≫ βY = βX ≫ φ := by
            simpa [βX, βY] using
              ((hc.pullbackIdIso (unop U)).inv.naturality φ)
          calc
            αX ≫ (hc.pullbackFunctor (𝟙 (unop U))).map φ ≫ δY
                = αX ≫ ((hc.pullbackFunctor (𝟙 (unop U))).map φ ≫ βY ≫ γY ≫ δY) := by
                    simpa [Category.assoc] using
                      congrArg (fun k ↦ αX ≫ (hc.pullbackFunctor (𝟙 (unop U))).map φ ≫ k)
                        hcancel.symm
            _ = αX ≫ ((hc.pullbackFunctor (𝟙 (unop U))).map φ ≫ βY) ≫ γY ≫ δY := by
                    simp [Category.assoc]
            _ = αX ≫ (βX ≫ φ) ≫ γY ≫ δY := by
                    exact congrArg (fun k ↦ αX ≫ k ≫ γY ≫ δY) hnat
            _ = αX ≫ βX ≫ φ ≫ γY ≫ δY := by
                    simp [Category.assoc]
            _ = (αX ≫ βX) ≫ φ ≫ (γY ≫ δY) := by
                    simp [Category.assoc]
            _ = ((hc.pullbackCompIso arrowX (𝟙 (unop U))).hom.app fiberObjX ≫
                    (hc.pullbackIdIso (unop U)).inv.app
                      ((hc.pullbackFunctor arrowX).obj fiberObjX)) ≫
                  φ ≫
                  ((hc.pullbackIdIso (unop U)).hom.app
                      ((hc.pullbackFunctor arrowY).obj fiberObjY) ≫
                    (hc.pullbackCompIso arrowY (𝟙 (unop U))).inv.app fiberObjY) := by
                    simp [αX, βX, γY, δY, Category.assoc]
            _ = ((hc.pullbackCompIso arrowX (𝟙 (unop U))).hom.app fiberObjX ≫
                    (hc.pullbackIdIso (unop U)).inv.app
                      ((hc.pullbackFunctor arrowX).obj fiberObjX)) ≫
                  φ ≫
                  eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj fiberObjY)
                    (Category.id_comp arrowY)).symm := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦
                          ((hc.pullbackCompIso arrowX (𝟙 (unop U))).hom.app fiberObjX ≫
                              (hc.pullbackIdIso (unop U)).inv.app
                                ((hc.pullbackFunctor arrowX).obj fiberObjX)) ≫
                            φ ≫ k)
                        htarget.symm

/-- Helper for Lemma 4.36.4: pushing `g^*` through the inner comparison chain expands into the
three expected factors. This isolates the reusable functoriality step from the later comparison
cancellations in the strict `map_comp` proof. -/
theorem pullback_strictification_reindex_map_expand
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {T T' U V W : C} {a : U ⟶ T} {b : U ⟶ T'} (f : V ⟶ U) (g : W ⟶ V)
    {x : Fiber p T} {y : Fiber p T'}
    (φ : (hc.pullbackFunctor a).obj x ⟶ (hc.pullbackFunctor b).obj y) :
    (hc.pullbackFunctor g).map
        ((hc.pullbackCompIso a f).hom.app x ≫
          (hc.pullbackFunctor f).map φ ≫
          (hc.pullbackCompIso b f).inv.app y) =
      (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x) ≫
        ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ) ≫
        (hc.pullbackFunctor g).map ((hc.pullbackCompIso b f).inv.app y) := by
  -- Expand `g^*` across the three-term comparison chain so later proofs can cancel each
  -- comparison factor separately.
  calc
    (hc.pullbackFunctor g).map
        ((hc.pullbackCompIso a f).hom.app x ≫
          (hc.pullbackFunctor f).map φ ≫
          (hc.pullbackCompIso b f).inv.app y)
        =
      (hc.pullbackFunctor g).map
          (((hc.pullbackCompIso a f).hom.app x ≫
            (hc.pullbackFunctor f).map φ) ≫
            (hc.pullbackCompIso b f).inv.app y) := by
              simp [Category.assoc]
    _ =
      (hc.pullbackFunctor g).map
          ((hc.pullbackCompIso a f).hom.app x ≫
            (hc.pullbackFunctor f).map φ) ≫
        (hc.pullbackFunctor g).map ((hc.pullbackCompIso b f).inv.app y) := by
              rw [Functor.map_comp]
    _ =
      (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x) ≫
        (hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map φ) ≫
        (hc.pullbackFunctor g).map ((hc.pullbackCompIso b f).inv.app y) := by
              rw [Functor.map_comp]
              simp [Category.assoc]
    _ =
      (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x) ≫
        ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ) ≫
        (hc.pullbackFunctor g).map ((hc.pullbackCompIso b f).inv.app y) := by
              simp [Functor.comp_map]

/-- Helper for Lemma 4.36.4: after applying a further pullback functor, the inverse and hom of a
composition-comparison component still cancel to the identity. -/
theorem pullback_strictification_mapped_compIso_inv_hom
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {T U V W : C} (a : U ⟶ T) (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p T) :
    (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).inv.app x) ≫
      (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x) =
        𝟙 ((hc.pullbackFunctor g).obj ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x))) := by
  -- Map the inverse-hom identity through `g^*`; functoriality preserves the cancellation.
  rw [← Functor.map_comp]
  simpa using
    congrArg (fun k ↦ (hc.pullbackFunctor g).map k)
      (Iso.inv_hom_id_app (hc.pullbackCompIso a f) x)

/-- Helper for Lemma 4.36.4: reindexing along a composite in the strict model is strictly the
composite reindexing functor. -/
theorem pullback_strictification_functor_map_comp_chain
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {X Y : PullbackStrictificationFiber p hc U} (φ : X ⟶ Y) :
    eqToHom
        (congrArg (pullbackStrictificationFiberForget p hc W)
          (pullback_strictification_reindex_obj_comp p hc f g X)) ≫
      pullbackStrictificationReindexMap p hc g
        (pullbackStrictificationReindexMap p hc f φ) ≫
    eqToHom
        (congrArg (pullbackStrictificationFiberForget p hc W)
          (pullback_strictification_reindex_obj_comp p hc f g Y)).symm =
    pullbackStrictificationReindexMap p hc (g ≫ f) φ := by
  -- Route correction: instead of attacking the transported equality abstractly, unpack the two
  -- presentations and rewrite every transport into the explicit comparison chain supplied by the
  -- chosen pullback system.
  cases X with
  | mk targetX arrowX fiberObjX =>
      cases Y with
      | mk targetY arrowY fiberObjY =>
          -- After unpacking the strictification objects, the source and target transports are the
          -- associativity comparison chains from the chosen pullback comparison isomorphisms.
          change
            eqToHom
                (congrArg (fun k ↦ (hc.pullbackFunctor k).obj fiberObjX)
                  (Category.assoc g f arrowX)) ≫
              ((hc.pullbackCompIso (f ≫ arrowX) g).hom.app fiberObjX ≫
                (hc.pullbackFunctor g).map
                  ((hc.pullbackCompIso arrowX f).hom.app fiberObjX ≫
                    (hc.pullbackFunctor f).map φ ≫
                    (hc.pullbackCompIso arrowY f).inv.app fiberObjY) ≫
                (hc.pullbackCompIso (f ≫ arrowY) g).inv.app fiberObjY) ≫
              eqToHom
                (congrArg (fun k ↦ (hc.pullbackFunctor k).obj fiberObjY)
                  (Category.assoc g f arrowY)).symm =
            (hc.pullbackCompIso arrowX (g ≫ f)).hom.app fiberObjX ≫
              (hc.pullbackFunctor (g ≫ f)).map φ ≫
              (hc.pullbackCompIso arrowY (g ≫ f)).inv.app fiberObjY
          rw [pullback_strictification_comp_eqToHom
              (p := p) (hc := hc) (a := arrowX) (f := f) (g := g) (x := fiberObjX)]
          rw [pullback_strictification_comp_eqToHom_symm
              (p := p) (hc := hc) (a := arrowY) (f := f) (g := g) (x := fiberObjY)]
          have hexpand :
              (hc.pullbackFunctor g).map
                  ((hc.pullbackCompIso arrowX f).hom.app fiberObjX ≫
                    (hc.pullbackFunctor f).map φ ≫
                    (hc.pullbackCompIso arrowY f).inv.app fiberObjY) =
                (hc.pullbackFunctor g).map
                    ((hc.pullbackCompIso arrowX f).hom.app fiberObjX) ≫
                  ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ) ≫
                  (hc.pullbackFunctor g).map
                    ((hc.pullbackCompIso arrowY f).inv.app fiberObjY) := by
            simpa using
              (pullback_strictification_reindex_map_expand
                (p := p) (hc := hc) (a := arrowX) (b := arrowY)
                (f := f) (g := g) (φ := φ))
          rw [hexpand]
          -- Name the successive comparison factors so each cancellation step can be applied to an
          -- exact subchain instead of relying on fragile raw reassociation.
          let α₀ := (hc.pullbackCompIso arrowX (g ≫ f)).hom.app fiberObjX
          let α₁ := (hc.pullbackCompIso f g).hom.app ((hc.pullbackFunctor arrowX).obj fiberObjX)
          let α₂ := (hc.pullbackFunctor g).map ((hc.pullbackCompIso arrowX f).inv.app fiberObjX)
          let β₁ := (hc.pullbackCompIso (f ≫ arrowX) g).inv.app fiberObjX
          let β₂ := (hc.pullbackCompIso (f ≫ arrowX) g).hom.app fiberObjX
          let β₃ := (hc.pullbackFunctor g).map ((hc.pullbackCompIso arrowX f).hom.app fiberObjX)
          let β₄ := ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ)
          let β₅ := (hc.pullbackFunctor g).map ((hc.pullbackCompIso arrowY f).inv.app fiberObjY)
          let γ₁ := (hc.pullbackCompIso (f ≫ arrowY) g).inv.app fiberObjY
          let γ₂ := (hc.pullbackCompIso (f ≫ arrowY) g).hom.app fiberObjY
          let γ₃ := (hc.pullbackFunctor g).map ((hc.pullbackCompIso arrowY f).hom.app fiberObjY)
          let γ₄ := (hc.pullbackCompIso f g).inv.app ((hc.pullbackFunctor arrowY).obj fiberObjY)
          let γ₅ := (hc.pullbackCompIso arrowY (g ≫ f)).inv.app fiberObjY
          have hcancel₁ :
              β₁ ≫ β₂ ≫ β₃ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅ =
                β₃ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅ := by
            simpa [β₁, β₂, β₃, β₄, β₅, γ₁, γ₂, γ₃, γ₄, γ₅, Category.assoc] using
              Iso.inv_hom_id_assoc ((hc.pullbackCompIso (f ≫ arrowX) g).app fiberObjX)
                (β₃ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅)
          have hmapped₁ :
              α₂ ≫ β₃ = 𝟙 _ := by
            simpa [α₂, β₃] using
              (pullback_strictification_mapped_compIso_inv_hom
                (p := p) (hc := hc) (a := arrowX) (f := f) (g := g) (x := fiberObjX))
          have hcancel₂ :
              γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅ =
                γ₃ ≫ γ₄ ≫ γ₅ := by
            simpa [γ₁, γ₂, γ₃, γ₄, γ₅, Category.assoc] using
              Iso.inv_hom_id_assoc ((hc.pullbackCompIso (f ≫ arrowY) g).app fiberObjY)
                (γ₃ ≫ γ₄ ≫ γ₅)
          have hmapped₂ :
              β₅ ≫ γ₃ = 𝟙 _ := by
            simpa [β₅, γ₃] using
              (pullback_strictification_mapped_compIso_inv_hom
                (p := p) (hc := hc) (a := arrowY) (f := f) (g := g) (x := fiberObjY))
          have hnat :
              α₁ ≫ β₄ ≫ γ₄ = (hc.pullbackFunctor (g ≫ f)).map φ := by
            simpa [α₁, β₄, γ₄, Category.assoc] using
              (pullback_strictification_compIso_naturality_inv
                (p := p) (hc := hc) (f := f) (g := g) (φ := φ))
          have hchain :
              α₀ ≫ α₁ ≫ α₂ ≫ β₁ ≫ β₂ ≫ β₃ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅ =
                α₀ ≫ (hc.pullbackFunctor (g ≫ f)).map φ ≫ γ₅ := by
            calc
            α₀ ≫ α₁ ≫ α₂ ≫ β₁ ≫ β₂ ≫ β₃ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅
                =
              α₀ ≫ α₁ ≫ α₂ ≫ (β₁ ≫ β₂ ≫ β₃ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅) := by
                  simp [Category.assoc]
            _ = α₀ ≫ α₁ ≫ α₂ ≫ (β₃ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅) := by
                  exact congrArg (fun k ↦ α₀ ≫ α₁ ≫ α₂ ≫ k) hcancel₁
            _ = α₀ ≫ α₁ ≫ ((α₂ ≫ β₃) ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅) := by
                  simp [Category.assoc]
            _ = α₀ ≫ α₁ ≫ (𝟙 _ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅) := by
                  exact congrArg
                    (fun k ↦ α₀ ≫ α₁ ≫ (k ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅))
                    hmapped₁
            _ = α₀ ≫ α₁ ≫ β₄ ≫ β₅ ≫ γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅ := by
                  simp [Category.assoc]
            _ = α₀ ≫ α₁ ≫ β₄ ≫ β₅ ≫ (γ₁ ≫ γ₂ ≫ γ₃ ≫ γ₄ ≫ γ₅) := by
                  simp [Category.assoc]
            _ = α₀ ≫ α₁ ≫ β₄ ≫ β₅ ≫ (γ₃ ≫ γ₄ ≫ γ₅) := by
                  exact congrArg (fun k ↦ α₀ ≫ α₁ ≫ β₄ ≫ β₅ ≫ k) hcancel₂
            _ = α₀ ≫ α₁ ≫ β₄ ≫ ((β₅ ≫ γ₃) ≫ γ₄ ≫ γ₅) := by
                  simp [Category.assoc]
            _ = α₀ ≫ α₁ ≫ β₄ ≫ (𝟙 _ ≫ γ₄ ≫ γ₅) := by
                  exact congrArg (fun k ↦ α₀ ≫ α₁ ≫ β₄ ≫ (k ≫ γ₄ ≫ γ₅)) hmapped₂
            _ = α₀ ≫ (α₁ ≫ β₄ ≫ γ₄) ≫ γ₅ := by
                  simp [Category.assoc]
            _ = α₀ ≫ (hc.pullbackFunctor (g ≫ f)).map φ ≫ γ₅ := by
                  exact congrArg (fun k ↦ α₀ ≫ k ≫ γ₅) hnat
            _ = α₀ ≫ (hc.pullbackFunctor (g ≫ f)).map φ ≫
                (hc.pullbackCompIso arrowY (g ≫ f)).inv.app fiberObjY := by
                  simp [α₀, γ₅]
          simpa [α₀, α₁, α₂, β₁, β₂, β₃, β₄, β₅, γ₁, γ₂, γ₃, γ₄, γ₅, Category.assoc] using
            hchain

/-- Helper for Lemma 4.36.4: reindexing along a composite in the strict model is strictly the
composite reindexing functor. -/
theorem pullback_strictification_functor_map_comp
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    (pullbackStrictificationReindex p hc (g.unop ≫ f.unop)).toCatHom =
      (pullbackStrictificationReindex p hc f.unop).toCatHom ≫
        (pullbackStrictificationReindex p hc g.unop).toCatHom := by
  -- Compare the two `Cat`-functors objectwise and then use the packaged morphism transport from
  -- `pullback_strictification_functor_map_comp_chain`.
  apply CategoryTheory.Cat.ext
  refine CategoryTheory.Functor.ext
    (fun X ↦ pullback_strictification_reindex_obj_comp p hc f.unop g.unop X) ?_
  intro X Y φ
  simpa using
    (pullback_strictification_functor_map_comp_chain
      (p := p) (hc := hc) (f := f.unop) (g := g.unop) (φ := φ)).symm

/-- Helper for Lemma 4.36.4: the source-text strictification is an actual contravariant
`Cat`-valued functor whose objects are the strict fibers of pullback presentations. -/
noncomputable def pullback_strictification_functor
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    Cᵒᵖ ⥤ Cat.{max v₁ v₂, max (max u₁ u₂) v₁} where
  obj := fun U ↦ Cat.of (PullbackStrictificationFiber p hc (unop U))
  map := fun f ↦ (pullbackStrictificationReindex p hc f.unop).toCatHom
  map_id := pullback_strictification_functor_map_id p hc
  map_comp := pullback_strictification_functor_map_comp p hc

-- Proof sketch: replace the invalid direct-split shortcut by the source strictification
-- construction. The remaining work is the explicit comparison equivalence to the strict model.

/-- Helper for Lemma 4.36.4: the literal strict target of the source construction is the
co-Grothendieck projection of the strict contravariant functor built above. -/
noncomputable abbrev pullback_strictification_projection_surface
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    Pseudofunctor.CoGrothendieck
        ((pullback_strictification_functor p hc).toPseudofunctor') ⥤ C :=
  Pseudofunctor.CoGrothendieck.forget
    ((pullback_strictification_functor p hc).toPseudofunctor')

/-- Helper for Lemma 4.36.4: the chapter-facing strictification owner is the literal strict
co-Grothendieck surface built from the strict pair model. -/
noncomputable def pullback_strictification
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    FibredCategoryOver C :=
  -- Route correction: make the chapter-facing owner literally be the strict co-Grothendieck
  -- surface, so the remaining comparison problem is only `p` versus the strict model itself.
  FibredCategoryOver.ofFunctor (pullback_strictification_projection_surface p hc)

/-- Helper for Lemma 4.36.4: forgetting the owner wrapper on `pullback_strictification p hc`
recovers the strict co-Grothendieck projection functor built from the same pullback choice. -/
theorem pullback_strictification_owner_projection
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    (pullback_strictification p hc).p = pullback_strictification_projection_surface p hc := by
  -- The chapter-facing strictification was defined by wrapping exactly this projection functor.
  rfl

/-- Helper for Lemma 4.36.4: the literal strict co-Grothendieck model built from
`pullback_strictification_functor p hc` is split by construction. -/
theorem pullback_strictification_projection_surface_isSplit
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    Functor.IsSplitFibredCategory (pullback_strictification_projection_surface p hc) := by
  -- The literal target already is the co-Grothendieck construction of the strict functor, so the
  -- comparison functors can both be taken to be identities.
  refine ⟨?_⟩
  refine ⟨pullback_strictification_functor p hc, ?_, ?_, ?_, ?_⟩
  · exact 𝟙 (BasedCategory.ofFunctor (pullback_strictification_projection_surface p hc))
  · exact 𝟙 (BasedCategory.ofFunctor (pullback_strictification_projection_surface p hc))
  · change
      𝟙 (BasedCategory.ofFunctor (pullback_strictification_projection_surface p hc)) ⋙
          𝟙 (BasedCategory.ofFunctor (pullback_strictification_projection_surface p hc)) =
        𝟙 (BasedCategory.ofFunctor (pullback_strictification_projection_surface p hc))
    simp
  · change
      𝟙 (BasedCategory.ofFunctor (pullback_strictification_projection_surface p hc)) ⋙
          𝟙 (BasedCategory.ofFunctor (pullback_strictification_projection_surface p hc)) =
        𝟙
          (BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget
              (pullback_strictification_functor p hc).toPseudofunctor'))
    simp

/-- Helper for Lemma 4.36.4: the chosen strictification is split because it is literally the
strict co-Grothendieck surface built from the contravariant `Cat`-valued functor above. -/
theorem pullback_strictification_projection_surface_owner_isSplit
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    Functor.IsSplitFibredCategory
      (FibredCategoryOver.ofFunctor (pullback_strictification_projection_surface p hc)).p := by
  -- This packages the literal strict surface at the owner level, ready for the final comparison.
  simpa using pullback_strictification_projection_surface_isSplit p hc

/-- Helper for Lemma 4.36.4: forgetting the owner wrapper on the literal strict surface recovers
the strict co-Grothendieck projection functor itself. This isolates the owner-level projection
used in the remaining comparison step from the later equivalence packaging. -/
theorem pullback_strictification_projection_surface_owner_projection
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    (FibredCategoryOver.ofFunctor (pullback_strictification_projection_surface p hc)).p =
      pullback_strictification_projection_surface p hc := by
  rfl

/-- Helper for Lemma 4.36.4: the literal strict co-Grothendieck surface already furnishes a split
owner-level model. -/
theorem pullback_strictification_projection_surface_exists_split_owner
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    ∃ Y : FibredCategoryOver C,
      Y = FibredCategoryOver.ofFunctor (pullback_strictification_projection_surface p hc) ∧
        Functor.IsSplitFibredCategory Y.p := by
  -- Package the literal strict surface as the verified split owner object used in the final
  -- existence statement.
  refine ⟨FibredCategoryOver.ofFunctor (pullback_strictification_projection_surface p hc), rfl, ?_⟩
  simpa using pullback_strictification_projection_surface_owner_isSplit p hc

/-- Helper for Lemma 4.36.4: the literal strict surface already gives a split witness over the
base, independently of the later owner-comparison step. -/
theorem pullback_strictification_projection_surface_split_witness
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    ∃ Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C,
      Functor.IsSplitFibredCategory Y.p := by
  rcases pullback_strictification_projection_surface_exists_split_owner p hc with ⟨Y, _hY, hsplit⟩
  exact ⟨Y, hsplit⟩

/-- Helper for Lemma 4.36.4: lifting the split structure from the literal strict model to the
chapter-facing owner target is exactly the remaining owner-bridge blocker. -/
theorem pullback_strictification_isSplit
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    Functor.IsSplitFibredCategory (pullback_strictification p hc).p := by
  -- After the owner pivot, splitness is exactly the already-verified splitness of the literal
  -- strict co-Grothendieck surface.
  simpa [pullback_strictification] using
    pullback_strictification_projection_surface_owner_isSplit p hc

/-- Helper for Lemma 4.36.4: the chosen strictification owner already packages the split target
used in the final existence statement. -/
theorem pullback_strictification_split_target
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    ∃ Y : FibredCategoryOver C,
      Y = pullback_strictification p hc ∧ Functor.IsSplitFibredCategory Y.p := by
  -- Package the strict target together with the split structure already proved above.
  refine ⟨pullback_strictification p hc, rfl, ?_⟩
  exact pullback_strictification_isSplit p hc

/-- Helper for Lemma 4.36.4: the canonical pullback choice already determines the split target
that will appear in the final existence statement. This isolates the solved split half of the
source proof from the remaining comparison-equivalence construction. -/
theorem canonical_pullback_strictification_isSplit
    (p : S ⥤ C) [p.IsFibered] :
    Functor.IsSplitFibredCategory
      (pullback_strictification p (canonicalPullbackChoice p)).p := by
  -- Specialize the previously verified splitness of the strict target to the canonical cleavage
  -- chosen for the main theorem.
  simpa using
    pullback_strictification_isSplit p (canonicalPullbackChoice p)

/-- Helper for Lemma 4.36.4: forgetting the owner wrapper on the canonical strictification
recovers the literal strict projection functor built from the same canonical pullback choice. -/
theorem canonical_pullback_strictification_owner_projection
    (p : S ⥤ C) [p.IsFibered] :
    (pullback_strictification p (canonicalPullbackChoice p)).p =
      pullback_strictification_projection_surface p (canonicalPullbackChoice p) := by
  -- The canonical strictification owner was defined by wrapping this literal strict surface.
  rfl

/-- Helper for Lemma 4.36.4: the canonical pullback choice already packages the final split target
that remains to be equipped with the comparison equivalence from `p`. -/
theorem canonical_pullback_strictification_split_target
    (p : S ⥤ C) [p.IsFibered] :
    ∃ Y : FibredCategoryOver C,
      Y = pullback_strictification p (canonicalPullbackChoice p) ∧
        Functor.IsSplitFibredCategory Y.p := by
  -- The canonical cleavage specializes the previously proved strictification target package.
  refine ⟨pullback_strictification p (canonicalPullbackChoice p), rfl, ?_⟩
  simpa using canonical_pullback_strictification_isSplit p

/-- Helper for Lemma 4.36.4: forgetting the defining equality in the canonical strictification
package leaves a plain split witness over `C`. This isolates the solved split half of the source
argument from the remaining equivalence-over-base construction. -/
theorem canonical_pullback_strictification_exists_split_witness
    (p : S ⥤ C) [p.IsFibered] :
    ∃ Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C,
      Functor.IsSplitFibredCategory Y.p := by
  rcases canonical_pullback_strictification_split_target p with ⟨Y, _hY, hsplit⟩
  exact ⟨Y, hsplit⟩

end CategoryTheory
