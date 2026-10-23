module

public import stacks_project.Chap04.Lemma_4_36_4.Strictification.Presentation
public import stacks_project.Chap04.Lemma_4_2_18

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

/-- Helper for Lemma 4.36.4: expanding the composite co-Grothendieck fiber exposes the raw strict
reindex chain that the remaining rhs factorization must normalize. This isolates the bicategorical
composition expansion from the later transport-heavy comparison steps. -/
private theorem pullback_strictification_identity_presentation_map_comp_rhs_raw_expansion
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
    Fiber.fiberInclusion.map
        ((pullback_strictification_identity_presentation_map p hc f ≫
            pullback_strictification_identity_presentation_map p hc g).fiber ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
            (pullback_strictification_identity_presentation_map_comp_target_base
              p hc f g))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber =
      Fiber.fiberInclusion.map
        (((pullback_strictification_identity_presentation_map p hc f).fiber ≫
            ((pullback_strictification_functor p hc).toPseudofunctor'.map
                  (pullback_strictification_identity_presentation_map p hc f).base.op.toLoc).toFunctor.map
              (pullback_strictification_identity_presentation_map p hc g).fiber ≫
            ((pullback_strictification_functor p hc).toPseudofunctor'.mapComp
                  (pullback_strictification_identity_presentation_map p hc g).base.op.toLoc
                  (pullback_strictification_identity_presentation_map p hc f).base.op.toLoc).inv.toNatTrans.app
                (pullback_strictification_identity_presentation p hc z).fiber) ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
            (pullback_strictification_identity_presentation_map_comp_target_base
              p hc f g))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber := by
  -- Expand only the co-Grothendieck composition fiber; the later normalization of the two
  -- packaged identity-presentation fibers is kept as the remaining focused blocker.
  dsimp only
  rw [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber]
  rfl

/-- Helper for Lemma 4.36.4: precomposing the final target-transport collapse by an arbitrary
leading strict fiber morphism out of the identity presentation of `x` is just functoriality of the
fiber inclusion. This isolates the
dependent rewrite on the terminal `eqToHom` tail from the remaining strict reindex-chain
normalization. -/
private theorem
    pullback_strictification_identity_presentation_map_comp_target_transport_precompose
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z)
    (β :
      (hc.pullbackFunctor (𝟙 (p.obj x))).obj (Fiber.mk (rfl : p.obj x = p.obj x)) ⟶
        (hc.pullbackFunctor
          ((pullback_strictification_identity_presentation_map p hc f ≫
              pullback_strictification_identity_presentation_map p hc g).base ≫
            𝟙 (p.obj z))).obj (Fiber.mk (rfl : p.obj z = p.obj z))) :
    Fiber.fiberInclusion.map
        (β ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj (Fiber.mk (rfl : p.obj z = p.obj z)))
            (pullback_strictification_identity_presentation_map_comp_target_base
              p hc f g))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) (Fiber.mk (rfl : p.obj z = p.obj z)) =
      Fiber.fiberInclusion.map β ≫
        hc.map
          ((pullback_strictification_identity_presentation_map p hc f ≫
              pullback_strictification_identity_presentation_map p hc g).base ≫
            𝟙 (p.obj z))
          (Fiber.mk (rfl : p.obj z = p.obj z)) := by
  -- Push the target-transport collapse one step to the right so the remaining proof only has to
  -- normalize the strict reindex chain sitting in `β`.
  have htarget :=
    pullback_strictification_identity_presentation_map_comp_target_transport_fac
      (p := p) (hc := hc) (f := f) (g := g)
  have hmap :
      Fiber.fiberInclusion.map
          (β ≫
            eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj (Fiber.mk (rfl : p.obj z = p.obj z)))
              (pullback_strictification_identity_presentation_map_comp_target_base
                p hc f g))) =
        Fiber.fiberInclusion.map β ≫
          Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj (Fiber.mk (rfl : p.obj z = p.obj z)))
              (pullback_strictification_identity_presentation_map_comp_target_base
                p hc f g))) := by
    simpa using
      (Functor.map_comp Fiber.fiberInclusion β
        (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj (Fiber.mk (rfl : p.obj z = p.obj z)))
          (pullback_strictification_identity_presentation_map_comp_target_base
            p hc f g))))
  calc
    Fiber.fiberInclusion.map
          (β ≫
            eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj (Fiber.mk (rfl : p.obj z = p.obj z)))
              (pullback_strictification_identity_presentation_map_comp_target_base
                p hc f g))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) (Fiber.mk (rfl : p.obj z = p.obj z)) =
      (Fiber.fiberInclusion.map β ≫
          Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj (Fiber.mk (rfl : p.obj z = p.obj z)))
              (pullback_strictification_identity_presentation_map_comp_target_base
                p hc f g)))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) (Fiber.mk (rfl : p.obj z = p.obj z)) := by
          exact congrArg (fun k ↦ k ≫ hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z))
            (Fiber.mk (rfl : p.obj z = p.obj z))) hmap
    _ =
      Fiber.fiberInclusion.map β ≫
        (Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj (Fiber.mk (rfl : p.obj z = p.obj z)))
              (pullback_strictification_identity_presentation_map_comp_target_base
                p hc f g))) ≫
          hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) (Fiber.mk (rfl : p.obj z = p.obj z))) := by
          simp
    _ =
      Fiber.fiberInclusion.map β ≫
        hc.map
          ((pullback_strictification_identity_presentation_map p hc f ≫
              pullback_strictification_identity_presentation_map p hc g).base ≫
            𝟙 (p.obj z))
          (Fiber.mk (rfl : p.obj z = p.obj z)) := by
          exact congrArg (fun k ↦ Fiber.fiberInclusion.map β ≫ k) htarget

/-- Helper for Lemma 4.36.4: the tail of the right-hand composite identity-presentation
fiber factors as the chosen pullback arrow for `f` followed by the original morphism `g`. -/
private theorem pullback_strictification_identity_presentation_map_comp_rhs_tail_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
    let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
    Fiber.fiberInclusion.map
        (((pullback_strictification_functor p hc).toPseudofunctor'.map
              (pullback_strictification_identity_presentation_map p hc f).base.op.toLoc).toFunctor.map
            (pullback_strictification_identity_presentation_map p hc g).fiber ≫
          ((pullback_strictification_functor p hc).toPseudofunctor'.mapComp
                (pullback_strictification_identity_presentation_map p hc g).base.op.toLoc
                (pullback_strictification_identity_presentation_map p hc f).base.op.toLoc).inv.toNatTrans.app
              (pullback_strictification_identity_presentation p hc z).fiber) ≫
      hc.map
        ((pullback_strictification_identity_presentation_map p hc f ≫
              pullback_strictification_identity_presentation_map p hc g).base ≫
          𝟙 (p.obj z))
        zFiber =
      hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber ≫ g := by
  dsimp only
  let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
  let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
  rw [pullback_strictification_identity_presentation_map_fiber]
  dsimp [pullback_strictification_functor, pullbackStrictificationReindex,
    pullbackStrictificationReindexMap, pullbackStrictificationReindexObj,
    pullbackStrictificationFiberForget, pullback_strictification_identity_presentation, eqToIso]
  rw [CategoryTheory.Cat.eqToHom_app]
  change Fiber.fiberInclusion.map
      (((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber ≫
          (hc.pullbackFunctor (p.map f)).map
            (pullback_strictification_identity_presentation_fiber_map p hc g ≫
              eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
                (Category.comp_id (p.map g)).symm)) ≫
          (hc.pullbackCompIso (p.map g ≫ 𝟙 (p.obj z)) (p.map f)).inv.app zFiber) ≫
        eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
          (Category.assoc (p.map f) (p.map g) (𝟙 (p.obj z))).symm)) ≫
      hc.map ((p.map f ≫ p.map g) ≫ 𝟙 (p.obj z)) zFiber =
    hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber ≫ g
  let θ : (hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber ⟶
      (hc.pullbackFunctor (p.map g ≫ 𝟙 (p.obj z))).obj zFiber :=
    pullback_strictification_identity_presentation_fiber_map p hc g ≫
      eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
        (Category.comp_id (p.map g)).symm)
  have hassoc :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
            (Category.assoc (p.map f) (p.map g) (𝟙 (p.obj z))).symm)) ≫
        hc.map ((p.map f ≫ p.map g) ≫ 𝟙 (p.obj z)) zFiber =
      hc.map (p.map f ≫ p.map g ≫ 𝟙 (p.obj z)) zFiber := by
    have htmp :=
      pullback_strictification_eqToHom_component_postcompose_eq
        (p := p) (hc := hc)
        (f := p.map f ≫ p.map g ≫ 𝟙 (p.obj z))
        (g := (p.map f ≫ p.map g) ≫ 𝟙 (p.obj z))
        (e := (Category.assoc (p.map f) (p.map g) (𝟙 (p.obj z))).symm)
        (x := zFiber)
    simpa using htmp
  have htarget :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (p.map g ≫ 𝟙 (p.obj z)) (p.map f)).inv.app zFiber) ≫
        hc.map (p.map f ≫ p.map g ≫ 𝟙 (p.obj z)) zFiber =
      hc.map (p.map f) ((hc.pullbackFunctor (p.map g ≫ 𝟙 (p.obj z))).obj zFiber) ≫
        hc.map (p.map g ≫ 𝟙 (p.obj z)) zFiber := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_inv_fac (f := p.map g ≫ 𝟙 (p.obj z))
        (g := p.map f) zFiber
  have hmap :
      Fiber.fiberInclusion.map ((hc.pullbackFunctor (p.map f)).map θ) ≫
        hc.map (p.map f) ((hc.pullbackFunctor (p.map g ≫ 𝟙 (p.obj z))).obj zFiber) =
      hc.map (p.map f) ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber) ≫
        Fiber.fiberInclusion.map θ := by
    simpa using
      pullback_strictification_pullbackFunctor_map_fac
        (p := p) (hc := hc) (f := p.map f) (φ := θ)
  have hg :
      Fiber.fiberInclusion.map θ ≫ hc.map (p.map g ≫ 𝟙 (p.obj z)) zFiber =
      (((hc.pullbackIdIso (p.obj y)).symm.app yFiber).hom.1) ≫ g := by
    have hg0 :=
      (pullback_strictification_identity_presentation_map_fiber_fac
        (p := p) (hc := hc) (f := g))
    rw [pullback_strictification_identity_presentation_map_fiber] at hg0
    change Fiber.fiberInclusion.map θ ≫ hc.map (p.map g ≫ 𝟙 (p.obj z)) zFiber =
      (((hc.pullbackIdIso (p.obj y)).symm.app yFiber).hom.1) ≫ g at hg0
    exact hg0
  have hyid :
      (((hc.pullbackIdIso (p.obj y)).symm.app yFiber).hom.1) =
        hc.map (𝟙 (p.obj y)) yFiber := by
    simpa [PullbackChoice.pullbackIdIso] using
      hc.pullbackIdComponentIso_inv_eq (p.obj y) yFiber
  have hsource :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
        hc.map (p.map f) ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber) ≫
          (((hc.pullbackIdIso (p.obj y)).symm.app yFiber).hom.1) =
      hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber := by
    rw [hyid]
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := 𝟙 (p.obj y)) (g := p.map f) yFiber
  calc
    Fiber.fiberInclusion.map
        (((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber ≫
            (hc.pullbackFunctor (p.map f)).map θ ≫
            (hc.pullbackCompIso (p.map g ≫ 𝟙 (p.obj z)) (p.map f)).inv.app zFiber) ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
            (Category.assoc (p.map f) (p.map g) (𝟙 (p.obj z))).symm)) ≫
        hc.map ((p.map f ≫ p.map g) ≫ 𝟙 (p.obj z)) zFiber
        = Fiber.fiberInclusion.map
            ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber ≫
              (hc.pullbackFunctor (p.map f)).map θ ≫
              (hc.pullbackCompIso (p.map g ≫ 𝟙 (p.obj z)) (p.map f)).inv.app zFiber) ≫
          hc.map (p.map f ≫ p.map g ≫ 𝟙 (p.obj z)) zFiber := by
            rw [Functor.map_comp]
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ Fiber.fiberInclusion.map
                  ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber ≫
                    (hc.pullbackFunctor (p.map f)).map θ ≫
                    (hc.pullbackCompIso (p.map g ≫ 𝟙 (p.obj z)) (p.map f)).inv.app zFiber) ≫ k)
                hassoc
    _ = Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
        Fiber.fiberInclusion.map ((hc.pullbackFunctor (p.map f)).map θ) ≫
        (Fiber.fiberInclusion.map
            ((hc.pullbackCompIso (p.map g ≫ 𝟙 (p.obj z)) (p.map f)).inv.app zFiber) ≫
          hc.map (p.map f ≫ p.map g ≫ 𝟙 (p.obj z)) zFiber) := by
          rw [Functor.map_comp, Functor.map_comp]
          simp [Category.assoc]
    _ = Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
        Fiber.fiberInclusion.map ((hc.pullbackFunctor (p.map f)).map θ) ≫
        (hc.map (p.map f) ((hc.pullbackFunctor (p.map g ≫ 𝟙 (p.obj z))).obj zFiber) ≫
          hc.map (p.map g ≫ 𝟙 (p.obj z)) zFiber) := by
          exact congrArg
            (fun k ↦ Fiber.fiberInclusion.map
              ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
              Fiber.fiberInclusion.map ((hc.pullbackFunctor (p.map f)).map θ) ≫ k)
            htarget
    _ = Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
        (Fiber.fiberInclusion.map ((hc.pullbackFunctor (p.map f)).map θ) ≫
          hc.map (p.map f) ((hc.pullbackFunctor (p.map g ≫ 𝟙 (p.obj z))).obj zFiber)) ≫
        hc.map (p.map g ≫ 𝟙 (p.obj z)) zFiber := by
          simp [Category.assoc]
    _ = Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
        (hc.map (p.map f) ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber) ≫
          Fiber.fiberInclusion.map θ) ≫
        hc.map (p.map g ≫ 𝟙 (p.obj z)) zFiber := by
          exact congrArg
            (fun k ↦ Fiber.fiberInclusion.map
              ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
              k ≫ hc.map (p.map g ≫ 𝟙 (p.obj z)) zFiber)
            hmap
    _ = Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
        hc.map (p.map f) ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber) ≫
        (Fiber.fiberInclusion.map θ ≫ hc.map (p.map g ≫ 𝟙 (p.obj z)) zFiber) := by
          simp [Category.assoc]
    _ = hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber ≫ g := by
          erw [hg]
          calc
            Fiber.fiberInclusion.map
                ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
              hc.map (p.map f) ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber) ≫
              (((hc.pullbackIdIso (p.obj y)).symm.app yFiber).hom.1) ≫ g =
                (Fiber.fiberInclusion.map
                    ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
                  hc.map (p.map f) ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber) ≫
                  (((hc.pullbackIdIso (p.obj y)).symm.app yFiber).hom.1)) ≫ g := by
                  simp [Category.assoc]
            _ = hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber ≫ g := by
                  exact congrArg (fun k ↦ k ≫ g) hsource











private theorem pullback_strictification_identity_presentation_map_comp_rhs_fiber_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
    let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
    Fiber.fiberInclusion.map
        ((pullback_strictification_identity_presentation_map p hc f ≫
            pullback_strictification_identity_presentation_map p hc g).fiber ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
            (pullback_strictification_identity_presentation_map_comp_target_base
              p hc f g))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber =
      (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ (f ≫ g) := by
  -- Route correction: the raw composite fiber has now been expanded into one explicit strict
  -- reindex chain. The remaining blocker is precisely to normalize that chain and factor it
  -- through the chosen pullback arrows.
  dsimp only
  have hexpand :=
    pullback_strictification_identity_presentation_map_comp_rhs_raw_expansion
      (p := p) (hc := hc) (f := f) (g := g)
  -- TODO for Lemma 4.36.4: after this raw expansion, collapse the tail transport with
  -- `pullback_strictification_identity_presentation_map_comp_target_transport_fac`, rewrite the
  -- remaining `eqToHom` transports by `pullback_strictification_id_eqToHom_symm` and
  -- `pullback_strictification_comp_eqToHom_symm`, then factor the reindexed `g`-part with
  -- `pullback_strictification_comp_target_transport_postcompose_eq`,
  -- `pullback_strictification_pullbackFunctor_map_fac`, and
  -- `pullback_strictification_identity_presentation_map_fiber_fac`.
  exact hexpand.trans <| by
    -- TODO for Lemma 4.36.4: normalize this explicit strict reindex chain and factor it through
    -- the chosen pullback arrows using the named transport and pullback-functor lemmas above.
    rw [pullback_strictification_identity_presentation_map_fiber]
    let β :=
      ((pullback_strictification_identity_presentation_fiber_map p hc f ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj (Fiber.mk (rfl : p.obj y = p.obj y)))
            (Category.comp_id (p.map f)).symm)) ≫
        ((pullback_strictification_functor p hc).toPseudofunctor'.map
              (pullback_strictification_identity_presentation_map p hc f).base.op.toLoc).toFunctor.map
          (pullback_strictification_identity_presentation_map p hc g).fiber ≫
        ((pullback_strictification_functor p hc).toPseudofunctor'.mapComp
              (pullback_strictification_identity_presentation_map p hc g).base.op.toLoc
              (pullback_strictification_identity_presentation_map p hc f).base.op.toLoc).inv.toNatTrans.app
          (pullback_strictification_identity_presentation p hc z).fiber)
    have htarget :=
      pullback_strictification_identity_presentation_map_comp_target_transport_precompose
        (p := p) (hc := hc) (f := f) (g := g) (β := β)
    exact htarget.trans <| by
      let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
      let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
      let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
      let α :=
        pullback_strictification_identity_presentation_fiber_map p hc f ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj yFiber)
            (Category.comp_id (p.map f)).symm)
      let γ :=
        ((pullback_strictification_functor p hc).toPseudofunctor'.map
              (pullback_strictification_identity_presentation_map p hc f).base.op.toLoc).toFunctor.map
          (pullback_strictification_identity_presentation_map p hc g).fiber ≫
        ((pullback_strictification_functor p hc).toPseudofunctor'.mapComp
              (pullback_strictification_identity_presentation_map p hc g).base.op.toLoc
              (pullback_strictification_identity_presentation_map p hc f).base.op.toLoc).inv.toNatTrans.app
          (pullback_strictification_identity_presentation p hc z).fiber
      have htail :=
        pullback_strictification_identity_presentation_map_comp_rhs_tail_fac
          (p := p) (hc := hc) (f := f) (g := g)
      dsimp only at htail
      have hf :=
        pullback_strictification_identity_presentation_map_fiber_fac
          (p := p) (hc := hc) (f := f)
      rw [pullback_strictification_identity_presentation_map_fiber] at hf
      change Fiber.fiberInclusion.map α ≫ hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber =
        (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ f at hf
      change Fiber.fiberInclusion.map (α ≫ γ) ≫
          hc.map
            ((pullback_strictification_identity_presentation_map p hc f ≫
                pullback_strictification_identity_presentation_map p hc g).base ≫
              𝟙 (p.obj z)) zFiber =
        (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ (f ≫ g)
      rw [Functor.map_comp]
      simp only [Category.assoc]
      erw [htail]
      calc
        Fiber.fiberInclusion.map α ≫
            (hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber ≫ g) =
          (Fiber.fiberInclusion.map α ≫ hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber) ≫ g := by
          simp [Category.assoc]
        _ = ((((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ f) ≫ g := by
          exact congrArg (fun k ↦ k ≫ g) hf
        _ = (((hc.pullbackIdIso (p.obj x)).symm.app xFiber).hom.1) ≫ (f ≫ g) := by
          simp [Category.assoc]

/-- Helper for Lemma 4.36.4: after identifying the composite target-base arrow with
`p.map (f ≫ g)`, the postcomposed composite fiber of the two identity-presentation maps already
agrees with the postcomposed direct composite fiber. This records the exact stabilized goal shape
used by the `map_comp` proof. -/
private theorem pullback_strictification_identity_presentation_map_comp_fiber_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
    Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_map p hc (f ≫ g)).fiber ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber =
      Fiber.fiberInclusion.map
        ((pullback_strictification_identity_presentation_map p hc f ≫
            pullback_strictification_identity_presentation_map p hc g).fiber ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
            (pullback_strictification_identity_presentation_map_comp_target_base
              p hc f g))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber := by
  -- Route correction: the left-hand direct composite factorization is already proved, so the only
  -- remaining blocker is the explicit factorization of the raw right-hand composite fiber.
  have hleft :=
    pullback_strictification_identity_presentation_map_comp_lhs_fiber_fac
      (p := p) (hc := hc) (f := f) (g := g)
  have hright :=
    pullback_strictification_identity_presentation_map_comp_rhs_fiber_fac
      (p := p) (hc := hc) (f := f) (g := g)
  exact hleft.trans hright.symm

/-- Helper for Lemma 4.36.4: temporary composition-law probe. -/
private theorem pullback_strictification_identity_presentation_map_comp_probe
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y z : S} (f : x ⟶ y) (g : y ⟶ z) :
    pullback_strictification_identity_presentation_map p hc (f ≫ g) =
      pullback_strictification_identity_presentation_map p hc f ≫
        pullback_strictification_identity_presentation_map p hc g := by
  -- First match the base components; the remaining work is the fiber comparison after
  -- postcomposing with the chosen pullback arrow over `p.map (f ≫ g)`.
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _
    (pullback_strictification_identity_presentation_map_comp_base p hc f g) ?_
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let zFiber : Fiber p (p.obj z) := Fiber.mk (rfl : p.obj z = p.obj z)
  -- The strict target pullback arrow is strongly cartesian, so it suffices to compare both
  -- fiber components after postcomposition with it.
  apply pullback_strictification_hom_ext p hc (p.map (f ≫ g) ≫ 𝟙 (p.obj z))
  -- Route correction: first rewrite the target into the explicit composite-fiber expression with
  -- the named base transport from `pullback_strictification_identity_presentation_map_comp_target_base`.
  change Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_map p hc (f ≫ g)).fiber ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber =
      Fiber.fiberInclusion.map
        ((pullback_strictification_identity_presentation_map p hc f ≫
            pullback_strictification_identity_presentation_map p hc g).fiber ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj zFiber)
            (pullback_strictification_identity_presentation_map_comp_target_base
              p hc f g))) ≫
        hc.map (p.map (f ≫ g) ≫ 𝟙 (p.obj z)) zFiber
  -- One rewrite by the raw composite-fiber comparison identifies the two sides before any
  -- postcomposition with the chosen pullback arrow.
  exact pullback_strictification_identity_presentation_map_comp_fiber_eq
    (p := p) (hc := hc) (f := f) (g := g)

/-- Helper for Lemma 4.36.4: the forward identity-presentation comparison carries the
source object and source morphism over exactly the original base object and base morphism. This
keeps the later based-functor construction on concrete data instead of re-expanding the
co-Grothendieck presentation. -/
private theorem pullback_strictification_identity_presentation_over_base_data
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    (pullback_strictification_identity_presentation p hc x).base = p.obj x ∧
      (pullback_strictification_identity_presentation_map p hc f).base = p.map f := by
  constructor
  · exact pullback_strictification_identity_presentation_base p hc x
  · exact pullback_strictification_identity_presentation_map_base p hc f

/-- Helper for Lemma 4.36.4: the forward identity-presentation comparison is literally over
`p` after applying the strictification projection surface. This is the based-functor surface of the
source-text map `x ↦ (x, id)`. -/
private theorem pullback_strictification_identity_presentation_projection_data
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    (pullback_strictification_projection_surface p hc).obj
        (pullback_strictification_identity_presentation p hc x) = p.obj x ∧
      (pullback_strictification_projection_surface p hc).map
        (pullback_strictification_identity_presentation_map p hc f) = p.map f := by
  constructor
  · exact pullback_strictification_identity_presentation_base p hc x
  · exact pullback_strictification_identity_presentation_map_base p hc f

/-- Helper for Lemma 4.36.4: the source-text assignment `x ↦ (x, id)` is a based functor from the
original fibred category to the strictification surface over the same base. -/
private noncomputable def pullback_strictification_identity_presentation_basedFunctor
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor (pullback_strictification_projection_surface p hc) where
  toFunctor :=
    { obj := fun x ↦ pullback_strictification_identity_presentation p hc x
      map := fun f ↦ pullback_strictification_identity_presentation_map p hc f
      map_id := fun x ↦
        pullback_strictification_identity_presentation_map_id (p := p) (hc := hc) x
      map_comp := fun f g ↦
        pullback_strictification_identity_presentation_map_comp_probe
          (p := p) (hc := hc) f g }

/-- Helper for Lemma 4.36.4: the target-side transport tail in the evaluation of an
identity-presentation morphism collapses to the original chosen pullback arrow. -/
private theorem pullback_strictification_identity_presentation_target_tail_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (y : Fiber p T) :
    Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj y) (Category.comp_id f).symm) ≫
          (hc.pullbackCompIso (𝟙 T) f).hom.app y) ≫
        hc.map f ((hc.pullbackFunctor (𝟙 T)).obj y) ≫
          ((hc.pullbackIdIso T).inv.app y).1 =
      hc.map f y := by
  rw [Functor.map_comp]
  have hinv : ((hc.pullbackIdIso T).inv.app y).1 = hc.map (𝟙 T) y := by
    simpa [PullbackChoice.pullbackIdIso] using hc.pullbackIdComponentIso_inv_eq T y
  have hcomp :
      ((hc.pullbackCompIso (𝟙 T) f).hom.app y).1 ≫
          hc.map f ((hc.pullbackFunctor (𝟙 T)).obj y) ≫
            ((hc.pullbackIdIso T).inv.app y).1 =
        hc.map (f ≫ 𝟙 T) y := by
    rw [hinv]
    simpa [PullbackChoice.pullbackCompIso, Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := 𝟙 T) (g := f) y
  have htransport :=
    pullback_strictification_eqToHom_component_postcompose_eq
      (p := p) (hc := hc) (f := f) (g := f ≫ 𝟙 T)
      (e := (Category.comp_id f).symm) (x := y)
  have htransportObj :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj y) (Category.comp_id f).symm)) ≫
        hc.map (f ≫ 𝟙 T) y = hc.map f y := by
    simpa using htransport
  have hleft :
      (Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj y) (Category.comp_id f).symm)) ≫
          Fiber.fiberInclusion.map ((hc.pullbackCompIso (𝟙 T) f).hom.app y)) ≫
        hc.map f ((hc.pullbackFunctor (𝟙 T)).obj y) ≫
          ((hc.pullbackIdIso T).inv.app y).1 =
        Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj y) (Category.comp_id f).symm)) ≫
        hc.map (f ≫ 𝟙 T) y := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj y) (Category.comp_id f).symm)) ≫ t)
        hcomp
  exact hleft.trans htransportObj

/-- Helper for Lemma 4.36.4: the target-side transport tail specialized to an identity base
arrow collapses to the chosen identity pullback arrow. This is the identity-case piece needed for
the eventual evaluation functoriality proof. -/
private theorem pullback_strictification_identity_presentation_identity_target_tail_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {T : C} (y : Fiber p T) :
    Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj y)
          (Category.comp_id (𝟙 T)).symm) ≫
          (hc.pullbackCompIso (𝟙 T) (𝟙 T)).hom.app y) ≫
        hc.map (𝟙 T) ((hc.pullbackFunctor (𝟙 T)).obj y) ≫
          ((hc.pullbackIdIso T).inv.app y).1 =
      hc.map (𝟙 T) y := by
  rw [Functor.map_comp]
  exact pullback_strictification_identity_presentation_target_tail_fac
    (p := p) (hc := hc) (f := 𝟙 T) (y := y)

/-- Helper for Lemma 4.36.4: evaluating the forward identity-presentation morphism and then
applying the identity-pullback comparison recovers the original morphism. This is the naturality
calculation for the unit side of the eventual comparison equivalence. -/
private theorem pullback_strictification_identity_presentation_map_evaluation_naturality
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    pullback_strictification_evaluation_map p hc
        (pullback_strictification_identity_presentation_map p hc f) ≫
      (pullback_strictification_identity_presentation_evaluation_iso p hc y).hom =
    (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ≫ f := by
  dsimp [pullback_strictification_evaluation_map, pullback_strictification_identity_presentation_map]
  simp [pullback_strictification_identity_presentation_evaluation_iso,
    pullback_strictification_identity_presentation, pullbackStrictificationFiberForget]
  let xFiber : Fiber p (p.obj x) := Fiber.mk (rfl : p.obj x = p.obj x)
  let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
  change Fiber.fiberInclusion.map
        (pullback_strictification_identity_presentation_fiber_map p hc f ≫
          eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj yFiber)
            (Category.comp_id (p.map f)).symm)) ≫
      ((hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber).1 ≫
        hc.map (p.map f) ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber) ≫
          ((hc.pullbackIdIso (p.obj y)).inv.app yFiber).1 =
    ((hc.pullbackIdIso (p.obj x)).inv.app xFiber).1 ≫ f
  rw [Functor.map_comp]
  have htail :=
    pullback_strictification_identity_presentation_target_tail_fac
      (p := p) (hc := hc) (f := p.map f) (y := yFiber)
  have hfac :=
    pullback_strictification_identity_presentation_fiber_map_fac
      (p := p) (hc := hc) f
  have hleft :
      Fiber.fiberInclusion.map
          (pullback_strictification_identity_presentation_fiber_map p hc f) ≫
        (Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj yFiber)
            (Category.comp_id (p.map f)).symm) ≫
            (hc.pullbackCompIso (𝟙 (p.obj y)) (p.map f)).hom.app yFiber) ≫
          hc.map (p.map f) ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber) ≫
            ((hc.pullbackIdIso (p.obj y)).inv.app yFiber).1) =
      ((hc.pullbackIdIso (p.obj x)).inv.app xFiber).1 ≫ f := by
    rw [htail]
    simpa [xFiber, yFiber] using hfac
  simpa [Category.assoc] using hleft

/-- Helper for Lemma 4.36.4: the inverse form of the identity-presentation evaluation
naturality square. This is the same unit-side compatibility rewritten for the inverse components of
the objectwise comparison isomorphisms. -/
private theorem pullback_strictification_identity_presentation_map_evaluation_naturality_inv
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ≫
      pullback_strictification_evaluation_map p hc
        (pullback_strictification_identity_presentation_map p hc f) =
    f ≫ (pullback_strictification_identity_presentation_evaluation_iso p hc y).inv := by
  let αx := pullback_strictification_identity_presentation_evaluation_iso p hc x
  let αy := pullback_strictification_identity_presentation_evaluation_iso p hc y
  let g := pullback_strictification_evaluation_map p hc
        (pullback_strictification_identity_presentation_map p hc f)
  have hnat : g ≫ αy.hom = αx.hom ≫ f := by
    simpa [g, αx, αy] using
      pullback_strictification_identity_presentation_map_evaluation_naturality p hc f
  calc
    αx.inv ≫ g = (αx.inv ≫ g) ≫ (αy.hom ≫ αy.inv) := by simp
    _ = αx.inv ≫ (g ≫ αy.hom) ≫ αy.inv := by simp [Category.assoc]
    _ = αx.inv ≫ (αx.hom ≫ f) ≫ αy.inv := by rw [hnat]
    _ = (αx.inv ≫ αx.hom) ≫ f ≫ αy.inv := by simp [Category.assoc]
    _ = f ≫ αy.inv := by simp [αx.inv_hom_id]

/-- Helper for Lemma 4.36.4: package the two concrete naturality equations for the
identity-presentation comparison. Keeping this as data avoids repeatedly unfolding the transport-heavy
evaluation map when the unit-side natural isomorphism is assembled. -/
private theorem pullback_strictification_identity_presentation_map_evaluation_naturality_data
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) {x y : S} (f : x ⟶ y) :
    pullback_strictification_evaluation_map p hc
        (pullback_strictification_identity_presentation_map p hc f) ≫
      (pullback_strictification_identity_presentation_evaluation_iso p hc y).hom =
    (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ≫ f ∧
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ≫
        pullback_strictification_evaluation_map p hc
          (pullback_strictification_identity_presentation_map p hc f) =
      f ≫ (pullback_strictification_identity_presentation_evaluation_iso p hc y).inv := by
  constructor
  · exact pullback_strictification_identity_presentation_map_evaluation_naturality p hc f
  · exact pullback_strictification_identity_presentation_map_evaluation_naturality_inv p hc f

/-- Helper for Lemma 4.36.4: the unit-side naturality calculation specialized to an
identity morphism. This is the identity component of the source-text comparison
`S -> S' -> S`. -/
theorem pullback_strictification_identity_presentation_map_evaluation_id_naturality_data
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (x : S) :
    pullback_strictification_evaluation_map p hc
        (pullback_strictification_identity_presentation_map p hc (𝟙 x)) ≫
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
    (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ∧
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ≫
        pullback_strictification_evaluation_map p hc
          (pullback_strictification_identity_presentation_map p hc (𝟙 x)) =
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv := by
  constructor
  · calc
      pullback_strictification_evaluation_map p hc
          (pullback_strictification_identity_presentation_map p hc (𝟙 x)) ≫
        (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom =
          (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom ≫ 𝟙 x :=
            pullback_strictification_identity_presentation_map_evaluation_naturality
              (p := p) (hc := hc) (f := 𝟙 x)
      _ = (pullback_strictification_identity_presentation_evaluation_iso p hc x).hom := by simp
  · calc
      (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ≫
          pullback_strictification_evaluation_map p hc
            (pullback_strictification_identity_presentation_map p hc (𝟙 x)) =
        𝟙 x ≫ (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv :=
          pullback_strictification_identity_presentation_map_evaluation_naturality_inv
            (p := p) (hc := hc) (f := 𝟙 x)
      _ = (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv := by simp

/-- Helper for Lemma 4.36.4: once a comparison equivalence to a split fibred category has been
built, the final existence statement is immediate by packaging that target together with its split
structure. -/
private theorem exists_split_package_of_equivalence
    {X Y :
      FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C}
    (e : X ≌ Y) (hY : Functor.IsSplitFibredCategory Y.p) :
    ∃ (Z : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C)
      (_ : X ≌ Z), Functor.IsSplitFibredCategory Z.p := by
  -- This is the final owner-level packaging step used after the comparison equivalence is built.
  exact ⟨Y, e, hY⟩

/-- Helper for Lemma 4.36.4: the canonical strictification already carries a split fibred
structure, so the remaining work in the main theorem is purely to build the comparison
equivalence from `p`. -/
private theorem canonical_pullback_strictification_has_split_structure
    (p : S ⥤ C) [p.IsFibered] :
    Nonempty
      (Functor.IsSplitFibredCategory
        (pullback_strictification p (canonicalPullbackChoice p)).p) := by
  -- This isolates the solved split half of the argument in a form that the final equivalence
  -- packaging can consume directly.
  exact ⟨canonical_pullback_strictification_isSplit p⟩

/-- Helper for Lemma 4.36.4: the canonical strictification target can be packaged together with
its split structure as a single owner-level witness. This isolates the already-complete target
half of the final existence theorem from the still-missing comparison equivalence. -/
private theorem canonical_pullback_strictification_target_with_split
    (p : S ⥤ C) [p.IsFibered] :
    ∃ Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C,
      Y = pullback_strictification p (canonicalPullbackChoice p) ∧
        Functor.IsSplitFibredCategory Y.p := by
  -- Keep the canonical strictification object explicit and attach its already-proved split
  -- structure so the future final proof only has to construct the comparison equivalence.
  refine ⟨pullback_strictification p (canonicalPullbackChoice p), rfl, ?_⟩
  simpa using canonical_pullback_strictification_isSplit p

/-- Helper for Lemma 4.36.4: the canonical strictification already provides an inhabited
owner-level split witness, packaged as a sigma-type so the final theorem only has to attach the
comparison equivalence from `p`. -/
private theorem canonical_pullback_strictification_sigma_split_witness
    (p : S ⥤ C) [p.IsFibered] :
    Nonempty
      { Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C //
        Functor.IsSplitFibredCategory Y.p } := by
  -- The canonical strictification itself is already split, so it is an immediate subtype witness.
  exact ⟨⟨pullback_strictification p (canonicalPullbackChoice p),
    canonical_pullback_strictification_isSplit p⟩⟩

/-- Helper for Lemma 4.36.4: the projection surface of the canonical strictification is itself a
split fibred category. This rewrites the already proved owner-level split structure to the
explicit strictification surface that the eventual comparison equivalence must target. -/
private theorem canonical_pullback_strictification_surface_isSplit
    (p : S ⥤ C) [p.IsFibered] :
    Functor.IsSplitFibredCategory
      (pullback_strictification_projection_surface p (canonicalPullbackChoice p)) := by
  -- The owner-level strictification `pullback_strictification p _` is definitionally the fibred
  -- category obtained from this projection surface, so its split structure transfers directly.
  simpa [pullback_strictification] using
    canonical_pullback_strictification_isSplit p

/-- Helper for Lemma 4.36.4: the canonical strictification already furnishes an inhabited split
witness over `C`, so the unresolved part of the main theorem is only the comparison equivalence
from `p` to that witness. -/
private theorem canonical_pullback_strictification_exists_split_witness_nonempty
    (p : S ⥤ C) [p.IsFibered] :
    Nonempty
      (∃ Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C,
        Functor.IsSplitFibredCategory Y.p) := by
  -- This packages the already-proved strictification split witness into a form ready for later
  -- classical choice, without touching the still-missing comparison equivalence.
  exact ⟨canonical_pullback_strictification_exists_split_witness p⟩

/-- Helper for Lemma 4.36.4: the canonical strictification owner is literally the owner obtained
by wrapping its strict co-Grothendieck surface as a fibred category over `C`. This isolates the
owner-level identification that the final comparison equivalence must target. -/
private theorem canonical_pullback_strictification_eq_ofFunctor_surface
    (p : S ⥤ C) [p.IsFibered] :
    pullback_strictification p (canonicalPullbackChoice p) =
      FibredCategoryOver.ofFunctor
        (pullback_strictification_projection_surface p (canonicalPullbackChoice p)) := by
  -- Both sides are definitionally the same owner built from the canonical strict surface.
  rfl

/-- Helper for Lemma 4.36.4: the canonical strictification packages the exact target-side data
needed by the final theorem, namely the explicit projection description and the split witness that
will be attached once the comparison equivalence from `p` is available. -/
private theorem canonical_pullback_strictification_surface_split_data
    (p : S ⥤ C) [p.IsFibered] :
    (pullback_strictification p (canonicalPullbackChoice p)).p =
        pullback_strictification_projection_surface p (canonicalPullbackChoice p) ∧
      Functor.IsSplitFibredCategory
        (pullback_strictification p (canonicalPullbackChoice p)).p := by
  -- Package the already proved owner-projection identification with the split structure of the
  -- canonical strictification so the remaining blocker is only the comparison equivalence.
  constructor
  · exact canonical_pullback_strictification_owner_projection p
  · exact canonical_pullback_strictification_isSplit p

/-- Helper for Lemma 4.36.4: the canonical strictification already gives the split target object
for the final theorem; the only missing datum is the equivalence from `FibredCategoryOver.ofFunctor p`
to this target. -/
private theorem canonical_pullback_strictification_exists_split_target
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C),
      Functor.IsSplitFibredCategory Y.p := by
  -- The strictification itself is already split, so it serves as the target owner.
  refine ⟨pullback_strictification p (canonicalPullbackChoice p), ?_⟩
  simpa using canonical_pullback_strictification_isSplit p

/-- Helper for Lemma 4.36.4: once the comparison equivalence from `p` to the canonical
strictification has been built, the final existence statement follows immediately by attaching the
already proved split structure on that canonical target. -/
private theorem exists_split_of_canonical_pullback_strictification_equivalence
    {X₀ : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C}
    (p : S ⥤ C) [p.IsFibered]
    (e : X₀ ≌ pullback_strictification p (canonicalPullbackChoice p)) :
    ∃ (Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C)
      (e' : X₀ ≌ Y),
      Functor.IsSplitFibredCategory Y.p := by
  -- The canonical strictification is already split, so the comparison equivalence is the only
  -- remaining datum to package.
  refine ⟨(pullback_strictification p (canonicalPullbackChoice p) : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C), e, ?_⟩
  simpa using canonical_pullback_strictification_isSplit p

/-- Helper for Lemma 4.36.4: once the source-text comparison functor is upgraded to explicit
based equivalence data over `C`, it already satisfies the standard
`IsEquivalenceOverBase` predicate. This packages the future quasi-inverse, unit, and counit in
the exact form expected by the owner-level comparison bridge. -/
private theorem
    pullback_strictification_identity_presentation_isEquivalenceOverBase_of_basedEquivalence
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    (e : BasedFunctor.EquivalenceOverBase
      (pullback_strictification_identity_presentation_basedFunctor p hc)) :
    (pullback_strictification_identity_presentation_basedFunctor p hc).IsEquivalenceOverBase := by
  -- The explicit quasi-inverse, unit, and counit data are already exactly the constructor fields
  -- for `BasedFunctor.IsEquivalenceOverBase`.
  exact BasedFunctor.IsEquivalenceOverBase.mkPrime
    (F := pullback_strictification_identity_presentation_basedFunctor p hc)
    e.inverse e.unitIso e.counitIso

/-- Helper for Lemma 4.36.4: the canonical strictification owner is trivially equivalent to
itself. This isolates the target-side bicategorical identity package that the final theorem will
reuse once the source-to-target comparison equivalence has been constructed. -/
private noncomputable def canonical_pullback_strictification_self_equivalence
    (p : S ⥤ C) [p.IsFibered] :
    pullback_strictification p (canonicalPullbackChoice p) ≌
      pullback_strictification p (canonicalPullbackChoice p) := by
  -- The strictification owner carries the identity equivalence given by identity unit and counit.
  refine
    Bicategory.Equivalence.mkOfAdjointifyCounit
      (f := 𝟙 (pullback_strictification p (canonicalPullbackChoice p)))
      (g := 𝟙 (pullback_strictification p (canonicalPullbackChoice p)))
      ?_ ?_
  · simpa using
      (Iso.refl
        (𝟙 (pullback_strictification p (canonicalPullbackChoice p))))
  · simpa using
      (Iso.refl
        (𝟙 (pullback_strictification p (canonicalPullbackChoice p))))

/-- Helper for Lemma 4.36.4: the canonical strictification already packages a self-equivalence
and its split structure in the target owner universe. This isolates the completely solved target
side of the final existence theorem from the remaining source-to-target comparison equivalence. -/
private theorem canonical_pullback_strictification_self_equivalence_with_split
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C)
      (e : Y ≌ Y), Functor.IsSplitFibredCategory Y.p := by
  -- The canonical strictification is already split, and its identity comparison supplies the
  -- trivial target-side equivalence package.
  refine ⟨pullback_strictification p (canonicalPullbackChoice p), ?_, ?_⟩
  · exact canonical_pullback_strictification_self_equivalence p
  simpa using canonical_pullback_strictification_isSplit p

/-- Helper for Lemma 4.36.4: for the canonical pullback choice, the objectwise unit isomorphism
already packages the exact over-base and triangle identities needed to build the source-side based
natural isomorphism in the final theorem. -/
private theorem canonical_pullback_strictification_identity_presentation_unit_data
    (p : S ⥤ C) [p.IsFibered] (x : S) :
    p.map
        (pullback_strictification_identity_presentation_evaluation_iso
          p (canonicalPullbackChoice p) x).hom =
      eqToHom
        (pullback_strictification_identity_presentation_evaluation_obj_base_eq
          p (canonicalPullbackChoice p) x) ∧
      p.map
          (pullback_strictification_identity_presentation_evaluation_iso
            p (canonicalPullbackChoice p) x).inv =
        eqToHom
          (pullback_strictification_identity_presentation_evaluation_obj_base_eq
            p (canonicalPullbackChoice p) x).symm ∧
      ((pullback_strictification_identity_presentation_evaluation_iso
            p (canonicalPullbackChoice p) x).hom ≫
            (pullback_strictification_identity_presentation_evaluation_iso
              p (canonicalPullbackChoice p) x).inv =
          𝟙
            (pullback_strictification_evaluation_obj p (canonicalPullbackChoice p)
              (pullback_strictification_identity_presentation
                p (canonicalPullbackChoice p) x)) ∧
        (pullback_strictification_identity_presentation_evaluation_iso
            p (canonicalPullbackChoice p) x).inv ≫
            (pullback_strictification_identity_presentation_evaluation_iso
              p (canonicalPullbackChoice p) x).hom =
          𝟙 x) := by
  -- This is exactly the previously established over-base-and-triangle package, specialized to the
  -- canonical pullback choice used by the final strictification.
  exact
    pullback_strictification_identity_presentation_evaluation_iso_over_base_triangle
      (p := p) (hc := canonicalPullbackChoice p) x

private noncomputable def identity_presentation_comparison_preimage_hom
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y : S}
    (φ : (pullback_strictification_identity_presentation_basedFunctor p hc).obj x ⟶
      (pullback_strictification_identity_presentation_basedFunctor p hc).obj y) : x ⟶ y :=
  (pullback_strictification_identity_presentation_evaluation_iso p hc x).inv ≫
    pullback_strictification_evaluation_map p hc φ ≫
      (pullback_strictification_identity_presentation_evaluation_iso p hc y).hom

private theorem identity_presentation_comparison_preimage_hom_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y : S}
    (φ : (pullback_strictification_identity_presentation_basedFunctor p hc).obj x ⟶
      (pullback_strictification_identity_presentation_basedFunctor p hc).obj y) :
    p.map (identity_presentation_comparison_preimage_hom p hc φ) = φ.base := by
  let αx := pullback_strictification_identity_presentation_evaluation_iso p hc x
  let αy := pullback_strictification_identity_presentation_evaluation_iso p hc y
  let hX := pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc x
  let hY := pullback_strictification_identity_presentation_evaluation_obj_base_eq p hc y
  have hInv : p.map αx.inv = eqToHom hX.symm := by
    simpa [αx, hX] using
      pullback_strictification_identity_presentation_evaluation_iso_inv_over_base
        (p := p) (hc := hc) (x := x)
  have hEval := pullback_strictification_evaluation_map_over_base (p := p) (hc := hc) (φ := φ)
  have hHom : p.map αy.hom = eqToHom hY := by
    simpa [αy, hY] using
      pullback_strictification_identity_presentation_evaluation_iso_hom_over_base
        (p := p) (hc := hc) (x := y)
  dsimp [identity_presentation_comparison_preimage_hom]
  rw [Functor.map_comp, Functor.map_comp]
  calc
    p.map αx.inv ≫ p.map (pullback_strictification_evaluation_map p hc φ) ≫ p.map αy.hom =
        eqToHom hX.symm ≫ p.map (pullback_strictification_evaluation_map p hc φ) ≫ p.map αy.hom := by
          exact congrArg (fun k ↦ k ≫ p.map (pullback_strictification_evaluation_map p hc φ) ≫ p.map αy.hom) hInv
    _ = eqToHom hX.symm ≫
          (eqToHom (pullback_strictification_evaluation_obj_base p hc
              ((pullback_strictification_identity_presentation_basedFunctor p hc).obj x)) ≫
            φ.base ≫
              eqToHom (pullback_strictification_evaluation_obj_base p hc
                ((pullback_strictification_identity_presentation_basedFunctor p hc).obj y)).symm) ≫
          p.map αy.hom := by
          exact congrArg (fun k ↦ eqToHom hX.symm ≫ k ≫ p.map αy.hom) hEval
    _ = eqToHom hX.symm ≫
          (eqToHom (pullback_strictification_evaluation_obj_base p hc
              ((pullback_strictification_identity_presentation_basedFunctor p hc).obj x)) ≫
            φ.base ≫
              eqToHom (pullback_strictification_evaluation_obj_base p hc
                ((pullback_strictification_identity_presentation_basedFunctor p hc).obj y)).symm) ≫
          eqToHom hY := by
          exact congrArg (fun k ↦ eqToHom hX.symm ≫
            (eqToHom (pullback_strictification_evaluation_obj_base p hc
              ((pullback_strictification_identity_presentation_basedFunctor p hc).obj x)) ≫
            φ.base ≫
              eqToHom (pullback_strictification_evaluation_obj_base p hc
                ((pullback_strictification_identity_presentation_basedFunctor p hc).obj y)).symm) ≫ k) hHom
    _ = φ.base := by
          change eqToHom hX.symm ≫ (eqToHom hX ≫ φ.base ≫ eqToHom hY.symm) ≫ eqToHom hY = φ.base
          simp [Category.assoc]
          have hwY :
              BasedFunctor.w_obj (pullback_strictification_identity_presentation_basedFunctor p hc) y =
                pullback_strictification_identity_presentation_base p hc y := by
            apply Subsingleton.elim
          change φ.base ≫
              eqToHom (BasedFunctor.w_obj
                (pullback_strictification_identity_presentation_basedFunctor p hc) y) = φ.base
          have hwYid :
              eqToHom (BasedFunctor.w_obj
                (pullback_strictification_identity_presentation_basedFunctor p hc) y) =
                𝟙 (p.obj y) := by
            rw [hwY]
            rfl
          exact (congrArg (fun k ↦ φ.base ≫ k) hwYid).trans (Category.comp_id φ.base)


private theorem identity_presentation_comparison_eval_target_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y : S}
    (φ : (pullback_strictification_identity_presentation_basedFunctor p hc).obj x ⟶
      (pullback_strictification_identity_presentation_basedFunctor p hc).obj y) :
    let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
    pullback_strictification_evaluation_map p hc φ ≫
        (pullback_strictification_identity_presentation_evaluation_iso p hc y).hom =
      Fiber.fiberInclusion.map φ.fiber ≫
        hc.map (φ.base ≫ 𝟙 (p.obj y)) yFiber := by
  dsimp only
  let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
  dsimp [pullback_strictification_evaluation_map,
    pullback_strictification_identity_presentation_evaluation_iso,
    pullback_strictification_identity_presentation_basedFunctor,
    pullback_strictification_identity_presentation,
    pullbackStrictificationFiberForget]
  change (Fiber.fiberInclusion.map φ.fiber ≫
      ((hc.pullbackCompIso (𝟙 (p.obj y)) φ.base).hom.app yFiber).1 ≫
        hc.map φ.base ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber)) ≫
      ((hc.pullbackIdIso (p.obj y)).inv.app yFiber).1 =
    Fiber.fiberInclusion.map φ.fiber ≫ hc.map (φ.base ≫ 𝟙 (p.obj y)) yFiber
  have hid :
      ((hc.pullbackIdIso (p.obj y)).inv.app yFiber).1 =
        hc.map (𝟙 (p.obj y)) yFiber := by
    simpa [PullbackChoice.pullbackIdIso] using
      hc.pullbackIdComponentIso_inv_eq (p.obj y) yFiber
  have hcomp :
      (((hc.pullbackCompIso (𝟙 (p.obj y)) φ.base).hom.app yFiber).1 ≫
          hc.map φ.base ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber)) ≫
        hc.map (𝟙 (p.obj y)) yFiber =
      hc.map (φ.base ≫ 𝟙 (p.obj y)) yFiber := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := 𝟙 (p.obj y)) (g := φ.base) yFiber
  calc
    (Fiber.fiberInclusion.map φ.fiber ≫
      ((hc.pullbackCompIso (𝟙 (p.obj y)) φ.base).hom.app yFiber).1 ≫
        hc.map φ.base ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber)) ≫
      ((hc.pullbackIdIso (p.obj y)).inv.app yFiber).1 =
        Fiber.fiberInclusion.map φ.fiber ≫
          ((((hc.pullbackCompIso (𝟙 (p.obj y)) φ.base).hom.app yFiber).1 ≫
            hc.map φ.base ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber)) ≫
              ((hc.pullbackIdIso (p.obj y)).inv.app yFiber).1) := by
          simp [Category.assoc]
    _ = Fiber.fiberInclusion.map φ.fiber ≫
          ((((hc.pullbackCompIso (𝟙 (p.obj y)) φ.base).hom.app yFiber).1 ≫
            hc.map φ.base ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber)) ≫
              hc.map (𝟙 (p.obj y)) yFiber) := by
          exact congrArg (fun k ↦ Fiber.fiberInclusion.map φ.fiber ≫
            ((((hc.pullbackCompIso (𝟙 (p.obj y)) φ.base).hom.app yFiber).1 ≫
              hc.map φ.base ((hc.pullbackFunctor (𝟙 (p.obj y))).obj yFiber)) ≫ k)) hid
    _ = Fiber.fiberInclusion.map φ.fiber ≫ hc.map (φ.base ≫ 𝟙 (p.obj y)) yFiber := by
          exact congrArg (fun k ↦ Fiber.fiberInclusion.map φ.fiber ≫ k) hcomp


private theorem identity_presentation_comparison_map_preimage_hom
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y : S}
    (φ : (pullback_strictification_identity_presentation_basedFunctor p hc).obj x ⟶
      (pullback_strictification_identity_presentation_basedFunctor p hc).obj y) :
    (pullback_strictification_identity_presentation_basedFunctor p hc).map
      (identity_presentation_comparison_preimage_hom p hc φ) = φ := by
  let F := pullback_strictification_identity_presentation_basedFunctor p hc
  let αx := pullback_strictification_identity_presentation_evaluation_iso p hc x
  let αy := pullback_strictification_identity_presentation_evaluation_iso p hc y
  let f : x ⟶ y := identity_presentation_comparison_preimage_hom p hc φ
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · dsimp [F, f, pullback_strictification_identity_presentation_basedFunctor]
    exact identity_presentation_comparison_preimage_hom_base p hc φ
  · let yFiber : Fiber p (p.obj y) := Fiber.mk (rfl : p.obj y = p.obj y)
    apply pullback_strictification_hom_ext p hc (p.map f ≫ 𝟙 (p.obj y))
    change Fiber.fiberInclusion.map
          (pullback_strictification_identity_presentation_map p hc f).fiber ≫
        hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber =
      Fiber.fiberInclusion.map (φ.fiber ≫ eqToHom (congrArg
        (fun k ↦ (hc.pullbackFunctor k).obj yFiber)
        (congrArg (fun k ↦ k ≫ 𝟙 (p.obj y))
          (identity_presentation_comparison_preimage_hom_base p hc φ).symm))) ≫
        hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber
    rw [pullback_strictification_identity_presentation_map_fiber_fac]
    rw [Functor.map_comp]
    have htransport :
        Fiber.fiberInclusion.map
            (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj yFiber)
              (congrArg (fun k ↦ k ≫ 𝟙 (p.obj y))
                (identity_presentation_comparison_preimage_hom_base p hc φ).symm))) ≫
          hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber =
        hc.map (φ.base ≫ 𝟙 (p.obj y)) yFiber := by
      have h0 :=
        pullback_strictification_eqToHom_component_postcompose_eq
          (p := p) (hc := hc)
          (f := φ.base ≫ 𝟙 (p.obj y))
          (g := p.map f ≫ 𝟙 (p.obj y))
          (e := congrArg (fun k ↦ k ≫ 𝟙 (p.obj y))
            (identity_presentation_comparison_preimage_hom_base p hc φ).symm)
          (x := yFiber)
      rw [eqToHom_app] at h0
      exact h0
    have hleft :
        (((hc.pullbackIdIso (p.obj x)).symm.app (Fiber.mk (rfl : p.obj x = p.obj x))).hom.1) ≫ f =
          pullback_strictification_evaluation_map p hc φ ≫
            (pullback_strictification_identity_presentation_evaluation_iso p hc y).hom := by
      change αx.hom ≫ f =
        pullback_strictification_evaluation_map p hc φ ≫ αy.hom
      dsimp [f, identity_presentation_comparison_preimage_hom]
      simp [αy]
      rw [Iso.hom_inv_id_assoc]
      rfl
    have htarget :
        pullback_strictification_evaluation_map p hc φ ≫
            (pullback_strictification_identity_presentation_evaluation_iso p hc y).hom =
          Fiber.fiberInclusion.map φ.fiber ≫
            hc.map (φ.base ≫ 𝟙 (p.obj y)) yFiber :=
      identity_presentation_comparison_eval_target_fac p hc φ
    have hright :
        Fiber.fiberInclusion.map φ.fiber ≫
            hc.map (φ.base ≫ 𝟙 (p.obj y)) yFiber =
          (Fiber.fiberInclusion.map φ.fiber ≫
            Fiber.fiberInclusion.map
              (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj yFiber)
                (congrArg (fun k ↦ k ≫ 𝟙 (p.obj y))
                  (identity_presentation_comparison_preimage_hom_base p hc φ).symm)))) ≫
            hc.map (p.map f ≫ 𝟙 (p.obj y)) yFiber := by
      have h := congrArg (fun k ↦ Fiber.fiberInclusion.map φ.fiber ≫ k) htransport.symm
      simpa [Category.assoc] using h
    exact hleft.trans (htarget.trans hright)


private theorem identity_presentation_comparison_preimage_map_hom
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {x y : S} (g : x ⟶ y) :
    identity_presentation_comparison_preimage_hom p hc
      ((pullback_strictification_identity_presentation_basedFunctor p hc).map g) = g := by
  let αx := pullback_strictification_identity_presentation_evaluation_iso p hc x
  let αy := pullback_strictification_identity_presentation_evaluation_iso p hc y
  have hnat :=
    pullback_strictification_identity_presentation_map_evaluation_naturality_inv
      (p := p) (hc := hc) (f := g)
  change αx.inv ≫
      pullback_strictification_evaluation_map p hc
        ((pullback_strictification_identity_presentation_basedFunctor p hc).map g) =
    g ≫ αy.inv at hnat
  dsimp [identity_presentation_comparison_preimage_hom]
  calc
    αx.inv ≫
          pullback_strictification_evaluation_map p hc
            ((pullback_strictification_identity_presentation_basedFunctor p hc).map g) ≫
        αy.hom =
      (αx.inv ≫
          pullback_strictification_evaluation_map p hc
            ((pullback_strictification_identity_presentation_basedFunctor p hc).map g)) ≫
        αy.hom := by
        simp [Category.assoc]
    _ = (g ≫ αy.inv) ≫ αy.hom := by
        exact congrArg (fun k ↦ k ≫ αy.hom) hnat
    _ = g := by
        simp [Category.assoc]


private noncomputable def identity_presentation_comparison_fullyFaithful
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    (pullback_strictification_identity_presentation_basedFunctor p hc).toFunctor.FullyFaithful where
  preimage := fun φ ↦ identity_presentation_comparison_preimage_hom p hc φ
  map_preimage := by
    intro X Y φ
    exact identity_presentation_comparison_map_preimage_hom p hc φ
  preimage_map := by
    intro X Y g
    exact identity_presentation_comparison_preimage_map_hom p hc g


private noncomputable def identity_presentation_comparison_obj_iso
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    (X : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')) :
    X ≅ (pullback_strictification_identity_presentation_basedFunctor p hc).obj
      (pullbackStrictificationFiberForget p hc X.base X.fiber).1 := by
  cases X with
  | mk U A =>
      let P := (pullback_strictification_functor p hc).toPseudofunctor'
      let yFiber : Fiber p U := pullbackStrictificationFiberForget p hc U A
      let strictId : PullbackStrictificationFiber p hc U :=
        { target := U, arrow := 𝟙 U, fiberObj := yFiber }
      let idIso := (hc.pullbackIdIso U).app yFiber
      let strictIso : A ≅ strictId :=
        { hom := idIso.hom
          inv := idIso.inv
          hom_inv_id := by
            exact idIso.hom_inv_id
          inv_hom_id := by
            exact idIso.inv_hom_id }
      let totalIso : ({ base := U, fiber := A } : Pseudofunctor.CoGrothendieck P) ≅
          { base := U, fiber := strictId } :=
        (Pseudofunctor.CoGrothendieck.ι P U).mapIso strictIso
      have hObj : { base := U, fiber := strictId } =
          (pullback_strictification_identity_presentation_basedFunctor p hc).obj yFiber.1 := by
        cases hY : yFiber with
        | mk obj h =>
            cases h
            have hy : yFiber = (Fiber.mk (rfl : p.obj obj = p.obj obj) : Fiber p (p.obj obj)) := by
              rw [hY]
              apply Subtype.ext
              rfl
            simp [pullback_strictification_identity_presentation_basedFunctor,
              pullback_strictification_identity_presentation, strictId, hy]
      exact totalIso ≪≫ eqToIso hObj


private theorem identity_presentation_comparison_eqToHom_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {X Y : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')}
    (h : X = Y) :
    (eqToHom h : X ⟶ Y).base = eqToHom (congrArg (fun Z ↦ Z.base) h) := by
  cases h
  rfl

private theorem identity_presentation_comparison_eqToHom_proof_irrel
    {X Y : C} (h₁ h₂ : X = Y) :
    (eqToHom h₁ : X ⟶ Y) = eqToHom h₂ := by
  cases h₁
  rfl

private theorem identity_presentation_comparison_eqToHom_comp_inv_proof_irrel
    {X Y : C} (h₁ : X = Y) (h₂ : Y = X) :
    (eqToHom h₁ : X ⟶ Y) ≫ eqToHom h₂ = 𝟙 X := by
  cases h₁
  simp

private theorem identity_presentation_comparison_eqToHom_comp_proof_irrel
    {X Y Z : C} (h₁ : X = Y) (h₂ : Y = Z) (h₃ : X = Z) :
    (eqToHom h₁ : X ⟶ Y) ≫ eqToHom h₂ = eqToHom h₃ := by
  cases h₁
  cases h₂
  cases h₃
  simp

private theorem identity_presentation_comparison_obj_iso_hom_isHomLift
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    (X : Pseudofunctor.CoGrothendieck ((pullback_strictification_functor p hc).toPseudofunctor')) :
    (pullback_strictification_projection_surface p hc).IsHomLift
      (𝟙 ((pullback_strictification_projection_surface p hc).obj X))
      (identity_presentation_comparison_obj_iso p hc X).hom := by
  cases X with
  | mk U A =>
      let P := (pullback_strictification_functor p hc).toPseudofunctor'
      let q := pullback_strictification_projection_surface p hc
      let yFiber : Fiber p U := pullbackStrictificationFiberForget p hc U A
      let strictId : PullbackStrictificationFiber p hc U :=
        { target := U, arrow := 𝟙 U, fiberObj := yFiber }
      let idIso := (hc.pullbackIdIso U).app yFiber
      let strictIso : A ≅ strictId :=
        { hom := idIso.hom
          inv := idIso.inv
          hom_inv_id := by exact idIso.hom_inv_id
          inv_hom_id := by exact idIso.inv_hom_id }
      let totalIso : ({ base := U, fiber := A } : Pseudofunctor.CoGrothendieck P) ≅
          { base := U, fiber := strictId } :=
        (Pseudofunctor.CoGrothendieck.ι P U).mapIso strictIso
      have hObj : { base := U, fiber := strictId } =
          (pullback_strictification_identity_presentation_basedFunctor p hc).obj yFiber.1 := by
        cases hY : yFiber with
        | mk obj h =>
            cases h
            have hy : yFiber = (Fiber.mk (rfl : p.obj obj = p.obj obj) : Fiber p (p.obj obj)) := by
              rw [hY]
              apply Subtype.ext
              rfl
            simp [pullback_strictification_identity_presentation_basedFunctor,
              pullback_strictification_identity_presentation, strictId, hy]
      have htotal : q.IsHomLift (𝟙 U) totalIso.hom := by
        apply IsHomLift.of_fac' q (𝟙 U) totalIso.hom rfl rfl
        dsimp [q, totalIso, pullback_strictification_projection_surface]
        simp
      have heq : q.IsHomLift (𝟙 U) (eqToIso hObj).hom := by
        apply IsHomLift.of_fac' q (𝟙 U) (eqToIso hObj).hom rfl yFiber.2
        have hmap := identity_presentation_comparison_eqToHom_base p hc hObj
        have hbase : congrArg (fun Z ↦ Z.base) hObj = yFiber.2.symm := by
          apply Subsingleton.elim
        calc
          (eqToHom hObj).base = eqToHom (congrArg (fun Z ↦ Z.base) hObj) := hmap
          _ = eqToHom yFiber.2.symm := by
            exact identity_presentation_comparison_eqToHom_proof_irrel
              (congrArg (fun Z ↦ Z.base) hObj) yFiber.2.symm
          _ = 𝟙 U ≫ 𝟙 U ≫ eqToHom yFiber.2.symm := by
            simp
      letI : q.IsHomLift (𝟙 U) totalIso.hom := htotal
      letI : q.IsHomLift (𝟙 U) (eqToIso hObj).hom := heq
      change q.IsHomLift (𝟙 U) (totalIso.hom ≫ (eqToIso hObj).hom)
      infer_instance


private theorem identity_presentation_comparison_same_fiber_lift_commutes_with_base
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {j : Pseudofunctor.CoGrothendieck
        ((pullback_strictification_functor p hc).toPseudofunctor') ⥤ S}
    (α : 𝟭 (Pseudofunctor.CoGrothendieck
        ((pullback_strictification_functor p hc).toPseudofunctor')) ≅
        j ⋙ (pullback_strictification_identity_presentation_basedFunctor p hc).toFunctor)
    (hjBaseObj : ∀ y : Pseudofunctor.CoGrothendieck
        ((pullback_strictification_functor p hc).toPseudofunctor'),
        p.obj (j.obj y) = (pullback_strictification_projection_surface p hc).obj y)
    (hαLift : ∀ y : Pseudofunctor.CoGrothendieck
        ((pullback_strictification_functor p hc).toPseudofunctor'),
        (pullback_strictification_projection_surface p hc).IsHomLift
          (𝟙 ((pullback_strictification_projection_surface p hc).obj y)) (α.hom.app y)) :
    j ⋙ p = pullback_strictification_projection_surface p hc := by
  let F := pullback_strictification_identity_presentation_basedFunctor p hc
  let q := pullback_strictification_projection_surface p hc
  refine CategoryTheory.Functor.ext hjBaseObj ?_
  intro y y' g
  have hyBase :
      IsHomLift.codomain_eq q (𝟙 (q.obj y)) (α.hom.app y) =
        Eq.trans (BasedFunctor.w_obj F (j.obj y)) (hjBaseObj y) := by
    apply Subsingleton.elim
  have hy'Base :
      IsHomLift.codomain_eq q (𝟙 (q.obj y')) (α.hom.app y') =
        Eq.trans (BasedFunctor.w_obj F (j.obj y')) (hjBaseObj y') := by
    apply Subsingleton.elim
  have hyVert :
      q.map (α.hom.app y) =
        eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y))
          (hjBaseObj y)).symm := by
    rw [← hyBase]
    simpa using (IsHomLift.fac' q (𝟙 (q.obj y)) (α.hom.app y))
  have hy'Vert :
      q.map (α.hom.app y') =
        eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y'))
          (hjBaseObj y')).symm := by
    rw [← hy'Base]
    simpa using (IsHomLift.fac' q (𝟙 (q.obj y')) (α.hom.app y'))
  have hnat := congrArg (Functor.map q) (α.hom.naturality g)
  rw [Functor.map_comp, Functor.map_comp, hyVert, hy'Vert] at hnat
  have hleft :
      eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y))
          (hjBaseObj y)) ≫
        q.map g ≫
          eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y'))
            (hjBaseObj y')).symm =
      q.map (F.toFunctor.map (j.map g)) := by
    have h0 :
        q.map g ≫
            eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y'))
              (hjBaseObj y')).symm =
          eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y))
            (hjBaseObj y)).symm ≫
            q.map (F.toFunctor.map (j.map g)) := by
      simpa using hnat
    let Aeq := Eq.trans (BasedFunctor.w_obj F (j.obj y)) (hjBaseObj y)
    have h1 := congrArg (fun k ↦ eqToHom Aeq ≫ k) h0
    have hcancel : (eqToHom Aeq : q.obj (F.toFunctor.obj (j.obj y)) ⟶ q.obj y) ≫
        eqToHom Aeq.symm = 𝟙 (q.obj (F.toFunctor.obj (j.obj y))) :=
      identity_presentation_comparison_eqToHom_comp_inv_proof_irrel Aeq Aeq.symm
    exact h1.trans (by
      calc
        eqToHom Aeq ≫ eqToHom Aeq.symm ≫ q.map (F.toFunctor.map (j.map g)) =
            (eqToHom Aeq ≫ eqToHom Aeq.symm) ≫ q.map (F.toFunctor.map (j.map g)) := by
          simp
        _ = 𝟙 (q.obj (F.toFunctor.obj (j.obj y))) ≫ q.map (F.toFunctor.map (j.map g)) := by
          exact congrArg (fun k ↦ k ≫ q.map (F.toFunctor.map (j.map g))) hcancel
        _ = q.map (F.toFunctor.map (j.map g)) := by
          simp)
  have hcomm :
      p.map (j.map g) =
        eqToHom (BasedFunctor.w_obj F (j.obj y)).symm ≫
          q.map (F.toFunctor.map (j.map g)) ≫
            eqToHom (BasedFunctor.w_obj F (j.obj y')) := by
    have h' := congrArg
      (fun k ↦
        eqToHom (BasedFunctor.w_obj F (j.obj y)).symm ≫
          k ≫
            eqToHom (BasedFunctor.w_obj F (j.obj y')))
      (Functor.congr_hom F.w (j.map g))
    simpa [Category.assoc] using h'.symm
  have hstep :
      eqToHom (BasedFunctor.w_obj F (j.obj y)).symm ≫
          q.map (F.toFunctor.map (j.map g)) ≫
            eqToHom (BasedFunctor.w_obj F (j.obj y')) =
        eqToHom (BasedFunctor.w_obj F (j.obj y)).symm ≫
          (eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y))
              (hjBaseObj y)) ≫
            q.map g ≫
              eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y'))
                (hjBaseObj y')).symm) ≫
            eqToHom (BasedFunctor.w_obj F (j.obj y')) := by
    have h' := congrArg
      (fun k ↦
        eqToHom (BasedFunctor.w_obj F (j.obj y)).symm ≫
          k ≫
            eqToHom (BasedFunctor.w_obj F (j.obj y')))
      hleft
    simpa [Category.assoc] using h'.symm
  have hfinal :
      eqToHom (BasedFunctor.w_obj F (j.obj y)).symm ≫
          (eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y))
              (hjBaseObj y)) ≫
            q.map g ≫
              eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y'))
                (hjBaseObj y')).symm) ≫
            eqToHom (BasedFunctor.w_obj F (j.obj y')) =
        eqToHom (hjBaseObj y) ≫ q.map g ≫ eqToHom (hjBaseObj y').symm := by
    have hleftPair :
        eqToHom (BasedFunctor.w_obj F (j.obj y)).symm ≫
            eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y)) (hjBaseObj y)) =
          eqToHom (hjBaseObj y) :=
      identity_presentation_comparison_eqToHom_comp_proof_irrel
        (BasedFunctor.w_obj F (j.obj y)).symm
        (Eq.trans (BasedFunctor.w_obj F (j.obj y)) (hjBaseObj y))
        (hjBaseObj y)
    have hrightPair :
        eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y')) (hjBaseObj y')).symm ≫
            eqToHom (BasedFunctor.w_obj F (j.obj y')) =
          eqToHom (hjBaseObj y').symm :=
      identity_presentation_comparison_eqToHom_comp_proof_irrel
        (Eq.trans (BasedFunctor.w_obj F (j.obj y')) (hjBaseObj y')).symm
        (BasedFunctor.w_obj F (j.obj y'))
        (hjBaseObj y').symm
    simp only [Category.assoc]
    have hL := congrArg (fun k ↦
      k ≫ q.map g ≫
        eqToHom (Eq.trans (BasedFunctor.w_obj F (j.obj y')) (hjBaseObj y')).symm ≫
          eqToHom (BasedFunctor.w_obj F (j.obj y'))) hleftPair
    have hR := congrArg (fun k ↦ eqToHom (hjBaseObj y) ≫ q.map g ≫ k) hrightPair
    simpa [Category.assoc] using hL.trans hR
  exact hcomm.trans (hstep.trans hfinal)

private theorem identity_presentation_comparison_isEquivalenceOverBase
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) :
    (pullback_strictification_identity_presentation_basedFunctor p hc).IsEquivalenceOverBase := by
  classical
  let F := pullback_strictification_identity_presentation_basedFunctor p hc
  let q := pullback_strictification_projection_surface p hc
  let jObj : Pseudofunctor.CoGrothendieck
      ((pullback_strictification_functor p hc).toPseudofunctor') → S :=
    fun X ↦ (pullbackStrictificationFiberForget p hc X.base X.fiber).1
  let i : ∀ X : Pseudofunctor.CoGrothendieck
      ((pullback_strictification_functor p hc).toPseudofunctor'), X ≅ F.obj (jObj X) :=
    fun X ↦ by
      simpa [F, jObj] using identity_presentation_comparison_obj_iso p hc X
  let hFF := identity_presentation_comparison_fullyFaithful p hc
  haveI : Full F.toFunctor := hFF.full
  haveI : Faithful F.toFunctor := hFF.faithful
  rcases (Functor.fully_faithful_objwise_iso_existsUnique_lift (F := F.toFunctor) jObj i) with
    ⟨j, ⟨hjObj, α, hα⟩, _⟩
  have hjBaseObj : ∀ y : Pseudofunctor.CoGrothendieck
      ((pullback_strictification_functor p hc).toPseudofunctor'),
      p.obj (j.obj y) = q.obj y := by
    intro y
    rw [hjObj y]
    exact (pullbackStrictificationFiberForget p hc y.base y.fiber).2
  have hαLift : ∀ y : Pseudofunctor.CoGrothendieck
      ((pullback_strictification_functor p hc).toPseudofunctor'),
      q.IsHomLift (𝟙 (q.obj y)) (α.hom.app y) := by
    intro y
    have hiLift : q.IsHomLift (𝟙 (q.obj y)) (i y).hom := by
      simpa [i, F, jObj] using identity_presentation_comparison_obj_iso_hom_isHomLift p hc y
    let hObjEq : F.obj (jObj y) = (j ⋙ F.toFunctor).obj y := by
      simpa using congrArg (fun Z ↦ F.obj Z) (hjObj y).symm
    let hb : q.obj ((j ⋙ F.toFunctor).obj y) = q.obj (F.obj (jObj y)) := by
      simpa using congrArg (fun Z ↦ q.obj (F.obj Z)) (hjObj y)
    have hEqLift : q.IsHomLift (𝟙 (q.obj (F.obj (jObj y)))) (eqToHom hObjEq) := by
      apply IsHomLift.of_fac' q (𝟙 (q.obj (F.obj (jObj y)))) (eqToHom hObjEq) rfl hb
      have hmap := identity_presentation_comparison_eqToHom_base p hc hObjEq
      have hbase : congrArg (fun Z ↦ Z.base) hObjEq = hb.symm := by
        apply Subsingleton.elim
      calc
        (eqToHom hObjEq).base = eqToHom (congrArg (fun Z ↦ Z.base) hObjEq) := hmap
        _ = eqToHom hb.symm := by
          exact identity_presentation_comparison_eqToHom_proof_irrel (congrArg (fun Z ↦ Z.base) hObjEq) hb.symm
        _ = 𝟙 (q.obj (F.obj (jObj y))) ≫ 𝟙 (q.obj (F.obj (jObj y))) ≫ eqToHom hb.symm := by
          simp
    letI : q.IsHomLift (𝟙 (q.obj y)) (i y).hom := hiLift
    letI : q.IsHomLift (𝟙 (q.obj (F.obj (jObj y)))) (eqToHom hObjEq) := hEqLift
    have hcomp : q.IsHomLift (𝟙 (q.obj y)) ((i y).hom ≫ eqToHom hObjEq) := by
      infer_instance
    rw [hα y]
    change q.IsHomLift (𝟙 (q.obj y)) ((i y).hom ≫ eqToHom hObjEq)
    exact hcomp
  have hjBase : j ⋙ p = q :=
    identity_presentation_comparison_same_fiber_lift_commutes_with_base (p := p) (hc := hc) α hjBaseObj hαLift
  let jBased : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p :=
    { toFunctor := j
      w := hjBase }
  have hCounitLift : ∀ y : Pseudofunctor.CoGrothendieck
      ((pullback_strictification_functor p hc).toPseudofunctor'),
      q.IsHomLift (𝟙 (q.obj y)) (α.inv.app y) := by
    intro y
    letI : q.IsHomLift (𝟙 (q.obj y)) (α.app y).hom := by simpa using hαLift y
    have : q.IsHomLift (𝟙 (q.obj y)) (α.app y).inv := by infer_instance
    simpa using this
  have eps : BasedFunctor.comp jBased F ≅ BasedFunctor.id (BasedCategory.ofFunctor q) := by
    simpa [jBased, F, q] using BasedNatIso.mkNatIso α.symm hCounitLift
  let H : S ⥤ Pseudofunctor.CoGrothendieck
      ((pullback_strictification_functor p hc).toPseudofunctor') := F.toFunctor
  haveI : Full H := by
    dsimp [H]
    exact hFF.full
  haveI : Faithful H := by
    dsimp [H]
    exact hFF.faithful
  let compIso : (𝟭 S) ⋙ H ≅ (H ⋙ j) ⋙ H :=
    (Functor.leftUnitor H).symm ≪≫
      (Functor.rightUnitor H).symm ≪≫
      Functor.isoWhiskerLeft H α ≪≫
      (Functor.associator H j H).symm
  let ηNat : 𝟭 S ≅ H ⋙ j :=
    Functor.fullyFaithfulCancelRight (H := H) compIso
  have hηLift : ∀ x : S, p.IsHomLift (𝟙 (p.obj x)) (ηNat.hom.app x) := by
    intro x
    have hcompRaw :
        q.IsHomLift (𝟙 (q.obj (H.obj x))) (compIso.hom.app x) := by
      simpa [compIso, H, Category.assoc] using hαLift (H.obj x)
    have hcomp :
        q.IsHomLift (𝟙 (p.obj x)) (compIso.hom.app x) := by
      letI : q.IsHomLift (𝟙 (q.obj (H.obj x))) (compIso.hom.app x) := hcompRaw
      let hb : q.obj (((H ⋙ j) ⋙ H).obj x) = p.obj x :=
        (IsHomLift.codomain_eq q (𝟙 (q.obj (H.obj x))) (compIso.hom.app x)).trans
          (BasedFunctor.w_obj F x)
      apply IsHomLift.of_fac' q (𝟙 (p.obj x)) (compIso.hom.app x)
        (BasedFunctor.w_obj F x) hb
      have hraw := IsHomLift.fac' q (𝟙 (q.obj (H.obj x))) (compIso.hom.app x)
      simpa [hb, H, Category.assoc] using hraw
    have hmap : q.IsHomLift (𝟙 (p.obj x)) (H.map (ηNat.hom.app x)) := by
      simpa [ηNat, Functor.fullyFaithfulCancelRight_hom_app] using hcomp
    simpa [H] using (F.isHomLift_iff (𝟙 (p.obj x)) (ηNat.hom.app x)).1 hmap
  have eta : BasedFunctor.id (BasedCategory.ofFunctor p) ≅ BasedFunctor.comp F jBased := by
    simpa [jBased, F, q, H, BasedFunctor.comp_assoc] using BasedNatIso.mkNatIso ηNat hηLift
  exact BasedFunctor.IsEquivalenceOverBase.mkPrime jBased eta eps

-- Route correction: the old proof tried to show that the original fibred category was already
-- split by using `canonicalPullbackChoice p` directly. The source proof instead strictifies the
-- chosen pullbacks into a new fibred category and only then proves splitness.
/-- Helper for Lemma 4.36.4: the canonical strictification is split and the identity-presentation
comparison is an equivalence over the base. The target owner lives in the larger object universe
needed to store the base arrow in each strictification object. -/
theorem exists_split_fibred_category_over_base_aux
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C)
      (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p),
      F.IsEquivalenceOverBase ∧ Functor.IsSplitFibredCategory Y.p := by
  classical
  let hc := canonicalPullbackChoice p
  let Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C :=
    pullback_strictification p hc
  let F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p := by
    simpa [Y, pullback_strictification] using
      pullback_strictification_identity_presentation_basedFunctor p hc
  have hF : F.IsEquivalenceOverBase := by
    simpa [F, Y, pullback_strictification] using
      identity_presentation_comparison_isEquivalenceOverBase p hc
  refine ⟨Y, F, hF, ?_⟩
  simpa [Y, hc] using canonical_pullback_strictification_isSplit p

end CategoryTheory
