module

public import Mathlib
public import stacks_project.Chap04.Lemma_4_34_1
public import stacks_project.Chap08.Lemma_8_4_2
public import stacks_project.Chap08.Lemma_8_4_4.Index


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open BasedFunctor
open Functor IsHomLift IsStronglyCartesian

section

variable {C : Type u₁} {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S₁] [Category.{v₃} S₂]
variable (J : GrothendieckTopology C)

variable (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C)

/- Domain-style sampling for Lemma 8.4.4:
- primary domain: stacks over a site, transported along equivalences in the based category
  `Cat/C`.
- inspected owner-level declarations:
  `IsStackOnSite`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `BasedFunctor.isFibered_iff_of_equivalence_over_base`,
  `isStackOnSite_iff_canonicalFiberPseudofunctor_toDescentData_isEquivalence`.
- best owner abstraction: the source-facing owner remains `IsStackOnSite J p`; the based functor
  `F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂` and the predicate
  `F.IsEquivalenceOverBase` are the canonical Chapter 4 transport interface.
- primitive data: only the two projection functors `p₁`, `p₂` and the over-base equivalence data
  `hF`.
- derived API: the induced transport of fibredness and of the canonical descent-data equivalences
  used to compare the stack conditions.

Source/core/bridge triage:
- `source-facing`: `isStackOnSite_iff_of_equivalence_over_base`.
- `core/canonical`: `IsStackOnSite`, `BasedFunctor.IsEquivalenceOverBase`, and
  `Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J`.
- `bridge/view`: the coverwise descent-data criterion from Lemma `8.4.2`. -/

/-
Proof sketch: use `BasedFunctor.isFibered_iff_of_equivalence_over_base` to transport the
fibredness part of `IsStackOnSite`, then apply Lemma `8.4.2` to rewrite the stack condition for
each side in terms of equivalence of the canonical descent functors for every cover. The
equivalence-over-base data also upgrades to full faithfulness of the underlying based functor by
the Chapter 4 owner API, which is the canonical input for comparing the resulting descent-data
functors coverwise.
-/

/-- Helper for Lemma 8.4.4: once a fixed-cover transport functor on descent data is known to be
an equivalence and to compare the two canonical descent functors up to whiskering by the fiber
equivalence over `U`, the equivalence condition on the canonical descent functor cancels across
that comparison. -/
private theorem coverwise_canonicalDescentFunctor_isEquivalence_iff_of_transport
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (TF :
      ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
        ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f)))
    [TF.IsEquivalence]
    (e :
      ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF ≅
        (F.fiberFunctor U) ⋙
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f))) :
    ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
      ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  letI fiberEquivU :
      (F.fiberFunctor U).IsEquivalence :=
    fiberFunctor_isEquivalence_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF U
  constructor
  · intro h₁
    -- Compose the source descent functor with the transport equivalence, then cancel the
    -- fiberwise equivalence on the left of the comparison isomorphism.
    letI :
        ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := h₁
    have hsrcComp :
        (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF).IsEquivalence :=
      Functor.isEquivalence_trans
        ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) TF
    have hcomp :
        ((F.fiberFunctor U) ⋙ ((canonicalFiberPseudofunctor p₂).toDescentData
          (fun I : S.Arrow ↦ I.f))).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso e).1 hsrcComp
    letI :
        ((F.fiberFunctor U) ⋙ ((canonicalFiberPseudofunctor p₂).toDescentData
          (fun I : S.Arrow ↦ I.f))).IsEquivalence := hcomp
    exact
      Functor.isEquivalence_of_comp_left (F.fiberFunctor U)
        ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f))
  · intro h₂
    -- Reverse the same cancellation argument: first whisker by the fiber equivalence over `U`,
    -- then transport back across `TF`.
    have htargetComp :
        ((F.fiberFunctor U) ⋙ ((canonicalFiberPseudofunctor p₂).toDescentData
          (fun I : S.Arrow ↦ I.f))).IsEquivalence := by
      exact
        @Functor.isEquivalence_trans _ _ _ _ _ _
          (F.fiberFunctor U)
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f))
          fiberEquivU h₂
    have hcomp :
        (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso e).2 htargetComp
    letI :
        (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF).IsEquivalence := hcomp
    exact
      Functor.isEquivalence_of_comp_right
        ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) TF

/-- Helper for Lemma 8.4.4: for a fixed cover, transport one descent morphism by conjugating it
with the pullback-comparison isomorphisms coming from the equivalence over the base. -/
private noncomputable def cover_descent_data_transport_hom_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.obj
        ((F.fiberFunctor I₁.Y).obj (D.obj I₁))) ⟶
      (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.obj
        ((F.fiberFunctor I₂.Y).obj (D.obj I₂))) := by
  -- Route correction: fix the conjugation normal form first so the remaining descent-data laws
  -- can rewrite to one stable comparison term instead of reopening transport coercions each time.
  simpa using
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)).hom ≫
      (F.fiberFunctor Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)).inv

/-- Helper for Lemma 8.4.4: the inverse pullback-comparison isomorphism rewrites the right-hand
comparison inverse into a form that can be consumed by `rw` in the fixed-cover transport proofs. -/
theorem basedFunctor_pullbackComparison_inv_naturality_over_vertical
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (φ : x ⟶ y) :
    (F.fiberFunctor V).map
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f y).inv =
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).inv ≫
          (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
            ((F.fiberFunctor U).map φ)) := by
  -- Move the left comparison hom across the known naturality square, then move the right
  -- comparison hom back to the other side to obtain the inverse-side rewrite.
  let ex :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f x
  let ey :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f y
  let η :=
    ((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
      ((F.fiberFunctor U).map φ)
  let θ :=
    (F.fiberFunctor V).map
      (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)
  have hhom :
      η ≫ ey.hom = ex.hom ≫ θ := by
    simpa [ex, ey, η, θ] using
      basedFunctor_pullbackComparison_naturality_over_vertical
        (p₁ := p₁) (p₂ := p₂) F hF f φ
  -- Move the right comparison hom back across the naturality square, then cancel the left
  -- comparison isomorphism in the resulting owner-level equality.
  symm
  apply (Iso.eq_comp_inv ey).2
  -- Expand the local abbreviations, then precompose the hom-side naturality square with
  -- `ex.inv` so that `ex.inv ≫ ex.hom` cancels on the right.
  have hhom' := hhom
  dsimp [η, θ] at hhom' ⊢
  have hpre :
      ex.inv ≫
          ((((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
              ((F.fiberFunctor U).map φ)) ≫ ey.hom) =
        ex.inv ≫
          (ex.hom ≫
            (F.fiberFunctor V).map
              (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom'
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

/-- Helper for Lemma 8.4.4: transporting an overlap map along the same cover leg on both sides
produces the identity morphism. -/
private theorem cover_descent_data_transport_hom_self_map_id
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    (F.fiberFunctor Y).map (D.hom q g g hg hg) =
      𝟙 ((F.fiberFunctor Y).obj
        (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) := by
  -- Rewrite the source overlap map to the identity and then map that identity through the fiber
  -- functor.
  calc
    (F.fiberFunctor Y).map (D.hom q g g hg hg)
        =
          (F.fiberFunctor Y).map
            (𝟙 (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) := by
              simpa using
                congrArg (fun k ↦ (F.fiberFunctor Y).map k) (D.hom_self q g hg)
    _ = 𝟙 ((F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) := by
          exact (F.fiberFunctor Y).map_id _

/-- Helper for Lemma 8.4.4: transporting an overlap map along the same cover leg on both sides
produces the identity morphism. -/
private theorem basedFunctor_pullbackComparison_hom_inv_id_normalized
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U Y : C} (g : Y ⟶ U) (x : p₁.Fiber U) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g x).hom ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g x).inv =
      𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
        ((F.fiberFunctor U).obj x)) := by
  -- This is the exact cancellation shape needed after rewriting the middle transported overlap
  -- map to the identity.
  calc
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g x).hom ≫
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF g x).inv =
        𝟙 (g ^*[canonicalPullbackChoice p₂] ((F.fiberFunctor U).obj x)) := by
          exact
            (basedFunctor_pullbackComparison_of_equivalence_over_base
              (p₁ := p₁) (p₂ := p₂) F hF g x).hom_inv_id
    _ = 𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
          ((F.fiberFunctor U).obj x)) := by
          rfl

/-- Helper for Lemma 8.4.4: insert the explicit middle identity that appears after rewriting the
self-overlap descent morphism, without changing the pullback-comparison cancellation. -/
private theorem basedFunctor_pullbackComparison_hom_id_inv_normalized
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U Y : C} (g : Y ⟶ U) (x : p₁.Fiber U) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g x).hom ≫
        𝟙 ((F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj x)) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g x).inv =
      𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
        ((F.fiberFunctor U).obj x)) := by
  -- Reassociate away the inserted identity so the already normalized cancellation lemma applies
  -- to the literal displayed shape used in the self-overlap transport proof.
  let e :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g x
  have hη :
      e.hom ≫
          𝟙 ((F.fiberFunctor Y).obj
            (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj x)) ≫
          e.inv =
        e.hom ≫ e.inv := by
    -- Move the inserted identity onto `e.inv`, then reassociate back to the displayed form.
    change e.hom ≫
        (𝟙 ((F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj x)) ≫ e.inv) =
      e.hom ≫ e.inv
    exact congrArg (fun k ↦ e.hom ≫ k) (Category.id_comp e.inv)
  have hcancel :
      e.hom ≫ e.inv =
        𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
          ((F.fiberFunctor U).obj x)) := by
    simpa [e] using
      basedFunctor_pullbackComparison_hom_inv_id_normalized
        (p₁ := p₁) (p₂ := p₂) F hF g x
  exact hη.trans hcancel

/-- Helper for Lemma 8.4.4: after reassociating to the literal cocycle shape, the middle factor
`comparison.inv ≫ comparison.hom` can be canceled before postcomposing by the remaining tail. -/
private theorem basedFunctor_pullbackComparison_inv_hom_postcompose_normalized
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U Y : C} (g : Y ⟶ U) (x : p₁.Fiber U)
    {z : p₂.Fiber Y}
    (k :
      (F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj x) ⟶ z) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g x).inv ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g x).hom ≫
      k = k := by
  -- Use the owner-level iso cancellation in the exact postcomposed shape that appears after the
  -- cocycle proof is reassociated.
  let e :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g x
  simpa [e, Category.assoc] using Iso.inv_hom_id_assoc e k

/-- Helper for Lemma 8.4.4: transporting an overlap map along the same cover leg on both sides
produces the identity morphism. -/
private theorem cover_descent_data_transport_hom_self_normalize
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    cover_descent_data_transport_hom_of_equivalence_over_base
      (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q g g hg hg = 𝟙 _ := by
  -- Route correction: normalize the self-overlap transport to the literal
  -- `comparison.hom ≫ 𝟙 ≫ comparison.inv` shape before canceling the comparison isomorphism.
  change
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g (D.obj I)).hom ≫
          (F.fiberFunctor Y).map (D.hom q g g hg hg) ≫
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF g (D.obj I)).inv =
      𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
        ((F.fiberFunctor I.Y).obj (D.obj I)))
  let e :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g (D.obj I)
  have hself :
      (F.fiberFunctor Y).map (D.hom q g g hg hg) =
        𝟙 ((F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) :=
    cover_descent_data_transport_hom_self_map_id
      (p₁ := p₁) (p₂ := p₂) (J := J) F S D q g hg
  have hself_conj :
      e.hom ≫ (F.fiberFunctor Y).map (D.hom q g g hg hg) ≫ e.inv =
        e.hom ≫
          𝟙 ((F.fiberFunctor Y).obj
            (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) ≫
          e.inv := by
    -- Conjugate the source self-overlap identity by the comparison isomorphism.
    simpa [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k ≫ e.inv) hself
  -- Collapse the source self-overlap morphism to the identity in the middle factor.
  calc
    e.hom ≫ (F.fiberFunctor Y).map (D.hom q g g hg hg) ≫ e.inv
        = e.hom ≫
            𝟙 ((F.fiberFunctor Y).obj
              (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) ≫
            e.inv := hself_conj
    -- The remaining displayed composite is the exact cancellation wrapper proved just above.
    _ = 𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
          ((F.fiberFunctor I.Y).obj (D.obj I))) := by
            simpa [e] using
              basedFunctor_pullbackComparison_hom_id_inv_normalized
                (p₁ := p₁) (p₂ := p₂) F hF g (D.obj I)

/-- Helper for Lemma 8.4.4: transporting the source cocycle relation through the comparison
isomorphisms yields the target cocycle relation for the fixed cover. -/
private theorem cover_descent_data_transport_hom_comp_normalize
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂ ≫
    cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₂ f₃ hf₂ hf₃ =
      cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₃ hf₁ hf₃ := by
  -- Rewrite all three overlap maps into the same comparison-conjugated normal form, cancel the
  -- middle comparison isomorphism with
  -- `basedFunctor_pullbackComparison_inv_hom_postcompose_normalized`, and then map the source
  -- cocycle identity through the fiber functor over `Y`.
  change
    ((basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)).hom ≫
      (F.fiberFunctor Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)).inv) ≫
    ((basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)).hom ≫
      (F.fiberFunctor Y).map (D.hom q f₂ f₃ hf₂ hf₃) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₃ (D.obj I₃)).inv) =
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)).hom ≫
      (F.fiberFunctor Y).map (D.hom q f₁ f₃ hf₁ hf₃) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₃ (D.obj I₃)).inv
  let e₁ :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)
  let e₂ :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)
  let e₃ :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₃ (D.obj I₃)
  let d₁₂ := D.hom q f₁ f₂ hf₁ hf₂
  let d₂₃ := D.hom q f₂ f₃ hf₂ hf₃
  let d₁₃ := D.hom q f₁ f₃ hf₁ hf₃
  have hcancel :
      e₂.inv ≫ e₂.hom ≫ ((F.fiberFunctor Y).map d₂₃ ≫ e₃.inv) =
        (F.fiberFunctor Y).map d₂₃ ≫ e₃.inv := by
    -- Use the dedicated comparison-cancellation wrapper in exactly the postcomposed shape
    -- created by the transported cocycle composite.
    exact
      basedFunctor_pullbackComparison_inv_hom_postcompose_normalized
        (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)
        ((F.fiberFunctor Y).map d₂₃ ≫ e₃.inv)
  have hmapped :
      (F.fiberFunctor Y).map d₁₂ ≫ (F.fiberFunctor Y).map d₂₃ =
        (F.fiberFunctor Y).map d₁₃ := by
    -- Map the source descent cocycle through the fiber functor over `Y`.
    calc
      (F.fiberFunctor Y).map d₁₂ ≫ (F.fiberFunctor Y).map d₂₃ =
          (F.fiberFunctor Y).map (d₁₂ ≫ d₂₃) := by
            exact ((F.fiberFunctor Y).map_comp d₁₂ d₂₃).symm
      _ = (F.fiberFunctor Y).map d₁₃ := by
            exact congrArg (fun k ↦ (F.fiberFunctor Y).map k)
              (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
  have hpostcancel :
      (e₁.hom ≫ (F.fiberFunctor Y).map d₁₂ ≫ e₂.inv) ≫
          (e₂.hom ≫ (F.fiberFunctor Y).map d₂₃ ≫ e₃.inv) =
        e₁.hom ≫ (F.fiberFunctor Y).map d₁₂ ≫
          ((F.fiberFunctor Y).map d₂₃ ≫ e₃.inv) := by
    -- Apply the comparison cancellation inside the surrounding left context.
    have hcontext :=
      congrArg (fun k ↦ e₁.hom ≫ (F.fiberFunctor Y).map d₁₂ ≫ k) hcancel
    calc
      (e₁.hom ≫ (F.fiberFunctor Y).map d₁₂ ≫ e₂.inv) ≫
          (e₂.hom ≫ (F.fiberFunctor Y).map d₂₃ ≫ e₃.inv)
          = e₁.hom ≫ (F.fiberFunctor Y).map d₁₂ ≫
              (e₂.inv ≫ e₂.hom ≫ (F.fiberFunctor Y).map d₂₃ ≫ e₃.inv) := by
              simp [Category.assoc]
      _ = e₁.hom ≫ (F.fiberFunctor Y).map d₁₂ ≫
            ((F.fiberFunctor Y).map d₂₃ ≫ e₃.inv) := hcontext
  have hpostmap :
      e₁.hom ≫
          ((F.fiberFunctor Y).map d₁₂ ≫ (F.fiberFunctor Y).map d₂₃) ≫ e₃.inv =
        e₁.hom ≫ (F.fiberFunctor Y).map d₁₃ ≫ e₃.inv := by
    -- Apply the mapped source cocycle inside the same comparison shell.
    exact congrArg (fun k ↦ e₁.hom ≫ k ≫ e₃.inv) hmapped
  calc
    (e₁.hom ≫ (F.fiberFunctor Y).map d₁₂ ≫ e₂.inv) ≫
        (e₂.hom ≫ (F.fiberFunctor Y).map d₂₃ ≫ e₃.inv)
        = e₁.hom ≫ (F.fiberFunctor Y).map d₁₂ ≫
            ((F.fiberFunctor Y).map d₂₃ ≫ e₃.inv) := hpostcancel
    _ = e₁.hom ≫ (F.fiberFunctor Y).map d₁₃ ≫ e₃.inv := by
            -- Apply the source descent cocycle before transporting it through the comparison.
            simpa [Category.assoc] using hpostmap
    _ = (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)).hom ≫
          (F.fiberFunctor Y).map (D.hom q f₁ f₃ hf₁ hf₃) ≫
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF f₃ (D.obj I₃)).inv := by
            rfl

/-- Helper for Chap08 Lemma 8 4 4: composing in the base and then passing to the locally
discrete opposite is the same as composing the corresponding `toLoc` arrows. -/
theorem baseComp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the displayed composite equality to the locally discrete opposite category.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Chap08 Lemma 8 4 4: the hom component of the canonical fiber pseudofunctor's
flexible composition comparison factors through the chosen composite pullback arrow. -/
private theorem canonicalFiberPseudofunctor_mapComp'_hom_app_fac_local
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x =
      (canonicalPullbackChoice p).map gf x := by
  -- Reduce the flexible comparison to the owner-level chosen pullback-composition comparison.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_fac f g x

/-- Helper for Chap08 Lemma 8 4 4: the inverse component of the canonical fiber pseudofunctor's
flexible composition comparison factors the chosen composite pullback through the iterated one. -/
private theorem canonicalFiberPseudofunctor_mapComp'_inv_app_fac_local
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map gf x =
      (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x := by
  -- Read the same chosen comparison in the inverse factorization direction.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_inv_fac f g x

/-- Helper for Chap08 Lemma 8 4 4: a functor maps a threefold composite to the threefold
composite of the mapped morphisms. -/
private theorem functor_map_threefold_comp
    {D E : Type*} [Category D] [Category E] (G : D ⥤ E)
    {W X Y Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    G.map (f ≫ g ≫ h) = G.map f ≫ G.map g ≫ G.map h := by
  -- Split the composite into two ordinary functoriality identities.
  rw [Functor.map_comp, Functor.map_comp]

/-- Helper for Chap08 Lemma 8 4 4: postcomposing the inverse pullback comparison with the chosen
target pullback arrow recovers the mapped chosen source pullback arrow. -/
private theorem basedFunctor_pullbackComparison_inv_postcompose
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f x).inv.1 ≫
      (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x) =
        F.map ((canonicalPullbackChoice p₁).map f x) := by
  -- Cancel the inverse against the hom comparison before reading off the hom-side
  -- postcomposition identity.
  let e := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f x
  have hcancel : e.inv.1 ≫ e.hom.1 =
      𝟙 (((F.fiberFunctor V).obj (f ^*[canonicalPullbackChoice p₁] x)).1) := by
    exact congrArg (fun k ↦ k.1) e.inv_hom_id
  have hhom :
      e.hom.1 ≫ F.map ((canonicalPullbackChoice p₁).map f x) =
        (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x) := by
    simpa [e] using
      basedFunctor_pullbackComparison_hom_postcompose
        (p₁ := p₁) (p₂ := p₂) F hF f x
  change e.inv.1 ≫ (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x) =
    F.map ((canonicalPullbackChoice p₁).map f x)
  rw [← hhom]
  have hcancel' :
      (e.inv.1 ≫ e.hom.1) ≫ F.map ((canonicalPullbackChoice p₁).map f x) =
        F.map ((canonicalPullbackChoice p₁).map f x) := by
    rw [hcancel]
    exact Category.id_comp (F.map ((canonicalPullbackChoice p₁).map f x))
  exact
    (Category.assoc e.inv.1 e.hom.1
      (F.map ((canonicalPullbackChoice p₁).map f x))).symm.trans hcancel'

/-- Helper for Chap08 Lemma 8 4 4: after postcomposing the raw left `pullHom` boundary and the
strict composite-leg boundary by the chosen `g`- then `f`-tails, both reduce to the same chosen
composite pullback arrow. -/
private theorem basedFunctor_pullbackComparison_pullHom_left_boundary_postcompose_g_then_f_target
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V V' : C} (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U)
    (hgf : g ≫ f = gf) (x : p₁.Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor p₂).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((F.fiberFunctor U).obj x)) ≫
        (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF f x).hom)
    let strict :=
      (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF gf x).hom ≫
        (F.fiberFunctor V').map
          (((canonicalFiberPseudofunctor p₁).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)).inv
    let tailg :=
      (canonicalPullbackChoice p₂).map g
        ((F.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x))
    let tailf := F.map ((canonicalPullbackChoice p₁).map f x)
    raw.1 ≫ tailg ≫ tailf = strict.1 ≫ tailg ≫ tailf := by
  let raw :=
    (((canonicalFiberPseudofunctor p₂).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((F.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).hom)
  let strict :=
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF gf x).hom ≫
      (F.fiberFunctor V').map
        (((canonicalFiberPseudofunctor p₁).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)).inv
  let tailg :=
    (canonicalPullbackChoice p₂).map g
      ((F.fiberFunctor V).obj
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x))
  let tailf := F.map ((canonicalPullbackChoice p₁).map f x)
  let e := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF gf x
  let cg := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF g
    (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)
  let ef := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f x
  let leftRaw :=
    ((canonicalFiberPseudofunctor p₂).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((F.fiberFunctor U).obj x)
  let leftSource :=
    ((canonicalFiberPseudofunctor p₁).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc
      (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x
  have hraw_expand :
      raw.1 =
        leftRaw.1 ≫
          ((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.hom)).1 := by
    rfl
  have hstrict_expand :
      strict.1 = e.hom.1 ≫ ((F.fiberFunctor V').map leftSource).1 ≫ cg.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice p₂).map gf ((F.fiberFunctor U).obj x) := by
    have hraw_flank :
        (leftRaw.1 ≫
            (canonicalPullbackChoice p₂).map g
              (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
                ((F.fiberFunctor U).obj x))) ≫
            (canonicalPullbackChoice p₂).map f
              ((F.fiberFunctor U).obj x) =
          (canonicalPullbackChoice p₂).map gf
            ((F.fiberFunctor U).obj x) := by
      simpa [leftRaw, Category.assoc] using
        canonicalFiberPseudofunctor_mapComp'_hom_app_fac_local
          (p := p₂) (f := f) (g := g) (gf := gf) (hgf := hgf) ((F.fiberFunctor U).obj x)
    calc
      raw.1 ≫ tailg ≫ tailf =
          leftRaw.1 ≫
            ((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
            tailg ≫ tailf := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.hom)).1 ≫
              tailg) ≫ tailf := by
              simp only [Category.assoc]
      _ =
          leftRaw.1 ≫
            (((canonicalPullbackChoice p₂).map g
                (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
                  ((F.fiberFunctor U).obj x))) ≫
              ef.hom.1) ≫ tailf := by
              exact
                congrArg (fun t ↦ leftRaw.1 ≫ t ≫ tailf)
                  (equivalenceTransport_canonical_pullbackFunctor_map_fac
                    (p := p₂) (f := g) (φ := ef.hom))
      _ =
          leftRaw.1 ≫
            (canonicalPullbackChoice p₂).map g
              (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
                ((F.fiberFunctor U).obj x)) ≫
            ef.hom.1 ≫ tailf := by
              simp only [Category.assoc]
      _ =
          (canonicalPullbackChoice p₂).map gf
            ((F.fiberFunctor U).obj x) := by
              have hpostf :
                  leftRaw.1 ≫
                      (canonicalPullbackChoice p₂).map g
                        (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
                          ((F.fiberFunctor U).obj x)) ≫
                      ef.hom.1 ≫ tailf =
                    (leftRaw.1 ≫
                      (canonicalPullbackChoice p₂).map g
                        (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
                          ((F.fiberFunctor U).obj x))) ≫
                      (canonicalPullbackChoice p₂).map f
                        ((F.fiberFunctor U).obj x) := by
                simpa only [tailf, Category.assoc] using
                  congrArg
                    (fun t ↦
                      leftRaw.1 ≫
                        (canonicalPullbackChoice p₂).map g
                          (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
                            ((F.fiberFunctor U).obj x)) ≫ t)
                    (basedFunctor_pullbackComparison_hom_postcompose
                      (p₁ := p₁) (p₂ := p₂) F hF f x)
              exact hpostf.trans hraw_flank
  have hstrict :
      strict.1 ≫ tailg ≫ tailf =
        (canonicalPullbackChoice p₂).map gf
          ((F.fiberFunctor U).obj x) := by
    have hpostg :
        cg.inv.1 ≫ tailg =
          F.map ((canonicalPullbackChoice p₁).map g
            (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)) := by
      exact basedFunctor_pullbackComparison_inv_postcompose
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)
    have hpostg' :
        (cg.inv.1 ≫ tailg) ≫ tailf =
          F.map ((canonicalPullbackChoice p₁).map g
              (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)) ≫
            tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hpostg
    calc
      strict.1 ≫ tailg ≫ tailf =
          e.hom.1 ≫ ((F.fiberFunctor V').map leftSource).1 ≫
            cg.inv.1 ≫ tailg ≫ tailf := by
              rw [hstrict_expand]
              simp only [Category.assoc]
      _ =
          e.hom.1 ≫ ((F.fiberFunctor V').map leftSource).1 ≫
            (cg.inv.1 ≫ tailg ≫ tailf) := by
              rfl
      _ =
          e.hom.1 ≫ ((F.fiberFunctor V').map leftSource).1 ≫
            (F.map ((canonicalPullbackChoice p₁).map g
              (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)) ≫
              tailf) := by
              simpa only [Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ ((F.fiberFunctor V').map leftSource).1 ≫ t)
                  hpostg'
      _ =
          e.hom.1 ≫
            F.map
              (leftSource.1 ≫
                (canonicalPullbackChoice p₁).map g
                  (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x) ≫
                (canonicalPullbackChoice p₁).map f x) := by
              simpa only [tailf, Category.assoc] using
                congrArg
                  (fun t ↦ e.hom.1 ≫ t)
                  (functor_map_threefold_comp F.toFunctor leftSource.1
                    ((canonicalPullbackChoice p₁).map g
                      (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x))
                    ((canonicalPullbackChoice p₁).map f x)).symm
      _ =
          e.hom.1 ≫ F.map ((canonicalPullbackChoice p₁).map gf x) := by
              exact
                congrArg (fun t ↦ e.hom.1 ≫ F.map t)
                  (canonicalFiberPseudofunctor_mapComp'_hom_app_fac_local
                    (p := p₁) (f := f) (g := g) (gf := gf) (hgf := hgf) x)
      _ =
          (canonicalPullbackChoice p₂).map gf
            ((F.fiberFunctor U).obj x) := by
              exact basedFunctor_pullbackComparison_hom_postcompose
                (p₁ := p₁) (p₂ := p₂) F hF gf x
  -- Both postcomposed shells reduce to the same composite-leg pullback arrow.
  exact hraw.trans hstrict.symm

/-- Helper for Chap08 Lemma 8 4 4: after postcomposing the raw and strict left `pullHom`
boundaries by the common chosen `g`-tail, the owner-level arrows agree. -/
private theorem basedFunctor_pullbackComparison_pullHom_left_boundary_postcompose_g_target
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V V' : C} (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U)
    (hgf : g ≫ f = gf) (x : p₁.Fiber U) :
    let raw :=
      (((canonicalFiberPseudofunctor p₂).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((F.fiberFunctor U).obj x)) ≫
        (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF f x).hom)
    let strict :=
      (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF gf x).hom ≫
        (F.fiberFunctor V').map
          (((canonicalFiberPseudofunctor p₁).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)).inv
    let tail :=
      (canonicalPullbackChoice p₂).map g
        ((F.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x))
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (((canonicalFiberPseudofunctor p₂).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((F.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).hom)
  let strict :=
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF gf x).hom ≫
      (F.fiberFunctor V').map
        (((canonicalFiberPseudofunctor p₁).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice p₂).map g
      ((F.fiberFunctor V).obj
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x))
  let tailf := F.map ((canonicalPullbackChoice p₁).map f x)
  have htailf : p₂.IsStronglyCartesian f tailf := by
    change p₂.IsStronglyCartesian f (F.map ((canonicalPullbackChoice p₁).map f x))
    exact
      basedFunctor_map_stronglyCartesian_of_lift
        (p₁ := p₁) (p₂ := p₂) F hF f
        ((canonicalPullbackChoice p₁).map f x)
        ((canonicalPullbackChoice p₁).isStronglyCartesian f x)
  have htail : p₂.IsHomLift g tail := by
    change p₂.IsHomLift g
      ((canonicalPullbackChoice p₂).map g
        ((F.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)))
    exact
      ((canonicalPullbackChoice p₂).isStronglyCartesian g
        ((F.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x))).toIsHomLift
  letI : p₂.IsStronglyCartesian f tailf := htailf
  letI : p₂.IsHomLift (𝟙 V') raw.1 := raw.2
  letI : p₂.IsHomLift (𝟙 V') strict.1 := strict.2
  letI : p₂.IsHomLift g tail := htail
  have hrawtail : p₂.IsHomLift g (raw.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ p₂ _ _ _
      V' raw.1 raw.2 _ _ g tail htail
  have hstricttail : p₂.IsHomLift g (strict.1 ≫ tail) := by
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ p₂ _ _ _
      V' strict.1 strict.2 _ _ g tail htail
  have hpost : (raw.1 ≫ tail) ≫ tailf = (strict.1 ≫ tail) ≫ tailf := by
    -- Compare after composing with the common strongly cartesian leg over `f`.
    simpa only [Category.assoc] using
      basedFunctor_pullbackComparison_pullHom_left_boundary_postcompose_g_then_f_target
        (p₁ := p₁) (p₂ := p₂) F hF f g gf hgf x
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p₂ _ _ _ _
      f tailf htailf _ _ g (raw.1 ≫ tail) (strict.1 ≫ tail) hrawtail hstricttail hpost

/-- Helper for Chap08 Lemma 8 4 4: the raw left `pullHom` boundary is the strict
composite-leg comparison shell in the fiber over the refinement base. -/
theorem basedFunctor_pullbackComparison_pullHom_left_boundary
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V V' : C} (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U)
    (hgf : g ≫ f = gf) (x : p₁.Fiber U) :
    (((canonicalFiberPseudofunctor p₂).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
        ((F.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).hom) =
      (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF gf x).hom ≫
        (F.fiberFunctor V').map
          (((canonicalFiberPseudofunctor p₁).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)).inv := by
  let raw :=
    (((canonicalFiberPseudofunctor p₂).mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
        (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app
      ((F.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).hom)
  let strict :=
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF gf x).hom ≫
      (F.fiberFunctor V').map
        (((canonicalFiberPseudofunctor p₁).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (baseComp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)).inv
  let tail :=
    (canonicalPullbackChoice p₂).map g
      ((F.fiberFunctor V).obj
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x))
  have htail : p₂.IsStronglyCartesian g tail := by
    change p₂.IsStronglyCartesian g
      ((canonicalPullbackChoice p₂).map g
        ((F.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)))
    exact
      (canonicalPullbackChoice p₂).isStronglyCartesian g
        ((F.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x))
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level comparison after composing with the `g`-leg.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact basedFunctor_pullbackComparison_pullHom_left_boundary_postcompose_g_target
      (p₁ := p₁) (p₂ := p₂) F hF f g gf hgf x
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p₂ _ _ _ _
      g tail htail _ _ (𝟙 V') raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Chap08 Lemma 8 4 4: after postcomposing the raw and strict right `pullHom`
boundaries with the chosen `gf`-tail, both reduce to the same mapped source factorization. -/
private theorem basedFunctor_pullbackComparison_pullHom_right_boundary_postcompose_target
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V V' : C} (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U)
    (hgf : g ≫ f = gf) (y : p₁.Fiber U) :
    let raw :=
      (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)).inv ≫
        (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF f y).inv) ≫
        (((canonicalFiberPseudofunctor p₂).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
          ((F.fiberFunctor U).obj y))
    let strict :=
      (F.fiberFunctor V').map
          (((canonicalFiberPseudofunctor p₁).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF gf y).inv
    let tail := (canonicalPullbackChoice p₂).map gf ((F.fiberFunctor U).obj y)
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let raw :=
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f y).inv) ≫
      (((canonicalFiberPseudofunctor p₂).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((F.fiberFunctor U).obj y))
  let strict :=
    (F.fiberFunctor V').map
        (((canonicalFiberPseudofunctor p₁).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF gf y).inv
  let tail := (canonicalPullbackChoice p₂).map gf ((F.fiberFunctor U).obj y)
  let e := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF gf y
  let cg := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF g
    (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)
  let ef := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f y
  let tailg :=
    (canonicalPullbackChoice p₂).map g
      (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
        ((F.fiberFunctor U).obj y))
  let tailf := (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj y)
  let sourceTailg :=
    F.map ((canonicalPullbackChoice p₁).map g
      (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y))
  let sourceTailf := F.map ((canonicalPullbackChoice p₁).map f y)
  let rightSource :=
    ((canonicalFiberPseudofunctor p₁).mapComp'
      f.op.toLoc g.op.toLoc gf.op.toLoc (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y
  have hraw_expand :
      raw.1 =
        cg.inv.1 ≫
          ((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
          (((canonicalFiberPseudofunctor p₂).mapComp'
              f.op.toLoc g.op.toLoc gf.op.toLoc
              (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
            ((F.fiberFunctor U).obj y)).1 := by
    rfl
  have hstrict_expand : strict.1 = ((F.fiberFunctor V').map rightSource).1 ≫ e.inv.1 := by
    rfl
  have hraw :
      raw.1 ≫ tail = sourceTailg ≫ sourceTailf := by
    have hmap_tailg :
        ((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫ tailg =
          (canonicalPullbackChoice p₂).map g
              ((F.fiberFunctor V).obj
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1 := by
      exact equivalenceTransport_canonical_pullbackFunctor_map_fac
        (p := p₂) (f := g) (φ := ef.inv)
    have hsourceTailg :
        cg.inv.1 ≫
            (canonicalPullbackChoice p₂).map g
              ((F.fiberFunctor V).obj
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)) =
          sourceTailg := by
      exact basedFunctor_pullbackComparison_inv_postcompose
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)
    have hmap_tailg' :
        (((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫ tailg) ≫
            tailf =
          ((canonicalPullbackChoice p₂).map g
              ((F.fiberFunctor V).obj
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1) ≫ tailf := by
      exact congrArg (fun t ↦ t ≫ tailf) hmap_tailg
    have hsourceTailg' :
        (cg.inv.1 ≫
            (canonicalPullbackChoice p₂).map g
              ((F.fiberFunctor V).obj
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf =
          sourceTailg ≫ sourceTailf := by
      exact congrArg (fun t ↦ t ≫ sourceTailf) hsourceTailg
    have hraw_mid :
        raw.1 ≫ tail =
          (cg.inv.1 ≫
            (canonicalPullbackChoice p₂).map g
              ((F.fiberFunctor V).obj
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf := by
      calc
      raw.1 ≫ tail =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (((canonicalFiberPseudofunctor p₂).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((F.fiberFunctor U).obj y)).1 ≫ tail := by
              rw [hraw_expand]
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            ((((canonicalFiberPseudofunctor p₂).mapComp'
                f.op.toLoc g.op.toLoc gf.op.toLoc
                (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
              ((F.fiberFunctor U).obj y)).1 ≫ tail) := by
              rfl
      _ =
          cg.inv.1 ≫
            ((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
            (tailg ≫ tailf) := by
              exact
                congrArg
                  (fun t ↦
                    cg.inv.1 ≫
                      ((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
                      t)
                  (canonicalFiberPseudofunctor_mapComp'_inv_app_fac_local
                    (p := p₂) (f := f) (g := g) (gf := gf) (hgf := hgf)
                    ((F.fiberFunctor U).obj y))
      _ =
          cg.inv.1 ≫
            (((((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map ef.inv)).1 ≫
              tailg) ≫ tailf := by
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            (((canonicalPullbackChoice p₂).map g
                ((F.fiberFunctor V).obj
                  (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y))) ≫
              ef.inv.1) ≫ tailf := by
              simpa only [Category.assoc] using congrArg (fun t ↦ cg.inv.1 ≫ t) hmap_tailg'
      _ =
          cg.inv.1 ≫
            (canonicalPullbackChoice p₂).map g
              ((F.fiberFunctor V).obj
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)) ≫
            ef.inv.1 ≫ tailf := by
              simp only [Category.assoc]
      _ =
          cg.inv.1 ≫
            (canonicalPullbackChoice p₂).map g
              ((F.fiberFunctor V).obj
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)) ≫
            sourceTailf := by
              simpa only [sourceTailf, Category.assoc] using
                congrArg
                  (fun t ↦
                    cg.inv.1 ≫
                      (canonicalPullbackChoice p₂).map g
                        ((F.fiberFunctor V).obj
                          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)) ≫ t)
                  (basedFunctor_pullbackComparison_inv_postcompose
                    (p₁ := p₁) (p₂ := p₂) F hF f y)
      _ =
          (cg.inv.1 ≫
            (canonicalPullbackChoice p₂).map g
              ((F.fiberFunctor V).obj
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y))) ≫
            sourceTailf := by
              simp only [Category.assoc]
    exact hraw_mid.trans hsourceTailg'
  have hstrict :
      strict.1 ≫ tail = sourceTailg ≫ sourceTailf := by
    have hstrict_tail :
        F.map rightSource.1 ≫ F.map ((canonicalPullbackChoice p₁).map gf y) =
          sourceTailg ≫ sourceTailf := by
      have hfac :
          rightSource.1 ≫ (canonicalPullbackChoice p₁).map gf y =
            ((canonicalPullbackChoice p₁).map g
                (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)) ≫
              (canonicalPullbackChoice p₁).map f y := by
        exact
          canonicalFiberPseudofunctor_mapComp'_inv_app_fac_local
            (p := p₁) (f := f) (g := g) (gf := gf) (hgf := hgf) y
      calc
        F.map rightSource.1 ≫ F.map ((canonicalPullbackChoice p₁).map gf y) =
            F.map (rightSource.1 ≫ (canonicalPullbackChoice p₁).map gf y) := by
              exact (F.map_comp rightSource.1 ((canonicalPullbackChoice p₁).map gf y)).symm
        _ =
            F.map
              (((canonicalPullbackChoice p₁).map g
                  (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)) ≫
                (canonicalPullbackChoice p₁).map f y) := by
              exact congrArg F.map hfac
        _ = sourceTailg ≫ sourceTailf := by
              rw [Functor.map_comp]
              rfl
    have hstrict_mid :
        strict.1 ≫ tail =
          F.map rightSource.1 ≫ F.map ((canonicalPullbackChoice p₁).map gf y) := by
      calc
      strict.1 ≫ tail =
          ((F.fiberFunctor V').map rightSource).1 ≫ e.inv.1 ≫ tail := by
            rw [hstrict_expand]
            simp only [Category.assoc]
      _ =
          ((F.fiberFunctor V').map rightSource).1 ≫ (e.inv.1 ≫ tail) := by
            rfl
      _ =
          F.map rightSource.1 ≫ F.map ((canonicalPullbackChoice p₁).map gf y) := by
            exact
              congrArg (fun t ↦ F.map rightSource.1 ≫ t)
                (basedFunctor_pullbackComparison_inv_postcompose
                  (p₁ := p₁) (p₂ := p₂) F hF gf y)
    exact hstrict_mid.trans hstrict_tail
  exact hraw.trans hstrict.symm

/-- Helper for Chap08 Lemma 8 4 4: the raw right `pullHom` boundary is the strict
composite-leg inverse shell in the refinement fiber. -/
theorem basedFunctor_pullbackComparison_pullHom_right_boundary
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V V' : C} (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U)
    (hgf : g ≫ f = gf) (y : p₁.Fiber U) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f y).inv) ≫
      (((canonicalFiberPseudofunctor p₂).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((F.fiberFunctor U).obj y)) =
    (F.fiberFunctor V').map
        (((canonicalFiberPseudofunctor p₁).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF gf y).inv := by
  let raw :=
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y)).inv ≫
      (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f y).inv) ≫
      (((canonicalFiberPseudofunctor p₂).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app
        ((F.fiberFunctor U).obj y))
  let strict :=
    (F.fiberFunctor V').map
        (((canonicalFiberPseudofunctor p₁).mapComp'
            f.op.toLoc g.op.toLoc gf.op.toLoc
            (baseComp_toLoc_eq f g gf hgf)).inv.toNatTrans.app y) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF gf y).inv
  let tail := (canonicalPullbackChoice p₂).map gf ((F.fiberFunctor U).obj y)
  have htail : p₂.IsStronglyCartesian gf tail := by
    change p₂.IsStronglyCartesian gf
      ((canonicalPullbackChoice p₂).map gf ((F.fiberFunctor U).obj y))
    exact (canonicalPullbackChoice p₂).isStronglyCartesian gf ((F.fiberFunctor U).obj y)
  have hpost : raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Reduce the fiber equality to the owner-level postcomposed inverse-shell comparison.
    change raw.1 ≫ tail = strict.1 ≫ tail
    exact basedFunctor_pullbackComparison_pullHom_right_boundary_postcompose_target
      (p₁ := p₁) (p₂ := p₂) F hF f g gf hgf y
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p₂ _ _ _ _
      gf tail htail _ _ (𝟙 V') raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Chap08 Lemma 8 4 4: the middle `g`-pullback comparison moves a transported
source overlap map across the comparison shell. -/
private theorem cover_descent_data_transport_pullHom_middle_conjugation
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U)
    {I₁ I₂ : S.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g
        (((canonicalFiberPseudofunctor p₁).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))).inv ≫
        (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
          ((F.fiberFunctor V).map (D.hom q f₁ f₂ hf₁ hf₂))) =
      (F.fiberFunctor V').map
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g
          (((canonicalFiberPseudofunctor p₁).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))).inv := by
  -- Move the source overlap morphism across the `g`-leg pullback comparisons.
  simpa only using
    (basedFunctor_pullbackComparison_inv_naturality_over_vertical
      (p₁ := p₁) (p₂ := p₂) F hF g (D.hom q f₁ f₂ hf₁ hf₂)).symm

/-- Helper for Chap08 Lemma 8 4 4: after boundary normalization, the three source-side pieces
fold back to the source `pullHom` under the fiber functor. -/
private theorem cover_descent_data_transport_pullHom_source_shell_map
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U)
    {I₁ I₂ : S.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let leftSource :=
      (((canonicalFiberPseudofunctor p₁).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (baseComp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
    let rightSource :=
      (((canonicalFiberPseudofunctor p₁).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (baseComp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
    (F.fiberFunctor V').map leftSource ≫
        (F.fiberFunctor V').map
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫
        (F.fiberFunctor V').map rightSource =
      (F.fiberFunctor V').map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) := by
  let leftSource :=
    (((canonicalFiberPseudofunctor p₁).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (baseComp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let rightSource :=
    (((canonicalFiberPseudofunctor p₁).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (baseComp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
  change
    (F.fiberFunctor V').map leftSource ≫
        (F.fiberFunctor V').map
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫
        (F.fiberFunctor V').map rightSource =
      (F.fiberFunctor V').map
        (leftSource ≫
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫
          rightSource)
  rw [functor_map_threefold_comp]

/-- Helper for Chap08 Lemma 8 4 4: unfolding the transported overlap and `pullHom` exposes the
single mapped middle composite before boundary normalization. -/
private theorem cover_descent_data_transport_pullHom_unfolded
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U)
    {I₁ I₂ : S.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_transport_hom_of_equivalence_over_base
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (((canonicalFiberPseudofunctor p₂).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (baseComp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          ((F.fiberFunctor I₁.Y).obj (D.obj I₁))) ≫
        (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.map
          ((basedFunctor_pullbackComparison_of_equivalence_over_base
              (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)).hom ≫
            (F.fiberFunctor V).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
            (basedFunctor_pullbackComparison_of_equivalence_over_base
              (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)).inv)) ≫
        (((canonicalFiberPseudofunctor p₂).mapComp'
            f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (baseComp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
          ((F.fiberFunctor I₂.Y).obj (D.obj I₂))) := by
  -- Expand only the transported overlap map and the pseudofunctorial `pullHom`.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    cover_descent_data_transport_hom_of_equivalence_over_base]
  rfl

/-- Helper for Chap08 Lemma 8 4 4: the transported `pullHom` shell normalizes to the
comparison-conjugated image of the source `pullHom`. -/
private theorem cover_descent_data_transport_hom_pullHom_normalized_shell
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {V' V : C} (g : V' ⟶ V) (q : V ⟶ U) (q' : V' ⟶ U) (_hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : V' ⟶ I₁.Y) (gf₂ : V' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_transport_hom_of_equivalence_over_base
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF gf₁ (D.obj I₁)).hom ≫
        (F.fiberFunctor V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF gf₂ (D.obj I₂)).inv := by
  let FYg := ((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor
  let FXg := ((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let e₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)
  let e₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)
  let eg₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF gf₁ (D.obj I₁)
  let eg₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF gf₂ (D.obj I₂)
  let cg₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF g
    (((canonicalFiberPseudofunctor p₁).map f₁.op.toLoc).toFunctor.obj (D.obj I₁))
  let cg₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF g
    (((canonicalFiberPseudofunctor p₁).map f₂.op.toLoc).toFunctor.obj (D.obj I₂))
  let leftTarget :=
    (((canonicalFiberPseudofunctor p₂).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (baseComp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
      ((F.fiberFunctor I₁.Y).obj (D.obj I₁)))
  let rightTarget :=
    (((canonicalFiberPseudofunctor p₂).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (baseComp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
      ((F.fiberFunctor I₂.Y).obj (D.obj I₂)))
  let leftSource :=
    (((canonicalFiberPseudofunctor p₁).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (baseComp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj I₁))
  let rightSource :=
    (((canonicalFiberPseudofunctor p₁).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (baseComp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj I₂))
  have hunfolded :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (cover_descent_data_transport_hom_of_equivalence_over_base
            (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        leftTarget ≫ FYg.map (e₁.hom ≫ (F.fiberFunctor V).map d ≫ e₂.inv) ≫ rightTarget := by
    -- Expand the transported overlap before the boundary reassociations begin.
    simpa only [FYg, d, e₁, e₂, leftTarget, rightTarget] using
      cover_descent_data_transport_pullHom_unfolded
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D g q f₁ f₂ hf₁ hf₂
        gf₁ gf₂ hgf₁ hgf₂
  have hmap :
      FYg.map (e₁.hom ≫ (F.fiberFunctor V).map d ≫ e₂.inv) =
        FYg.map e₁.hom ≫ FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv := by
    -- Split the mapped middle composite into the visible threefold shell.
    simpa only [FYg, d, e₁, e₂] using
      functor_map_threefold_comp FYg e₁.hom ((F.fiberFunctor V).map d) e₂.inv
  have hleft :
      leftTarget ≫ FYg.map e₁.hom =
        eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ cg₁.inv := by
    -- Normalize the left boundary to the common refinement leg `gf₁`.
    simpa only [FYg, e₁, eg₁, cg₁, leftTarget, leftSource] using
      basedFunctor_pullbackComparison_pullHom_left_boundary
        (p₁ := p₁) (p₂ := p₂) F hF f₁ g gf₁ hgf₁ (D.obj I₁)
  have hmid :
      cg₁.inv ≫ FYg.map ((F.fiberFunctor V).map d) =
        (F.fiberFunctor V').map (FXg.map d) ≫ cg₂.inv := by
    -- Move the source overlap morphism across the `g`-leg comparison shell.
    simpa only [FYg, FXg, d, cg₁, cg₂] using
      cover_descent_data_transport_pullHom_middle_conjugation
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D g q f₁ f₂ hf₁ hf₂
  have hright :
      cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget =
        (F.fiberFunctor V').map rightSource ≫ eg₂.inv := by
    -- Normalize the right boundary to the common refinement leg `gf₂`.
    simpa only [FYg, e₂, eg₂, cg₂, rightTarget, rightSource] using
      basedFunctor_pullbackComparison_pullHom_right_boundary
        (p₁ := p₁) (p₂ := p₂) F hF f₂ g gf₂ hgf₂ (D.obj I₂)
  have hfold :
      (F.fiberFunctor V').map leftSource ≫
          (F.fiberFunctor V').map (FXg.map d) ≫
          (F.fiberFunctor V').map rightSource =
        (F.fiberFunctor V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            d g gf₁ gf₂ hgf₁ hgf₂) := by
    -- Fold the normalized source-side pieces back into the source `pullHom` shell.
    simpa only [FXg, d, leftSource, rightSource] using
      cover_descent_data_transport_pullHom_source_shell_map
        (J := J) (p₁ := p₁) (p₂ := p₂) F S D g q f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hright' :
      eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ (F.fiberFunctor V').map (FXg.map d) ≫
        (cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget) =
      eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ (F.fiberFunctor V').map (FXg.map d) ≫
        ((F.fiberFunctor V').map rightSource ≫ eg₂.inv) := by
    -- Freeze the normalized left and middle factors while replacing the right boundary shell.
    simpa only [Category.assoc] using
      congrArg
        (fun k ↦ eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫
          (F.fiberFunctor V').map (FXg.map d) ≫ k)
        hright
  have hmap' :
      leftTarget ≫ FYg.map (e₁.hom ≫ (F.fiberFunctor V).map d ≫ e₂.inv) ≫ rightTarget =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((F.fiberFunctor V).map d) ≫
          FYg.map e₂.inv ≫ rightTarget := by
    -- Expand the mapped middle shell while keeping the boundary factors fixed.
    calc
      leftTarget ≫ FYg.map (e₁.hom ≫ (F.fiberFunctor V).map d ≫ e₂.inv) ≫ rightTarget =
        leftTarget ≫ (FYg.map e₁.hom ≫ FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv) ≫
          rightTarget := by
            exact congrArg (fun k ↦ leftTarget ≫ k ≫ rightTarget) hmap
      _ =
        leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫
          rightTarget := by
            simp only [Category.assoc]
  have hleft' :
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫
          rightTarget =
        eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ cg₁.inv ≫
          FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Replace the left boundary with the normalized shell over `gf₁`.
    calc
      leftTarget ≫ FYg.map e₁.hom ≫ FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫
          rightTarget =
        (leftTarget ≫ FYg.map e₁.hom) ≫ FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫
          rightTarget := by
            simp only [Category.assoc]
      _ =
        (eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ cg₁.inv) ≫
          FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun k ↦ k ≫ FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫ rightTarget)
              hleft
      _ =
        eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ cg₁.inv ≫
          FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hmid' :
      eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ cg₁.inv ≫
          FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ (F.fiberFunctor V').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Replace the middle shell by the normalized `g`-transported source overlap.
    calc
      eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ cg₁.inv ≫
          FYg.map ((F.fiberFunctor V).map d) ≫ FYg.map e₂.inv ≫ rightTarget =
        eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫
          (cg₁.inv ≫ FYg.map ((F.fiberFunctor V).map d)) ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫
          ((F.fiberFunctor V').map (FXg.map d) ≫ cg₂.inv) ≫ FYg.map e₂.inv ≫ rightTarget := by
            exact congrArg
              (fun k ↦ eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ k ≫
                FYg.map e₂.inv ≫ rightTarget)
              hmid
      _ =
        eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ (F.fiberFunctor V').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
            simp only [Category.assoc]
  have hstep_source_flat :
      eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ (F.fiberFunctor V').map (FXg.map d) ≫
          (F.fiberFunctor V').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          (F.fiberFunctor V').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
    -- Fold the source shell after flattening associations.
    calc
      eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ (F.fiberFunctor V').map (FXg.map d) ≫
          (F.fiberFunctor V').map rightSource ≫ eg₂.inv =
        eg₁.hom ≫
          ((F.fiberFunctor V').map leftSource ≫ (F.fiberFunctor V').map (FXg.map d) ≫
            (F.fiberFunctor V').map rightSource) ≫
          eg₂.inv := by
            simp only [Category.assoc]
      _ =
        eg₁.hom ≫
          (F.fiberFunctor V').map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              d g gf₁ gf₂ hgf₁ hgf₂) ≫
          eg₂.inv := by
            exact congrArg (fun k ↦ eg₁.hom ≫ k ≫ eg₂.inv) hfold
  have hprefix :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (cover_descent_data_transport_hom_of_equivalence_over_base
            (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂)
          g gf₁ gf₂ hgf₁ hgf₂ =
        eg₁.hom ≫ (F.fiberFunctor V').map leftSource ≫ (F.fiberFunctor V').map (FXg.map d) ≫
          cg₂.inv ≫ FYg.map e₂.inv ≫ rightTarget := by
    -- Chain the unfolded shell expansion with the left and middle normalization steps.
    exact hunfolded.trans (hmap'.trans (hleft'.trans hmid'))
  exact
    hprefix.trans
      (hright'.trans
        (hstep_source_flat.trans rfl))

/-- Helper for Lemma 8.4.4: the pullback compatibility for the transported overlap maps is the
remaining fixed-cover coherence obligation after the conjugation normal form is fixed. -/
private theorem cover_descent_data_transport_hom_pullHom_hom
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_transport_hom_of_equivalence_over_base
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      cover_descent_data_transport_hom_of_equivalence_over_base
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
    let e₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF gf₁ (D.obj I₁)
    let e₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF gf₂ (D.obj I₂)
    -- Normalize the full transported shell, then replace the middle factor by the source
    -- descent-data pullback law.
    have hnormalize :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (cover_descent_data_transport_hom_of_equivalence_over_base
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂)
            g gf₁ gf₂ hgf₁ hgf₂ =
          e₁.hom ≫
            (F.fiberFunctor Y').map
              (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
                (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
            e₂.inv := by
      simpa only [e₁, e₂] using
        cover_descent_data_transport_hom_pullHom_normalized_shell
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D g q q' hq f₁ f₂ hf₁ hf₂
          gf₁ gf₂ hgf₁ hgf₂
    have hmiddle :
        e₁.hom ≫
            (F.fiberFunctor Y').map
              (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
                (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂) ≫
            e₂.inv =
          e₁.hom ≫
            (F.fiberFunctor Y').map
              (D.hom q' gf₁ gf₂
                (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
                (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
            e₂.inv := by
      exact congrArg (fun k ↦ e₁.hom ≫ (F.fiberFunctor Y').map k ≫ e₂.inv)
        (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
    have hfinal :
        e₁.hom ≫
            (F.fiberFunctor Y').map
              (D.hom q' gf₁ gf₂
                (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
                (by rw [← hq, ← hgf₂, Category.assoc, hf₂])) ≫
            e₂.inv =
          cover_descent_data_transport_hom_of_equivalence_over_base
            (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q' gf₁ gf₂
            (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
            (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
      -- Fold the target back to the comparison-conjugated transported overlap map.
      rfl
    exact hnormalize.trans (hmiddle.trans hfinal)

/-- Helper for Lemma 8.4.4: the component map of a morphism of descent data is compatible with
the transported overlap maps after conjugating by the pullback-comparison isomorphisms. -/
private theorem cover_descent_data_transport_functor_comm
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
        ((F.fiberFunctor I₁.Y).map (φ.hom I₁))) ≫
      cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D₂ q f₁ f₂ hf₁ hf₂ =
      cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D₁ q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
          ((F.fiberFunctor I₂.Y).map (φ.hom I₂))) := by
  -- TODO: rewrite both sides into the comparison-conjugated normal form, use `φ.comm` in the
  -- middle, and move the right comparison inverse with
  -- `basedFunctor_pullbackComparison_inv_naturality_over_vertical`.
  change
    (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
        ((F.fiberFunctor I₁.Y).map (φ.hom I₁))) ≫
      ((basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f₁ (D₂.obj I₁)).hom ≫
        (F.fiberFunctor Y).map (D₂.hom q f₁ f₂ hf₁ hf₂) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f₂ (D₂.obj I₂)).inv) =
    ((basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₁ (D₁.obj I₁)).hom ≫
      (F.fiberFunctor Y).map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₂ (D₁.obj I₂)).inv) ≫
      (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
        ((F.fiberFunctor I₂.Y).map (φ.hom I₂)))
  let e₁₁ :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₁ (D₁.obj I₁)
  let e₁₂ :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₁ (D₂.obj I₁)
  let e₂₁ :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₂ (D₁.obj I₂)
  let e₂₂ :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₂ (D₂.obj I₂)
  let θ₁ :=
    ((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
      ((F.fiberFunctor I₁.Y).map (φ.hom I₁))
  let θ₂ :=
    ((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
      ((F.fiberFunctor I₂.Y).map (φ.hom I₂))
  let α₁ :=
    (F.fiberFunctor Y).map
      (((canonicalFiberPseudofunctor p₁).map f₁.op.toLoc).toFunctor.map (φ.hom I₁))
  let α₂ :=
    (F.fiberFunctor Y).map
      (((canonicalFiberPseudofunctor p₁).map f₂.op.toLoc).toFunctor.map (φ.hom I₂))
  let d₁ := D₁.hom q f₁ f₂ hf₁ hf₂
  let d₂ := D₂.hom q f₁ f₂ hf₁ hf₂
  have hleft : θ₁ ≫ e₁₂.hom = e₁₁.hom ≫ α₁ := by
    -- Move the left component map across the pullback-comparison hom boundary.
    simpa [e₁₁, e₁₂, θ₁, α₁] using
      basedFunctor_pullbackComparison_naturality_over_vertical
        (p₁ := p₁) (p₂ := p₂) F hF f₁ (φ.hom I₁)
  have hmid0 :=
    congrArg (fun k ↦ (F.fiberFunctor Y).map k) (φ.comm q f₁ f₂ hf₁ hf₂)
  change
      (F.fiberFunctor Y).map
          ((((canonicalFiberPseudofunctor p₁).map f₁.op.toLoc).toFunctor.map
              (φ.hom I₁)) ≫ D₂.hom q f₁ f₂ hf₁ hf₂) =
        (F.fiberFunctor Y).map
          (D₁.hom q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor p₁).map f₂.op.toLoc).toFunctor.map
              (φ.hom I₂))) at hmid0
  rw [Functor.map_comp, Functor.map_comp] at hmid0
  have hmid :
      α₁ ≫ (F.fiberFunctor Y).map d₂ =
        (F.fiberFunctor Y).map d₁ ≫ α₂ := by
    -- Transport the descent-data morphism compatibility through the fiber functor over `Y`.
    simpa [α₁, α₂, d₁, d₂] using hmid0
  have hright : α₂ ≫ e₂₂.inv = e₂₁.inv ≫ θ₂ := by
    -- Move the right component map across the inverse comparison boundary.
    simpa [e₂₁, e₂₂, θ₂, α₂] using
      basedFunctor_pullbackComparison_inv_naturality_over_vertical
        (p₁ := p₁) (p₂ := p₂) F hF f₂ (φ.hom I₂)
  have hright_step :
      e₁₁.hom ≫ (F.fiberFunctor Y).map d₁ ≫ (α₂ ≫ e₂₂.inv) =
        e₁₁.hom ≫ (F.fiberFunctor Y).map d₁ ≫ (e₂₁.inv ≫ θ₂) := by
    -- Apply the inverse-side comparison naturality under the fixed left context.
    exact congrArg (fun k ↦ e₁₁.hom ≫ (F.fiberFunctor Y).map d₁ ≫ k) hright
  have hflat :
      ((θ₁ ≫ e₁₂.hom) ≫ (F.fiberFunctor Y).map d₂) ≫ e₂₂.inv =
        ((e₁₁.hom ≫ (F.fiberFunctor Y).map d₁) ≫ e₂₁.inv) ≫ θ₂ := by
    have hleft_step :
        ((θ₁ ≫ e₁₂.hom) ≫ (F.fiberFunctor Y).map d₂) ≫ e₂₂.inv =
          ((e₁₁.hom ≫ α₁) ≫ (F.fiberFunctor Y).map d₂) ≫ e₂₂.inv := by
      -- Apply the hom-side comparison square in the left context of the composite.
      exact congrArg (fun k ↦ ((k ≫ (F.fiberFunctor Y).map d₂) ≫ e₂₂.inv)) hleft
    have hmid_step :
        ((e₁₁.hom ≫ α₁) ≫ (F.fiberFunctor Y).map d₂) ≫ e₂₂.inv =
          ((e₁₁.hom ≫ (F.fiberFunctor Y).map d₁) ≫ α₂) ≫ e₂₂.inv := by
      -- Apply the descent-data morphism square between the two comparison boundaries.
      calc
        ((e₁₁.hom ≫ α₁) ≫ (F.fiberFunctor Y).map d₂) ≫ e₂₂.inv
            = (e₁₁.hom ≫ (α₁ ≫ (F.fiberFunctor Y).map d₂)) ≫ e₂₂.inv := by
                simp only [Category.assoc]
        _ = (e₁₁.hom ≫ ((F.fiberFunctor Y).map d₁ ≫ α₂)) ≫ e₂₂.inv := by
                simpa using
                  congrArg (fun k ↦ ((e₁₁.hom ≫ k) ≫ e₂₂.inv)) hmid
        _ = ((e₁₁.hom ≫ (F.fiberFunctor Y).map d₁) ≫ α₂) ≫ e₂₂.inv := by
                rw [← Category.assoc]
    have hright_flat :
        ((e₁₁.hom ≫ (F.fiberFunctor Y).map d₁) ≫ α₂) ≫ e₂₂.inv =
          ((e₁₁.hom ≫ (F.fiberFunctor Y).map d₁) ≫ e₂₁.inv) ≫ θ₂ := by
      -- Apply the inverse-side comparison square in the right context of the composite.
      simpa only [Category.assoc] using hright_step
    exact hleft_step.trans (hmid_step.trans hright_flat)
  simpa [e₁₁, e₁₂, e₂₁, e₂₂, θ₁, θ₂, d₁, d₂, Category.assoc] using hflat

/-- Helper for Lemma 8.4.4: transport a fixed-cover descent datum objectwise along the given
equivalence over the base. -/
private noncomputable def cover_descent_data_transport_obj_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) →
      ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f))
  | D =>
      { obj := fun I ↦ (F.fiberFunctor I.Y).obj (D.obj I)
        hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
          cover_descent_data_transport_hom_of_equivalence_over_base
            (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂
        pullHom_hom := by
          intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
          -- Delegate the remaining pullback-compatibility field to the dedicated transport lemma.
          simpa using
            cover_descent_data_transport_hom_pullHom_hom
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D g q q' hq f₁ f₂ hf₁ hf₂
              gf₁ gf₂ hgf₁ hgf₂
        hom_self := by
          intro Y q I g hg
          -- Use the dedicated normalization lemma so the object constructor stays flat.
          simpa using
            cover_descent_data_transport_hom_self_normalize
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q g hg
        hom_comp := by
          intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
          -- Use the dedicated cocycle transport lemma so the main object definition only records
          -- the source-faithful proof skeleton.
          simpa using
            cover_descent_data_transport_hom_comp_normalize
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ f₃ hf₁ hf₂ hf₃ }

/-- Helper for Lemma 8.4.4: assemble the fixed-cover transport on descent data into a functor.
Only the componentwise morphism compatibility remains after the objectwise transport is fixed. -/
private noncomputable def cover_descent_data_transport_functor_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f)) where
  obj D :=
    cover_descent_data_transport_obj_of_equivalence_over_base
      (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D
  map {D₁ D₂} φ :=
    { hom := fun I ↦ (F.fiberFunctor I.Y).map (φ.hom I)
      comm := by
        intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
        -- Invoke the dedicated conjugation compatibility lemma for morphisms of descent data.
        simpa using
          cover_descent_data_transport_functor_comm
            (J := J) (p₁ := p₁) (p₂ := p₂) F hF S φ q f₁ f₂ hf₁ hf₂ }
  map_id X := by
    -- The transport functor acts by the identity on each component because every fiber functor
    -- preserves identity morphisms.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change (F.fiberFunctor I.Y).map (𝟙 (X.obj I)) = 𝟙 ((F.fiberFunctor I.Y).obj (X.obj I))
    exact (F.fiberFunctor I.Y).map_id (X.obj I)
  map_comp f g := by
    -- Composition is computed objectwise since the transport functor maps each component through
    -- the corresponding fiber functor.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change (F.fiberFunctor I.Y).map (f.hom I ≫ g.hom I) =
      (F.fiberFunctor I.Y).map (f.hom I) ≫ (F.fiberFunctor I.Y).map (g.hom I)
    exact (F.fiberFunctor I.Y).map_comp (f.hom I) (g.hom I)

/-- Helper for Chap08 Lemma 8 4 4: the right leg of the canonical target overlap, after
postcomposing with the mapped `I₂`-comparison hom, is the specialized left-boundary shell over
the common map `q`. -/
private theorem canonical_target_descent_right_leg_postcompose_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) (x : p₁.Fiber U)
    {V : C} (q : V ⟶ U) {I₂ : S.Arrow}
    (f₂ : V ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p₂).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (baseComp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
        ((F.fiberFunctor U).obj x)) ≫
      (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).hom) =
      (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF q x).hom ≫
        (F.fiberFunctor V).map
          (((canonicalFiberPseudofunctor p₁).mapComp'
              I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (baseComp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f₂
          (((canonicalFiberPseudofunctor p₁).map I₂.f.op.toLoc).toFunctor.obj x)).inv := by
  -- Specialize the already proved left-boundary normalization to the cover leg followed by `f₂`.
  simpa only [Category.id_comp] using
    basedFunctor_pullbackComparison_pullHom_left_boundary
      (p₁ := p₁) (p₂ := p₂) F hF I₂.f f₂ q hf₂ x

/-- Helper for Chap08 Lemma 8 4 4: the left leg of the canonical target overlap is the specialized
right-boundary shell whose target comparison lives over the common map `q`. -/
private theorem canonical_target_descent_left_leg_normalized_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) (x : p₁.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ : S.Arrow}
    (f₁ : V ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₁
        (((canonicalFiberPseudofunctor p₁).map I₁.f.op.toLoc).toFunctor.obj x)).inv ≫
      (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF I₁.f x).inv) ≫
      (((canonicalFiberPseudofunctor p₂).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (baseComp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
        ((F.fiberFunctor U).obj x)) =
    (F.fiberFunctor V).map
        (((canonicalFiberPseudofunctor p₁).mapComp'
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (baseComp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF q x).inv := by
  -- Specialize the right-boundary normalization to the cover leg followed by `f₁`.
  simpa only [Category.id_comp] using
    basedFunctor_pullbackComparison_pullHom_right_boundary
      (p₁ := p₁) (p₂ := p₂) F hF I₁.f f₁ q hf₁ x

/-- Helper for Chap08 Lemma 8 4 4: before cancelling the final mapped `I₂`-comparison, the
canonical target overlap shell agrees with the grouped comparison-conjugate shell. -/
private theorem canonical_target_descent_component_comm_rhs_owner_normal_form_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) (x : p₁.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
        ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
      (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).hom) =
    ((((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF I₁.f x).hom) ≫
        ((cover_descent_data_transport_functor_of_equivalence_over_base
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S).obj
          (((canonicalFiberPseudofunctor p₁).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).inv)) ≫
      (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).hom) := by
  let F₁ := ((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor
  let F₂ := ((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor
  let D :=
    ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).obj x
  let e₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF I₁.f x
  let e₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF I₂.f x
  let eq₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f₁
    (((canonicalFiberPseudofunctor p₁).map I₁.f.op.toLoc).toFunctor.obj x)
  let eq₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f₂
    (((canonicalFiberPseudofunctor p₁).map I₂.f.op.toLoc).toFunctor.obj x)
  let eqq := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF q x
  let leftSource :=
    (((canonicalFiberPseudofunctor p₁).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (baseComp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)
  let rightSource :=
    (((canonicalFiberPseudofunctor p₁).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (baseComp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)
  let targetLeft :=
    (((canonicalFiberPseudofunctor p₂).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (baseComp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
      ((F.fiberFunctor U).obj x))
  let targetRight :=
    (((canonicalFiberPseudofunctor p₂).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (baseComp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
      ((F.fiberFunctor U).obj x))
  let core :=
    F₁.map e₁.hom ≫
      ((cover_descent_data_transport_functor_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S).obj D).hom q f₁ f₂ hf₁ hf₂
  have hleft_raw :
      eq₁.inv ≫ F₁.map e₁.inv ≫ targetLeft =
        (F.fiberFunctor V).map leftSource ≫ eqq.inv := by
    -- Normalize the left target leg to the common `q`-comparison shell.
    simpa only [F₁, eq₁, e₁, leftSource, eqq, targetLeft] using
      canonical_target_descent_left_leg_normalized_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S x (q := q)
        (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
  have hleft_cancel₁ :
      F₁.map e₁.inv ≫ targetLeft =
        eq₁.hom ≫ ((F.fiberFunctor V).map leftSource ≫ eqq.inv) := by
    -- Cancel the iterated `f₁`-comparison on the far left.
    exact (Iso.inv_comp_eq eq₁).1 (by simpa only [Category.assoc] using hleft_raw)
  have hleft :
      targetLeft =
        F₁.map e₁.hom ≫ eq₁.hom ≫ (F.fiberFunctor V).map leftSource ≫ eqq.inv := by
    -- Cancel the mapped `I₁`-comparison to isolate the raw target left leg.
    exact
      (Iso.inv_comp_eq (F₁.mapIso e₁)).1 <| by
        simpa only [Category.assoc] using hleft_cancel₁
  have hright :
      targetRight ≫ F₂.map e₂.hom =
        eqq.hom ≫ (F.fiberFunctor V).map rightSource ≫ eq₂.inv := by
    -- Normalize the right leg after the final mapped `I₂`-comparison postcomposition.
    simpa only [F₂, e₂, eqq, rightSource, eq₂] using
      canonical_target_descent_right_leg_postcompose_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S x (q := q)
        (I₂ := I₂) (f₂ := f₂) (hf₂ := hf₂)
  have hq_cancel :
      eqq.inv ≫ eqq.hom ≫ ((F.fiberFunctor V).map rightSource ≫ eq₂.inv) =
        (F.fiberFunctor V).map rightSource ≫ eq₂.inv := by
    -- The inserted `q`-comparison inverse-hom pair cancels before the frozen right tail.
    simpa only [Category.assoc] using
      basedFunctor_pullbackComparison_inv_hom_postcompose_normalized
        (p₁ := p₁) (p₂ := p₂) F hF q x
        ((F.fiberFunctor V).map rightSource ≫ eq₂.inv)
  have hcore :
      ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom =
        core := by
    -- Rewrite left and right legs to the common `q`-comparison shell, cancel that shell, and
    -- fold the mapped source overlap back to the transported source descent datum.
    let lhsOwner :=
      ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
        F₂.map e₂.hom
    have hstart :
        lhsOwner = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
      calc
        lhsOwner = (targetLeft ≫ targetRight) ≫ F₂.map e₂.hom := by
          rfl
        _ = targetLeft ≫ (targetRight ≫ F₂.map e₂.hom) := by
          simp only [Category.assoc]
    have hstep_right :
        lhsOwner = targetLeft ≫ (eqq.hom ≫ (F.fiberFunctor V).map rightSource ≫ eq₂.inv) := by
      exact hstart.trans (congrArg (fun k ↦ targetLeft ≫ k) hright)
    have hstep_left :
        lhsOwner =
          (F₁.map e₁.hom ≫ eq₁.hom ≫ (F.fiberFunctor V).map leftSource ≫ eqq.inv) ≫
            (eqq.hom ≫ (F.fiberFunctor V).map rightSource ≫ eq₂.inv) := by
      exact hstep_right.trans <|
        congrArg
          (fun k ↦ k ≫ (eqq.hom ≫ (F.fiberFunctor V).map rightSource ≫ eq₂.inv))
          hleft
    have hstep_flat :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((F.fiberFunctor V).map leftSource ≫ eqq.inv ≫ eqq.hom ≫
              (F.fiberFunctor V).map rightSource ≫ eq₂.inv) := by
      simpa only [Category.assoc] using hstep_left
    have hstep_cancel :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            ((F.fiberFunctor V).map leftSource ≫
              ((F.fiberFunctor V).map rightSource ≫ eq₂.inv)) := by
      exact hstep_flat.trans <|
        congrArg
          (fun k ↦ F₁.map e₁.hom ≫ eq₁.hom ≫ ((F.fiberFunctor V).map leftSource ≫ k))
          hq_cancel
    have hstep_map :
        lhsOwner =
          F₁.map e₁.hom ≫ eq₁.hom ≫
            (F.fiberFunctor V).map (leftSource ≫ rightSource) ≫ eq₂.inv := by
      have hstep_grouped :
          lhsOwner =
            F₁.map e₁.hom ≫ eq₁.hom ≫
              ((F.fiberFunctor V).map leftSource ≫
                (F.fiberFunctor V).map rightSource) ≫ eq₂.inv := by
        simpa only [Category.assoc] using hstep_cancel
      exact hstep_grouped.trans <|
        congrArg
          (fun k ↦ F₁.map e₁.hom ≫ eq₁.hom ≫ k ≫ eq₂.inv)
          ((F.fiberFunctor V).map_comp leftSource rightSource).symm
    -- Fold the source overlap shell to the fixed-cover transport functor's normal form.
    simpa only [lhsOwner] using hstep_map.trans rfl
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    -- The final mapped `I₂`-comparison pair cancels on the right.
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
        exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
        rw [F₂.map_id]
  have hinsert :
      core =
        ((((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
              (basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₁) (p₂ := p₂) F hF I₁.f x).hom) ≫
            ((cover_descent_data_transport_functor_of_equivalence_over_base
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S).obj
              (((canonicalFiberPseudofunctor p₁).toDescentData
                (fun I : S.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
            (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
              (basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).inv)) ≫
          (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
            (basedFunctor_pullbackComparison_of_equivalence_over_base
              (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).hom) := by
    -- Insert the final mapped inverse-hom identity on the right so the owner theorem has the
    -- postcomposed shape needed by the later cancellation lemma.
    calc
      core = core ≫ 𝟙 _ := by
        rw [Category.comp_id]
      _ = core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
        exact congrArg (fun k ↦ core ≫ k) htail.symm
      _ = (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
        simp only [Category.assoc]
      _ =
          ((((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
                (basedFunctor_pullbackComparison_of_equivalence_over_base
                  (p₁ := p₁) (p₂ := p₂) F hF I₁.f x).hom) ≫
              ((cover_descent_data_transport_functor_of_equivalence_over_base
                (J := J) (p₁ := p₁) (p₂ := p₂) F hF S).obj
                (((canonicalFiberPseudofunctor p₁).toDescentData
                  (fun I : S.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
              (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
                (basedFunctor_pullbackComparison_of_equivalence_over_base
                  (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).inv)) ≫
            (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
              (basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).hom) := by
            simpa only [core, D, F₁, F₂, e₁, e₂, Category.assoc]
  exact hcore.trans hinsert

/-- Helper for Chap08 Lemma 8 4 4: the canonical target overlap morphism is the
pullback-comparison conjugate of the transported canonical source overlap on a fixed cover. -/
private theorem canonical_target_descent_hom_eq_comparison_conjugate_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) (x : p₁.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
        ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) =
      (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF I₁.f x).hom) ≫
        ((cover_descent_data_transport_functor_of_equivalence_over_base
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S).obj
          (((canonicalFiberPseudofunctor p₁).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).inv) := by
  let F₂ := ((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor
  let e₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF I₂.f x
  -- Cancel the final mapped `I₂`-comparison in the grouped owner normal form.
  exact
    (Iso.cancel_iso_hom_right _ _ (F₂.mapIso e₂)).1 <| by
      change
        ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
              ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
            F₂.map e₂.hom =
          ((((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
                (basedFunctor_pullbackComparison_of_equivalence_over_base
                  (p₁ := p₁) (p₂ := p₂) F hF I₁.f x).hom) ≫
              ((cover_descent_data_transport_functor_of_equivalence_over_base
                (J := J) (p₁ := p₁) (p₂ := p₂) F hF S).obj
                (((canonicalFiberPseudofunctor p₁).toDescentData
                  (fun I : S.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂ ≫
              F₂.map e₂.inv) ≫
            F₂.map e₂.hom
      simpa only [F₂, e₂, Category.assoc] using
        canonical_target_descent_component_comm_rhs_owner_normal_form_of_equivalence_over_base
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S x (q := q)
          (I₁ := I₁) (I₂ := I₂)
          (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)

/-- Helper for Chap08 Lemma 8 4 4: pullback-comparison components identify the transported
canonical source descent datum with the canonical target descent datum. -/
private theorem cover_descent_data_transport_toDescentData_component_comm
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) (x : p₁.Fiber U)
    {V : C} (q : V ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF I₁.f x).hom) ≫
      ((cover_descent_data_transport_functor_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S).obj
        (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).obj x)).hom
          q f₁ f₂ hf₁ hf₂ =
      ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
          ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
        (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF I₂.f x).hom) := by
  let F₂ := ((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor
  let e₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF I₂.f x
  let core :=
    (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF I₁.f x).hom) ≫
      ((cover_descent_data_transport_functor_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S).obj
        (((canonicalFiberPseudofunctor p₁).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj x)).hom q f₁ f₂ hf₁ hf₂
  have hstrong :
      ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) =
        core ≫ F₂.map e₂.inv := by
    -- Reassociate the comparison-conjugate theorem to the `core ≫ map(inv)` form.
    simpa only [core, F₂, e₂, Category.assoc] using
      canonical_target_descent_hom_eq_comparison_conjugate_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S x (q := q)
        (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hpost :
      ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
            ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom =
        (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom := by
    -- Postcompose the strong comparison-conjugate identity by the mapped right comparison hom.
    exact congrArg (fun k ↦ k ≫ F₂.map e₂.hom) hstrong
  have htail : F₂.map e₂.inv ≫ F₂.map e₂.hom = 𝟙 _ := by
    -- The mapped right comparison pair cancels by functoriality.
    calc
      F₂.map e₂.inv ≫ F₂.map e₂.hom = F₂.map (e₂.inv ≫ e₂.hom) := by
        rw [← F₂.map_comp]
      _ = F₂.map (𝟙 _) := by
        exact congrArg F₂.map e₂.inv_hom_id
      _ = 𝟙 _ := by
        rw [F₂.map_id]
  have hcancel : (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom = core := by
    -- The mapped right comparison pair cancels in one step.
    calc
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
          core ≫ (F₂.map e₂.inv ≫ F₂.map e₂.hom) := by
            simp only [Category.assoc]
      _ = core ≫ 𝟙 _ := by
            exact congrArg (fun k ↦ core ≫ k) htail
      _ = core := by
            rw [Category.comp_id]
  have hpost' :
      (core ≫ F₂.map e₂.inv) ≫ F₂.map e₂.hom =
        ((((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).obj
              ((F.fiberFunctor U).obj x)).hom q f₁ f₂ hf₁ hf₂) ≫
          F₂.map e₂.hom := by
    exact hpost.symm
  exact hcancel.symm.trans hpost'

/-- Helper for Chap08 Lemma 8 4 4: the fixed-cover transport functor carries canonical descent
data to canonical descent data, with components given by pullback comparison. -/
private noncomputable def cover_descent_data_transport_toDescentData_iso
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) :
    (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙
      cover_descent_data_transport_functor_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S) ≅
      ((F.fiberFunctor U) ⋙
        ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f))) := by
  let η :
      ((F.fiberFunctor U) ⋙
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f))) ≅
        (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙
          cover_descent_data_transport_functor_of_equivalence_over_base
            (J := J) (p₁ := p₁) (p₂ := p₂) F hF S) :=
    NatIso.ofComponents
      (fun x ↦
        -- Package the pullback-comparison components into an isomorphism of descent data.
        Pseudofunctor.DescentData.isoMk
          (fun I ↦
            basedFunctor_pullbackComparison_of_equivalence_over_base
              (p₁ := p₁) (p₂ := p₂) F hF I.f x)
          (fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
            cover_descent_data_transport_toDescentData_component_comm
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S x (q := q)
              (I₁ := I₁) (I₂ := I₂)
              (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)))
      (fun φ ↦ by
        -- Naturality is exactly the hom-side pullback-comparison square on each cover leg.
        apply Pseudofunctor.DescentData.hom_ext
        intro I
        rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
        simpa only [Functor.comp_map, cover_descent_data_transport_functor_of_equivalence_over_base] using
          basedFunctor_pullbackComparison_naturality_over_vertical
            (p₁ := p₁) (p₂ := p₂) F hF I.f φ)
  exact η.symm

/-- Helper for Chap08 Lemma 8 4 4: cancel two consecutive isomorphism tails on the right of a
composite. -/
private theorem comp_hom_hom_inv_inv_cancel
    {K : Type*} [Category K] {A B D E : K}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (h' : E ⟶ D) (g' : D ⟶ B)
    (hh : h ≫ h' = 𝟙 D) (hg : g ≫ g' = 𝟙 B) :
    f ≫ g ≫ h ≫ h' ≫ g' = f := by
  -- First collapse the inner inverse pair, then collapse the outer inverse pair.
  calc
    f ≫ g ≫ h ≫ h' ≫ g' = f ≫ g ≫ (h ≫ h') ≫ g' := by
      simp [Category.assoc]
    _ = f ≫ g ≫ 𝟙 D ≫ g' := by
      rw [hh]
    _ = f ≫ g ≫ g' := by
      simp
    _ = f ≫ (g ≫ g') := by
      simp
    _ = f ≫ 𝟙 B := by
      rw [hg]
    _ = f := by
      simp

/-- Helper for Chap08 Lemma 8 4 4: cancel two consecutive isomorphism heads on the left of a
composite. -/
private theorem comp_inv_inv_hom_hom_cancel
    {K : Type*} [Category K] {B D E Z : K}
    (jInv : E ⟶ D) (iInv : D ⟶ B) (iHom : B ⟶ D) (jHom : D ⟶ E) (f : E ⟶ Z)
    (hi : iInv ≫ iHom = 𝟙 D) (hj : jInv ≫ jHom = 𝟙 E) :
    jInv ≫ iInv ≫ iHom ≫ jHom ≫ f = f := by
  -- Reassociate just enough to expose the two inverse pairs in order.
  calc
    jInv ≫ iInv ≫ iHom ≫ jHom ≫ f = jInv ≫ (iInv ≫ iHom) ≫ jHom ≫ f := by
      simp [Category.assoc]
    _ = jInv ≫ 𝟙 D ≫ jHom ≫ f := by
      rw [hi]
    _ = jInv ≫ jHom ≫ f := by
      simp
    _ = (jInv ≫ jHom) ≫ f := by
      simp [Category.assoc]
    _ = 𝟙 E ≫ f := by
      rw [hj]
    _ = f := by
      simp

/-- Helper for Chap08 Lemma 8 4 4: the unit component of an equivalence over the base commutes
with one canonical pullback comparison for `F` followed by one for the chosen inverse. -/
private theorem unit_comp_pullbackComparison_hom_boundary
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) (e : EquivalenceOverBase F)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U)
    (ηU : x ⟶ (e.inverse.fiberFunctor U).obj ((F.fiberFunctor U).obj x))
    (ηV :
      (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x) ⟶
        (e.inverse.fiberFunctor V).obj
          ((F.fiberFunctor V).obj
            (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x)))
    (hηU : ηU.1 = e.unitIso.hom.app x.1)
    (hηV :
      ηV.1 =
        e.unitIso.hom.app
          ((((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x).1)) :
    (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map ηU) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₂) (p₂ := p₁) e.inverse e.inverse_isEquivalenceOverBase f
          ((F.fiberFunctor U).obj x)).hom ≫
      (e.inverse.fiberFunctor V).map
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).hom =
      ηV := by
  -- Compare after the common strongly cartesian image of the source pullback arrow.
  apply Functor.Fiber.hom_ext
  let Fpb := ((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor
  let cF := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f x
  let cG := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₂) (p₂ := p₁) e.inverse e.inverse_isEquivalenceOverBase f
    ((F.fiberFunctor U).obj x)
  let tau := (canonicalPullbackChoice p₁).map f x
  let tauGF := (canonicalPullbackChoice p₁).map f
    ((e.inverse.fiberFunctor U).obj ((F.fiberFunctor U).obj x))
  let tail := e.inverse.map (F.map tau)
  have hFtau : p₂.IsStronglyCartesian f (F.map tau) := by
    change p₂.IsStronglyCartesian f (F.map ((canonicalPullbackChoice p₁).map f x))
    exact basedFunctor_map_stronglyCartesian_of_lift
      (p₁ := p₁) (p₂ := p₂) F hF f
      ((canonicalPullbackChoice p₁).map f x)
      ((canonicalPullbackChoice p₁).isStronglyCartesian f x)
  have htail : p₁.IsStronglyCartesian f tail := by
    change p₁.IsStronglyCartesian f (e.inverse.map (F.map tau))
    exact basedFunctor_map_stronglyCartesian_of_lift
      (p₁ := p₂) (p₂ := p₁) e.inverse e.inverse_isEquivalenceOverBase f
      (F.map tau) hFtau
  have hcf : cF.hom.1 ≫ F.map tau =
      (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x) := by
    -- The `F` comparison becomes the chosen target pullback arrow after postcomposition.
    simpa [cF, tau] using
      basedFunctor_pullbackComparison_hom_postcompose
        (p₁ := p₁) (p₂ := p₂) F hF f x
  have hmapcf : ((e.inverse.fiberFunctor V).map cF.hom).1 ≫ tail =
      e.inverse.map ((canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x)) := by
    -- Map the preceding postcomposition identity through the chosen inverse functor.
    change e.inverse.map cF.hom.1 ≫ e.inverse.map (F.map tau) =
      e.inverse.map ((canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x))
    rw [← Functor.map_comp]
    exact congrArg e.inverse.map hcf
  have hcg : cG.hom.1 ≫
      e.inverse.map ((canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x)) =
      tauGF := by
    -- The inverse-functor comparison then becomes the chosen pullback arrow for `G(F x)`.
    simpa [cG, tauGF] using
      basedFunctor_pullbackComparison_hom_postcompose
        (p₁ := p₂) (p₂ := p₁) e.inverse e.inverse_isEquivalenceOverBase f
        ((F.fiberFunctor U).obj x)
  have hfac : (Fpb.map ηU).1 ≫ tauGF = tau ≫ ηU.1 := by
    -- Pullback functoriality moves the unit component across the chosen pullback arrow.
    simpa [Fpb, tau, tauGF] using
      equivalenceTransport_canonical_pullbackFunctor_map_fac (p := p₁) f ηU
  have hnat : tau ≫ ηU.1 = ηV.1 ≫ tail := by
    -- Naturality of the based unit identifies the two postcomposed normal forms.
    simpa [tau, tail, hηU, hηV] using
      (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.naturality
        ((canonicalPullbackChoice p₁).map f x))
  have h0 :
      (Fpb.map ηU ≫ cG.hom ≫ (e.inverse.fiberFunctor V).map cF.hom).1 ≫ tail =
        ((Fpb.map ηU).1 ≫ cG.hom.1 ≫ ((e.inverse.fiberFunctor V).map cF.hom).1) ≫ tail := by
    rfl
  have h1 :
      ((Fpb.map ηU).1 ≫ cG.hom.1 ≫ ((e.inverse.fiberFunctor V).map cF.hom).1) ≫ tail =
      (Fpb.map ηU).1 ≫ cG.hom.1 ≫ (((e.inverse.fiberFunctor V).map cF.hom).1 ≫ tail) := by
    simp only [Category.assoc]
  have h2 :
      (Fpb.map ηU).1 ≫ cG.hom.1 ≫ (((e.inverse.fiberFunctor V).map cF.hom).1 ≫ tail) =
      (Fpb.map ηU).1 ≫ cG.hom.1 ≫
          e.inverse.map ((canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x)) := by
    exact congrArg (fun k ↦ (Fpb.map ηU).1 ≫ cG.hom.1 ≫ k) hmapcf
  have h3 :
      (Fpb.map ηU).1 ≫ cG.hom.1 ≫
          e.inverse.map ((canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x)) =
      (Fpb.map ηU).1 ≫ tauGF := by
    simpa only [Category.assoc] using congrArg (fun k ↦ (Fpb.map ηU).1 ≫ k) hcg
  have h4 :
      (Fpb.map ηU).1 ≫ tauGF = ηV.1 ≫ tail :=
    hfac.trans hnat
  have hpost :
      (Fpb.map ηU ≫ cG.hom ≫ (e.inverse.fiberFunctor V).map cF.hom).1 ≫ tail =
        ηV.1 ≫ tail :=
    h0.trans (h1.trans (h2.trans (h3.trans h4)))
  have hlhs : p₁.IsHomLift (𝟙 V)
      (Fpb.map ηU ≫ cG.hom ≫ (e.inverse.fiberFunctor V).map cF.hom).1 :=
    (Fpb.map ηU ≫ cG.hom ≫ (e.inverse.fiberFunctor V).map cF.hom).2
  have hrhs : p₁.IsHomLift (𝟙 V) ηV.1 := ηV.2
  exact @Functor.IsStronglyCartesian.ext _ _ _ _ p₁ _ _ _ _
    f tail htail _ _ (𝟙 V)
    (Fpb.map ηU ≫ cG.hom ≫ (e.inverse.fiberFunctor V).map cF.hom).1
    ηV.1 hlhs hrhs hpost

/-- Helper for Chap08 Lemma 8 4 4: the counit component of an equivalence over the base commutes
with one inverse pullback comparison followed by one `F`-comparison. -/
private theorem counit_comp_pullbackComparison_hom_boundary
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) (e : EquivalenceOverBase F)
    {U V : C} (f : V ⟶ U) (y : p₂.Fiber U)
    (εU : (F.fiberFunctor U).obj ((e.inverse.fiberFunctor U).obj y) ⟶ y)
    (εV :
      (F.fiberFunctor V).obj
          ((e.inverse.fiberFunctor V).obj
            (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj y)) ⟶
        (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj y))
    (hεU : εU.1 = e.counitIso.hom.app y.1)
    (hεV :
      εV.1 =
        e.counitIso.hom.app
          ((((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj y).1)) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f ((e.inverse.fiberFunctor U).obj y)).hom ≫
        (F.fiberFunctor V).map
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₂) (p₂ := p₁) e.inverse e.inverse_isEquivalenceOverBase f y).hom ≫
      εV =
      (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map εU) := by
  -- Compare after the canonical target pullback arrow and use counit naturality on that arrow.
  apply Functor.Fiber.hom_ext
  let Fpb := ((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor
  let cG := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₂) (p₂ := p₁) e.inverse e.inverse_isEquivalenceOverBase f y
  let cF := basedFunctor_pullbackComparison_of_equivalence_over_base
    (p₁ := p₁) (p₂ := p₂) F hF f ((e.inverse.fiberFunctor U).obj y)
  let tau := (canonicalPullbackChoice p₂).map f y
  let tauG := (canonicalPullbackChoice p₁).map f ((e.inverse.fiberFunctor U).obj y)
  let tauFG := (canonicalPullbackChoice p₂).map f
    ((F.fiberFunctor U).obj ((e.inverse.fiberFunctor U).obj y))
  have htail : p₂.IsStronglyCartesian f tau := by
    change p₂.IsStronglyCartesian f ((canonicalPullbackChoice p₂).map f y)
    exact (canonicalPullbackChoice p₂).isStronglyCartesian f y
  have hcg : cG.hom.1 ≫ e.inverse.map tau = tauG := by
    -- Postcompose the inverse-functor comparison by the chosen target pullback arrow.
    simpa [cG, tau, tauG] using
      basedFunctor_pullbackComparison_hom_postcompose
        (p₁ := p₂) (p₂ := p₁) e.inverse e.inverse_isEquivalenceOverBase f y
  have hmapcg : ((F.fiberFunctor V).map cG.hom).1 ≫ F.map (e.inverse.map tau) =
      F.map tauG := by
    -- Map the inverse-functor postcomposition identity through `F`.
    change F.map cG.hom.1 ≫ F.map (e.inverse.map tau) = F.map tauG
    rw [← Functor.map_comp]
    exact congrArg F.map hcg
  have hcf : cF.hom.1 ≫ F.map tauG = tauFG := by
    -- The remaining `F` comparison is characterized by the same chosen pullback arrow.
    simpa [cF, tauG, tauFG] using
      basedFunctor_pullbackComparison_hom_postcompose
        (p₁ := p₁) (p₂ := p₂) F hF f ((e.inverse.fiberFunctor U).obj y)
  have hnat : εV.1 ≫ tau = F.map (e.inverse.map tau) ≫ εU.1 := by
    -- Naturality of the based counit identifies the two postcomposed composites.
    simpa [tau, hεU, hεV] using
      (((BasedNatTrans.forgetful _ _).mapIso e.counitIso).hom.naturality
        ((canonicalPullbackChoice p₂).map f y)).symm
  have hfac : (Fpb.map εU).1 ≫ tau = tauFG ≫ εU.1 := by
    -- Pullback functoriality gives the canonical right-hand postcomposition normal form.
    simpa [Fpb, tau, tauFG] using
      equivalenceTransport_canonical_pullbackFunctor_map_fac (p := p₂) f εU
  have h0 :
      (cF.hom ≫ (F.fiberFunctor V).map cG.hom ≫ εV).1 ≫ tau =
        (cF.hom.1 ≫ ((F.fiberFunctor V).map cG.hom).1 ≫ εV.1) ≫ tau := by
    rfl
  have h1 :
      (cF.hom.1 ≫ ((F.fiberFunctor V).map cG.hom).1 ≫ εV.1) ≫ tau =
      cF.hom.1 ≫ ((F.fiberFunctor V).map cG.hom).1 ≫ (εV.1 ≫ tau) := by
    simp only [Category.assoc]
  have h2 :
      cF.hom.1 ≫ ((F.fiberFunctor V).map cG.hom).1 ≫ (εV.1 ≫ tau) =
      cF.hom.1 ≫ ((F.fiberFunctor V).map cG.hom).1 ≫
        (F.map (e.inverse.map tau) ≫ εU.1) := by
    exact congrArg (fun k ↦ cF.hom.1 ≫ ((F.fiberFunctor V).map cG.hom).1 ≫ k) hnat
  have h3 :
      cF.hom.1 ≫ ((F.fiberFunctor V).map cG.hom).1 ≫
        (F.map (e.inverse.map tau) ≫ εU.1) =
      cF.hom.1 ≫ (((F.fiberFunctor V).map cG.hom).1 ≫ F.map (e.inverse.map tau)) ≫
        εU.1 := by
    simp only [Category.assoc]
  have h4 :
      cF.hom.1 ≫ (((F.fiberFunctor V).map cG.hom).1 ≫ F.map (e.inverse.map tau)) ≫
          εU.1 =
      cF.hom.1 ≫ F.map tauG ≫ εU.1 := by
    exact congrArg (fun k ↦ cF.hom.1 ≫ k ≫ εU.1) hmapcg
  have h5 :
      cF.hom.1 ≫ F.map tauG ≫ εU.1 = tauFG ≫ εU.1 := by
    calc
      cF.hom.1 ≫ F.map tauG ≫ εU.1 = (cF.hom.1 ≫ F.map tauG) ≫ εU.1 := by
        rw [Category.assoc]
      _ = tauFG ≫ εU.1 := by
        exact congrArg (fun k ↦ k ≫ εU.1) hcf
  have hpost :
      (cF.hom ≫ (F.fiberFunctor V).map cG.hom ≫ εV).1 ≫ tau =
        (Fpb.map εU).1 ≫ tau :=
    h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans hfac.symm)))))
  have hlhs : p₂.IsHomLift (𝟙 V)
      (cF.hom ≫ (F.fiberFunctor V).map cG.hom ≫ εV).1 :=
    (cF.hom ≫ (F.fiberFunctor V).map cG.hom ≫ εV).2
  have hrhs : p₂.IsHomLift (𝟙 V) (Fpb.map εU).1 := (Fpb.map εU).2
  exact @Functor.IsStronglyCartesian.ext _ _ _ _ p₂ _ _ _ _
    f tau htail _ _ (𝟙 V)
    (cF.hom ≫ (F.fiberFunctor V).map cG.hom ≫ εV).1
    (Fpb.map εU).1 hlhs hrhs hpost

/-- Chap08 Lemma 8 4 4: for a fixed cover, an equivalence over the base transports the
equivalence of the canonical descent functor between the two fiber pseudofunctors. -/
theorem coverwise_canonicalDescentFunctor_isEquivalence_iff_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
      ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  classical
  -- Route correction: the mixed-hom pullback comparison is already in place, so the remaining
  -- source-faithful step is to package the fixed-cover descent-data transport and then invoke the
  -- abstract cancellation lemma proved just above.
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  let G := e.inverse
  let _i := e.counitIso
  let _j := e.unitIso
  let _eU :
      (F.fiberFunctor U).IsEquivalence :=
    fiberFunctor_isEquivalence_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF U
  let _eUinv :
      (G.fiberFunctor U).IsEquivalence :=
    inverse_fiberFunctor_isEquivalence_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF U
  -- The forward transport functor is the fixed-cover descent-data transport built objectwise from
  -- the fiber functors and pullback-comparison isomorphisms.
  let TF :
      ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
        ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f)) :=
    cover_descent_data_transport_functor_of_equivalence_over_base
      (J := J) (p₁ := p₁) (p₂ := p₂) F hF S
  have hTF : TF.IsEquivalence := by
    -- Build the inverse fixed-cover transport from the chosen inverse based functor.
    let hG : G.IsEquivalenceOverBase := e.inverse_isEquivalenceOverBase
    let TG :
        ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
          ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) :=
      cover_descent_data_transport_functor_of_equivalence_over_base
        (J := J) (p₁ := p₂) (p₂ := p₁) G hG S
    let fiberUnitIso :
        ∀ (I : S.Arrow) (x : p₁.Fiber I.Y),
          x ≅ (G.fiberFunctor I.Y).obj ((F.fiberFunctor I.Y).obj x) :=
      fun I x ↦ by
        -- The based unit components are vertical, so they restrict to isomorphisms in each
        -- fiber over the cover member.
        let α := e.unitIso
        let αHom := α.hom
        let αInv := α.inv
        have hhom : (BasedCategory.ofFunctor p₁).p.IsHomLift (𝟙 I.Y) (αHom.app x.1) := by
          simpa [x.2] using αHom.isHomLift x.2
        have hinv : (BasedCategory.ofFunctor p₁).p.IsHomLift (𝟙 I.Y) (αInv.app x.1) := by
          simpa [x.2] using αInv.isHomLift x.2
        letI := hhom
        letI := hinv
        refine
          { hom := Functor.Fiber.homMk (BasedCategory.ofFunctor p₁).p I.Y (αHom.app x.1)
            inv := Functor.Fiber.homMk (BasedCategory.ofFunctor p₁).p I.Y (αInv.app x.1)
            hom_inv_id := by
              apply Functor.Fiber.hom_ext
              change αHom.app x.1 ≫ αInv.app x.1 = 𝟙 _
              exact NatTrans.congr_app (congrArg BasedNatTrans.toNatTrans α.hom_inv_id) x.1
            inv_hom_id := by
              apply Functor.Fiber.hom_ext
              change αInv.app x.1 ≫ αHom.app x.1 = 𝟙 _
              exact NatTrans.congr_app (congrArg BasedNatTrans.toNatTrans α.inv_hom_id) x.1 }
    let fiberCounitIso :
        ∀ (I : S.Arrow) (y : p₂.Fiber I.Y),
          (F.fiberFunctor I.Y).obj ((G.fiberFunctor I.Y).obj y) ≅ y :=
      fun I y ↦ by
        -- The same fiber restriction packages the based counit over the target cover member.
        let ε := e.counitIso
        let εHom := ε.hom
        let εInv := ε.inv
        have hhom : (BasedCategory.ofFunctor p₂).p.IsHomLift (𝟙 I.Y) (εHom.app y.1) := by
          simpa [y.2] using εHom.isHomLift y.2
        have hinv : (BasedCategory.ofFunctor p₂).p.IsHomLift (𝟙 I.Y) (εInv.app y.1) := by
          simpa [y.2] using εInv.isHomLift y.2
        letI := hhom
        letI := hinv
        refine
          { hom := Functor.Fiber.homMk (BasedCategory.ofFunctor p₂).p I.Y (εHom.app y.1)
            inv := Functor.Fiber.homMk (BasedCategory.ofFunctor p₂).p I.Y (εInv.app y.1)
            hom_inv_id := by
              apply Functor.Fiber.hom_ext
              change εHom.app y.1 ≫ εInv.app y.1 = 𝟙 _
              exact NatTrans.congr_app (congrArg BasedNatTrans.toNatTrans ε.hom_inv_id) y.1
            inv_hom_id := by
              apply Functor.Fiber.hom_ext
              change εInv.app y.1 ≫ εHom.app y.1 = 𝟙 _
              exact NatTrans.congr_app (congrArg BasedNatTrans.toNatTrans ε.inv_hom_id) y.1 }
    let unitIso :
        𝟭 ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) ≅
          TF ⋙ TG :=
      NatIso.ofComponents
        (fun D ↦
          Pseudofunctor.DescentData.isoMk
            (fun I ↦ fiberUnitIso I (D.obj I))
            (fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦ by
              -- Expose the transported overlap as a two-step comparison shell, then insert the
              -- pulled-back unit components on the two sides.
              let F₁ := ((canonicalFiberPseudofunctor p₁).map f₁.op.toLoc).toFunctor
              let F₂ := ((canonicalFiberPseudofunctor p₁).map f₂.op.toLoc).toFunctor
              let cF₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)
              let cF₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)
              let cG₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₂) (p₂ := p₁) G hG f₁
                ((F.fiberFunctor I₁.Y).obj (D.obj I₁))
              let cG₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₂) (p₂ := p₁) G hG f₂
                ((F.fiberFunctor I₂.Y).obj (D.obj I₂))
              let d := D.hom q f₁ f₂ hf₁ hf₂
              let x₁ := F₁.obj (D.obj I₁)
              let x₂ := F₂.obj (D.obj I₂)
              have hη₁_lift :
                  (BasedCategory.ofFunctor p₁).p.IsHomLift (𝟙 V)
                    (e.unitIso.hom.app x₁.1) := by
                simpa [x₁] using e.unitIso.hom.isHomLift x₁.2
              have hη₂_lift :
                  (BasedCategory.ofFunctor p₁).p.IsHomLift (𝟙 V)
                    (e.unitIso.hom.app x₂.1) := by
                simpa [x₂] using e.unitIso.hom.isHomLift x₂.2
              letI : (BasedCategory.ofFunctor p₁).p.IsHomLift (𝟙 V)
                    (e.unitIso.hom.app x₁.1) := hη₁_lift
              letI : (BasedCategory.ofFunctor p₁).p.IsHomLift (𝟙 V)
                    (e.unitIso.hom.app x₂.1) := hη₂_lift
              let η₁ : x₁ ⟶ (G.fiberFunctor V).obj ((F.fiberFunctor V).obj x₁) :=
                Functor.Fiber.homMk (BasedCategory.ofFunctor p₁).p V
                  (e.unitIso.hom.app x₁.1)
              let η₂ : x₂ ⟶ (G.fiberFunctor V).obj ((F.fiberFunctor V).obj x₂) :=
                Functor.Fiber.homMk (BasedCategory.ofFunctor p₁).p V
                  (e.unitIso.hom.app x₂.1)
              have hleft :
                  F₁.map (fiberUnitIso I₁ (D.obj I₁)).hom ≫ cG₁.hom ≫
                      (G.fiberFunctor V).map cF₁.hom = η₁ := by
                -- The left boundary is the single-arrow unit comparison for `f₁`.
                simpa [F₁, cF₁, cG₁, x₁, η₁] using
                  unit_comp_pullbackComparison_hom_boundary
                    (p₁ := p₁) (p₂ := p₂) F hF e f₁ (D.obj I₁)
                    (fiberUnitIso I₁ (D.obj I₁)).hom η₁ rfl rfl
              have hright :
                  η₂ ≫ (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv =
                    F₂.map (fiberUnitIso I₂ (D.obj I₂)).hom := by
                -- Reuse the same boundary at `f₂`, then cancel the two comparison isomorphisms.
                have hboundary :
                    F₂.map (fiberUnitIso I₂ (D.obj I₂)).hom ≫ cG₂.hom ≫
                        (G.fiberFunctor V).map cF₂.hom = η₂ := by
                  simpa [F₂, cF₂, cG₂, x₂, η₂] using
                    unit_comp_pullbackComparison_hom_boundary
                      (p₁ := p₁) (p₂ := p₂) F hF e f₂ (D.obj I₂)
                      (fiberUnitIso I₂ (D.obj I₂)).hom η₂ rfl rfl
                rw [← hboundary]
                have htail :
                    (G.fiberFunctor V).map cF₂.hom ≫
                        (G.fiberFunctor V).map cF₂.inv = 𝟙 _ := by
                  calc
                    (G.fiberFunctor V).map cF₂.hom ≫
                        (G.fiberFunctor V).map cF₂.inv =
                        (G.fiberFunctor V).map (cF₂.hom ≫ cF₂.inv) := by
                          rw [Functor.map_comp]
                    _ = (G.fiberFunctor V).map (𝟙 _) := by
                          exact congrArg (G.fiberFunctor V).map cF₂.hom_inv_id
                    _ = 𝟙 _ := by
                          rw [Functor.map_id]
                calc
                  (F₂.map (fiberUnitIso I₂ (D.obj I₂)).hom ≫ cG₂.hom ≫
                      (G.fiberFunctor V).map cF₂.hom) ≫
                      (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv =
                    F₂.map (fiberUnitIso I₂ (D.obj I₂)).hom ≫ cG₂.hom ≫
                      (G.fiberFunctor V).map cF₂.hom ≫
                      (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv := by
                      simp [Category.assoc]
                  _ = F₂.map (fiberUnitIso I₂ (D.obj I₂)).hom := by
                      exact
                        comp_hom_hom_inv_inv_cancel
                          (F₂.map (fiberUnitIso I₂ (D.obj I₂)).hom) cG₂.hom
                          ((G.fiberFunctor V).map cF₂.hom)
                          ((G.fiberFunctor V).map cF₂.inv)
                          cG₂.inv htail cG₂.hom_inv_id
              have hnat :
                  η₁ ≫ (G.fiberFunctor V).map ((F.fiberFunctor V).map d) =
                    d ≫ η₂ := by
                -- The middle equality is ordinary naturality of the based unit on the overlap
                -- morphism `d`.
                apply Functor.Fiber.hom_ext
                change e.unitIso.hom.app x₁.1 ≫ G.map (F.map d.1) =
                  d.1 ≫ e.unitIso.hom.app x₂.1
                simpa [x₁, x₂, η₁, η₂, d] using
                  (((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.naturality d.1).symm
              have hsplit :
                  (G.fiberFunctor V).map (cF₁.hom ≫ (F.fiberFunctor V).map d ≫ cF₂.inv) =
                    (G.fiberFunctor V).map cF₁.hom ≫
                      (G.fiberFunctor V).map ((F.fiberFunctor V).map d) ≫
                        (G.fiberFunctor V).map cF₂.inv := by
                exact functor_map_threefold_comp (G.fiberFunctor V) cF₁.hom
                  ((F.fiberFunctor V).map d) cF₂.inv
              -- TODO: combine `hsplit`, `hleft`, unit naturality `hnat`, and the right-tail
              -- cancellation `hright` to close the descent-data square.
              change F₁.map (fiberUnitIso I₁ (D.obj I₁)).hom ≫
                  (cG₁.hom ≫ (G.fiberFunctor V).map
                    (cF₁.hom ≫ (F.fiberFunctor V).map d ≫ cF₂.inv) ≫ cG₂.inv) =
                d ≫ F₂.map (fiberUnitIso I₂ (D.obj I₂)).hom
              calc
                F₁.map (fiberUnitIso I₁ (D.obj I₁)).hom ≫
                    (cG₁.hom ≫ (G.fiberFunctor V).map
                      (cF₁.hom ≫ (F.fiberFunctor V).map d ≫ cF₂.inv) ≫ cG₂.inv) =
                  F₁.map (fiberUnitIso I₁ (D.obj I₁)).hom ≫
                    (cG₁.hom ≫ ((G.fiberFunctor V).map cF₁.hom ≫
                      (G.fiberFunctor V).map ((F.fiberFunctor V).map d) ≫
                      (G.fiberFunctor V).map cF₂.inv) ≫ cG₂.inv) := by
                    exact congrArg (fun k ↦ F₁.map (fiberUnitIso I₁ (D.obj I₁)).hom ≫
                      (cG₁.hom ≫ k ≫ cG₂.inv)) hsplit
                _ = η₁ ≫ (G.fiberFunctor V).map ((F.fiberFunctor V).map d) ≫
                    (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv := by
                    calc
                      F₁.map (fiberUnitIso I₁ (D.obj I₁)).hom ≫
                          (cG₁.hom ≫ ((G.fiberFunctor V).map cF₁.hom ≫
                            (G.fiberFunctor V).map ((F.fiberFunctor V).map d) ≫
                            (G.fiberFunctor V).map cF₂.inv) ≫ cG₂.inv) =
                        (F₁.map (fiberUnitIso I₁ (D.obj I₁)).hom ≫ cG₁.hom ≫
                          (G.fiberFunctor V).map cF₁.hom) ≫
                          (G.fiberFunctor V).map ((F.fiberFunctor V).map d) ≫
                          (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv := by
                          simp [Category.assoc]
                      _ = η₁ ≫ (G.fiberFunctor V).map ((F.fiberFunctor V).map d) ≫
                          (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv := by
                          exact congrArg
                            (fun k ↦ k ≫ (G.fiberFunctor V).map ((F.fiberFunctor V).map d) ≫
                              (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv) hleft
                _ = d ≫ η₂ ≫ (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv := by
                    calc
                      η₁ ≫ (G.fiberFunctor V).map ((F.fiberFunctor V).map d) ≫
                          (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv =
                        (η₁ ≫ (G.fiberFunctor V).map ((F.fiberFunctor V).map d)) ≫
                          (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv := by
                          simp [Category.assoc]
                      _ = (d ≫ η₂) ≫ (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv := by
                          rw [hnat]
                      _ = d ≫ η₂ ≫ (G.fiberFunctor V).map cF₂.inv ≫ cG₂.inv := by
                          simp [Category.assoc]
                _ = d ≫ F₂.map (fiberUnitIso I₂ (D.obj I₂)).hom := by
                    simpa [Category.assoc] using congrArg (fun k ↦ d ≫ k) hright))
        (fun {X Y} φ ↦ by
          -- After component extensionality, this is ordinary naturality of the based unit on the
          -- cover-indexed component `φ.hom I`.
          apply Pseudofunctor.DescentData.hom_ext
          intro I
          rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
          simp only [Functor.comp_map]
          apply Functor.Fiber.hom_ext
          change (φ.hom I).1 ≫ e.unitIso.hom.app (Y.obj I).1 =
            e.unitIso.hom.app (X.obj I).1 ≫ G.map (F.map (φ.hom I).1)
          simpa using
            ((BasedNatTrans.forgetful _ _).mapIso e.unitIso).hom.naturality (φ.hom I).1)
    let counitIso :
        TG ⋙ TF ≅
          𝟭 ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f)) :=
      NatIso.ofComponents
        (fun D ↦
          Pseudofunctor.DescentData.isoMk
            (fun I ↦ fiberCounitIso I (D.obj I))
            (fun V q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦ by
              -- Expose the transported overlap as the `F`-image of the inverse-transport shell,
              -- then move the counit components across the two comparison boundaries.
              let F₁ := ((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor
              let F₂ := ((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor
              let cG₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₂) (p₂ := p₁) G hG f₁ (D.obj I₁)
              let cG₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₂) (p₂ := p₁) G hG f₂ (D.obj I₂)
              let cF₁ := basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₁) (p₂ := p₂) F hF f₁
                ((G.fiberFunctor I₁.Y).obj (D.obj I₁))
              let cF₂ := basedFunctor_pullbackComparison_of_equivalence_over_base
                (p₁ := p₁) (p₂ := p₂) F hF f₂
                ((G.fiberFunctor I₂.Y).obj (D.obj I₂))
              let d := D.hom q f₁ f₂ hf₁ hf₂
              let y₁ := F₁.obj (D.obj I₁)
              let y₂ := F₂.obj (D.obj I₂)
              have hε₁_lift :
                  (BasedCategory.ofFunctor p₂).p.IsHomLift (𝟙 V)
                    (e.counitIso.hom.app y₁.1) := by
                simpa [y₁] using e.counitIso.hom.isHomLift y₁.2
              have hε₂_lift :
                  (BasedCategory.ofFunctor p₂).p.IsHomLift (𝟙 V)
                    (e.counitIso.hom.app y₂.1) := by
                simpa [y₂] using e.counitIso.hom.isHomLift y₂.2
              letI : (BasedCategory.ofFunctor p₂).p.IsHomLift (𝟙 V)
                    (e.counitIso.hom.app y₁.1) := hε₁_lift
              letI : (BasedCategory.ofFunctor p₂).p.IsHomLift (𝟙 V)
                    (e.counitIso.hom.app y₂.1) := hε₂_lift
              let ε₁ : (F.fiberFunctor V).obj ((G.fiberFunctor V).obj y₁) ⟶ y₁ :=
                Functor.Fiber.homMk (BasedCategory.ofFunctor p₂).p V
                  (e.counitIso.hom.app y₁.1)
              let ε₂ : (F.fiberFunctor V).obj ((G.fiberFunctor V).obj y₂) ⟶ y₂ :=
                Functor.Fiber.homMk (BasedCategory.ofFunctor p₂).p V
                  (e.counitIso.hom.app y₂.1)
              have hleft :
                  cF₁.hom ≫ (F.fiberFunctor V).map cG₁.hom ≫ ε₁ =
                    F₁.map (fiberCounitIso I₁ (D.obj I₁)).hom := by
                -- The left boundary is the single-arrow counit comparison for `f₁`.
                simpa [F₁, cG₁, cF₁, y₁, ε₁] using
                  counit_comp_pullbackComparison_hom_boundary
                    (p₁ := p₁) (p₂ := p₂) F hF e f₁ (D.obj I₁)
                    (fiberCounitIso I₁ (D.obj I₁)).hom ε₁ rfl rfl
              have hright :
                  (F.fiberFunctor V).map cG₂.inv ≫ cF₂.inv ≫
                      F₂.map (fiberCounitIso I₂ (D.obj I₂)).hom = ε₂ := by
                -- Cancel the right boundary to express the pulled counit as the inverse tail.
                have hboundary :
                    cF₂.hom ≫ (F.fiberFunctor V).map cG₂.hom ≫ ε₂ =
                      F₂.map (fiberCounitIso I₂ (D.obj I₂)).hom := by
                  simpa [F₂, cG₂, cF₂, y₂, ε₂] using
                    counit_comp_pullbackComparison_hom_boundary
                      (p₁ := p₁) (p₂ := p₂) F hF e f₂ (D.obj I₂)
                      (fiberCounitIso I₂ (D.obj I₂)).hom ε₂ rfl rfl
                rw [← hboundary]
                have hhead :
                    (F.fiberFunctor V).map cG₂.inv ≫
                        (F.fiberFunctor V).map cG₂.hom = 𝟙 _ := by
                  calc
                    (F.fiberFunctor V).map cG₂.inv ≫
                        (F.fiberFunctor V).map cG₂.hom =
                        (F.fiberFunctor V).map (cG₂.inv ≫ cG₂.hom) := by
                          rw [Functor.map_comp]
                    _ = (F.fiberFunctor V).map (𝟙 _) := by
                          exact congrArg (F.fiberFunctor V).map cG₂.inv_hom_id
                    _ = 𝟙 _ := by
                          rw [Functor.map_id]
                simpa [Category.assoc] using
                  comp_inv_inv_hom_hom_cancel
                    ((F.fiberFunctor V).map cG₂.inv) cF₂.inv cF₂.hom
                    ((F.fiberFunctor V).map cG₂.hom) ε₂ cF₂.inv_hom_id hhead
              have hnat :
                  ε₁ ≫ d =
                    (F.fiberFunctor V).map ((G.fiberFunctor V).map d) ≫ ε₂ := by
                -- The middle equality is ordinary naturality of the based counit on the overlap
                -- morphism `d`.
                apply Functor.Fiber.hom_ext
                change e.counitIso.hom.app y₁.1 ≫ d.1 =
                  F.map (G.map d.1) ≫ e.counitIso.hom.app y₂.1
                simpa [y₁, y₂, ε₁, ε₂, d] using
                  (((BasedNatTrans.forgetful _ _).mapIso e.counitIso).hom.naturality d.1).symm
              have hsplit :
                  (F.fiberFunctor V).map (cG₁.hom ≫ (G.fiberFunctor V).map d ≫ cG₂.inv) =
                    (F.fiberFunctor V).map cG₁.hom ≫
                      (F.fiberFunctor V).map ((G.fiberFunctor V).map d) ≫
                        (F.fiberFunctor V).map cG₂.inv := by
                exact functor_map_threefold_comp (F.fiberFunctor V) cG₁.hom
                  ((G.fiberFunctor V).map d) cG₂.inv
              -- TODO: combine `hleft`, counit naturality `hnat`, `hsplit`, and `hright` after
              -- unfolding the transported inverse-cover hom.
              change F₁.map (fiberCounitIso I₁ (D.obj I₁)).hom ≫ d =
                (cF₁.hom ≫ (F.fiberFunctor V).map
                    (cG₁.hom ≫ (G.fiberFunctor V).map d ≫ cG₂.inv) ≫ cF₂.inv) ≫
                  F₂.map (fiberCounitIso I₂ (D.obj I₂)).hom
              calc
                F₁.map (fiberCounitIso I₁ (D.obj I₁)).hom ≫ d =
                    (cF₁.hom ≫ (F.fiberFunctor V).map cG₁.hom ≫ ε₁) ≫ d := by
                      exact congrArg (fun k ↦ k ≫ d) hleft.symm
                _ = cF₁.hom ≫ (F.fiberFunctor V).map cG₁.hom ≫ (ε₁ ≫ d) := by
                      simp [Category.assoc]
                _ = cF₁.hom ≫ (F.fiberFunctor V).map cG₁.hom ≫
                    ((F.fiberFunctor V).map ((G.fiberFunctor V).map d) ≫ ε₂) := by
                      exact congrArg
                        (fun k ↦ cF₁.hom ≫ (F.fiberFunctor V).map cG₁.hom ≫ k) hnat
                _ = cF₁.hom ≫ (F.fiberFunctor V).map cG₁.hom ≫
                    (F.fiberFunctor V).map ((G.fiberFunctor V).map d) ≫
                    ((F.fiberFunctor V).map cG₂.inv ≫ cF₂.inv ≫
                      F₂.map (fiberCounitIso I₂ (D.obj I₂)).hom) := by
                      exact congrArg
                        (fun k ↦ cF₁.hom ≫ (F.fiberFunctor V).map cG₁.hom ≫
                          (F.fiberFunctor V).map ((G.fiberFunctor V).map d) ≫ k) hright.symm
                _ = (cF₁.hom ≫ ((F.fiberFunctor V).map cG₁.hom ≫
                        (F.fiberFunctor V).map ((G.fiberFunctor V).map d) ≫
                        (F.fiberFunctor V).map cG₂.inv) ≫ cF₂.inv) ≫
                    F₂.map (fiberCounitIso I₂ (D.obj I₂)).hom := by
                      simp [Category.assoc]
                _ = (cF₁.hom ≫ (F.fiberFunctor V).map
                        (cG₁.hom ≫ (G.fiberFunctor V).map d ≫ cG₂.inv) ≫ cF₂.inv) ≫
                    F₂.map (fiberCounitIso I₂ (D.obj I₂)).hom := by
                      exact congrArg
                        (fun k ↦ (cF₁.hom ≫ k ≫ cF₂.inv) ≫
                          F₂.map (fiberCounitIso I₂ (D.obj I₂)).hom) hsplit.symm))
        (fun {X Y} φ ↦ by
          -- After component extensionality, this is ordinary naturality of the based counit on
          -- the cover-indexed component `φ.hom I`.
          apply Pseudofunctor.DescentData.hom_ext
          intro I
          rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
          simp only [Functor.comp_map]
          apply Functor.Fiber.hom_ext
          change F.map (G.map (φ.hom I).1) ≫ e.counitIso.hom.app (Y.obj I).1 =
            e.counitIso.hom.app (X.obj I).1 ≫ (φ.hom I).1
          simpa using
            ((BasedNatTrans.forgetful _ _).mapIso e.counitIso).hom.naturality (φ.hom I).1)
    -- The componentwise unit and counit descent-data isomorphisms exhibit `TG` as a quasi-inverse.
    exact Functor.IsEquivalence.mk' TG unitIso counitIso
  letI : TF.IsEquivalence := hTF
  let eTF :
      ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF ≅
        (F.fiberFunctor U) ⋙
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)) := by
    -- Package the already normalized canonical-descent comparison as the whiskering isomorphism
    -- required by the abstract cancellation lemma.
    simpa [TF] using
      cover_descent_data_transport_toDescentData_iso
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S
  -- Once the fixed-cover transport is packaged, the remaining argument is the general
  -- equivalence-cancellation lemma for canonical descent functors.
  exact
    coverwise_canonicalDescentFunctor_isEquivalence_iff_of_transport
      (J := J) (p₁ := p₁) (p₂ := p₂) F hF S TF eTF

/-- Source-facing consequence for Chap08 Lemma 8 4 4: if two categories over the site `(C, J)`
are equivalent over the base category `C`, then one is a stack over `(C, J)` if and only if the
other is. -/
theorem isStackOnSite_iff_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    IsStackOnSite J p₁ ↔ IsStackOnSite J p₂ := by
  constructor
  · intro h
    letI : IsStackOnSite J p₁ := h
    letI : p₂.IsFibered :=
      fibered_target_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF
    have hcover :
        ∀ (U : C) (S : J.Cover U),
          ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence :=
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p₁).1 h
    -- Reduce the target stack condition to the fixed-cover descent-data comparison.
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p₂).2
        (fun U S ↦
          (coverwise_canonicalDescentFunctor_isEquivalence_iff_of_equivalence_over_base
            J p₁ p₂ F hF S).1 (hcover U S))
  · intro h
    let e : EquivalenceOverBase F := Classical.choice hF.nonempty
    let G := e.inverse
    have hG : G.IsEquivalenceOverBase := e.inverse_isEquivalenceOverBase
    letI : IsStackOnSite J p₂ := h
    letI : p₁.IsFibered :=
      fibered_target_of_equivalence_over_base (p₁ := p₂) (p₂ := p₁) G hG
    have hcover :
        ∀ (U : C) (S : J.Cover U),
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence :=
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p₂).1 h
    -- Reuse the same fixed-cover comparison for the chosen inverse over-base equivalence.
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p₁).2
        (fun U S ↦
          (coverwise_canonicalDescentFunctor_isEquivalence_iff_of_equivalence_over_base
            J p₂ p₁ G hG S).1 (hcover U S))

end

end CategoryTheory
