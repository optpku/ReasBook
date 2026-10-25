module

public import stacks_project.Chap07.Definition_7_8_1
public import stacks_project.Chap07.Definition_7_8_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SemiRepresentableFamily
open SemiRepresentableFamily.Over

noncomputable section

universe uC vC uD vD w

section

/- Domain-style sampling for 7.20.2.1:
- primary domain: the coproduct-of-representables presentation attached to a fixed-target family
  and its pairwise overlaps, after pullback of representables along `u`;
- sampled owner declarations:
  `SemiRepresentableFamily.Over`,
  the file-local bridge `toPresheaf`,
  the file-local augmentation `augmentation`,
  `Cofork.ofπ`;
- best owner abstraction: the fixed-target family owner `SemiRepresentableFamily.Over V`, with the
  displayed cofork derived from the augmentation to the representable presheaf of `V` and the two
  canonical family morphisms from the overlap family to `𝒰`;
- primitive data: the functor `u`, the family `𝒰 : SemiRepresentableFamily.Over V`, and pairwise
  pullbacks of its members over `V`, canonically packaged as
  `𝒰.toPresieve.HasPairwisePullbacks`;
- derived API: the overlap family, the two projection morphisms to `𝒰`, the induced parallel pair
  after applying `toPresheaf` and `u.op.whiskerLeft`, and finally the standard cofork
  `Cofork.ofπ`.

Source/core/bridge triage:
- `source-facing`: the displayed canonical cofork
  `∐ u^p h_{V_i ×_V V_j} ⇉ ∐ u^p h_{V_i} ⟶ u^p h_V`;
- `core/canonical`: `SemiRepresentableFamily.Over` and `Cofork.ofπ`;
- `bridge/view`: the file-local presheaf presentation of a fixed-target family and the overlap
  family morphisms.

There is no available earlier owner module for the needed presheaf bridge in this workspace, so
this file reconstructs only the thin bridge layer needed for the displayed cofork and keeps it
private.
-/

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (u : C ⥤ D)
variable {V : D}
variable (𝒰 : SemiRepresentableFamily.Over.{w, vD, uD} V)
variable [𝒰.toPresieve.HasPairwisePullbacks]

/-- Helper for 7.20.2.1: pairwise pullbacks in the generated presieve give the pullback of any
two members of the fixed-target family. -/
private theorem hasPullback_obj_hom' (i j : 𝒰.index) :
    HasPullback (𝒰.obj i).hom (𝒰.obj j).hom := by
  -- Read the requested pullback directly from the pairwise-pullback hypothesis on `𝒰`.
  let hpair : 𝒰.toPresieve.HasPairwisePullbacks := inferInstance
  exact hpair.has_pullbacks (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j)

/-- Helper for 7.20.2.1: the chosen pullbacks are available as local instances for overlap
constructions. -/
private instance hasPullback_obj_hom (i j : 𝒰.index) :
    HasPullback (𝒰.obj i).hom (𝒰.obj j).hom :=
  hasPullback_obj_hom' 𝒰 i j

/-- Helper for 7.20.2.1: fixed-target families compose by composing the reindexing maps and the
component morphisms in the slice category. -/
private instance overCategory : Category (SemiRepresentableFamily.Over.{w, vD, uD} V) where
  Hom 𝒲 𝒵 := SemiRepresentableFamily.Over.Hom 𝒲 𝒵
  id 𝒲 :=
    { α := fun i ↦ i
      f := fun i ↦ 𝟙 (𝒲.obj i) }
  comp φ ψ :=
    { α := fun i ↦ ψ.α (φ.α i)
      f := fun i ↦ φ.f i ≫ ψ.f (φ.α i) }
  id_comp := by
    -- The identity refinement leaves both the index map and each slice morphism unchanged.
    intro 𝒲 𝒵 φ
    cases φ
    simp
  comp_id := by
    -- The same componentwise simplification shows right composition by the identity is trivial.
    intro 𝒲 𝒵 φ
    cases φ
    simp
  assoc := by
    -- Associativity is inherited pointwise from associativity in the slice category.
    intro 𝒱 𝒲 𝒳 𝒴 φ ψ χ
    cases φ
    cases ψ
    cases χ
    simp [Category.assoc]

-- Route correction: the original file imported a missing later-chapter bridge module.  This file
-- instead rebuilds only the small presheaf interface needed for the canonical cofork.

/-- Helper for 7.20.2.1: the representable presheaf of `W`, lifted to the ambient universe used by
the family coproduct presentation. -/
private def representablePresheaf (W : D) : Dᵒᵖ ⥤ Type (max vD w) where
  obj X := ULift (X.unop ⟶ W)
  map f s := ULift.up (f.unop ≫ s.down)
  map_id := by
    -- Identity restriction on a representable is identity on each underlying morphism.
    intro X
    funext s
    rcases s with ⟨t⟩
    apply ULift.ext
    simp
  map_comp := by
    -- Successive restrictions compose by associativity of morphism composition.
    intro X Y Z f g
    funext s
    rcases s with ⟨t⟩
    apply ULift.ext
    simp [Category.assoc]

/-- Helper for 7.20.2.1: the coproduct-of-representables presheaf attached to a fixed-target
family, written objectwise as a sigma type of representing arrows. -/
private def toPresheaf :
    SemiRepresentableFamily.Over.{w, vD, uD} V ⥤ Dᵒᵖ ⥤ Type (max vD w) where
  obj 𝒲 :=
    { obj := fun X ↦ ULift (Σ i : 𝒲.index, X.unop ⟶ (𝒲.obj i).left)
      map := fun f s ↦ ULift.up ⟨s.down.1, f.unop ≫ s.down.2⟩
      map_id := by
        -- Restricting along an identity morphism does nothing on either the chosen index or the
        -- corresponding section.
        intro X
        funext s
        rcases s with ⟨⟨i, t⟩⟩
        apply ULift.ext
        apply Sigma.ext <;> simp
      map_comp := by
        -- Restriction along a composite is successive restriction on the represented section.
        intro X Y Z f g
        funext s
        rcases s with ⟨⟨i, t⟩⟩
        apply ULift.ext
        apply Sigma.ext <;> simp [Category.assoc] }
  map {𝒲 𝒵} φ :=
    { app := fun X s ↦ ULift.up ⟨φ.α s.down.1, s.down.2 ≫ (φ.f s.down.1).left⟩
      naturality := by
        -- Reindexing commutes with restriction because both sides are just associativity of
        -- composition in `D`.
        intro X Y f
        funext s
        rcases s with ⟨⟨i, t⟩⟩
        apply ULift.ext
        apply Sigma.ext <;> simp [Category.assoc] }
  map_id := by
    -- On each represented section, mapping the identity family morphism leaves the summand and
    -- arrow unchanged.
    intro 𝒲
    apply NatTrans.ext
    funext X
    funext s
    rcases s with ⟨⟨i, t⟩⟩
    apply ULift.ext
    apply Sigma.ext
    · change i = i
      rfl
    · have h :
        ((𝟙 𝒲 : 𝒲 ⟶ 𝒲).f i).left =
          ((𝟙 (𝒲.obj i) : 𝒲.obj i ⟶ 𝒲.obj i).left) := by
        rfl
      simp [h]
  map_comp := by
    -- On each summand, mapping a composite family morphism is the same as composing the induced
    -- maps between represented sections.
    intro 𝒲 𝒵 𝒳 φ ψ
    apply NatTrans.ext
    funext X
    funext s
    rcases s with ⟨⟨i, t⟩⟩
    apply ULift.ext
    apply Sigma.ext
    · change ψ.α (φ.α i) = ψ.α (φ.α i)
      rfl
    · have h :
        ((φ ≫ ψ).f i).left =
          (((φ.f i) ≫ ψ.f (φ.α i) : 𝒲.obj i ⟶ 𝒳.obj (ψ.α (φ.α i))).left) := by
        rfl
      simp [h]

/-- Helper for 7.20.2.1: the canonical augmentation from the coproduct-of-representables
presentation of a fixed-target family to the representable presheaf of the target object. -/
private def augmentation (𝒲 : SemiRepresentableFamily.Over.{w, vD, uD} V) :
    toPresheaf.obj 𝒲 ⟶ representablePresheaf V where
  app X s := ULift.up (s.down.2 ≫ (𝒲.obj s.down.1).hom)
  naturality := by
    -- Restricting a local section and then augmenting is the same as first augmenting and then
    -- restricting the resulting section of `h_V`.
    intro X Y f
    funext s
    rcases s with ⟨⟨i, t⟩⟩
    apply ULift.ext
    change (f.unop ≫ t) ≫ (𝒲.obj i).hom = f.unop ≫ (t ≫ (𝒲.obj i).hom)
    simp [Category.assoc]

/-- Helper for 7.20.2.1: the overlap family indexed by ordered pairs of members of `𝒰`, with each
component represented by the chosen pullback over `V`. -/
private def overlapFamily :
    SemiRepresentableFamily.Over.{w, vD, uD} V :=
  ofArrows
    (fun ij : 𝒰.index × 𝒰.index ↦ pullback (𝒰.obj ij.1).hom (𝒰.obj ij.2).hom)
    (fun ij ↦ pullback.fst (𝒰.obj ij.1).hom (𝒰.obj ij.2).hom ≫ (𝒰.obj ij.1).hom)

/-- Helper for 7.20.2.1: the first pullback projection is a morphism in the slice over `V` from an
overlap object to the first component family member. -/
private theorem pullback_fst_over_w (i j : 𝒰.index) :
    pullback.fst (𝒰.obj i).hom (𝒰.obj j).hom ≫ (𝒰.obj i).hom =
      ((overlapFamily 𝒰).obj (i, j)).hom := by
  -- This is the defining triangle for the overlap family.
  rfl

/-- Helper for 7.20.2.1: the second pullback projection is a morphism in the slice over `V` from
an overlap object to the second component family member. -/
private theorem pullback_snd_over_w (i j : 𝒰.index) :
    pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom ≫ (𝒰.obj j).hom =
      ((overlapFamily 𝒰).obj (i, j)).hom := by
  -- The pullback square identifies the second projection with the same map to `V`.
  simpa [overlapFamily] using
    (pullback.condition :
      pullback.fst (𝒰.obj i).hom (𝒰.obj j).hom ≫ (𝒰.obj i).hom =
        pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom ≫ (𝒰.obj j).hom).symm

/-- Helper for 7.20.2.1: the first projection from the overlap family to the original family as a
morphism of fixed-target families. -/
private def overlapFstHom :
    overlapFamily 𝒰 ⟶ 𝒰 where
  α := Prod.fst
  f := fun ij ↦
    Over.homMk
      (pullback.fst (𝒰.obj ij.1).hom (𝒰.obj ij.2).hom)
      (pullback_fst_over_w 𝒰 ij.1 ij.2)

/-- Helper for 7.20.2.1: the second projection from the overlap family to the original family as a
morphism of fixed-target families. -/
private def overlapSndHom :
    overlapFamily 𝒰 ⟶ 𝒰 where
  α := Prod.snd
  f := fun ij ↦
    Over.homMk
      (pullback.snd (𝒰.obj ij.1).hom (𝒰.obj ij.2).hom)
      (pullback_snd_over_w 𝒰 ij.1 ij.2)

-- Proof sketch: evaluate both composites on a represented section of an overlap object.  The two
-- resulting sections of `h_V` differ only by the pullback commutativity relation.
/-- Helper for 7.20.2.1: the two overlap projection maps induce a parallel pair over the
augmentation to the representable presheaf of `V`. -/
private theorem representableParallelPair :
    u.op.whiskerLeft (toPresheaf.map (overlapFstHom 𝒰)) ≫
        u.op.whiskerLeft (augmentation 𝒰) =
      u.op.whiskerLeft (toPresheaf.map (overlapSndHom 𝒰)) ≫
        u.op.whiskerLeft (augmentation 𝒰) := by
  -- Evaluate at an object of `C` and a chosen section of one overlap summand.
  apply NatTrans.ext
  funext X
  funext s
  rcases s with ⟨⟨ij, t⟩⟩
  apply ULift.ext
  -- Both composites are postcomposition of `t` with the two maps out of the pullback square.
  simpa [augmentation, toPresheaf, overlapFstHom, overlapSndHom, Category.assoc] using
    congrArg (fun k ↦ t ≫ k)
      (pullback.condition :
        pullback.fst (𝒰.obj ij.1).hom (𝒰.obj ij.2).hom ≫ (𝒰.obj ij.1).hom =
          pullback.snd (𝒰.obj ij.1).hom (𝒰.obj ij.2).hom ≫ (𝒰.obj ij.2).hom)

/- 7.20.2.1: for a fixed family `𝒰` over `V` with pairwise pullbacks, the canonical cofork in
presheaves
`∐ u^p h_{V_i ×_V V_j} ⇉ ∐ u^p h_{V_i} ⟶ u^p h_V`
is the standard `Cofork.ofπ` built from the overlap family of `𝒰`, the two overlap projection
maps, and the augmentation to the representable presheaf of `V`. -/
#check
  (Cofork.ofπ
      (u.op.whiskerLeft (augmentation 𝒰))
      (representableParallelPair u 𝒰) :
    Cofork
      (u.op.whiskerLeft (toPresheaf.map (overlapFstHom 𝒰)))
      (u.op.whiskerLeft (toPresheaf.map (overlapSndHom 𝒰))))

end
