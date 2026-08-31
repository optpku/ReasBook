module

public import stacks_project.Internal.Chap04.FibredInGroupoidsTwoFibreProductSquare
public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap04.Lemma_4_32_5
public import stacks_project.Chap04.Lemma_4_33_10
public import stacks_project.Chap04.Lemma_4_35_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 4.35.7:
- primary domain: categories fibred in groupoids over a fixed base and their `2`-fibre products;
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `FibredInGroupoidsOver`,
  `FibredInGroupoidsMor`,
  `FibredCategoryOver.twoFibreProduct`,
  `FibredCategoryOver.twoFibreProductSquare`,
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `FibredCategoryOver.twoFibreProductLeftProjection`,
  `FibredCategoryOver.twoFibreProductRightProjection`,
  `explicitTwoFibreProduct`;
- best owner abstraction: the source-facing statement for this item should live at the owner level
  `FibredInGroupoidsOver C`, with the canonical square and its `Bicategory.IsFinal` universal
  property obtained by restricting the ambient owner
  `FibredCategoryOver.twoFibreProductSquare`; the explicit pullback projection in `Cat/C` is the
  companion closure theorem feeding that owner-level statement.

Primitive-vs-derived split:
- primitive source-facing data: the based functors `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S` over `C`,
  with fibred-in-groupoids hypotheses on the source projections and fibredness of the target
  projection;
- derived API: the bundled owner-level rebundling
  `FibredInGroupoidsOver.twoFibreProduct`, its two projections, the canonical square
  `FibredInGroupoidsOver.twoFibreProductSquare`, and the resulting
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`, all obtained by restricting the
  ambient owner `FibredCategoryOver.twoFibreProductSquare` to the full sub-`2`-category
  `FibredInGroupoidsOver C`.

Source/core/bridge triage:
- `source-facing`: `FibredInGroupoidsOver.twoFibreProductSquare` and
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `IsFibredInGroupoids` on the explicit pullback projection in `Cat/C`;
- `bridge/view`: `explicitTwoFibreProductProjection_isFibredInGroupoids` and the owner-level
  rebundling `FibredInGroupoidsOver.twoFibreProduct`. -/

section Raw

variable {X Y S : BasedCategory.{v, max u v} C}

/-- Helper for Lemma 4.35.7: the categorical pullback of two groupoids is again a groupoid. -/
private theorem categorical_pullback_isGroupoid
    {A B T : Type*} [Category A] [Category B] [Category T]
    (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid A] [IsGroupoid B] :
    IsGroupoid (Limits.CategoricalPullback L R) where
  all_isIso := fun f ↦
    (Limits.CategoricalPullback.isIso_iff (F := L) (G := R) f).2
      ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 4.35.7: each fiber of the explicit `2`-fibre product is equivalent to the
categorical pullback of the source fibers, hence is a groupoid. -/
private theorem explicit_two_fibre_product_fiber_isGroupoid
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]
    (U : C) :
    IsGroupoid ((explicitTwoFibreProduct F G).p.Fiber U) := by
  -- Transport the fiber across the canonical equivalence from Lemma 4.32.5.
  let e := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F G U
  -- The pullback model is a groupoid because both source fibers are groupoids.
  letI : IsGroupoid (Limits.CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :=
    categorical_pullback_isGroupoid (F.fiberFunctor U) (G.fiberFunctor U)
  exact isGroupoid_of_reflects_iso e.functor

-- Proof sketch: apply Lemma `4.33.10` to the same explicit `2`-fibre-product model from
-- Lemma `4.32.3` using only that the target projection is fibred, then use Lemma `4.35.2` to
-- reduce the remaining work to checking that every fiber is a groupoid.
/-- Lemma 4.35.7 (1): if `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S` are based functors over `C` whose source
categories are fibred in groupoids and whose target category is fibred in groupoids over `C`, then
the
explicit `2`-fibre-product projection from Lemma 4.32.3 is again fibred in groupoids over `C`. -/
theorem explicitTwoFibreProductProjection_isFibredInGroupoids
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids S.p] :
    IsFibredInGroupoids (explicitTwoFibreProduct F G).p := by
  -- Rebundle `F` and `G` as morphisms of fibred categories over `C`.
  let Ff : FibredCategoryOver.ofFunctor X.p ⟶ FibredCategoryOver.ofFunctor S.p :=
    FibredCategoryMor.ofBasedFunctor
      (show (FibredCategoryOver.ofFunctor X.p).toBasedCategory ⥤ᵇ
          (FibredCategoryOver.ofFunctor S.p).toBasedCategory from F)
      (by
        intro a b φ hφ
        exact (inferInstance : IsFibredInGroupoids S.p).isStronglyCartesian_map (F.map φ))
  let Gf : FibredCategoryOver.ofFunctor Y.p ⟶ FibredCategoryOver.ofFunctor S.p :=
    FibredCategoryMor.ofBasedFunctor
      (show (FibredCategoryOver.ofFunctor Y.p).toBasedCategory ⥤ᵇ
          (FibredCategoryOver.ofFunctor S.p).toBasedCategory from G)
      (by
        intro a b φ hφ
        exact (inferInstance : IsFibredInGroupoids S.p).isStronglyCartesian_map (G.map φ))
  -- Lemma 4.33.10 supplies the ambient fibredness of the explicit pullback projection.
  have hp : (explicitTwoFibreProduct F G).p.IsFibered := by
    change (FibredCategoryOver.twoFibreProduct Ff Gf).p.IsFibered
    exact FibredCategoryOver.isFibred (X := FibredCategoryOver.twoFibreProduct Ff Gf)
  -- Lemma 4.35.2 then reduces the remaining work to the fiberwise groupoid statement proved above.
  exact
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (explicitTwoFibreProduct F G).p hp
      (explicit_two_fibre_product_fiber_isGroupoid F G)

instance (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids S.p] :
    IsFibredInGroupoids (explicitTwoFibreProduct F G).p :=
  explicitTwoFibreProductProjection_isFibredInGroupoids F G

end Raw

namespace FibredInGroupoidsOver

variable {X Y S : FibredInGroupoidsOver C}

open FibredInGroupoidsMor

/-- Helper for Lemma 4.35.7: forget a square in `FibredInGroupoidsOver C` to the ambient square
in `FibredCategoryOver C`. -/
private noncomputable abbrev toFibredCategorySquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare F.toHom G.toHom where
  obj := P.obj.toFibredCategoryOver
  p := P.p.toHom
  q := P.q.toHom
  ψ :=
    Functor.mapIso (((fibredInGroupoidsOverSubTwoCategory C).hom P.obj S).inclusion) P.ψ

theorem ambientTwoFibreProduct_isFibredInGroupoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p := by
  change IsFibredInGroupoids
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p
  exact explicitTwoFibreProductProjection_isFibredInGroupoids (toBasedFunctor F) (toBasedFunctor G)

/-- The canonical fibred `2`-fibre product of morphisms of categories fibred in groupoids over
`C`, obtained by restricting the chapter-level owner `FibredCategoryOver.twoFibreProduct` to the
full sub-`2`-category `FibredInGroupoidsOver C`. -/
noncomputable def twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    FibredInGroupoidsOver C :=
  ⟨FibredCategoryOver.twoFibreProduct F.toHom G.toHom,
    ambientTwoFibreProduct_isFibredInGroupoids F G⟩

/-- The left projection from the canonical fibred `2`-fibre product of categories fibred in
groupoids over `C`.  Kept as a (semireducible) `def`, not an `abbrev`: as a reducible abbrev it is
eagerly unfolded during `isDefEq`, exposing the heavy explicit-pullback projection and causing
whnf-heartbeat overflows when matched (e.g. in `Lemma_4_42_6`). -/
noncomputable def twoFibreProductLeftProjection
    (F : X ⟶ S) (G : Y ⟶ S) :
    twoFibreProduct F G ⟶ X :=
  by
    unfold twoFibreProduct
    exact ofAmbientHom (FibredCategoryOver.twoFibreProductLeftProjection F.toHom G.toHom)

/-- The right projection from the canonical fibred `2`-fibre product of categories fibred in
groupoids over `C`.  Kept as a (semireducible) `def` for the same reason as
`twoFibreProductLeftProjection`. -/
noncomputable def twoFibreProductRightProjection
    (F : X ⟶ S) (G : Y ⟶ S) :
    twoFibreProduct F G ⟶ Y :=
  by
    unfold twoFibreProduct
    exact ofAmbientHom (FibredCategoryOver.twoFibreProductRightProjection F.toHom G.toHom)

/- The canonical `2`-commutative square in `FibredInGroupoidsOver C` for the two-fibre-product
construction above. -/
noncomputable def twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  { obj := twoFibreProduct F G
    p := twoFibreProductLeftProjection F G
    q := twoFibreProductRightProjection F G
    ψ := by
      unfold twoFibreProduct
      exact (mkTwoFibreProductSquare F G
        (ambientTwoFibreProduct_isFibredInGroupoids F G)).ψ }

/-- Helper for Lemma 4.35.7: forget a morphism into the fibred-in-groupoids pullback square to the
ambient morphism into the fibred-category pullback square. -/
private noncomputable abbrev toAmbientSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ mkTwoFibreProductSquare F G hP) :
    toFibredCategorySquare P ⟶ FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom where
  hom := u.hom.toHom
  left := u.left.hom.hom
  right := u.right.hom.hom
  comm := by
    -- Forget the owner square equation to the underlying ambient `2`-cells.
    exact congrArg (fun α ↦ α.hom.hom) u.comm

/-- Helper for Lemma 4.35.7: rewrap an ambient morphism into the fibred-category pullback square
as a morphism into the fibred-in-groupoids pullback square. -/
private noncomputable abbrev ofAmbientSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : toFibredCategorySquare P ⟶ FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom) :
    P ⟶ mkTwoFibreProductSquare F G hP := by
  rcases u with ⟨hom, left, right, comm⟩
  refine
    { hom := ofAmbientHom hom
      left := ⟨ObjectProperty.homMk left, trivial⟩
      right := ⟨ObjectProperty.homMk right, trivial⟩
      comm := ?_ }
  -- Rebuild the owner square equation from the ambient equation by extensionality of the two
  -- wrapper layers on `2`-morphisms.
  unfold_projs
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact comm

/-- Helper for Lemma 4.35.7: forget a `2`-morphism between owner square morphisms to the ambient
`2`-morphism between their forgotten ambient square morphisms. -/
private noncomputable abbrev toAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ mkTwoFibreProductSquare F G hP}
    (η : u ⟶ v) :
    toAmbientSquareHom hP u ⟶ toAmbientSquareHom hP v where
  hom := η.hom.hom.hom
  left_comm := by
    -- Forgeting the owner `2`-cell equality gives the ambient left compatibility.
    exact congrArg (fun α ↦ α.hom.hom) η.left_comm
  right_comm := by
    -- Forgeting the owner `2`-cell equality gives the ambient right compatibility.
    exact congrArg (fun α ↦ α.hom.hom) η.right_comm

/-- Helper for Lemma 4.35.7: rewrap an ambient `2`-morphism between ambient square morphisms as
an owner `2`-morphism between their rewrapped owner square morphisms. -/
private noncomputable abbrev ofAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : toFibredCategorySquare P ⟶ FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom}
    (η : u ⟶ v) :
    ofAmbientSquareHom hP u ⟶ ofAmbientSquareHom hP v := by
  refine
    { hom := ⟨ObjectProperty.homMk η.hom, trivial⟩
      left_comm := ?_
      right_comm := ?_ }
  · -- Rebuild the left compatibility through the two wrapper layers on owner `2`-morphisms.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.left_comm
  · -- Rebuild the right compatibility through the two wrapper layers on owner `2`-morphisms.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.right_comm

/-- Helper for Lemma 4.35.7: rewrapping after forgetting a square `2`-morphism is definitionally
the original owner `2`-morphism. -/
private theorem of_toAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ mkTwoFibreProductSquare F G hP}
    (η : u ⟶ v) :
    ofAmbientSquareTwoHom hP (toAmbientSquareTwoHom hP η) = η := by
  rfl

/-- Helper for Lemma 4.35.7: for any competing square, the hom-category into the owner
fibred-in-groupoids pullback square has a terminal object obtained by transporting the ambient
terminal object from the fibred-category pullback square. -/
private theorem square_hasTerminal
    {F : X ⟶ S} {G : Y ⟶ S}
    (hP : IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p)
    (P : BicategoricalTwoCommutativeSquare F G) :
    Limits.HasTerminal (P ⟶ mkTwoFibreProductSquare F G hP) := by
  let Q := toFibredCategorySquare P
  let T := FibredCategoryOver.twoFibreProductSquare F.toHom G.toHom
  letI : Bicategory.IsFinal T := FibredCategoryOver.twoFibreProduct_isTwoFibreProduct F.toHom G.toHom
  let targetAmbient : Q ⟶ T := ⊤_ (Q ⟶ T)
  let targetOwner : P ⟶ mkTwoFibreProductSquare F G hP := ofAmbientSquareHom hP targetAmbient
  let htarget : Limits.IsTerminal targetAmbient := Limits.terminalIsTerminal
  -- Transport the ambient terminal object and its uniqueness through the owner/ambient square-hom
  -- conversions established above.
  exact
    (Limits.IsTerminal.ofUniqueHom (Y := targetOwner)
      (fun u ↦ ofAmbientSquareTwoHom hP (Limits.terminal.from (toAmbientSquareHom hP u)))
      (fun u η ↦ by
        have hηambient :
            toAmbientSquareTwoHom hP η = Limits.terminal.from (toAmbientSquareHom hP u) :=
          htarget.hom_ext _ _
        have hηowner :
            ofAmbientSquareTwoHom hP (toAmbientSquareTwoHom hP η) =
              ofAmbientSquareTwoHom hP (Limits.terminal.from (toAmbientSquareHom hP u)) :=
          congrArg (ofAmbientSquareTwoHom hP) hηambient
        exact (of_toAmbientSquareTwoHom hP η).symm.trans hηowner)).hasTerminal

-- Proof sketch: use the ambient `FibredCategoryOver.twoFibreProductSquare` and restrict its
-- universal property along the full sub-`2`-category `FibredInGroupoidsOver C`.
/-- Lemma 4.35.7 (2): the canonical square `twoFibreProductSquare F G` is a bicategorical
`2`-fibre product in the `2`-category of categories fibred in groupoids over `C`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  -- Route correction: instead of a looping `simpa`, transport the ambient terminal objects in the
  -- square-hom categories through the explicit owner/ambient square-hom conversions above.
  refine ⟨fun P ↦ ?_⟩
  unfold twoFibreProductSquare
  unfold twoFibreProductLeftProjection
  unfold twoFibreProductRightProjection
  unfold twoFibreProduct
  exact square_hasTerminal (ambientTwoFibreProduct_isFibredInGroupoids F G) P

end FibredInGroupoidsOver

end CategoryTheory
