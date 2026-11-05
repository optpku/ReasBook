module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}} (U : Opens X) (𝒪 : TopCat.Sheaf RingCat.{u} X)

/-- Restriction and extension by zero for module-valued sheaves: for an open subset `U ⊆ X`, the
restriction functor on sheaves of `𝒪`-modules to `U` is the inverse-image functor along the open
inclusion `j : U ↪ X`, modeled by the pullback of module sheaves along the unit
`𝒪 ⟶ j_* j^{-1} 𝒪`. -/
noncomputable abbrev moduleSheafRestrictionToOpen :
    SheafOfModules 𝒪 ⥤
      SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪) :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪)

/-- Helper for Restriction and extension by zero for module-valued sheaves: the restriction owner
is the pullback side of the canonical pullback/pushforward adjunction for the open inclusion
`U ↪ X`. -/
noncomputable def moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction :
    moduleSheafRestrictionToOpen U 𝒪 ⊣
      SheafOfModules.pushforward
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪) := by
  -- The restriction functor is defined as the module pullback along the unit of the sheaf
  -- pullback/pushforward adjunction, so the generic module adjunction applies directly.
  simpa [moduleSheafRestrictionToOpen] using
    (SheafOfModules.pullbackPushforwardAdjunction
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪))

-- Proof sketch: besides the extension-by-zero adjunction sought below, restriction already comes
-- with its canonical left-adjoint structure from the pullback/direct-image formalism.
/-- The module-valued restriction owner is also a left adjoint to the direct-image functor attached
to the open inclusion. -/
instance moduleSheafRestrictionToOpen_isLeftAdjoint :
    (moduleSheafRestrictionToOpen U 𝒪).IsLeftAdjoint := by
  -- This is the left-adjoint half of the canonical pullback/pushforward adjunction above.
  exact (moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction U 𝒪).isLeftAdjoint

/-- Helper for Restriction and extension by zero for module-valued sheaves: the open-embedding
module pushforward owner obtained from the canonical comparison
`TopCat.Sheaf.pullback ⟶ sheafPullback` is a right adjoint. -/
lemma open_embedding_module_pushforward_isRightAdjoint :
    letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
    (SheafOfModules.pushforward.{u} (F := U.isOpenEmbedding.functor)
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom)).IsRightAdjoint := by
  -- The open-embedding owner is itself a module pushforward, so its right-adjoint structure comes
  -- from the generic pullback/pushforward adjunction for sheaves of modules.
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  exact (SheafOfModules.pullbackPushforwardAdjunction.{u}
    (F := U.isOpenEmbedding.functor)
    (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom)).isRightAdjoint

/-- Helper for Restriction and extension by zero for module-valued sheaves: the inverse component
of `TopCat.Sheaf.pullbackIso` carries the sheafified presheaf pullback-unit section back to the
genuine sheaf pullback-unit section. -/
private theorem pullbackIso_inv_toSheafify_unit_section_eq
    {Y T : TopCat.{u}} (f : Y ⟶ T) (𝒢 : T.Sheaf RingCat.{u}) (V : Opens T)
    (s : 𝒢.1.obj (Opposite.op V)) :
    (((TopCat.Sheaf.pullbackIso RingCat.{u} f).inv.app 𝒢).1.app
        (Opposite.op ((Opens.map f).obj V)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget RingCat.{u} T ⋙ TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢)).app
          (Opposite.op ((Opens.map f).obj V)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
            (Opposite.op V)) s)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
          (Opposite.op V)) s) := by
  -- Compare the abstract sheaf pullback unit with the left-Kan/sheafification model.
  have h :=
    CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f)
      (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) RingCat.{u} (Opens.grothendieckTopology T) (Opens.grothendieckTopology Y))
      𝒢
  have happ :=
    congrArg (fun k ↦ (k.1.app (Opposite.op V)) s) h
  have happ' :
      (((TopCat.Sheaf.pullbackIso RingCat.{u} f).hom.app 𝒢).1.app
          (Opposite.op ((Opens.map f).obj V)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
            (Opposite.op V)) s) =
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget RingCat.{u} T ⋙ TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢)).app
          (Opposite.op ((Opens.map f).obj V)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
            (Opposite.op V)) s)) := by
    -- Evaluating the unit comparison at `V` yields the sectionwise identity.
    simpa using happ
  -- Apply the inverse pullback comparison to recover the abstract unit section.
  rw [← happ']
  simpa using
    congrArg
      (fun k ↦ (k.hom.app (Opposite.op ((Opens.map f).obj V)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
            (Opposite.op V)) s))
      (Iso.hom_inv_id_app (TopCat.Sheaf.pullbackIso RingCat.{u} f) 𝒢)

/-- Helper for Restriction and extension by zero for module-valued sheaves: on presheaf sections,
the open-map pullback comparison sends the presheaf pullback adjunction unit to restriction along
the opens-adjunction counit. -/
private abbrev open_embedding_presheaf_unit_app
    (W : Opens X) :
    𝒪.obj.obj (Opposite.op W) ⟶
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).obj
        (Opposite.op ((Opens.map U.inclusion').obj W)) :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪.obj).app
    (Opposite.op W)

/-- Helper for Restriction and extension by zero for module-valued sheaves: the presheaf pullback
adjunction unit evaluated on the image open `U ∩ W`. -/
private abbrev open_embedding_presheaf_unit_functor_app
    (V : Opens ((Opens.toTopCat X).obj U)) :
    (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V) ⟶
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).obj
        (Opposite.op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V))) :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪.obj).app
    (Opposite.op (U.isOpenEmbedding.functor.obj V))

/-- Helper for Restriction and extension by zero for module-valued sheaves: on presheaf sections,
the open-map pullback comparison sends the presheaf pullback adjunction unit to restriction along
the opens-adjunction counit. -/
private theorem open_embedding_presheaf_counit_app
    (W : Opens X) (s : 𝒪.obj.obj (Opposite.op W)) :
    ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
        (Opposite.op ((Opens.map U.inclusion').obj W)))
      ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) W) s) =
      (𝒪.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op) s := by
  let W' : Opens ((Opens.toTopCat X).obj U) := (Opens.map U.inclusion').obj W
  let Wimage : Opens X := ⟨_, U.isOpenEmbedding.isOpenMap _ W'.2⟩
  let x : CostructuredArrow (Opens.map U.inclusion').op (Opposite.op W') :=
    CostructuredArrow.mk (@homOfLE _ _ _ ((Opens.map U.inclusion').obj Wimage)
      (Set.image_preimage.le_u_l _)).op
  have hx : Limits.IsTerminal x := by
    -- The image-open object is terminal in the costructured-arrow fiber over `W ∩ U`.
    refine
      { lift := fun s ↦ by
          fapply CostructuredArrow.homMk
          · change Opposite.op (Opposite.unop s.pt.left) ⟶ Opposite.op Wimage
            refine (homOfLE ?_).op
            apply (Set.image_mono s.pt.hom.unop.le).trans
            exact Set.image_preimage.l_u_le (SetLike.coe s.pt.left.unop)
          · simp [eq_iff_true_of_subsingleton] }
  -- Evaluate the pointwise left-Kan cocone at the identity object, then transport to the
  -- terminal cocone that defines `pullbackObjObjOfImageOpen`.
  dsimp [W', Wimage, x, open_embedding_presheaf_unit_app, IsOpenMap.pullbackObjIso,
    TopCat.Presheaf.pullbackObjObjOfImageOpen]
  have h := Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    ((Opens.map U.inclusion').op.isPointwiseLeftKanExtensionLeftKanExtensionUnit 𝒪.obj
      (Opposite.op ((Opens.map U.inclusion').obj W)))
    (Limits.colimitOfDiagramTerminal hx
      (CostructuredArrow.proj (Opens.map U.inclusion').op
        (Opposite.op ((Opens.map U.inclusion').obj W)) ⋙ 𝒪.obj))
    (CostructuredArrow.mk (𝟙 (Opposite.op ((Opens.map U.inclusion').obj W))))
  rw [Limits.coconeOfDiagramTerminal_ι_app] at h
  simpa using congrArg (fun f ↦ RingCat.Hom.hom f s) h

/-- Helper for Restriction and extension by zero for module-valued sheaves: on presheaf sections,
the inverse open-map pullback comparison followed by restriction along the opens-adjunction unit is
the identity. -/
private theorem open_embedding_pullbackObjIso_hom_unit_app
    (V : Opens ((Opens.toTopCat X).obj U))
    (s : ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V))) :
    ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app (Opposite.op V))
      ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
        ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) =
      ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
        (((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
            (Opposite.op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V))))
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) := by
  -- Naturality of `pullbackObjIso.hom` moves the restriction map from the pullback side to the
  -- explicit open-embedding pullback side.
  let α := (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj)
  have hnat := α.hom.naturality (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op
  have happ := congrArg
    (fun k ↦ k ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) hnat
  simpa [Function.comp_apply] using happ

/-- Helper for Restriction and extension by zero for module-valued sheaves: on presheaf sections,
the inverse open-map pullback comparison followed by restriction along the opens-adjunction unit is
the identity. -/
private theorem open_embedding_presheaf_triangle_app
    (V : Opens ((Opens.toTopCat X).obj U))
    (s : (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V)) :
    (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
        (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
      ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s) =
      (((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).inv.app (Opposite.op V)) s) := by
  -- Apply the inverse pullback comparison after proving that the forward comparison sends the
  -- left-hand side to the original section `s`.
  let α := (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj)
  have hhom :
      ((α.hom.app (Opposite.op V))
          ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
            ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s))) = s := by
    -- Move the restriction map to the explicit open-embedding side, then use the counit formula
    -- on `U.isOpenEmbedding.functor.obj V`.
    have hmove :
        ((α.hom.app (Opposite.op V))
            ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
                (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
              ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)))
          =
        ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          (((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
              (Opposite.op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V))))
            ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) := by
      simpa using open_embedding_pullbackObjIso_hom_unit_app (U := U) (𝒪 := 𝒪) V s
    rw [hmove]
    -- First rewrite the inner comparison with the explicit counit formula.
    have hcounit :
        ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          (((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
              (Opposite.op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V))))
            ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) =
        ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          ((𝒪.obj.map
              (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
                (U.isOpenEmbedding.functor.obj V)).op) s) := by
      exact congrArg
        (fun t ↦
          ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op) t)
        (open_embedding_presheaf_counit_app (U := U) (𝒪 := 𝒪)
          (U.isOpenEmbedding.functor.obj V) s)
    rw [hcounit]
    -- The open-subset adjunction triangle identifies the resulting composite restriction with
    -- the identity on the section over `V`.
    change
      ((𝒪.obj.map
          (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
            (U.isOpenEmbedding.functor.obj V)).op) ≫
        (𝒪.obj.map
          ((U.isOpenEmbedding.functor.map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V)).op))) s = s
    rw [← Functor.map_comp]
    have htriangle := U.isOpenEmbedding.isOpenMap.adjunction.left_triangle_components V
    simpa [CategoryTheory.comp_apply] using congrArg (fun k ↦ (𝒪.obj.map k.op) s) htriangle
  have hinv := congrArg (fun t ↦ (α.inv.app (Opposite.op V)) t) hhom
  -- Cancel the forward comparison using the `pullbackObjIso` inverse at `V`.
  have hleft :
      (α.inv.app (Opposite.op V))
        ((α.hom.app (Opposite.op V))
          ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
            ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s))) =
        (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s) := by
    simpa using
      congrArg
        (fun k ↦ k
          ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
            ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)))
        (Iso.hom_inv_id_app α (Opposite.op V))
  calc
    (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
        (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
      ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)
        =
      (α.inv.app (Opposite.op V))
        ((α.hom.app (Opposite.op V))
          ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
            ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s))) := by
              symm
              exact hleft
    _ = (α.inv.app (Opposite.op V)) s := hinv
    _ = (((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).inv.app (Opposite.op V)) s) := rfl

/-- Helper for Restriction and extension by zero for module-valued sheaves: after rewriting the
sheaf pullback unit section through `TopCat.Sheaf.pullbackIso`, the remaining `sheafPullbackIso`
component evaluates to the open-map pullback comparison on the presheaf unit section. -/
private theorem open_embedding_pullbackIso_inv_hom_section_cancel
    (W : Opens ((Opens.toTopCat X).obj U))
    (t : (((CategoryTheory.sheafify
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      ((TopCat.Sheaf.forget RingCat.{u} X ⋙
        TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪))).obj
      (Opposite.op W))) :
    (RingCat.Hom.hom
        (((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').hom.app 𝒪).1.app
          (Opposite.op W)))
      ((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
          (Opposite.op W)) t) = t := by
  -- Evaluate `inv ≫ hom = 𝟙` on the chosen section to cancel the abstract pullback comparison.
  simpa using
    congrArg
      (fun k ↦ (k.hom.app (Opposite.op W)) t)
      (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion') 𝒪)

/-- Helper for Restriction and extension by zero for module-valued sheaves: after rewriting the
sheaf pullback unit section through `TopCat.Sheaf.pullbackIso`, the remaining `sheafPullbackIso`
component evaluates to the open-map pullback comparison on the presheaf unit section. -/
private theorem open_embedding_sheaf_pullback_tail_on_toSheafify_section
    (W : Opens ((Opens.toTopCat X).obj U))
    (t : ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).obj (Opposite.op W)) :
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op W)))
      (((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
          (Opposite.op W))
        (((CategoryTheory.toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            ((TopCat.Sheaf.forget RingCat.{u} X ⋙
              TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪)).app
            (Opposite.op W))
          t))) =
      ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app (Opposite.op W)) t := by
  let J := Opens.grothendieckTopology ((Opens.toTopCat X).obj U)
  let P :
      (Opens ((Opens.toTopCat X).obj U))ᵒᵖ ⥤ RingCat.{u} :=
    ((TopCat.Sheaf.forget RingCat.{u} X ⋙
      TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪)
  let hP : CategoryTheory.Presheaf.IsSheaf J (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj) :=
    TopCat.Presheaf.isSheaf_of_isOpenEmbedding U.isOpenEmbedding 𝒪.2
  have hcancel :
      (RingCat.Hom.hom
          (((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').hom.app 𝒪).hom.app
            (Opposite.op W)))
        (((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
            (Opposite.op W))
          (((CategoryTheory.toSheafify J P).app (Opposite.op W)) t))) =
      (((CategoryTheory.toSheafify J P).app (Opposite.op W)) t) := by
    -- Cancel the front `TopCat.Sheaf.pullbackIso` before normalizing the remaining tail.
    simpa [J, P] using
      open_embedding_pullbackIso_inv_hom_section_cancel
        (U := U) (𝒪 := 𝒪) (W := W) (t := (((CategoryTheory.toSheafify J P).app
          (Opposite.op W)) t))
  have htail :=
    congrArg
      (fun z ↦
        (RingCat.Hom.hom
          ((((CategoryTheory.presheafToSheaf J RingCat.{u}).map
                (U.isOpenEmbedding.isOpenMap.pullbackIso.hom.app 𝒪.obj)) ≫
              ObjectProperty.homMk
                (X := (CategoryTheory.presheafToSheaf J RingCat.{u}).obj
                  (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj))
                (Y := ⟨U.isOpenEmbedding.functor.op ⋙ 𝒪.obj, hP⟩)
                (CategoryTheory.sheafifyLift J (𝟙 (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj)) hP)).hom.app
            (Opposite.op W)))
          z)
      hcancel
  let m :=
    ((((CategoryTheory.presheafToSheaf J RingCat.{u}).map
          (U.isOpenEmbedding.isOpenMap.pullbackIso.hom.app 𝒪.obj)) ≫
        ObjectProperty.homMk
          (X := (CategoryTheory.presheafToSheaf J RingCat.{u}).obj
            (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj))
          (Y := ⟨U.isOpenEmbedding.functor.op ⋙ 𝒪.obj, hP⟩)
          (CategoryTheory.sheafifyLift J (𝟙 (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj)) hP)).hom.app
      (Opposite.op W))
  -- The remaining tail is the map `pullbackObjIso.hom`, because `toSheafify` followed by the
  -- inverse `isoSheafify` component is the identity on the open-embedding pullback presheaf.
  calc
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op W)))
      (((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
          (Opposite.op W))
        (((CategoryTheory.toSheafify J P).app (Opposite.op W)) t)))
        =
      (RingCat.Hom.hom m)
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').hom.app 𝒪).hom.app
              (Opposite.op W)))
          (((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
              (Opposite.op W))
            (((CategoryTheory.toSheafify J P).app (Opposite.op W)) t)))) := by
              dsimp [Topology.IsOpenEmbedding.sheafPullbackIso, m]
              rw [CategoryTheory.isoSheafify_inv]
              rfl
    _ = (RingCat.Hom.hom m) (((CategoryTheory.toSheafify J P).app (Opposite.op W)) t) := by
          simpa [m] using htail
    _ = ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app (Opposite.op W)) t := by
          have hm :
              m =
                (CategoryTheory.sheafifyLift J
                  (U.isOpenEmbedding.isOpenMap.pullbackIso.hom.app 𝒪.obj) hP).app
                  (Opposite.op W) := by
                    -- Collapse the explicit sheafification tail to a single `sheafifyLift`.
                    dsimp [m]
                    exact
                      congrArg
                        (fun k ↦ k.app (Opposite.op W))
                        (CategoryTheory.sheafifyMap_sheafifyLift
                          (J := J)
                          (η := U.isOpenEmbedding.isOpenMap.pullbackIso.hom.app 𝒪.obj)
                          (γ := 𝟙 (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj))
                          (hR := hP))
          rw [hm]
          exact
            congrArg
              (fun k ↦ RingCat.Hom.hom (k.app (Opposite.op W)) t)
              (CategoryTheory.toSheafify_sheafifyLift
                (J := J)
                (η := U.isOpenEmbedding.isOpenMap.pullbackIso.hom.app 𝒪.obj)
                (hQ := hP))

/-- Helper for Restriction and extension by zero for module-valued sheaves: after rewriting the
sheaf pullback unit section through `TopCat.Sheaf.pullbackIso`, the remaining `sheafPullbackIso`
component evaluates to the open-map pullback comparison on the presheaf unit section. -/
private theorem open_embedding_sheaf_pullback_counit_section_adapter
    (W : Opens X) (s : 𝒪.obj.obj (Opposite.op W)) :
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op ((Opens.map U.inclusion').obj W))))
      (((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
          (Opposite.op ((Opens.map U.inclusion').obj W)))
      (((CategoryTheory.toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            ((TopCat.Sheaf.forget RingCat.{u} X ⋙
              TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪)).app
            (Opposite.op ((Opens.map U.inclusion').obj W)))
          ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) W) s)))) =
      ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
        (Opposite.op ((Opens.map U.inclusion').obj W)))
        ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) W) s) := by
  -- Specialize the general tail normalization to the presheaf pullback-unit section.
  simpa [open_embedding_presheaf_unit_app] using
    open_embedding_sheaf_pullback_tail_on_toSheafify_section
      (U := U) (𝒪 := 𝒪) (W := (Opens.map U.inclusion').obj W)
      (t := ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) W) s))

/-- Helper for Restriction and extension by zero for module-valued sheaves: the counit comparison
needed to transport the open-subset adjunction to sheaves of `𝒪`-modules. -/
lemma open_embedding_pushforward_adjunction_counit_eq :
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit) 𝒪.obj =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom ≫
        (Opens.map U.inclusion').op.whiskerLeft
          (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom := by
  -- First pass the sheaf-level unit through `TopCat.Sheaf.pullbackIso`.
  ext W s
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.op_app, Functor.whiskerLeft_app]
  change
    (RingCat.Hom.hom (𝒪.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app (Opposite.unop W)).op))
        s =
      (RingCat.Hom.hom
          ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
            ((Opens.map U.inclusion').op.obj W)))
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app W))
          s)
  rw [← pullbackIso_inv_toSheafify_unit_section_eq
    (f := U.inclusion') (𝒢 := 𝒪) (V := Opposite.unop W) (s := s)]
  -- The remaining comparison is the open-embedding-specific normalization from sheafification to
  -- the concrete restriction map along the counit `W ∩ U ↪ W`, which is exactly the presheaf
  -- bridge isolated in `open_embedding_presheaf_counit_app`.
  have h₁ :
      (RingCat.Hom.hom
          (𝒪.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app (Opposite.unop W)).op))
        s =
      ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
        (Opposite.op ((Opens.map U.inclusion').obj (Opposite.unop W))))
        ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) (Opposite.unop W)) s) := by
          symm
          exact open_embedding_presheaf_counit_app (U := U) (𝒪 := 𝒪) (Opposite.unop W) s
  have h₂ :
      ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
        (Opposite.op ((Opens.map U.inclusion').obj (Opposite.unop W))))
        ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) (Opposite.unop W)) s) =
      (RingCat.Hom.hom
          ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
            ((Opens.map U.inclusion').op.obj W)))
        ((ConcreteCategory.hom
            (((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).hom.app
              (Opposite.op ((Opens.map U.inclusion').obj (Opposite.unop W)))))
          ((ConcreteCategory.hom
              ((CategoryTheory.toSheafify
                  (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
                  ((TopCat.Sheaf.forget RingCat.{u} X ⋙
                    TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪)).app
                  (Opposite.op ((Opens.map U.inclusion').obj (Opposite.unop W)))))
            ((ConcreteCategory.hom
                (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
                  𝒪.obj).app (Opposite.op (Opposite.unop W))))
              s))) := by
            symm
            simpa [open_embedding_presheaf_unit_app] using
              open_embedding_sheaf_pullback_counit_section_adapter
                (U := U) (𝒪 := 𝒪) (W := Opposite.unop W) (s := s)
  exact h₁.trans h₂

/-- Helper for Restriction and extension by zero for module-valued sheaves: transporting the full
unit-side composite across `U.isOpenEmbedding.sheafPullbackIso` identifies it with the presheaf
pullback comparison applied to the presheaf triangle input. -/
private theorem open_embedding_unit_section_transport_adapter
    (V : Opens ((Opens.toTopCat X).obj U))
    (s : (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V)) :
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op V)))
      ((RingCat.Hom.hom
          (((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj.map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op))
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
              (Opposite.op (U.isOpenEmbedding.functor.obj V))))
          s)) =
      ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app (Opposite.op V))
        ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) := by
  let α := U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj
  let β := ((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪)
  let W : Opens ((Opens.toTopCat X).obj U) :=
    (Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V)
  have hmove :
      (RingCat.Hom.hom (β.hom.hom.app (Opposite.op V)))
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj.map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op))
          ((RingCat.Hom.hom
              (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
                (Opposite.op (U.isOpenEmbedding.functor.obj V))))
            s)) =
      ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
        ((RingCat.Hom.hom (β.hom.hom.app (Opposite.op W)))
          ((RingCat.Hom.hom
              (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
                (Opposite.op (U.isOpenEmbedding.functor.obj V))))
            s)) := by
    -- Naturality moves the restriction map past the `sheafPullbackIso` comparison.
    have hnat := β.hom.hom.naturality (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op
    have happ := congrArg
      (fun k ↦
        k
          ((RingCat.Hom.hom
              (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
                (Opposite.op (U.isOpenEmbedding.functor.obj V))))
            s)) hnat
    convert happ using 1
  have hunit :
      (RingCat.Hom.hom
          (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
            (Opposite.op (U.isOpenEmbedding.functor.obj V))))
        s =
      (RingCat.Hom.hom
          (((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).hom.app
            (Opposite.op W)))
        ((RingCat.Hom.hom
            ((CategoryTheory.toSheafify
                (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
                ((TopCat.Sheaf.forget RingCat.{u} X ⋙
                  TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪)).app
                (Opposite.op W)))
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) := by
    -- Rewrite the sheaf unit as the sheafified presheaf unit through `TopCat.Sheaf.pullbackIso`.
    symm
    simpa [W, open_embedding_presheaf_unit_functor_app] using
      pullbackIso_inv_toSheafify_unit_section_eq
        (f := U.inclusion') (𝒢 := 𝒪) (V := U.isOpenEmbedding.functor.obj V) (s := s)
  have htail :
      (RingCat.Hom.hom (β.hom.hom.app (Opposite.op W)))
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
              (Opposite.op (U.isOpenEmbedding.functor.obj V))))
          s) =
      ((α.hom.app (Opposite.op W))
        ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) := by
    -- The sectionwise tail is exactly the already-proved sheafification normalization.
    rw [hunit]
    simpa [α, β, W, open_embedding_presheaf_unit_functor_app] using
      open_embedding_sheaf_pullback_tail_on_toSheafify_section
        (U := U) (𝒪 := 𝒪) (W := W)
        (t := (open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)
  have hmap :
      ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
        ((α.hom.app (Opposite.op W))
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) =
      ((α.hom.app (Opposite.op V))
        ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s))) := by
    -- The last rewrite is the presheaf-level naturality of `pullbackObjIso.hom`.
    symm
    simpa [α] using
      open_embedding_pullbackObjIso_hom_unit_app (U := U) (𝒪 := 𝒪) V s
  exact hmove.trans <|
    (congrArg
      (fun t ↦
        ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op) t)
      htail).trans hmap

/-- Helper for Restriction and extension by zero for module-valued sheaves: after transporting the
full unit-side composite across `U.isOpenEmbedding.sheafPullbackIso`, the remaining presheaf
composite collapses by the open-embedding triangle identity. -/
private theorem open_embedding_unit_section_transport_normalized
    (V : Opens ((Opens.toTopCat X).obj U))
    (s : (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V)) :
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op V)))
      ((RingCat.Hom.hom
          (((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj.map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op))
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
              (Opposite.op (U.isOpenEmbedding.functor.obj V))))
          s)) = s := by
  let α := U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj
  calc
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op V)))
      ((RingCat.Hom.hom
          (((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj.map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op))
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
              (Opposite.op (U.isOpenEmbedding.functor.obj V))))
          s)) =
      ((α.hom.app (Opposite.op V))
        ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s))) := by
            simpa [α] using
              open_embedding_unit_section_transport_adapter (U := U) (𝒪 := 𝒪) V s
    _ = ((α.hom.app (Opposite.op V)) ((α.inv.app (Opposite.op V)) s)) := by
          -- Replace the middle presheaf composite by the inverse pullback comparison.
          exact congrArg
            (fun t ↦ (α.hom.app (Opposite.op V)) t)
            (open_embedding_presheaf_triangle_app (U := U) (𝒪 := 𝒪) V s)
    _ = s := by
          -- The presheaf comparison is an isomorphism, so its `hom` and `inv` cancel.
          simpa using
            congrArg
              (fun f ↦ f s)
              (Iso.inv_hom_id_app α (Opposite.op V))

/-- Helper for Restriction and extension by zero for module-valued sheaves: the unit comparison
needed to transport the open-subset adjunction to sheaves of `𝒪`-modules. -/
lemma open_embedding_pushforward_adjunction_unit_eq :
    letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
    (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom ≫
        U.isOpenEmbedding.functor.op.whiskerLeft
          ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom ≫
        Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.unit)
          ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj =
      𝟙 ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  -- First expose the sectionwise composite that must become the presheaf triangle identity.
  ext V s
  simp only [Functor.comp_obj, Functor.op_obj, Functor.id_obj, Opposite.op_unop, Iso.app_hom,
    TopCat.Sheaf.pushforward_obj_val, ObjectProperty.ι_obj, NatTrans.comp_app,
    TopCat.Presheaf.pushforward_obj_obj, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app, RingCat.hom_comp, NatTrans.id_app, RingCat.hom_id]
  let β := ((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪)
  let s' := (RingCat.Hom.hom (β.hom.hom.app V)) s
  have htransport := by
    -- Transport the whole sectionwise equality to the naive open-embedding pullback side.
    simpa [β, s', Function.comp_apply] using
      open_embedding_unit_section_transport_normalized
        (U := U) (𝒪 := 𝒪) (V := Opposite.unop V) (s := s')
  have hleftInv : Function.LeftInverse
      (RingCat.Hom.hom (β.inv.hom.app V))
      (RingCat.Hom.hom (β.hom.hom.app V)) := by
    intro t
    -- The `sheafPullbackIso` component is an isomorphism, so its inverse cancels its `hom`.
    exact congrArg
        (fun k ↦ (k.hom.app V) t)
        (Iso.hom_inv_id_app (U.isOpenEmbedding.sheafPullbackIso RingCat.{u}) 𝒪)
  -- Use the sectionwise left inverse to descend from the transported equality.
  exact hleftInv.injective htransport

/-- Helper for Restriction and extension by zero for module-valued sheaves: the open-embedding
restriction owner is also a left adjoint to the module direct image along `U ↪ X`. -/
noncomputable abbrev open_embedding_module_pushforward_adjunction :
    letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
    SheafOfModules.pushforward.{u} (F := U.isOpenEmbedding.functor)
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom) ⊣
      SheafOfModules.pushforward
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪) :=
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  -- The open-embedding pushforward owner becomes a left adjoint once the two comparison
  -- identities above identify its unit and counit with the open-subset adjunction data.
  SheafOfModules.pushforwardPushforwardAdj
    (adj := U.isOpenEmbedding.isOpenMap.adjunction)
    (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪)
    (open_embedding_pushforward_adjunction_counit_eq U 𝒪)
    (open_embedding_pushforward_adjunction_unit_eq U 𝒪)

/-- Helper for Restriction and extension by zero for module-valued sheaves: the concrete
open-embedding restriction owner agrees with the pullback-based public API. -/
noncomputable abbrev moduleSheafRestrictionToOpen_compare_open_embedding_pushforward :
    letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
    SheafOfModules.pushforward.{u} (F := U.isOpenEmbedding.functor)
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom) ≅
        moduleSheafRestrictionToOpen U 𝒪 :=
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  -- The two functors are the unique left adjoints to the same module direct-image functor.
  Adjunction.leftAdjointUniq
    (open_embedding_module_pushforward_adjunction U 𝒪)
    (moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction U 𝒪)

-- Proof sketch: this is the module-valued analogue of the open-immersion restriction functor for
-- sheaves of sets and algebraic structures. One proves that for an open inclusion `j : U ↪ X`,
-- restriction of `𝒪`-modules has a left adjoint given by extension by zero, hence the displayed
-- restriction functor is a right adjoint.
/-- Restriction of sheaves of `𝒪`-modules to an open subset is a right adjoint. -/
instance moduleSheafRestrictionToOpen_isRightAdjoint :
    (moduleSheafRestrictionToOpen U 𝒪).IsRightAdjoint := by
  -- Route correction: identify restriction with the open-embedding pushforward owner, and then
  -- transport the generic right-adjoint structure across that comparison.
  letI :=
    Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  letI :
      (SheafOfModules.pushforward.{u} (F := U.isOpenEmbedding.functor)
        (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom)).IsRightAdjoint :=
    open_embedding_module_pushforward_isRightAdjoint U 𝒪
  -- Once the functor comparison is in place, the right-adjoint structure transports immediately.
  exact Functor.isRightAdjoint_of_iso
    (moduleSheafRestrictionToOpen_compare_open_embedding_pushforward U 𝒪)

/-- The extension-by-zero functor for sheaves of `𝒪|_U`-modules along the open inclusion
`j : U ↪ X`, defined as the chosen left adjoint to `moduleSheafRestrictionToOpen U 𝒪`. -/
noncomputable abbrev moduleSheafExtensionByZeroFromOpen :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪) ⥤
      SheafOfModules 𝒪 :=
  (moduleSheafRestrictionToOpen U 𝒪).leftAdjoint

/-- The chosen extension-by-zero functor is left adjoint to restriction to the open subset. -/
noncomputable abbrev moduleSheafExtensionByZeroAdjunction :
    moduleSheafExtensionByZeroFromOpen U 𝒪 ⊣ moduleSheafRestrictionToOpen U 𝒪 :=
  Adjunction.ofIsRightAdjoint (moduleSheafRestrictionToOpen U 𝒪)
