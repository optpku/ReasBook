module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import stacks_project.Chap04.Lemma_4_19_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor
open CategoryTheory.Limits

universe u v w

noncomputable section

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 7.25.10:
- primary domain: category-theoretic localization of presheaves via restriction and Kan extension
  along `Over.forget U`;
- sampled owner API:
  `Functor.whiskeringLeft`,
  `Functor.lanAdjunction`,
  `Functor.ranAdjunction`,
  `Functor.leftKanExtensionObjIsoColimit`;
- source-facing layer: the remark identifies the inverse-image functor on presheaves and its two
  canonical adjoints for localization at `U`;
- core/canonical owner: restriction by precomposition with `(Over.forget U).op` and the Kan
  extension adjunctions owned upstream by mathlib;
- bridge/view: the objectwise sigma-type formula for the left Kan extension and its finite
  connected limit preservation consequences.

Primitive data are the category `C`, the localization object `U`, and a presheaf on `Over U`.
The inverse-image functor and both adjunctions are derived API owned by
`Functor.whiskeringLeft`, `Functor.lanAdjunction`, and `Functor.ranAdjunction`, so this file
should recall those owners directly and keep only the genuinely local bridge results.
-/

namespace LocalizationLeftKanExtension

/-- Helper for Remark 7.25.10: evaluate a presheaf on `Over U` on the discrete family of morphisms
`V ⟶ U`. -/
def morphism_family_functor
    (U V : C) : ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Discrete (V ⟶ U) ⥤ Type (max u v)) :=
  -- Restriction to the discrete family `φ : V ⟶ U` is just precomposition with
  -- `φ ↦ op (Over.mk φ)`.
  (Functor.whiskeringLeft (Discrete (V ⟶ U)) (Over U)ᵒᵖ (Type (max u v))).obj
    (Discrete.functor fun φ ↦ op (Over.mk φ))

/-- Helper for Remark 7.25.10: the sigma-type functor collecting all fibers
`G(V \xrightarrow{φ} U)` at once. -/
def sigma_morphism_family_functor
    (U V : C) : ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ Type (max u v) where
  obj G := Σ φ : V ⟶ U, G.obj (op (Over.mk φ))
  map η := fun x ↦ ⟨x.1, η.app (op (Over.mk x.1)) x.2⟩
  map_id _ := funext fun
    | ⟨_, _⟩ => rfl
  map_comp _ _ := funext fun
    | ⟨_, _⟩ => rfl

/-- Helper for Remark 7.25.10: the owner-level colimit formula for the left Kan extension along
`(Over.forget U).op` is natural in the presheaf variable. -/
theorem leftKanExtensionObjIsoColimit_naturality
    (U V : C) {G H : (Over U)ᵒᵖ ⥤ Type (max u v)} (η : G ⟶ H) :
    ((((Over.forget U).op.lan :
            ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) ⋙
          (evaluation Cᵒᵖ (Type (max u v))).obj (op V)).map η) ≫
      ((Over.forget U).op.leftKanExtensionObjIsoColimit H (op V)).hom =
    ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
      colimMap ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η) := by
  let eG := (Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)
  let eH := (Over.forget U).op.leftKanExtensionObjIsoColimit H (op V)
  let FG :
      CostructuredArrow (Over.forget U).op (op V) ⥤ Type (max u v) :=
    CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G
  let FH :
      CostructuredArrow (Over.forget U).op (op V) ⥤ Type (max u v) :=
    CostructuredArrow.proj (Over.forget U).op (op V) ⋙ H
  -- Compare the two routes after precomposing with the inverse of the colimit comparison.
  exact (Iso.cancel_iso_inv_left eG _ _).1 <| by
    apply colimit.hom_ext
    intro A
    ext x
    simp [Functor.comp_map, Functor.lan]
    -- Rewrite the source colimit class using the owner-level inverse formula.
    have hG :
        eG.inv ((colimit.ι FG A) x) =
          ((((Over.forget U).op.leftKanExtensionUnit G).app A.left) ≫
              (((Over.forget U).op.leftKanExtension G).map A.hom)) x := by
      simpa [eG, FG, Functor.lan] using
        congrArg (fun k ↦ k x)
          ((Over.forget U).op.ι_leftKanExtensionObjIsoColimit_inv (F := G) (X := op V) A)
    -- Move the comparison map past the restriction map in the left Kan extension.
    have hNat :
        (((Over.forget U).op.leftKanExtensionUnit G).app A.left ≫
              ((Over.forget U).op.leftKanExtension G).map A.hom ≫
              ((Over.forget U).op.lan.map η).app (op V)) x =
          (((Over.forget U).op.leftKanExtensionUnit G).app A.left ≫
              ((Over.forget U).op.lan.map η).app ((Over.forget U).op.obj A.left) ≫
              ((Over.forget U).op.leftKanExtension H).map A.hom) x := by
      exact
        congrArg
          (fun k ↦ k ((((Over.forget U).op.leftKanExtensionUnit G).app A.left) x))
          (((Over.forget U).op.lan.map η).naturality A.hom)
    -- Identify the Kan-extension comparison with the defining descent from `η`.
    have hDesc :
        ((((Over.forget U).op.leftKanExtensionUnit G).app A.left) ≫
              ((Over.forget U).op.lan.map η).app ((Over.forget U).op.obj A.left)) x =
          ((η.app A.left) ≫ ((Over.forget U).op.leftKanExtensionUnit H).app A.left) x := by
      simpa [Functor.lan] using
        congrArg (fun k ↦ k x)
          (Functor.descOfIsLeftKanExtension_fac_app
            (F' := (Over.forget U).op.leftKanExtension G)
            (α := (Over.forget U).op.leftKanExtensionUnit G)
            (G := (Over.forget U).op.leftKanExtension H)
            (β := η ≫ (Over.forget U).op.leftKanExtensionUnit H)
            A.left)
    have hDesc' :
        ((((Over.forget U).op.leftKanExtensionUnit G).app A.left) ≫
              ((Over.forget U).op.lan.map η).app ((Over.forget U).op.obj A.left) ≫
              ((Over.forget U).op.leftKanExtension H).map A.hom) x =
          (((η.app A.left) ≫
              ((Over.forget U).op.leftKanExtensionUnit H).app A.left ≫
              ((Over.forget U).op.leftKanExtension H).map A.hom)) x := by
      exact congrArg
        (fun y ↦ (((Over.forget U).op.leftKanExtension H).map A.hom) y)
        hDesc
    -- Rewrite the target colimit class using the owner-level forward formula.
    have hH :
        eH.hom
            (((((Over.forget U).op.leftKanExtensionUnit H).app A.left) ≫
                (((Over.forget U).op.leftKanExtension H).map A.hom))
              (((η.app A.left) x))) =
          ((colimit.ι FH A) ((η.app A.left) x)) := by
      simpa [eH, FH, Functor.lan] using
        congrArg (fun k ↦ k ((η.app A.left) x))
          ((Over.forget U).op.ι_leftKanExtensionObjIsoColimit_hom (F := H) (X := op V) A)
    -- The colimit map on the indexing diagram acts by applying `η` at the left object.
    have hMap :
        colimMap ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η)
            ((colimit.ι FG A) x) =
          ((colimit.ι FH A) ((η.app A.left) x)) := by
      simpa [FG, FH] using
        congrArg (fun k ↦ k x)
          (ι_colimMap ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η) A)
    have hG_hom :
        eG.hom
            (((((Over.forget U).op.leftKanExtensionUnit G).app A.left) ≫
                (((Over.forget U).op.leftKanExtension G).map A.hom)) x) =
          ((colimit.ι FG A) x) := by
      rw [← hG]
      simp [eG]
    rw [hG]
    change
      eH.hom
          (((((Over.forget U).op.leftKanExtensionUnit G).app A.left) ≫
              ((Over.forget U).op.leftKanExtension G).map A.hom ≫
              ((Over.forget U).op.lan.map η).app (op V)) x) =
        _
    rw [hNat]
    rw [hDesc']
    rw [hG_hom]
    rw [hMap]
    exact hH

/-- The discrete family of terminal objects in the indexing category for the objectwise
left-Kan-extension formula along `(Over.forget U).op`. -/
abbrev indexFunctor
    (U V : C) : Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (op V) :=
  Discrete.functor fun φ ↦
    CostructuredArrow.mk
      (show (Over.forget U).op.obj (op (Over.mk φ)) ⟶ op V from 𝟙 (op V))

/-- The composite `V ⟶ U` attached to a costructured arrow over `(Over.forget U).op`. -/
abbrev overObj
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Over U :=
  X.left.unop

/-- The leg `V ⟶ A` of the underlying triangle `V ⟶ A ⟶ U`. -/
abbrev leg
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) :
    V ⟶ (overObj X).left :=
  X.hom.unop

/-- The composite `V ⟶ U` attached to a costructured arrow over `(Over.forget U).op`. -/
abbrev composite
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : V ⟶ U :=
  leg X ≫ (overObj X).hom

/-- The discrete index determined by the commutative triangle underlying `X`. -/
abbrev index
    {U V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Discrete (V ⟶ U) :=
  Discrete.mk (composite X)

/-- The distinguished morphism from an indexing object to the terminal object in its fiber. -/
abbrev terminalHom
    (U V : C) {X : CostructuredArrow (Over.forget U).op (op V)} :
    X ⟶ (indexFunctor U V).obj (index X) :=
  CostructuredArrow.homMk
    ((show Over.mk (composite X) ⟶ overObj X from Over.homMk (leg X)).op)
    (by
      simp [indexFunctor, index, leg])

/-- Any morphism into `indexFunctor U V` is indexed by the composite `V ⟶ U` of the underlying
commutative triangle. -/
lemma composite_eq_of_map
    (U V : C) {X Y : CostructuredArrow (Over.forget U).op (op V)} (hom : X ⟶ Y) :
    composite X = composite Y := by
  let triangle : overObj Y ⟶ overObj X := hom.left.unop
  have hleg : leg Y ≫ triangle.left = leg X := by
    have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
    simpa [triangle] using h
  have hw : triangle.left ≫ (overObj X).hom = (overObj Y).hom := Over.w triangle
  dsimp [composite]
  calc
    leg X ≫ (overObj X).hom = (leg Y ≫ triangle.left) ≫ (overObj X).hom := by
      rw [hleg]
    _ = leg Y ≫ (triangle.left ≫ (overObj X).hom) := by rw [Category.assoc]
    _ = leg Y ≫ (overObj Y).hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ leg Y ≫ k) hw

/-- Any morphism into `indexFunctor U V` is indexed by the composite `V ⟶ U` of the underlying
commutative triangle. -/
lemma composite_eq_of_hom
    (U V : C) {X : CostructuredArrow (Over.forget U).op (op V)}
    {φ : V ⟶ U} (hom : X ⟶ (indexFunctor U V).obj (Discrete.mk φ)) :
    composite X = φ := by
  simpa [indexFunctor, composite, leg, overObj] using composite_eq_of_map U V hom

/-- The distinguished morphism into an indexing object is obtained by reindexing the composite
attached to `X`. -/
def homToIndex
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite X = φ) :
    X ⟶ (indexFunctor U V).obj (Discrete.mk φ) := by
  cases hφ
  exact terminalHom U V

/-- A morphism into the chosen terminal object is determined uniquely by its commutative triangle. -/
lemma hom_eq_terminalHom
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (hom : X ⟶ (indexFunctor U V).obj (index X)) :
    hom = terminalHom U V := by
  ext
  exact by
    apply Quiver.Hom.unop_inj
    apply CommaMorphism.ext
    · have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
      simpa [indexFunctor] using h
    · simp [Over.homMk]

lemma hom_eq_homToIndex
    (U V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite X = φ)
    (hom : X ⟶ (indexFunctor U V).obj (Discrete.mk φ)) :
    hom = homToIndex U V X φ hφ := by
  cases hφ
  simpa [homToIndex] using hom_eq_terminalHom U V X hom

/-- The indexing category of triangles over `V ⟶ U` remembers only the composite map
`V ⟶ U`. -/
abbrev compositeFunctor
    (U V : C) :
    CostructuredArrow (Over.forget U).op (op V) ⥤ Discrete (V ⟶ U) where
  obj X := Discrete.mk (composite X)
  map hom := Discrete.eqToHom (composite_eq_of_map U V hom)

/-- The discrete inclusion of indices is right adjoint to the functor remembering the composite
`V ⟶ U`. -/
def compositeIndexAdjunction (U V : C) :
    compositeFunctor U V ⊣ indexFunctor U V :=
  Adjunction.mkOfHomEquiv
    { homEquiv := by
        intro X φ
        cases φ with
        | mk ψ =>
            refine
              { toFun := fun hom ↦ homToIndex U V X ψ (Discrete.eq_of_hom hom)
                invFun := fun hom ↦ Discrete.eqToHom (composite_eq_of_hom U V hom)
                left_inv := ?_
                right_inv := ?_ }
            · intro hom
              apply Subsingleton.elim
            · intro hom
              simpa using
                (hom_eq_homToIndex U V X ψ (composite_eq_of_hom U V hom) hom).symm
      homEquiv_naturality_left_symm := by
        intro X' X φ hom k
        apply Subsingleton.elim
      homEquiv_naturality_right := by
        intro X Y Y' hom g
        cases Y with
        | mk ψ =>
            cases Y' with
            | mk ψ' =>
                have h :=
                  (hom_eq_homToIndex U V X ψ'
                    (by simpa using Discrete.eq_of_hom (hom ≫ g))
                    (homToIndex U V X ψ (Discrete.eq_of_hom hom) ≫
                      (indexFunctor U V).map g)).symm
                simpa [homToIndex] using congrArg CommaMorphism.left h }

/-- The discrete inclusion of the chosen terminal objects is final. -/
theorem indexFunctor_final (U V : C) : Functor.Final (indexFunctor U V) := by
  let _ : (indexFunctor U V).IsRightAdjoint :=
    ⟨⟨compositeFunctor U V, ⟨compositeIndexAdjunction U V⟩⟩⟩
  infer_instance

/-- The restricted indexing diagram is literally the discrete family
`φ ↦ G(V \xrightarrow{φ} U)`. -/
abbrev indexFunctorProjIso
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) (V : C) :
    indexFunctor U V ⋙ CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G ≅
      Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) := by
  refine Discrete.natIso ?_
  intro φ
  exact Iso.refl _

end LocalizationLeftKanExtension

/-- The canonical left Kan extension along `(Over.forget U).op` is objectwise the coproduct of
the fibers `G(V \xrightarrow{} U)` over all morphisms `V ⟶ U`. -/
noncomputable def localization_leftKanExtension_objIsoSigma
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) (V : C) :
    (((Over.forget U).op.lan.obj G).obj (op V)) ≅ Σ φ : V ⟶ U, G.obj (op (Over.mk φ)) :=
  letI : Functor.Final (LocalizationLeftKanExtension.indexFunctor U V) :=
    LocalizationLeftKanExtension.indexFunctor_final U V
  (Over.forget U).op.leftKanExtensionObjIsoColimit G (op V) ≪≫
    (Functor.Final.colimitIso
      (LocalizationLeftKanExtension.indexFunctor U V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso (LocalizationLeftKanExtension.indexFunctorProjIso U G V) ≪≫
    Types.coproductIso (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))

namespace LocalizationLeftKanExtension

/-- Helper for Remark 7.25.10: discrete coproducts of sets commute with finite connected limits. -/
theorem morphism_family_colimit_preserves_finite_connected_limits
    (U V : C) (I : Type w) [SmallCategory I] [Small.{max u v} I] [FinCategory I]
    [IsConnected I] :
    PreservesLimitsOfShape I
      (colim : (Discrete (V ⟶ U) ⥤ Type (max u v)) ⥤ Type (max u v)) := by
  let _ : HasSpanCocones (Discrete (V ⟶ U)) := by
    refine ⟨?_⟩
    intro X Y Z f g
    refine ⟨X, Discrete.eqToHom (Discrete.eq_of_hom f).symm,
      Discrete.eqToHom (Discrete.eq_of_hom g).symm, ?_⟩
    apply Subsingleton.elim
  have hMap :
      ∀ ⦃X Y : Discrete (V ⟶ U)⦄ (f g : X ⟶ Y),
        ∃ (Z : Discrete (V ⟶ U)) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
    intro X Y f g
    refine ⟨Y, 𝟙 Y, ?_⟩
    apply Subsingleton.elim
  -- Lemma 4.19.9 applies once the discrete indexing category is seen to satisfy the
  -- span-completion and postcomposition-equalizer hypotheses trivially.
  simpa using
    CategoryTheory.Limits.colimit_preserves_finite_connected_limits_of_types
      (I := Discrete (V ⟶ U)) (J := I) hMap

/-- Helper for Remark 7.25.10: the evaluation of the discrete family functor followed by colimit is
canonically the sigma-type functor. -/
noncomputable def morphism_family_as_discrete
    (U V : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) :
    (morphism_family_functor U V).obj G ≅
      Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) :=
  Discrete.natIso (fun _ ↦ Iso.refl _)

/-- Helper for Remark 7.25.10: the discrete family presentation of `φ ↦ G(V \xrightarrow{φ} U)`
matches the sigma-type coproduct formula. -/
noncomputable def morphism_family_component_iso
    (U V : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) :
    colimit ((morphism_family_functor U V).obj G) ≅
      Σ φ : V ⟶ U, G.obj (op (Over.mk φ)) :=
  HasColimit.isoOfNatIso (morphism_family_as_discrete U V G) ≪≫
    Types.coproductIso (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))

/- Helper for Remark 7.25.10: the colimit-to-sigma comparison sends the `φ`-summand injection to
the sigma constructor `⟨φ, x⟩`. -/
theorem morphism_family_component_hom_ι
    (U V : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) (φ : V ⟶ U) :
    colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk φ) ≫
        (morphism_family_component_iso U V G).hom =
      fun x ↦ (⟨φ, x⟩ : Σ ψ : V ⟶ U, G.obj (op (Over.mk ψ))) := by
  -- Normalize the `HasColimit.isoOfNatIso` comparison first, so the remaining map is the
  -- standard coproduct injection into the sigma type.
  calc
    colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk φ) ≫
        (morphism_family_component_iso U V G).hom =
      colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk φ) ≫
        (HasColimit.isoOfNatIso (morphism_family_as_discrete U V G)).hom ≫
        (Types.coproductIso (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ)))).hom := by
          rfl
    _ =
        (morphism_family_as_discrete U V G).hom.app (Discrete.mk φ) ≫
          colimit.ι
            (Discrete.functor (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ))))
            (Discrete.mk φ) ≫
          (Types.coproductIso (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ)))).hom := by
          rw [HasColimit.isoOfNatIso_ι_hom_assoc]
    _ =
        (morphism_family_as_discrete U V G).hom.app (Discrete.mk φ) ≫
          (fun x ↦ (⟨φ, x⟩ : Σ ψ : V ⟶ U, G.obj (op (Over.mk ψ)))) := by
          congr 1
          simpa using
            (colimit.isoColimitCocone_ι_hom
              (Types.coproductColimitCocone (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ))))
              (Discrete.mk φ))
    _ = fun x ↦ (⟨φ, x⟩ : Σ ψ : V ⟶ U, G.obj (op (Over.mk ψ))) := by
          funext x
          simp [morphism_family_as_discrete]

/-- Helper for Remark 7.25.10: the direct coproduct comparison from the discrete reindexing
diagram agrees with the two-step route through `morphism_family_as_discrete`. -/
theorem indexFunctorProjIso_coproduct_comparison
    (U V : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) :
    (HasColimit.isoOfNatIso
        (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
          (morphism_family_as_discrete U V G).symm)).hom ≫
      (morphism_family_component_iso U V G).hom =
    (HasColimit.isoOfNatIso
        (LocalizationLeftKanExtension.indexFunctorProjIso U G V)).hom ≫
      (Types.coproductIso (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom := by
  -- On each discrete summand, both natural-isomorphism components are definitionally identities,
  -- so both routes identify with the same explicit sigma constructor.
  apply colimit.hom_ext
  intro j
  cases j with
  | mk φ =>
      have hLeft :
          colimit.ι
                (LocalizationLeftKanExtension.indexFunctor U V ⋙
                  CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)
                (Discrete.mk φ) ≫
              (HasColimit.isoOfNatIso
                  (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
                    (morphism_family_as_discrete U V G).symm)).hom ≫
              (morphism_family_component_iso U V G).hom =
            fun x ↦ (⟨φ, x⟩ : Σ ψ : V ⟶ U, G.obj (op (Over.mk ψ))) := by
        calc
          colimit.ι
                (LocalizationLeftKanExtension.indexFunctor U V ⋙
                  CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)
                (Discrete.mk φ) ≫
              (HasColimit.isoOfNatIso
                  (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
                    (morphism_family_as_discrete U V G).symm)).hom ≫
              (morphism_family_component_iso U V G).hom =
            ((LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
                  (morphism_family_as_discrete U V G).symm).hom.app (Discrete.mk φ)) ≫
              colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk φ) ≫
              (morphism_family_component_iso U V G).hom := by
              simpa [Category.assoc] using
                (HasColimit.isoOfNatIso_ι_hom_assoc
                  (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
                    (morphism_family_as_discrete U V G).symm)
                  (Discrete.mk φ)
                  ((morphism_family_component_iso U V G).hom))
          _ = fun x ↦ (⟨φ, x⟩ : Σ ψ : V ⟶ U, G.obj (op (Over.mk ψ))) := by
              simpa [LocalizationLeftKanExtension.indexFunctorProjIso, morphism_family_as_discrete]
                using morphism_family_component_hom_ι U V G φ
      have hRight :
          colimit.ι
                (LocalizationLeftKanExtension.indexFunctor U V ⋙
                  CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)
                (Discrete.mk φ) ≫
              (HasColimit.isoOfNatIso
                  (LocalizationLeftKanExtension.indexFunctorProjIso U G V)).hom ≫
              (Types.coproductIso (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ)))).hom =
            fun x ↦ (⟨φ, x⟩ : Σ ψ : V ⟶ U, G.obj (op (Over.mk ψ))) := by
        calc
          colimit.ι
                (LocalizationLeftKanExtension.indexFunctor U V ⋙
                  CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)
                (Discrete.mk φ) ≫
              (HasColimit.isoOfNatIso
                  (LocalizationLeftKanExtension.indexFunctorProjIso U G V)).hom ≫
              (Types.coproductIso (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ)))).hom =
            (LocalizationLeftKanExtension.indexFunctorProjIso U G V).hom.app (Discrete.mk φ) ≫
              colimit.ι
                (Discrete.functor (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ))))
                (Discrete.mk φ) ≫
              (Types.coproductIso (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ)))).hom := by
              simpa [Category.assoc] using
                (HasColimit.isoOfNatIso_ι_hom_assoc
                  (LocalizationLeftKanExtension.indexFunctorProjIso U G V)
                  (Discrete.mk φ)
                  ((Types.coproductIso (fun ψ : V ⟶ U ↦ G.obj (op (Over.mk ψ)))).hom))
          _ = fun x ↦ (⟨φ, x⟩ : Σ ψ : V ⟶ U, G.obj (op (Over.mk ψ))) := by
              simp [LocalizationLeftKanExtension.indexFunctorProjIso]
      exact hLeft.trans hRight.symm

/-- Helper for Remark 7.25.10: the component isomorphisms for the discrete coproduct formula are
natural in the presheaf variable. -/
theorem morphism_family_colimit_iso_sigma_naturality
    (U V : C) {G H : (Over U)ᵒᵖ ⥤ Type (max u v)} (η : G ⟶ H) :
    ((morphism_family_functor U V ⋙
          (colim : (Discrete (V ⟶ U) ⥤ Type (max u v)) ⥤ Type (max u v))).map η) ≫
        (morphism_family_component_iso U V H).hom =
      (morphism_family_component_iso U V G).hom ≫
        (sigma_morphism_family_functor U V).map η := by
  -- Check the equality on each coproduct summand, where both routes become the same sigma map
  -- `x ↦ ⟨ψ, η.app (op (Over.mk ψ)) x⟩`.
  apply colimit.hom_ext
  intro j
  cases j with
  | mk ψ =>
      calc
        colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk ψ) ≫
            ((morphism_family_functor U V ⋙
                (colim : (Discrete (V ⟶ U) ⥤ Type (max u v)) ⥤ Type (max u v))).map η) ≫
              (morphism_family_component_iso U V H).hom =
          ((morphism_family_functor U V).map η).app (Discrete.mk ψ) ≫
            colimit.ι ((morphism_family_functor U V).obj H) (Discrete.mk ψ) ≫
              (morphism_family_component_iso U V H).hom := by
            simpa [Functor.comp_map, colim_map] using
              (ι_colimMap_assoc ((morphism_family_functor U V).map η) (Discrete.mk ψ)
                ((morphism_family_component_iso U V H).hom))
        _ = colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk ψ) ≫
              (morphism_family_component_iso U V G).hom ≫
                (sigma_morphism_family_functor U V).map η := by
              funext x
              -- Evaluate both routes on the `ψ`-summand and rewrite the component isomorphisms
              -- to the explicit sigma constructors from `morphism_family_component_hom_ι`.
              have hH :
                  ((((morphism_family_functor U V).map η).app (Discrete.mk ψ) ≫
                        colimit.ι ((morphism_family_functor U V).obj H) (Discrete.mk ψ) ≫
                        (morphism_family_component_iso U V H).hom) x) =
                    ⟨ψ, ((morphism_family_functor U V).map η).app (Discrete.mk ψ) x⟩ := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ k (((morphism_family_functor U V).map η).app (Discrete.mk ψ) x))
                    (morphism_family_component_hom_ι U V H ψ)
              have hG :
                  ((colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk ψ) ≫
                        (morphism_family_component_iso U V G).hom) x) =
                    ⟨ψ, x⟩ := by
                simpa using
                  congrArg (fun k ↦ k x) (morphism_family_component_hom_ι U V G ψ)
              rw [hH]
              change
                ⟨ψ, ((morphism_family_functor U V).map η).app (Discrete.mk ψ) x⟩ =
                  (sigma_morphism_family_functor U V).map η
                    ((colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk ψ) ≫
                        (morphism_family_component_iso U V G).hom) x)
              rw [hG]
              simp [sigma_morphism_family_functor, morphism_family_functor]

/-- Helper for Remark 7.25.10: the evaluation of the discrete family functor followed by colimit is
canonically the sigma-type functor. -/
noncomputable def morphism_family_colimit_iso_sigma
    (U V : C) :
    morphism_family_functor U V ⋙
        (colim : (Discrete (V ⟶ U) ⥤ Type (max u v)) ⥤ Type (max u v)) ≅
      sigma_morphism_family_functor U V :=
  NatIso.ofComponents
    (fun G ↦ morphism_family_component_iso U V G)
    (fun {_ _} η ↦ morphism_family_colimit_iso_sigma_naturality U V η)

/-- Helper for Remark 7.25.10: evaluation on the discrete morphism family preserves all limits. -/
theorem morphism_family_functor_preserves_limits
    (U V : C) (I : Type w) [SmallCategory I] [Small.{max u v} I] :
    PreservesLimitsOfShape I (morphism_family_functor U V) := by
  -- Evaluation on a functor category reduces the claim to ordinary evaluation on `Over U`.
  apply preservesLimitsOfShape_of_evaluation
  intro j
  cases j with
  | mk φ =>
      change PreservesLimitsOfShape I
        ((evaluation (Over U)ᵒᵖ (Type (max u v))).obj (op (Over.mk φ)))
      infer_instance

/-- Helper for Remark 7.25.10: the sigma-type formula for `j_{U!}` is natural in the presheaf
variable. -/
theorem indexFunctor_colimitIso_naturality
    (U V : C) [Functor.Final (LocalizationLeftKanExtension.indexFunctor U V)]
    {G H : (Over U)ᵒᵖ ⥤ Type (max u v)} (η : G ⟶ H) :
    (Functor.Final.colimitIso
          (LocalizationLeftKanExtension.indexFunctor U V)
          (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).hom ≫
        colimMap ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η) =
      colimMap
          ((LocalizationLeftKanExtension.indexFunctor U V).whiskerLeft
            ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η)) ≫
        (Functor.Final.colimitIso
          (LocalizationLeftKanExtension.indexFunctor U V)
          (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ H)).hom := by
  -- This is exactly the naturality of the finality-induced colimit isomorphism.
  simpa [Functor.comp_map] using
    (((Functor.Final.colimIso (LocalizationLeftKanExtension.indexFunctor U V)).hom.naturality
      ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η)).symm)

/-- Helper for Remark 7.25.10: after restricting to the discrete morphism family, the tautological
diagram isomorphism is natural in the presheaf variable. -/
theorem indexFunctorProjIso_colimit_naturality
    (U V : C) {G H : (Over U)ᵒᵖ ⥤ Type (max u v)} (η : G ⟶ H) :
      colimMap
        ((LocalizationLeftKanExtension.indexFunctor U V).whiskerLeft
          ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η)) ≫
      (HasColimit.isoOfNatIso
          (LocalizationLeftKanExtension.indexFunctorProjIso U H V ≪≫
            (morphism_family_as_discrete U V H).symm)).hom =
    (HasColimit.isoOfNatIso
        (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
          (morphism_family_as_discrete U V G).symm)).hom ≫
      colimMap ((morphism_family_functor U V).map η) := by
  -- Normalize both sides on each discrete summand; the remaining component map is
  -- exactly `η.app (op (Over.mk ψ))`.
  apply colimit.hom_ext
  intro j
  cases j with
  | mk ψ =>
      let α :=
        ((LocalizationLeftKanExtension.indexFunctor U V).whiskerLeft
          ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η))
      let wG :=
        LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
          (morphism_family_as_discrete U V G).symm
      let wH :=
        LocalizationLeftKanExtension.indexFunctorProjIso U H V ≪≫
          (morphism_family_as_discrete U V H).symm
      calc
        colimit.ι
              (LocalizationLeftKanExtension.indexFunctor U V ⋙
                CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)
              (Discrete.mk ψ) ≫
            colimMap
              ((LocalizationLeftKanExtension.indexFunctor U V).whiskerLeft
                ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η)) ≫
            (HasColimit.isoOfNatIso
                (LocalizationLeftKanExtension.indexFunctorProjIso U H V ≪≫
                  (morphism_family_as_discrete U V H).symm)).hom =
          α.app (Discrete.mk ψ) ≫
            wH.hom.app (Discrete.mk ψ) ≫
            colimit.ι ((morphism_family_functor U V).obj H) (Discrete.mk ψ) := by
              rw [ι_colimMap_assoc]
              simpa [α, wH, Category.assoc] using
                congrArg (fun k ↦ α.app (Discrete.mk ψ) ≫ k)
                  (HasColimit.isoOfNatIso_ι_hom wH (Discrete.mk ψ))
        _ =
            wG.hom.app (Discrete.mk ψ) ≫
              ((morphism_family_functor U V).map η).app (Discrete.mk ψ) ≫
              colimit.ι ((morphism_family_functor U V).obj H) (Discrete.mk ψ) := by
                simp [α, wG, wH, LocalizationLeftKanExtension.indexFunctorProjIso,
                  morphism_family_as_discrete, morphism_family_functor]
        _ =
            colimit.ι
                (LocalizationLeftKanExtension.indexFunctor U V ⋙
                  CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)
                (Discrete.mk ψ) ≫
              (HasColimit.isoOfNatIso
                  (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
                    (morphism_family_as_discrete U V G).symm)).hom ≫
              colimMap ((morphism_family_functor U V).map η) := by
                calc
                  wG.hom.app (Discrete.mk ψ) ≫
                      ((morphism_family_functor U V).map η).app (Discrete.mk ψ) ≫
                      colimit.ι ((morphism_family_functor U V).obj H) (Discrete.mk ψ) =
                    wG.hom.app (Discrete.mk ψ) ≫
                      colimit.ι ((morphism_family_functor U V).obj G) (Discrete.mk ψ) ≫
                      colimMap ((morphism_family_functor U V).map η) := by
                        simpa [Category.assoc] using
                          congrArg
                            (fun k ↦ wG.hom.app (Discrete.mk ψ) ≫ k)
                            (ι_colimMap ((morphism_family_functor U V).map η) (Discrete.mk ψ)).symm
                  _ =
                      colimit.ι
                          (LocalizationLeftKanExtension.indexFunctor U V ⋙
                            CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)
                          (Discrete.mk ψ) ≫
                        (HasColimit.isoOfNatIso wG).hom ≫
                        colimMap ((morphism_family_functor U V).map η) := by
                          simpa [Category.assoc] using
                            (HasColimit.isoOfNatIso_ι_hom_assoc wG (Discrete.mk ψ)
                              (colimMap ((morphism_family_functor U V).map η))).symm

/-- Helper for Remark 7.25.10: after evaluating at `V`, the owner-level colimit formula reduces to
the discrete morphism-family colimit before any sigma-type comparison is used. -/
noncomputable def lan_evaluation_colimit_component_iso
    (U V : C) [Functor.Final (LocalizationLeftKanExtension.indexFunctor U V)]
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) :
    colimit (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G) ≅
      colimit ((morphism_family_functor U V).obj G) :=
  (Functor.Final.colimitIso
      (LocalizationLeftKanExtension.indexFunctor U V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso
      (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
        (morphism_family_as_discrete U V G).symm)

/-- Helper for Remark 7.25.10: the evaluation-to-discrete-colimit comparison is natural in the
presheaf variable. -/
theorem lan_evaluation_iso_morphism_family_colimit_naturality
    (U V : C) [Functor.Final (LocalizationLeftKanExtension.indexFunctor U V)]
    {G H : (Over U)ᵒᵖ ⥤ Type (max u v)} (η : G ⟶ H) :
    ((((Over.forget U).op.lan :
            ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) ⋙
          (evaluation Cᵒᵖ (Type (max u v))).obj (op V)).map η) ≫
        (((Over.forget U).op.leftKanExtensionObjIsoColimit H (op V)) ≪≫
            lan_evaluation_colimit_component_iso U V H).hom =
      (((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)) ≪≫
          lan_evaluation_colimit_component_iso U V G).hom ≫
        ((morphism_family_functor U V ⋙
            (colim : (Discrete (V ⟶ U) ⥤ Type (max u v)) ⥤ Type (max u v))).map η) := by
  let fG :=
    Functor.Final.colimitIso
      (LocalizationLeftKanExtension.indexFunctor U V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)
  let fH :=
    Functor.Final.colimitIso
      (LocalizationLeftKanExtension.indexFunctor U V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ H)
  let pη :=
    colimMap ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η)
  let qη :=
    colimMap
      ((LocalizationLeftKanExtension.indexFunctor U V).whiskerLeft
        ((CostructuredArrow.proj (Over.forget U).op (op V)).whiskerLeft η))
  let rη := colimMap ((morphism_family_functor U V).map η)
  let iG :=
    HasColimit.isoOfNatIso
      (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
        (morphism_family_as_discrete U V G).symm)
  let iH :=
    HasColimit.isoOfNatIso
      (LocalizationLeftKanExtension.indexFunctorProjIso U H V ≪≫
        (morphism_family_as_discrete U V H).symm)
  have hLeft := leftKanExtensionObjIsoColimit_naturality (U := U) (V := V) η
  have hFinal := indexFunctor_colimitIso_naturality (U := U) (V := V) η
  have hProj := indexFunctorProjIso_colimit_naturality (U := U) (V := V) η
  have hFinal' : pη ≫ fH.inv = fG.inv ≫ qη := by
    calc
      pη ≫ fH.inv = fG.inv ≫ (fG.hom ≫ pη) ≫ fH.inv := by
        simp [Category.assoc]
      _ = fG.inv ≫ (qη ≫ fH.hom) ≫ fH.inv := by
        rw [hFinal]
      _ = fG.inv ≫ qη := by
        simp [Category.assoc]
  have hLeft' :
      ((((Over.forget U).op.lan :
                ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) ⋙
              (evaluation Cᵒᵖ (Type (max u v))).obj (op V)).map η) ≫
            ((Over.forget U).op.leftKanExtensionObjIsoColimit H (op V)).hom ≫
            fH.inv ≫ iH.hom =
        ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
          pη ≫ fH.inv ≫ iH.hom := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ fH.inv ≫ iH.hom) hLeft
  have hFinal'' :
      ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
          pη ≫ fH.inv ≫ iH.hom =
        ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
          fG.inv ≫ qη ≫ iH.hom := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫ k ≫ iH.hom)
        hFinal'
  have hProj' :
      ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
          fG.inv ≫ qη ≫ iH.hom =
        ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
          fG.inv ≫ iG.hom ≫ rη := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫ fG.inv ≫ k)
        hProj
  -- Route correction: after the owner-level naturality, the remaining proof is only cancellation
  -- of the finality and discrete-reindexing comparison isomorphisms.
  simpa [lan_evaluation_colimit_component_iso, rη, Functor.comp_map, colim_map, Category.assoc]
    using
      calc
        ((((Over.forget U).op.lan :
                ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) ⋙
                (evaluation Cᵒᵖ (Type (max u v))).obj (op V)).map η) ≫
              ((Over.forget U).op.leftKanExtensionObjIsoColimit H (op V)).hom ≫
              fH.inv ≫ iH.hom =
          ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
            pη ≫ fH.inv ≫ iH.hom := hLeft'
        _ = ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
              fG.inv ≫ qη ≫ iH.hom := hFinal''
        _ = ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
              fG.inv ≫ iG.hom ≫ rη := hProj'

/-- Helper for Remark 7.25.10: after evaluating at `V`, the left Kan extension agrees with the
discrete colimit of the fiber family `φ ↦ G(V \xrightarrow{φ} U)`. -/
noncomputable def lan_evaluation_iso_morphism_family_colimit
    (U V : C) :
    (((Over.forget U).op.lan :
          ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) ⋙
        (evaluation Cᵒᵖ (Type (max u v))).obj (op V)) ≅
      morphism_family_functor U V ⋙
        (colim : (Discrete (V ⟶ U) ⥤ Type (max u v)) ⥤ Type (max u v)) :=
  let _ : Functor.Final (LocalizationLeftKanExtension.indexFunctor U V) :=
    LocalizationLeftKanExtension.indexFunctor_final U V
  NatIso.ofComponents
    (fun G ↦
      ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)) ≪≫
        lan_evaluation_colimit_component_iso U V G)
    (fun {_ _} η ↦ lan_evaluation_iso_morphism_family_colimit_naturality U V η)

/-- Helper for Remark 7.25.10: evaluating `j_{U!}` at `V` is naturally the sigma-type functor. -/
noncomputable def lan_evaluation_iso_sigma_morphism_family
    (U V : C) :
    (((Over.forget U).op.lan :
          ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) ⋙
        (evaluation Cᵒᵖ (Type (max u v))).obj (op V)) ≅
      sigma_morphism_family_functor U V :=
  lan_evaluation_iso_morphism_family_colimit U V ≪≫ morphism_family_colimit_iso_sigma U V

/-- Helper for Remark 7.25.10: the direct sigma comparison in
`localization_leftKanExtension_objIsoSigma` matches the already-factored evaluation-to-sigma
comparison. -/
theorem localization_leftKanExtension_objIsoSigma_hom_eq_lan_evaluation_iso_sigma_hom
    (U V : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v)) :
    (localization_leftKanExtension_objIsoSigma U G V).hom =
      ((lan_evaluation_iso_sigma_morphism_family U V).app G).hom := by
  let _ : Functor.Final (LocalizationLeftKanExtension.indexFunctor U V) :=
    LocalizationLeftKanExtension.indexFunctor_final U V
  have hcomparison :
      (((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
          (Functor.Final.colimitIso
            (LocalizationLeftKanExtension.indexFunctor U V)
            (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm.hom) ≫
          (HasColimit.isoOfNatIso
              (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
                (morphism_family_as_discrete U V G).symm)).hom ≫
            (morphism_family_component_iso U V G).hom =
        (((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
            (Functor.Final.colimitIso
              (LocalizationLeftKanExtension.indexFunctor U V)
              (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm.hom) ≫
          (HasColimit.isoOfNatIso
              (LocalizationLeftKanExtension.indexFunctorProjIso U G V)).hom ≫
            (Types.coproductIso (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom := by
    -- Prefix the fixed coproduct comparison by the already-established owner/finality part.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          (((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
                (Functor.Final.colimitIso
                  (LocalizationLeftKanExtension.indexFunctor U V)
                  (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm.hom) ≫
            k)
        (indexFunctorProjIso_coproduct_comparison U V G)
  -- Route correction: the remaining work is only the fixed comparison between the direct
  -- coproduct map and the factored comparison through the discrete morphism family.
  change
    ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
        (Functor.Final.colimitIso
          (LocalizationLeftKanExtension.indexFunctor U V)
          (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm.hom ≫
          (HasColimit.isoOfNatIso
            (LocalizationLeftKanExtension.indexFunctorProjIso U G V)).hom ≫
            (Types.coproductIso (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom =
      ((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom ≫
        (Functor.Final.colimitIso
          (LocalizationLeftKanExtension.indexFunctor U V)
          (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm.hom ≫
          (HasColimit.isoOfNatIso
            (LocalizationLeftKanExtension.indexFunctorProjIso U G V ≪≫
              (morphism_family_as_discrete U V G).symm)).hom ≫
            (morphism_family_component_iso U V G).hom
  simpa [localization_leftKanExtension_objIsoSigma, lan_evaluation_iso_sigma_morphism_family,
    lan_evaluation_iso_morphism_family_colimit, lan_evaluation_colimit_component_iso,
    morphism_family_colimit_iso_sigma, Category.assoc] using hcomparison.symm

/-- Helper for Remark 7.25.10: the sigma-type formula for `j_{U!}` is natural in the presheaf
variable. -/
theorem localization_leftKanExtension_objIsoSigma_naturality
    (U V : C) {G H : (Over U)ᵒᵖ ⥤ Type (max u v)} (η : G ⟶ H) :
    ((((Over.forget U).op.lan :
            ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) ⋙
          (evaluation Cᵒᵖ (Type (max u v))).obj (op V)).map η) ≫
        (localization_leftKanExtension_objIsoSigma U H V).hom =
      (localization_leftKanExtension_objIsoSigma U G V).hom ≫
        (sigma_morphism_family_functor U V).map η := by
  -- Rewrite both endpoints to the already-natural factored comparison, then use ordinary
  -- naturality of the constructed isomorphism to the sigma functor.
  rw [localization_leftKanExtension_objIsoSigma_hom_eq_lan_evaluation_iso_sigma_hom U V H,
    localization_leftKanExtension_objIsoSigma_hom_eq_lan_evaluation_iso_sigma_hom U V G]
  simpa [Functor.comp_map, Category.assoc] using
    ((lan_evaluation_iso_sigma_morphism_family U V).hom.naturality η)

/-- Helper for Remark 7.25.10: evaluating `j_{U!}` at `V` preserves finite connected limits. -/
theorem lan_evaluation_preserves_finite_connected_limits
    (U V : C) (I : Type w) [SmallCategory I] [Small.{max u v} I] [FinCategory I]
    [IsConnected I] :
    PreservesLimitsOfShape I
      ((((Over.forget U).op.lan :
            ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) ⋙
          (evaluation Cᵒᵖ (Type (max u v))).obj (op V))) := by
  let _ :
      PreservesLimitsOfShape I
        (morphism_family_functor U V ⋙
          (colim : (Discrete (V ⟶ U) ⥤ Type (max u v)) ⥤ Type (max u v))) := by
    let _ :
        PreservesLimitsOfShape I
          (morphism_family_functor U V) :=
      morphism_family_functor_preserves_limits U V I
    let _ :
        PreservesLimitsOfShape I
          (colim : (Discrete (V ⟶ U) ⥤ Type (max u v)) ⥤ Type (max u v)) :=
      morphism_family_colimit_preserves_finite_connected_limits U V I
    infer_instance
  -- Transport the finite-connected-limit theorem back across the evaluation/colimit comparison.
  exact preservesLimitsOfShape_of_natIso (J := I) (lan_evaluation_iso_morphism_family_colimit U V).symm

-- Proof sketch: evaluate `j_{U!} = (Over.forget U).op.lan` at `V`, identify the value with the
-- discrete coproduct of the fibers `G(V ⟶ U)`, and use that such coproducts commute with finite
-- connected limits in `Type`.
theorem preservesFiniteConnectedLimits
    (U : C) (I : Type w) [SmallCategory I] [Small.{max u v} I] [FinCategory I]
    [IsConnected I] :
    PreservesLimitsOfShape I
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) := by
  -- Evaluation detects preservation of limits in a presheaf category.
  apply preservesLimitsOfShape_of_evaluation
  intro V
  simpa using lan_evaluation_preserves_finite_connected_limits (U := U) (V := unop V) (I := I)

end LocalizationLeftKanExtension

variable (U : C)

/- Remark 7.25.10 (1): the inverse-image functor on presheaves for localization at `U` is
restriction along `Over.forget U : Over U ⥤ C`, i.e. precomposition with `(Over.forget U).op`. -/
/- Remark 7.25.10 (2): the localization inverse-image functor on presheaves has the canonical left
adjoint `j_{U!}`, namely left Kan extension along `(Over.forget U).op`. -/

/- Remark 7.25.10 (3): the same inverse-image functor on presheaves has the canonical right adjoint
`j_{U*}`, namely right Kan extension along `(Over.forget U).op`. -/

/-- Remark 7.25.10 (1): the presheaf-level localization lower shriek `j_{U!}`, realized as left Kan
extension along `(Over.forget U).op`, commutes with fibre products. -/
theorem localization_leftKanExtension_preserves_pullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) :=
  LocalizationLeftKanExtension.preservesFiniteConnectedLimits U WalkingCospan

/-- Remark 7.25.10 (2): the presheaf-level localization lower shriek `j_{U!}`, realized as left Kan
extension along `(Over.forget U).op`, commutes with equalizers. -/
theorem localization_leftKanExtension_preserves_equalizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) :=
  LocalizationLeftKanExtension.preservesFiniteConnectedLimits U WalkingParallelPair

end
