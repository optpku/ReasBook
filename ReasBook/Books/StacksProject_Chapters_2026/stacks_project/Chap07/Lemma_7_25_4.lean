module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_25_2
public import stacks_project.Chap07.Lemma_7_25_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.25.4:
- primary domain: the localized site `(C / U, J.over U)` and its comparison with the slice topos
  `Sh(C, J) / h_U^#`;
- sampled owner API:
  `Functor.toOver`,
  `Functor.toOver_comp_forget`,
  `Functor.isTerminalConst`,
  `continuous_sheafified_representable_iso`;
- source/core/bridge triage:
  `source-facing`: the comparison functor from sheaves on `(C / U, J.over U)` to sheaves over
    `h_U^#`;
  `core/canonical`: the lower-shriek owner `(Over.forget U).sheafPullback ...`, the general
    `Functor.toOver` construction of a functor into a slice category, and the terminal-object
    owners for constant presheaves/sheaves;
  `bridge/view`: the canonical structure morphism
    `representableLocalizationHom`, giving the `toOver` specialization for the localized
    lower-shriek.

Primitive data are the lower-shriek functor and the canonical terminality of the identity object in
`Over U`. The comparison functor is derived from the owner abstraction `Functor.toOver`; the
terminal comparison on the representable side should therefore reuse the canonical terminal-object
owners rather than re-encoding pointwise uniqueness data.
-/

-- Proof sketch: `Over.mk (𝟙 U)` is terminal in `Over U`, so its representable presheaf is
-- canonically the terminal `PUnit`-valued presheaf. Passing to sheaves identifies the
-- sheafified representable with the canonical terminal sheaf on `(C/U, J.over U)`.
/-- The representable presheaf of the identity object in `Over U` is the constant terminal
`PUnit`-valued presheaf. -/
noncomputable def localized_identity_representable_iso_terminal (U : C) :
    ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
      (Over U)ᵒᵖ ⥤ Type (max u v)) ≅
        (Functor.const (Over U)ᵒᵖ).obj (PUnit : Type (max u v)) :=
  let yonedaOver : Over U ⥤ (Over U)ᵒᵖ ⥤ Type (max u v) :=
    CategoryTheory.uliftYoneda.{max u v}
  let hRep :
      IsTerminal
        ((yonedaOver.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max u v)) :=
    IsTerminal.isTerminalObj yonedaOver (Over.mk (𝟙 U)) Over.mkIdTerminal
  IsTerminal.uniqueUpToIso hRep <|
    Functor.isTerminalConst (Over U)ᵒᵖ Types.isTerminalPUnit

/-- The sheafified representable of the identity object in `Over U` is canonically the terminal
sheaf on the localized site. -/
noncomputable def localized_identity_sheafifiedRepresentable_iso_terminal
    (U : C) [HasWeakSheafify (J.over U) (Type (max u v))] :
    (J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)) ≅
      Sheaf.terminal (J.over U) Types.isTerminalPUnit := by
  simpa [GrothendieckTopology.sheafifiedRepresentable,
    GrothendieckTopology.uliftSheafifiedRepresentable] using
    (Functor.mapIso (presheafToSheaf (J.over U) (Type (max u v)))
      (localized_identity_representable_iso_terminal U) ≪≫
        (sheafificationIso (Sheaf.terminal (J.over U) Types.isTerminalPUnit)).symm)

/-- The sheafified representable of the identity arrow `U ⟶ U` is terminal on the localized site.
-/
noncomputable instance localized_identity_sheafifiedRepresentable_isTerminal
    (U : C) [HasWeakSheafify (J.over U) (Type (max u v))] :
    IsTerminal ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))) := by
  exact IsTerminal.ofIso
    (Sheaf.isTerminalTerminal (J.over U) Types.isTerminalPUnit)
    (localized_identity_sheafifiedRepresentable_iso_terminal J U).symm

section

variable (U : C)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/-- The canonical map from the lower-shriek image `j_{U!} 𝒢` to the sheafified representable
`h[U]^#[J]`. -/
noncomputable def representableLocalizationHom
    (𝒢 : Sheaf (J.over U) (Type (max u v))) :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj 𝒢 ⟶
      h[U]^#[J] :=
  ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
      ((localized_identity_sheafifiedRepresentable_isTerminal J U).from 𝒢) ≫
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
      (Over.mk (𝟙 U))).symm.hom

-- Proof sketch: functoriality of `j_{U!}` carries any morphism `η : 𝒢 ⟶ 𝒢'` to a commutative
-- triangle with the terminal arrows to the identity representable, so the induced maps to
-- `h[U]^#[J]` are natural.
/-- Naturality of the canonical maps `j_{U!} 𝒢 ⟶ h[U]^#[J]`. -/
theorem representableLocalizationHom_naturality
    {𝒢 𝒢' : Sheaf (J.over U) (Type (max u v))} (η : 𝒢 ⟶ 𝒢') :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map η ≫
        J.representableLocalizationHom U 𝒢' =
      J.representableLocalizationHom U 𝒢 := by
  -- The two maps to the terminal sheafified representable coincide by uniqueness.
  have hterminal :
      η ≫ (localized_identity_sheafifiedRepresentable_isTerminal J U).from 𝒢' =
        (localized_identity_sheafifiedRepresentable_isTerminal J U).from 𝒢 := by
    exact (localized_identity_sheafifiedRepresentable_isTerminal J U).hom_ext _ _
  -- Apply `j_{U!}` to the unique terminal morphism and reassociate once.
  rw [representableLocalizationHom, representableLocalizationHom, ← Category.assoc,
    ← Functor.map_comp]
  rw [hterminal]

/-- The comparison functor from sheaves on the slice site `(C/U, J.over U)` to sheaves over the
sheafified representable `h[U]^#[J]`. -/
noncomputable def representableLocalizationComparison
    :
    Sheaf (J.over U) (Type (max u v)) ⥤ Over h[U]^#[J] :=
  ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).toOver
    h[U]^#[J]
    (J.representableLocalizationHom U)
    (J.representableLocalizationHom_naturality U)

/-- Forgetting the structure morphism from the representable-localization comparison functor
recovers the canonical lower-shriek `j_{U!}`. -/
@[simp] theorem representableLocalizationComparison_forget
    :
    J.representableLocalizationComparison U ⋙ Over.forget h[U]^#[J] =
      (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J := by
  rw [representableLocalizationComparison]
  exact Functor.toOver_comp_forget
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J)
    h[U]^#[J]
    (J.representableLocalizationHom U)
    (J.representableLocalizationHom_naturality U)

namespace RepresentableLocalizationComparison

/-- Helper for Lemma 7.25.4: package the family `φ ↦ G(V ⟶ U via φ)` as a discrete diagram. -/
abbrev morphismIndexFunctor
    (V : C) : Discrete (V ⟶ U) ⥤ (Over U)ᵒᵖ :=
  Discrete.functor fun φ ↦ op (Over.mk φ)

/-- Helper for Lemma 7.25.4: evaluate a presheaf on `Over U` on the discrete family of arrows
`V ⟶ U`. -/
abbrev morphism_family_functor
    (V : C) :
    ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Discrete (V ⟶ U) ⥤ Type (max u v)) :=
  (Functor.whiskeringLeft (Discrete (V ⟶ U)) (Over U)ᵒᵖ (Type (max u v))).obj
    (morphismIndexFunctor (U := U) V)

/-- Helper for Lemma 7.25.4: the sigma-type functor collecting all fibres
`G(V \xrightarrow{} U)` at once. -/
def sigma_morphism_family_functor
    (V : C) : ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ Type (max u v) where
  obj G := Σ φ : V ⟶ U, G.obj (op (Over.mk φ))
  map η := fun x ↦ ⟨x.1, η.app (op (Over.mk x.1)) x.2⟩
  map_id G := by
    funext x
    cases x
    rfl
  map_comp η θ := by
    funext x
    cases x
    rfl

/-- Helper for Lemma 7.25.4: the discrete family of terminal objects in the indexing category for
the objectwise left-Kan-extension formula along `(Over.forget U).op`. -/
abbrev indexFunctor
    (V : C) : Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (op V) :=
  Discrete.functor fun φ ↦
    CostructuredArrow.mk
      (show (Over.forget U).op.obj (op (Over.mk φ)) ⟶ op V from 𝟙 (op V))

/-- Helper for Lemma 7.25.4: the underlying object in `Over U` attached to a costructured arrow
over `(Over.forget U).op`. -/
abbrev overObj
    {V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Over U :=
  X.left.unop

/-- Helper for Lemma 7.25.4: the leg `V ⟶ A` of the underlying triangle `V ⟶ A ⟶ U`. -/
abbrev leg
    {V : C} (X : CostructuredArrow (Over.forget U).op (op V)) :
    V ⟶ (overObj (U := U) X).left :=
  X.hom.unop

/-- Helper for Lemma 7.25.4: the composite `V ⟶ U` attached to a costructured arrow over
`(Over.forget U).op`. -/
abbrev composite
    {V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : V ⟶ U :=
  leg (U := U) X ≫ (overObj (U := U) X).hom

/-- Helper for Lemma 7.25.4: the discrete index determined by the commutative triangle underlying
`X`. -/
abbrev index
    {V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Discrete (V ⟶ U) :=
  Discrete.mk (composite (U := U) X)

/-- Helper for Lemma 7.25.4: the distinguished morphism from an indexing object to the terminal
object in its fibre. -/
abbrev terminalHom
    (V : C) {X : CostructuredArrow (Over.forget U).op (op V)} :
    X ⟶ (indexFunctor (U := U) V).obj (index (U := U) X) :=
  CostructuredArrow.homMk
    ((show Over.mk (composite (U := U) X) ⟶ overObj (U := U) X from
        Over.homMk (leg (U := U) X)).op)
    (by
      simp [indexFunctor, index, leg])

/-- Helper for Lemma 7.25.4: any morphism in the indexing category preserves the composite
`V ⟶ U`. -/
lemma composite_eq_of_map
    (V : C) {X Y : CostructuredArrow (Over.forget U).op (op V)} (hom : X ⟶ Y) :
    composite (U := U) X = composite (U := U) Y := by
  let triangle : overObj (U := U) Y ⟶ overObj (U := U) X := hom.left.unop
  have hleg : leg (U := U) Y ≫ triangle.left = leg (U := U) X := by
    have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
    simpa [triangle] using h
  have hw : triangle.left ≫ (overObj (U := U) X).hom = (overObj (U := U) Y).hom := Over.w triangle
  dsimp [composite]
  calc
    leg (U := U) X ≫ (overObj (U := U) X).hom =
        (leg (U := U) Y ≫ triangle.left) ≫ (overObj (U := U) X).hom := by
      rw [hleg]
    _ = leg (U := U) Y ≫ (triangle.left ≫ (overObj (U := U) X).hom) := by
      rw [Category.assoc]
    _ = leg (U := U) Y ≫ (overObj (U := U) Y).hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ leg (U := U) Y ≫ k) hw

/-- Helper for Lemma 7.25.4: any map into the chosen terminal object is indexed by the composite
of the source triangle. -/
lemma composite_eq_of_hom
    (V : C) {X : CostructuredArrow (Over.forget U).op (op V)}
    {φ : V ⟶ U} (hom : X ⟶ (indexFunctor (U := U) V).obj (Discrete.mk φ)) :
    composite (U := U) X = φ := by
  simpa [indexFunctor, composite, leg, overObj] using composite_eq_of_map (U := U) V hom

/-- Helper for Lemma 7.25.4: reindex a costructured arrow by an explicitly identified composite
`V ⟶ U`. -/
def homToIndex
    (V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite (U := U) X = φ) :
    X ⟶ (indexFunctor (U := U) V).obj (Discrete.mk φ) := by
  cases hφ
  exact terminalHom (U := U) V

/-- Helper for Lemma 7.25.4: a morphism into the chosen terminal object is unique. -/
lemma hom_eq_terminalHom
    (V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (hom : X ⟶ (indexFunctor (U := U) V).obj (index (U := U) X)) :
    hom = terminalHom (U := U) V := by
  ext
  exact by
    apply Quiver.Hom.unop_inj
    apply CommaMorphism.ext
    · have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
      simpa [indexFunctor] using h
    · simp [Over.homMk]

/-- Helper for Lemma 7.25.4: the canonical map into a chosen indexed terminal object is unique. -/
lemma hom_eq_homToIndex
    (V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : composite (U := U) X = φ)
    (hom : X ⟶ (indexFunctor (U := U) V).obj (Discrete.mk φ)) :
    hom = homToIndex (U := U) V X φ hφ := by
  cases hφ
  simpa [homToIndex] using hom_eq_terminalHom (U := U) V X hom

/-- Helper for Lemma 7.25.4: the indexing category remembers only the composite map `V ⟶ U`. -/
abbrev compositeFunctor
    (V : C) :
    CostructuredArrow (Over.forget U).op (op V) ⥤ Discrete (V ⟶ U) where
  obj X := Discrete.mk (composite (U := U) X)
  map hom := Discrete.eqToHom (composite_eq_of_map (U := U) V hom)

/-- Helper for Lemma 7.25.4: the discrete inclusion of indices is right adjoint to the functor
remembering only the composite `V ⟶ U`. -/
def compositeIndexAdjunction (V : C) :
    compositeFunctor (U := U) V ⊣ indexFunctor (U := U) V :=
  Adjunction.mkOfHomEquiv
    { homEquiv := by
        intro X φ
        cases φ with
        | mk ψ =>
            refine
              { toFun := fun hom ↦ homToIndex (U := U) V X ψ (Discrete.eq_of_hom hom)
                invFun := fun hom ↦ Discrete.eqToHom (composite_eq_of_hom (U := U) V hom)
                left_inv := ?_
                right_inv := ?_ }
            · intro hom
              apply Subsingleton.elim
            · intro hom
              simpa using
                (hom_eq_homToIndex (U := U) V X ψ (composite_eq_of_hom (U := U) V hom) hom).symm
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
                  (hom_eq_homToIndex (U := U) V X ψ'
                    (by simpa using Discrete.eq_of_hom (hom ≫ g))
                    (homToIndex (U := U) V X ψ (Discrete.eq_of_hom hom) ≫
                      (indexFunctor (U := U) V).map g)).symm
                simpa [homToIndex] using congrArg CommaMorphism.left h }

/-- Helper for Lemma 7.25.4: the discrete inclusion of the chosen terminal objects is final. -/
theorem indexFunctor_final (V : C) :
    Functor.Final (indexFunctor (U := U) V) := by
  let _ : (indexFunctor (U := U) V).IsRightAdjoint :=
    ⟨⟨compositeFunctor (U := U) V, ⟨compositeIndexAdjunction (U := U) V⟩⟩⟩
  infer_instance

/-- Helper for Lemma 7.25.4: the restricted indexing diagram is literally the discrete family
`φ ↦ G(V \xrightarrow{φ} U)`. -/
abbrev indexFunctorProjIso
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) (V : C) :
    indexFunctor (U := U) V ⋙ CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G ≅
      Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) := by
  refine Discrete.natIso ?_
  intro φ
  exact Iso.refl _

/-- Helper for Lemma 7.25.4: the canonical left Kan extension along `(Over.forget U).op` is
objectwise the coproduct of the fibres `G(V \xrightarrow{} U)` over all arrows `V ⟶ U`. -/
noncomputable def localization_leftKanExtension_objIsoSigma
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) (V : C) :
    (((Over.forget U).op.lan.obj G).obj (op V)) ≅ Σ φ : V ⟶ U, G.obj (op (Over.mk φ)) :=
  letI : Functor.Final (indexFunctor (U := U) V) := indexFunctor_final (U := U) V
  (Over.forget U).op.leftKanExtensionObjIsoColimit G (op V) ≪≫
    (Functor.Final.colimitIso
      (indexFunctor (U := U) V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso (indexFunctorProjIso (U := U) G V) ≪≫
    Types.coproductIso (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))

/-- Helper for Lemma 7.25.4: in the sigma-model for the left Kan extension, the fibre over
`X.hom : X.left ⟶ U` is exactly `G(X)`. -/
noncomputable def fiber_of_localization_sigma_iso
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) (X : Over U) :
    { s : (((Over.forget U).op.lan.obj G).obj (op X.left)) //
        ((localization_leftKanExtension_objIsoSigma (U := U) G X.left).hom s).1 = X.hom } ≅
      G.obj (op X) := by
  let e := localization_leftKanExtension_objIsoSigma (U := U) G X.left
  let e₁ :
      { s : (((Over.forget U).op.lan.obj G).obj (op X.left)) // (e.hom s).1 = X.hom } ≃
        { t : Σ φ : X.left ⟶ U, G.obj (op (Over.mk φ)) // t.1 = X.hom } :=
    Equiv.subtypeEquiv e.toEquiv (by
      intro s
      simp)
  let e₂ :
      { t : Σ φ : X.left ⟶ U, G.obj (op (Over.mk φ)) // t.1 = X.hom } ≃
        G.obj (op X) := by
      refine
        { toFun := fun t ↦ ?_
          invFun := fun x ↦ ?_
          left_inv := ?_
          right_inv := ?_ }
      · rcases t with ⟨⟨φ, x⟩, hφ⟩
        cases hφ
        cases X
        simpa using x
      · refine ⟨⟨X.hom, ?_⟩, rfl⟩
        have hX : Over.mk X.hom = X := by
          cases X
          rfl
        simpa [hX] using x
      · rintro ⟨⟨φ, x⟩, hφ⟩
        cases hφ
        cases X
        rfl
      · intro x
        cases X
        rfl
  exact (e₁.trans e₂).toIso

/-- Helper for Lemma 7.25.4: a set is the disjoint union of the fibres of any map to
`(V ⟶ U)`. -/
noncomputable def sigma_of_fibres_iso_self
    (P : Over ((CategoryTheory.uliftYoneda.{max u v}.obj U) : Cᵒᵖ ⥤ Type (max u v))) (V : C) :
    (Σ a : V ⟶ U,
      { s : P.left.obj (op V) // (P.hom.app (op V) s).down = a }) ≅
        P.left.obj (op V) :=
  (Equiv.sigmaFiberEquiv fun s : P.left.obj (op V) => (P.hom.app (op V) s).down).toIso

/-- Helper for Lemma 7.25.4: the raw representable presheaf `h_U` on `C`. -/
abbrev representable_presheaf : Cᵒᵖ ⥤ Type (max u v) :=
  ((CategoryTheory.uliftYoneda.{max u v}.obj U) : Cᵒᵖ ⥤ Type (max u v))

/-- Helper for Lemma 7.25.4: restriction along a morphism in `Over U` preserves the defining
fibre condition in the textbook inverse construction. -/
theorem fiber_presheaf_map_property
    (P : Over (representable_presheaf (U := U))) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    (s : { t : P.left.obj (op X.unop.left) //
        (P.hom.app (op X.unop.left) t).down = X.unop.hom }) :
    (P.hom.app (op Y.unop.left) (P.left.map f.unop.left.op s.1)).down = Y.unop.hom := by
  -- Restrict the chosen section and rewrite its image in the representable using naturality.
  have hnat := congrFun (P.hom.naturality f.unop.left.op) s.1
  dsimp at hnat
  rw [s.2] at hnat
  exact Eq.trans (congrArg ULift.down hnat) (Over.w f.unop)

/-- Helper for Lemma 7.25.4: the restriction map on the fibre over a representable section. -/
def fiber_presheaf_map
    (P : Over (representable_presheaf (U := U))) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    { t : P.left.obj (op X.unop.left) // (P.hom.app (op X.unop.left) t).down = X.unop.hom } →
      { t : P.left.obj (op Y.unop.left) // (P.hom.app (op Y.unop.left) t).down = Y.unop.hom } :=
  fun s ↦ ⟨P.left.map f.unop.left.op s.1, fiber_presheaf_map_property (U := U) P f s⟩

/-- Helper for Lemma 7.25.4: the fibre restriction map is the identity on identity morphisms. -/
theorem fiber_presheaf_map_id
    (P : Over (representable_presheaf (U := U))) (X : (Over U)ᵒᵖ) :
    fiber_presheaf_map (U := U) P (𝟙 X) = id := by
  -- The underlying restriction on sections is the identity map.
  funext s
  apply Subtype.ext
  simp [fiber_presheaf_map]

/-- Helper for Lemma 7.25.4: the fibre restriction maps compose as expected. -/
theorem fiber_presheaf_map_comp
    (P : Over (representable_presheaf (U := U))) {X Y Z : (Over U)ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber_presheaf_map (U := U) P (f ≫ g) =
      fiber_presheaf_map (U := U) P g ∘ fiber_presheaf_map (U := U) P f := by
  -- Both sides are the same iterated restriction on the underlying section.
  funext s
  apply Subtype.ext
  simp [fiber_presheaf_map, FunctorToTypes.map_comp_apply]

/-- Helper for Lemma 7.25.4: a morphism over `h_U` preserves the fibre condition objectwise. -/
theorem fiber_presheaf_hom_property
    {P Q : Over (representable_presheaf (U := U))} (α : P ⟶ Q) (X : (Over U)ᵒᵖ)
    (s : { t : P.left.obj (op X.unop.left) //
        (P.hom.app (op X.unop.left) t).down = X.unop.hom }) :
    (Q.hom.app (op X.unop.left) (α.left.app (op X.unop.left) s.1)).down = X.unop.hom := by
  -- The square in the over category says the section stays above the same arrow `X ⟶ U`.
  have hcomp := congrFun (NatTrans.congr_app (Over.w α) (op X.unop.left)) s.1
  dsimp at hcomp
  exact (congrArg ULift.down hcomp).trans s.2

/-- Helper for Lemma 7.25.4: the objectwise map on fibres induced by a morphism over `h_U`. -/
def fiber_presheaf_hom
    {P Q : Over (representable_presheaf (U := U))} (α : P ⟶ Q) (X : (Over U)ᵒᵖ) :
    { t : P.left.obj (op X.unop.left) // (P.hom.app (op X.unop.left) t).down = X.unop.hom } →
      { t : Q.left.obj (op X.unop.left) // (Q.hom.app (op X.unop.left) t).down = X.unop.hom } :=
  fun s ↦ ⟨α.left.app (op X.unop.left) s.1, fiber_presheaf_hom_property (U := U) α X s⟩

/-- Helper for Lemma 7.25.4: the textbook fibre construction defines a presheaf on `C/U` from a
raw object over the representable presheaf `h_U`. -/
def fiber_presheaf_over_representable :
    Over (representable_presheaf (U := U)) ⥤ (Over U)ᵒᵖ ⥤ Type (max u v) where
  obj P :=
    { obj := fun X =>
        { t : P.left.obj (op X.unop.left) // (P.hom.app (op X.unop.left) t).down = X.unop.hom }
      map := fiber_presheaf_map (U := U) P
      map_id := fiber_presheaf_map_id (U := U) P
      map_comp := fiber_presheaf_map_comp (U := U) P }
  map α :=
    { app := fiber_presheaf_hom (U := U) α
      naturality := by
        intro X Y f
        funext s
        apply Subtype.ext
        simpa [fiber_presheaf_hom, fiber_presheaf_map] using
          congrFun (α.left.naturality f.unop.left.op) s.1 }
  map_id P := by
    ext X s
    rfl
  map_comp α β := by
    ext X s
    rfl

/-- Helper for Lemma 7.25.4: pull back a slice object over the sheafified representable `h_U^#`
to a raw slice object over the representable presheaf `h_U`. -/
noncomputable def pullback_to_representable :
    Over h[U]^#[J] ⥤ Over (representable_presheaf (U := U)) := by
  -- The source-proof bridge pulls back along the sheafification unit of `h_U`.
  simpa [GrothendieckTopology.sheafifiedRepresentable,
    GrothendieckTopology.uliftSheafifiedRepresentable] using
    (Over.post (sheafToPresheaf J (Type (max u v))) ⋙
      Over.pullback
        ((sheafificationAdjunction J (Type (max u v))).unit.app
          (representable_presheaf (U := U))))

/-- Helper for Lemma 7.25.4: the candidate inverse functor obtained by taking the textbook fibre
presheaf over `h_U` and then sheafifying on `(C/U, J.over U)`. -/
noncomputable def comparison_inverse :
    Over h[U]^#[J] ⥤ Sheaf (J.over U) (Type (max u v)) := by
  -- The source-proof inverse first forgets to the raw slice over `h_U`, then takes fibres, and
  -- finally sheafifies on the localized site.
  simpa using
    (pullback_to_representable (J := J) (U := U) ⋙
      fiber_presheaf_over_representable (U := U) ⋙
      presheafToSheaf (J.over U) (Type (max u v)))

/-- Helper for Lemma 7.25.4: the canonical recovery morphism from the sheafified pullback back to
the original slice object over `h_U^#`. -/
noncomputable def sheafified_pullback_recovery_hom
    (T : Over h[U]^#[J]) :
    ((pullback_to_representable (J := J) (U := U) ⋙
          Over.post (presheafToSheaf J (Type (max u v)))).obj T) ⟶
      T := by
  -- This is the counit of the slice adjunction induced by sheafification.
  simpa [pullback_to_representable] using
    ((Over.postAdjunctionLeft (X := representable_presheaf (U := U))
      (sheafificationAdjunction J (Type (max u v)))).counit.app T)

/-- Helper for Lemma 7.25.4: after sheafification, the unit map
`h_U ⟶ (h_U^#).val` becomes an isomorphism. -/
lemma representable_unit_map_isIso :
    IsIso
      ((presheafToSheaf J (Type (max u v))).map
        ((sheafificationAdjunction J (Type (max u v))).unit.app
          (representable_presheaf (U := U)))) := by
  -- Sheafification inverts each unit map `toSheafify`.
  exact (J.W_iff _).1 (J.W_toSheafify (representable_presheaf (U := U)))

/-- Helper for Lemma 7.25.4: the left component of the slice-adjunction counit is the mapped
pullback projection followed by the sheafification counit on `T.left`. -/
theorem sheafified_pullback_recovery_hom_left
    (T : Over h[U]^#[J]) :
    (sheafified_pullback_recovery_hom (J := J) (U := U) T).left =
      (presheafToSheaf J (Type (max u v))).map
          (pullback.fst
            ((sheafToPresheaf J (Type (max u v))).map T.hom)
            ((sheafificationAdjunction J (Type (max u v))).unit.app
              (representable_presheaf (U := U)))) ≫
        (sheafificationAdjunction J (Type (max u v))).counit.app T.left := by
  -- This is the explicit left-component formula supplied by the owner adjunction on over
  -- categories.
  simpa [sheafified_pullback_recovery_hom, pullback_to_representable] using
    (Over.postAdjunctionLeft_counit_app_left
      (a := sheafificationAdjunction J (Type (max u v))) T)

/-- Helper for Lemma 7.25.4: the mapped pullback projection appearing in the slice counit is an
isomorphism after sheafification. -/
lemma sheafified_pullback_projection_isIso
    (T : Over h[U]^#[J]) :
    IsIso
      ((presheafToSheaf J (Type (max u v))).map
        (pullback.fst
          ((sheafToPresheaf J (Type (max u v))).map T.hom)
            ((sheafificationAdjunction J (Type (max u v))).unit.app
              (representable_presheaf (U := U))))) := by
  -- Transport the pullback first projection across the owner pullback comparison for
  -- `presheafToSheaf`, where the right leg is already inverted by sheafification.
  let F := presheafToSheaf J (Type (max u v))
  let f := (sheafToPresheaf J (Type (max u v))).map T.hom
  let g := (sheafificationAdjunction J (Type (max u v))).unit.app
    (representable_presheaf (U := U))
  have hunitIso : IsIso (F.map g) := representable_unit_map_isIso (J := J) (U := U)
  letI : IsIso (F.map g) := hunitIso
  letI : HasPullback (F.map f) (F.map g) :=
    @Limits.hasPullback_of_right_iso _ _ _ _ _ (F.map f) (F.map g) hunitIso
  have hfstIso : IsIso (pullback.fst (F.map f) (F.map g)) :=
    @Limits.pullback_fst_iso_of_right_iso _ _ _ _ _ (F.map f) (F.map g) hunitIso
  have hcomparison_iso :
      IsIso ((PreservesPullback.iso F f g).hom ≫ pullback.fst (F.map f) (F.map g)) :=
    CategoryTheory.IsIso.comp_isIso' inferInstance hfstIso
  change IsIso (F.map (pullback.fst f g))
  rw [← PreservesPullback.iso_hom_fst F f g]
  exact hcomparison_iso

/-- Helper for Lemma 7.25.4: the left component of the slice counit is an isomorphism. -/
lemma sheafified_pullback_recovery_hom_left_isIso
    (T : Over h[U]^#[J]) :
    IsIso ((sheafified_pullback_recovery_hom (J := J) (U := U) T).left) := by
  -- Rewrite the left component into the explicit composition of the mapped pullback projection
  -- and the sheafification counit, both already known to be isomorphisms.
  let A :=
    (presheafToSheaf J (Type (max u v))).map
      (pullback.fst
        ((sheafToPresheaf J (Type (max u v))).map T.hom)
        ((sheafificationAdjunction J (Type (max u v))).unit.app
          (representable_presheaf (U := U))))
  letI : IsIso A := sheafified_pullback_projection_isIso (J := J) (U := U) T
  have hCounit : IsIso ((sheafificationAdjunction J (Type (max u v))).counit.app T.left) := by
    infer_instance
  rw [sheafified_pullback_recovery_hom_left]
  change IsIso (A ≫ (sheafificationAdjunction J (Type (max u v))).counit.app T.left)
  exact IsIso.comp_isIso' (inferInstance : IsIso A) hCounit

/-- Helper for Lemma 7.25.4: the slice counit from pulling back along `h_U ⟶ h_U^#` and then
sheafifying is natural in the slice object. -/
theorem sheafified_pullback_recovery_hom_naturality
    {T T' : Over h[U]^#[J]} (α : T ⟶ T') :
    (pullback_to_representable (J := J) (U := U) ⋙
          Over.post (presheafToSheaf J (Type (max u v)))).map α ≫
        sheafified_pullback_recovery_hom (J := J) (U := U) T' =
      sheafified_pullback_recovery_hom (J := J) (U := U) T ≫ α := by
  -- This is the naturality square of the counit of the induced adjunction on over categories.
  simpa [sheafified_pullback_recovery_hom, pullback_to_representable] using
    (Over.postAdjunctionLeft
      (X := representable_presheaf (U := U))
      (sheafificationAdjunction J (Type (max u v)))).counit.naturality α

/-- Helper for Lemma 7.25.4: the slice counit obtained by pulling back along `h_U ⟶ h_U^#` and
then sheafifying is already a natural isomorphism. -/
noncomputable def sheafified_pullback_recovery_natIso :
    pullback_to_representable (J := J) (U := U) ⋙
        Over.post (presheafToSheaf J (Type (max u v))) ≅
      𝟭 (Over h[U]^#[J]) := by
  -- Package the already-identified slice counit as an `Over`-isomorphism componentwise, then use
  -- the adjunction counit's naturality to show those components form a natural isomorphism.
  refine NatIso.ofComponents (fun T ↦ ?_) ?_
  · let e :
        ((pullback_to_representable (J := J) (U := U) ⋙
            Over.post (presheafToSheaf J (Type (max u v)))).obj T).left ≅
          T.left := by
      letI : IsIso ((sheafified_pullback_recovery_hom (J := J) (U := U) T).left) :=
        sheafified_pullback_recovery_hom_left_isIso (J := J) (U := U) T
      exact asIso ((sheafified_pullback_recovery_hom (J := J) (U := U) T).left)
    refine Over.isoMk e ?_
    change e.hom ≫ T.hom =
      ((pullback_to_representable (J := J) (U := U) ⋙
          Over.post (presheafToSheaf J (Type (max u v)))).obj T).hom
    simpa [e] using Over.w (sheafified_pullback_recovery_hom (J := J) (U := U) T)
  · intro T T' α
    apply Over.OverMorphism.ext
    simpa [Over.comp_left, sheafified_pullback_recovery_hom_left] using
      congrArg (fun f ↦ f.left)
        (sheafified_pullback_recovery_hom_naturality (J := J) (U := U) α)

/-- Helper for Lemma 7.25.4: the sigma-model for the left Kan extension sends the canonical
generator coming from `leftKanExtensionUnit` to the corresponding summand. -/
theorem localization_leftKanExtension_objIsoSigma_hom_unit_app
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) {V : C} (a : V ⟶ U)
    (s : G.obj (op (Over.mk a))) :
    (localization_leftKanExtension_objIsoSigma (U := U) G V).hom
        ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s) =
      ⟨a, s⟩ := by
  -- The sigma-model is built from four owner isomorphisms; on the canonical generator, each one
  -- has an explicit formula, so the composite lands in the expected coproduct summand.
  let F₁ :=
    indexFunctor (U := U) V
  let F₂ :=
    CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G
  let F₃ :=
    Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))
  letI : Functor.Final F₁ := indexFunctor_final (U := U) V
  have h₀ :=
    congrFun
      (Functor.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom
        (L := (Over.forget U).op) (F := G) (X := op (Over.mk a)))
      s
  have h₁ :=
    congrFun
      (Functor.Final.ι_colimitIso_inv
        (F := F₁) (G := F₂) (X := Discrete.mk a))
      s
  have h₂ :=
    congrFun
      (HasColimit.isoOfNatIso_ι_hom
        (w := indexFunctorProjIso (U := U) G V) (j := Discrete.mk a))
      s
  have h₃ :=
    congrFun
      (Types.coproductIso_ι_comp_hom
        (F := fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) a)
      s
  calc
    (localization_leftKanExtension_objIsoSigma (U := U) G V).hom
        ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s)
        =
          (Types.coproductIso fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))).hom
            ((HasColimit.isoOfNatIso (indexFunctorProjIso (U := U) G V)).hom
              ((Functor.Final.colimitIso F₁ F₂).inv
                (((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom
                  ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s)))) := by
      rfl
    _ =
          (Types.coproductIso fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))).hom
            ((HasColimit.isoOfNatIso (indexFunctorProjIso (U := U) G V)).hom
              ((Functor.Final.colimitIso F₁ F₂).inv
                (colimit.ι F₂ (F₁.obj (Discrete.mk a)) s))) := by
      simpa [F₁, indexFunctor] using congrArg
        ((Types.coproductIso fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))).hom ∘
          (HasColimit.isoOfNatIso (indexFunctorProjIso (U := U) G V)).hom ∘
            (Functor.Final.colimitIso F₁ F₂).inv) h₀
    _ =
          (Types.coproductIso fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))).hom
            ((HasColimit.isoOfNatIso (indexFunctorProjIso (U := U) G V)).hom
              (colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s)) := by
      have h₁' :
          ((Functor.Final.colimitIso F₁ F₂).inv
              (colimit.ι F₂ (F₁.obj (Discrete.mk a)) s)) =
            colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s := by
        simpa [F₁, F₂, indexFunctor] using h₁
      exact congrArg
        ((Types.coproductIso fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))).hom ∘
          (HasColimit.isoOfNatIso (indexFunctorProjIso (U := U) G V)).hom) h₁'
    _ =
          (Types.coproductIso fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))).hom
            (colimit.ι F₃ (Discrete.mk a) s) := by
      have h₂' :
          (HasColimit.isoOfNatIso (indexFunctorProjIso (U := U) G V)).hom
              (colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s) =
            colimit.ι F₃ (Discrete.mk a) s := by
        simpa [F₁, F₂, F₃, indexFunctorProjIso] using h₂
      exact congrArg
        ((Types.coproductIso fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))).hom) h₂'
    _ = ⟨a, s⟩ := by
      simpa [F₃] using h₃

/-- Helper for Lemma 7.25.4: the inverse sigma-model sends a chosen summand back to the canonical
left-Kan-extension generator. -/
theorem localization_leftKanExtension_objIsoSigma_inv_mk
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) {V : C} (a : V ⟶ U)
    (s : G.obj (op (Over.mk a))) :
    (localization_leftKanExtension_objIsoSigma (U := U) G V).inv ⟨a, s⟩ =
      (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s := by
  -- Apply the inverse sigma-model and cancel it against the generator computation above.
  apply (localization_leftKanExtension_objIsoSigma (U := U) G V).toEquiv.injective
  simp [localization_leftKanExtension_objIsoSigma_hom_unit_app]

/-- Helper for Lemma 7.25.4: the canonical over-arrow induced by `f : Y ⟶ V`. -/
abbrev representableLocalizationOverHomMk {U V Y : C} {φ : V ⟶ U} (f : Y ⟶ V) :
    Over.mk (f ≫ φ) ⟶ Over.mk φ :=
  Over.homMk f

/-- Helper for Lemma 7.25.4: in the sigma-model for the left Kan extension, restriction along
`f : Y ⟶ V` carries the summand indexed by `a : V ⟶ U` to the summand indexed by `f ≫ a`. -/
theorem localization_leftKanExtension_objIsoSigma_hom_map
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) {V Y : C} (f : Y ⟶ V)
    (x : (((Over.forget U).op.lan.obj G).obj (op V))) :
    (localization_leftKanExtension_objIsoSigma (U := U) G Y).hom
        (((Over.forget U).op.lan.obj G).map f.op x) =
      ⟨f ≫ ((localization_leftKanExtension_objIsoSigma (U := U) G V).hom x).1,
        G.map
          (representableLocalizationOverHomMk
            (U := U) (φ := ((localization_leftKanExtension_objIsoSigma (U := U) G V).hom x).1)
            f).op
          ((localization_leftKanExtension_objIsoSigma (U := U) G V).hom x).2⟩ := by
  -- Write `x` as the inverse image of its sigma coordinates, then use the naturality of the left
  -- Kan extension unit along the canonical map `Over.mk (f ≫ a) ⟶ Over.mk a`.
  rcases hV : (localization_leftKanExtension_objIsoSigma (U := U) G V).hom x with ⟨a, s⟩
  rw [← hV]
  have hx :
      x =
        (localization_leftKanExtension_objIsoSigma (U := U) G V).inv ⟨a, s⟩ := by
    apply (localization_leftKanExtension_objIsoSigma (U := U) G V).toEquiv.injective
    simp [hV]
  rw [hx, localization_leftKanExtension_objIsoSigma_inv_mk (U := U) G a s]
  let g : Over.mk (f ≫ a) ⟶ Over.mk a :=
    representableLocalizationOverHomMk (U := U) (φ := a) f
  have hnat :=
    congrFun (((Over.forget U).op.leftKanExtensionUnit G).naturality g.op) s
  dsimp at hnat
  have hnat' :
      (((Over.forget U).op.lan.obj G).map f.op
          ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s)) =
        (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk (f ≫ a))))
          (G.map g.op s) := by
    simpa [g] using hnat.symm
  rw [hnat']
  rw [localization_leftKanExtension_objIsoSigma_hom_unit_app (U := U) G a s]
  simpa using
    localization_leftKanExtension_objIsoSigma_hom_unit_app (U := U) G (f ≫ a)
      (G.map g.op s)

/-- Helper for Lemma 7.25.4: in the sigma-model for the left Kan extension, the map induced by a
natural transformation acts only on the fibre coordinate. -/
theorem localization_leftKanExtension_objIsoSigma_hom_natTrans
    {G G' : (Over U)ᵒᵖ ⥤ Type (max u v)} (η : G ⟶ G') {V : C}
    (x : (((Over.forget U).op.lan.obj G).obj (op V))) :
    (localization_leftKanExtension_objIsoSigma (U := U) G' V).hom
        ((((Over.forget U).op.lan.map η).app (op V)) x) =
      ⟨((localization_leftKanExtension_objIsoSigma (U := U) G V).hom x).1,
        η.app (op (Over.mk ((localization_leftKanExtension_objIsoSigma (U := U) G V).hom x).1))
          ((localization_leftKanExtension_objIsoSigma (U := U) G V).hom x).2⟩ := by
  -- Rewrite `x` as the canonical generator for its sigma coordinate, then use the naturality of
  -- the left Kan extension unit with respect to `η`.
  rcases hV : (localization_leftKanExtension_objIsoSigma (U := U) G V).hom x with ⟨a, s⟩
  rw [← hV]
  have hx :
      x =
        (localization_leftKanExtension_objIsoSigma (U := U) G V).inv ⟨a, s⟩ := by
    apply (localization_leftKanExtension_objIsoSigma (U := U) G V).toEquiv.injective
    simp [hV]
  rw [hx, localization_leftKanExtension_objIsoSigma_inv_mk (U := U) G a s]
  have hnat :=
    congrFun
      (congrArg (fun τ => τ.app (op (Over.mk a)))
        ((Over.forget U).op.lanUnit.naturality η)) s
  have hnat' :
      (((Over.forget U).op.lan.map η).app (op V))
          ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s) =
        (((Over.forget U).op.leftKanExtensionUnit G').app (op (Over.mk a)))
          (η.app (op (Over.mk a)) s) := by
    simpa [Functor.lanUnit] using hnat.symm
  rw [localization_leftKanExtension_objIsoSigma_hom_unit_app (U := U) G a s]
  rw [hnat']
  simpa using
    localization_leftKanExtension_objIsoSigma_hom_unit_app (U := U) G' a
      (η.app (op (Over.mk a)) s)

/-- Helper for Lemma 7.25.4: the summand formula for the left Kan extension of the representable
presheaf of the terminal object `U ⟶ U` collapses to the raw representable `h_U`. -/
noncomputable def identity_sigma_iso_representable
    (V : C) :
    (Σ a : V ⟶ U,
        ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max u v)).obj (op (Over.mk a))) ≅
      (representable_presheaf (U := U)).obj (op V) := by
  -- The sigma coordinate is exactly the arrow `V ⟶ U`; the second coordinate is unique because
  -- `Over.mk (𝟙 U)` is terminal in `Over U`.
  refine
    { hom := fun z ↦ ULift.up z.1
      inv := fun a ↦
        ⟨a.down, ULift.up (Over.homMk a.down (by simp))⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · funext z
    rcases z with ⟨a, s⟩
    rcases s with ⟨s⟩
    dsimp
    refine Sigma.ext ?_ ?_
    · rfl
    · apply heq_of_eq
      apply ULift.ext
      exact Over.mkIdTerminal.hom_ext _ _
  · funext a
    cases a
    rfl

/-- Helper for Lemma 7.25.4: the raw lower-shriek of the identity representable on `C/U` is
canonically the representable presheaf `h_U`. -/
noncomputable def localization_identity_leftKanExtension_iso_representable :
    (Over.forget U).op.lan.obj
        ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max u v)) ≅
      representable_presheaf (U := U) := by
  -- Use the sigma formula objectwise, then forget the unique second coordinate.
  refine NatIso.ofComponents
    (fun V ↦
      localization_leftKanExtension_objIsoSigma (U := U)
          ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
            (Over U)ᵒᵖ ⥤ Type (max u v)) (unop V) ≪≫
        identity_sigma_iso_representable (U := U) (unop V)) ?_
  intro X Y f
  ext x
  -- Naturality is just precomposition of the first sigma coordinate.
  cases X using Opposite.rec
  rename_i X
  cases Y using Opposite.rec
  rename_i Y
  have hmap :=
    localization_leftKanExtension_objIsoSigma_hom_map (U := U)
      ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
        (Over U)ᵒᵖ ⥤ Type (max u v)) f.unop x
  rw [← Quiver.Hom.op_unop f]
  change
    (identity_sigma_iso_representable (U := U) Y).hom
        ((localization_leftKanExtension_objIsoSigma (U := U)
          ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
            (Over U)ᵒᵖ ⥤ Type (max u v)) Y).hom
          (((Over.forget U).op.lan.obj
            ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
              (Over U)ᵒᵖ ⥤ Type (max u v))).map f.unop.op x)) =
      (representable_presheaf (U := U)).map f.unop.op
        ((identity_sigma_iso_representable (U := U) X).hom
          ((localization_leftKanExtension_objIsoSigma (U := U)
            ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
              (Over U)ᵒᵖ ⥤ Type (max u v)) X).hom x))
  rw [hmap]
  simp [identity_sigma_iso_representable, representable_presheaf]

/-- Helper for Lemma 7.25.4: the first-coordinate owner map of an arbitrary left Kan extension
is obtained by mapping to the identity representable and then using
`localization_identity_leftKanExtension_iso_representable`. -/
theorem localization_leftKanExtension_first_coordinate_eq_terminal
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) :
    let terminalMap : G ⟶
        ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max u v)) :=
      (IsTerminal.isTerminalObj CategoryTheory.uliftYoneda.{max u v}
        (Over.mk (𝟙 U)) Over.mkIdTerminal).from G
    ((Over.forget U).op.lan).map terminalMap ≫
        (localization_identity_leftKanExtension_iso_representable (U := U)).hom =
      { app := fun V x ↦
          ULift.up
            ((localization_leftKanExtension_objIsoSigma (U := U) G (unop V)).hom x).1
        naturality := by
          intro V Y f
          funext x
          apply ULift.ext
          simpa [representable_presheaf] using congrArg Sigma.fst
            (localization_leftKanExtension_objIsoSigma_hom_map (U := U) G f.unop x) } := by
  -- The sigma model for a natural transformation keeps the first coordinate; the terminal
  -- representable then forgets the unique second coordinate.
  ext V x
  cases V using Opposite.rec
  rename_i V
  dsimp
  change
    (identity_sigma_iso_representable (U := U) V).hom
        ((localization_leftKanExtension_objIsoSigma (U := U)
          ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
            (Over U)ᵒᵖ ⥤ Type (max u v)) V).hom
          ((((Over.forget U).op.lan).map
              ((IsTerminal.isTerminalObj CategoryTheory.uliftYoneda.{max u v}
                (Over.mk (𝟙 U)) Over.mkIdTerminal).from G)).app (op V) x)) =
      ULift.up ((localization_leftKanExtension_objIsoSigma (U := U) G V).hom x).1
  rw [localization_leftKanExtension_objIsoSigma_hom_natTrans]
  rfl

/-- Helper for Lemma 7.25.4: under the sigma-model for the left Kan extension, restriction along
`f : Y ⟶ V` sends the fibre over `a` to the fibre over `f ≫ a`. -/
theorem sigma_of_fibres_naturality
    (P : Over (representable_presheaf (U := U))) {V Y : C} (f : Y ⟶ V)
    (x : (((Over.forget U).op.lan.obj
      ((fiber_presheaf_over_representable (U := U)).obj P)).obj (op V))) :
    (sigma_of_fibres_iso_self (U := U) P Y).hom
        ((localization_leftKanExtension_objIsoSigma (U := U)
            ((fiber_presheaf_over_representable (U := U)).obj P) Y).hom
          (((Over.forget U).op.lan.obj
              ((fiber_presheaf_over_representable (U := U)).obj P)).map f.op x)) =
      P.left.map f.op
        ((sigma_of_fibres_iso_self (U := U) P V).hom
          ((localization_leftKanExtension_objIsoSigma (U := U)
              ((fiber_presheaf_over_representable (U := U)).obj P) V).hom x)) := by
  -- Rewrite the left Kan restriction in the sigma-model, then observe that the sigma-of-fibres
  -- isomorphism forgets the first coordinate and keeps exactly the restricted section.
  rw [localization_leftKanExtension_objIsoSigma_hom_map (U := U)
    ((fiber_presheaf_over_representable (U := U)).obj P) f x]
  rcases hV :
      (localization_leftKanExtension_objIsoSigma (U := U)
        ((fiber_presheaf_over_representable (U := U)).obj P) V).hom x with ⟨a, s⟩
  change (sigma_of_fibres_iso_self (U := U) P Y).hom
      ⟨f ≫ a, ?_⟩ = P.left.map f.op ((sigma_of_fibres_iso_self (U := U) P V).hom ⟨a, s⟩)
  simp [sigma_of_fibres_iso_self, fiber_presheaf_over_representable, fiber_presheaf_map]

/-- Helper for Lemma 7.25.4: the presheaf obtained by summing the fibres of a raw slice object
over `h_U` recovers the original presheaf. -/
noncomputable def sigma_of_fibres_natIso
    (P : Over (representable_presheaf (U := U))) :
    (Over.forget U).op.lan.obj ((fiber_presheaf_over_representable (U := U)).obj P) ≅
      P.left := by
  -- Package the objectwise disjoint-union-of-fibres identity into a presheaf isomorphism using
  -- the explicit restriction formula proved just above.
  refine NatIso.ofComponents
    (fun V ↦
      localization_leftKanExtension_objIsoSigma (U := U)
          ((fiber_presheaf_over_representable (U := U)).obj P) (unop V) ≪≫
        sigma_of_fibres_iso_self (U := U) P (unop V)) ?_
  intro X Y f
  ext x
  simpa using sigma_of_fibres_naturality (U := U) P f.unop x

/-- Helper for Lemma 7.25.4: the component of `sigma_of_fibres_natIso` is the explicit
objectwise composition of the sigma-model identification with the disjoint-union-of-fibres
isomorphism. -/
theorem sigma_of_fibres_natIso_hom_app
    (P : Over (representable_presheaf (U := U))) (V : C)
    (x : (((Over.forget U).op.lan.obj
      ((fiber_presheaf_over_representable (U := U)).obj P)).obj (op V))) :
    (sigma_of_fibres_natIso (U := U) P).hom.app (op V) x =
      (sigma_of_fibres_iso_self (U := U) P V).hom
        ((localization_leftKanExtension_objIsoSigma (U := U)
            ((fiber_presheaf_over_representable (U := U)).obj P) V).hom x) := by
  -- This is exactly the defining component of `sigma_of_fibres_natIso`.
  rfl

/-- Helper for Lemma 7.25.4: the sigma-of-fibres identification is natural in morphisms over the
raw representable presheaf `h_U`. -/
theorem sigma_of_fibres_natIso_over_hom
    {P Q : Over (representable_presheaf (U := U))} (α : P ⟶ Q) :
    ((Over.forget U).op.lan.map ((fiber_presheaf_over_representable (U := U)).map α)) ≫
        (sigma_of_fibres_natIso (U := U) Q).hom =
      (sigma_of_fibres_natIso (U := U) P).hom ≫ α.left := by
  -- Evaluate the sigma-model on a section, then observe that `fiber_presheaf_hom` changes only
  -- the second coordinate by applying `α.left`.
  ext V x
  change
      (sigma_of_fibres_natIso (U := U) Q).hom.app V
          ((((Over.forget U).op.lan.map
                ((fiber_presheaf_over_representable (U := U)).map α)).app V) x) =
        α.left.app V ((sigma_of_fibres_natIso (U := U) P).hom.app V x)
  rw [sigma_of_fibres_natIso_hom_app, sigma_of_fibres_natIso_hom_app]
  rw [localization_leftKanExtension_objIsoSigma_hom_natTrans (U := U)
    ((fiber_presheaf_over_representable (U := U)).map α) x]
  rcases hV :
      (localization_leftKanExtension_objIsoSigma (U := U)
        ((fiber_presheaf_over_representable (U := U)).obj P) (unop V)).hom x with ⟨a, s⟩
  change (sigma_of_fibres_iso_self (U := U) Q (unop V)).hom
      ⟨a, ⟨α.left.app V s.1, ?_⟩⟩ =
    α.left.app V ((sigma_of_fibres_iso_self (U := U) P (unop V)).hom ⟨a, s⟩)
  simp [sigma_of_fibres_iso_self, fiber_presheaf_hom]

/-- Helper for Lemma 7.25.4: after collapsing the disjoint union of fibres, the structure map to
`h_U` remembers exactly the chosen first coordinate. -/
theorem sigma_of_fibres_iso_self_owner_app
    (P : Over (representable_presheaf (U := U))) (V : C)
    (z : Σ a : V ⟶ U, { s : P.left.obj (op V) // (P.hom.app (op V) s).down = a }) :
    P.hom.app (op V) ((sigma_of_fibres_iso_self (U := U) P V).hom z) = ULift.up z.1 := by
  -- Unpack the sigma-of-fibres equivalence and rewrite the defining fibre condition.
  rcases z with ⟨a, s⟩
  rcases s with ⟨s, hs⟩
  apply ULift.ext
  simpa [sigma_of_fibres_iso_self] using hs

/-- Helper for Lemma 7.25.4: before sheafification, the sigma-of-fibres isomorphism is a morphism
over the raw representable `h_U`; its structure map is exactly the first sigma coordinate. -/
theorem sigma_of_fibres_natIso_owner
    (P : Over (representable_presheaf (U := U))) :
    (sigma_of_fibres_natIso (U := U) P).hom ≫ P.hom =
      { app := fun V x ↦
          ULift.up
            ((localization_leftKanExtension_objIsoSigma (U := U)
              ((fiber_presheaf_over_representable (U := U)).obj P) (unop V)).hom x).1
        naturality := by
          intro V Y f
          funext x
          apply ULift.ext
          simpa [representable_presheaf] using congrArg Sigma.fst
            (localization_leftKanExtension_objIsoSigma_hom_map (U := U)
              ((fiber_presheaf_over_representable (U := U)).obj P) f.unop x) } := by
  ext V x
  rw [NatTrans.comp_app]
  change
    P.hom.app V ((sigma_of_fibres_natIso (U := U) P).hom.app V x) =
      ULift.up
        ((localization_leftKanExtension_objIsoSigma (U := U)
          ((fiber_presheaf_over_representable (U := U)).obj P) (unop V)).hom x).1
  rw [sigma_of_fibres_natIso_hom_app]
  exact sigma_of_fibres_iso_self_owner_app (U := U) P (unop V)
    ((localization_leftKanExtension_objIsoSigma (U := U)
      ((fiber_presheaf_over_representable (U := U)).obj P) (unop V)).hom x)

/-- Helper for Lemma 7.25.4: the target-side textbook identity
`j_{U!}^{PSh}(F_φ) = F` packaged as a slice-level natural isomorphism before the final recovery
step to `Over h_U^#`. -/
theorem localization_over_representable_hom_naturality
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {V Y : C} (f : Y ⟶ V) :
    (fun x ↦ ULift.up ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y).hom
      (((Over.forget U).op.lan.obj 𝒢.obj).map f.op x)).1) =
    fun x ↦ (representable_presheaf (U := U)).map f.op
      (ULift.up ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj V).hom x).1) := by
  -- The first coordinate of the sigma-model transforms exactly as the representable presheaf does.
  funext x
  apply ULift.ext
  simpa [representable_presheaf] using congrArg Sigma.fst
    (localization_leftKanExtension_objIsoSigma_hom_map (U := U) 𝒢.obj f x)

/-- Helper for Lemma 7.25.4: the raw source-side localization object over the representable
presheaf `h_U`. -/
noncomputable def localization_over_representable
    (𝒢 : Sheaf (J.over U) (Type (max u v))) :
    Over (representable_presheaf (U := U)) :=
  Over.mk (Y := ((Over.forget U).op.lan.obj 𝒢.obj))
    { app := fun V x ↦
        ULift.up ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj (unop V)).hom x).1
      naturality := by
        -- This is the verified raw `h_U`-localization object used in the source-side unit plan.
        intro V Y f
        exact localization_over_representable_hom_naturality
          (J := J) (U := U) 𝒢 f.unop }

/-- Helper for Lemma 7.25.4: a morphism of slice-site sheaves induces the evident morphism
between the raw localization objects over `h_U`. -/
noncomputable def localization_over_representable_map
    {𝒢 𝒢' : Sheaf (J.over U) (Type (max u v))} (η : 𝒢 ⟶ 𝒢') :
    localization_over_representable (J := J) (U := U) 𝒢 ⟶
      localization_over_representable (J := J) (U := U) 𝒢' := by
  -- The left component is the left-Kan-extension map; the structure map over `h_U` is preserved
  -- because the sigma-model first coordinate is unchanged by a natural transformation.
  refine Over.homMk (((Over.forget U).op.lan).map η.hom) ?_
  ext V x
  apply ULift.ext
  simpa [localization_over_representable] using congrArg Sigma.fst
    (localization_leftKanExtension_objIsoSigma_hom_natTrans (U := U) η.hom x)

/-- Helper for Lemma 7.25.4: the raw presheaf-level localization construction as a functor into
the slice over the representable presheaf `h_U`. -/
noncomputable def localization_over_representableFunctor :
    Sheaf (J.over U) (Type (max u v)) ⥤ Over (representable_presheaf (U := U)) where
  obj 𝒢 := localization_over_representable (J := J) (U := U) 𝒢
  map η := localization_over_representable_map (J := J) (U := U) η
  map_id 𝒢 := by
    -- The left-Kan-extension functor preserves identities, hence so does the slice morphism.
    apply Over.OverMorphism.ext
    change (((Over.forget U).op.lan).map (𝟙 𝒢.obj)) =
      𝟙 (((Over.forget U).op.lan).obj 𝒢.obj)
    simp
  map_comp η θ := by
    -- Composition is inherited from the left-Kan-extension functor on the left component.
    apply Over.OverMorphism.ext
    change (((Over.forget U).op.lan).map (η.hom ≫ θ.hom)) =
      ((Over.forget U).op.lan).map η.hom ≫ ((Over.forget U).op.lan).map θ.hom
    simp

/-- Helper for Lemma 7.25.4: for the raw localization object over `h_U`, the fibre condition over
`X.hom` is exactly the statement that the sigma-model first coordinate is `X.hom`. -/
theorem localization_over_representable_fibre_condition
    (𝒢 : Sheaf (J.over U) (Type (max u v))) (X : Over U)
    (s : (((Over.forget U).op.lan.obj 𝒢.obj).obj (op X.left))) :
    ((localization_over_representable (J := J) (U := U) 𝒢).hom.app (op X.left) s).down = X.hom ↔
      ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 = X.hom := by
  -- Unfold the raw owner map once: it is literally the first sigma coordinate wrapped in `ULift`.
  simp [localization_over_representable]

theorem fiber_of_localization_sigma_first_coordinate
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : Over U} (f : op X ⟶ op Y)
    (s : (((Over.forget U).op.lan.obj 𝒢.obj).obj (op X.left)))
    (hs : ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 = X.hom) :
    ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y.left).hom
        (((Over.forget U).op.lan.obj 𝒢.obj).map f.unop.left.op s)).1 =
      Y.hom := by
  -- Compare first coordinates through the sigma-model map formula, then rewrite by the triangle
  -- identity in `Over U`.
  have hmap :=
    congrArg
      (fun z : Σ φ : Y.left ⟶ U, 𝒢.obj.obj (op (Over.mk φ)) ↦ z.1)
      (localization_leftKanExtension_objIsoSigma_hom_map (U := U) 𝒢.obj f.unop.left s)
  dsimp at hmap
  rw [hs] at hmap
  exact hmap.trans (Over.w f.unop)

/-- Helper for Lemma 7.25.4: the sigma-fibre identification returns the transported second
coordinate. -/
theorem fiber_of_localization_sigma_iso_hom_eq_snd
    (𝒢 : Sheaf (J.over U) (Type (max u v))) (X : Over U)
    (s : (((Over.forget U).op.lan.obj 𝒢.obj).obj (op X.left)))
    (hs : ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 = X.hom) :
    HEq
      ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs⟩)
      ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).2 := by
  -- Unfold the concrete fibre equivalence over `X`; once the witness equation is
  -- resolved, the equivalence simply reads off the second coordinate.
  let e := localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left
  rcases hσ : e.hom s with ⟨a, x⟩
  have hs' : a = X.hom := by
    simpa [e, hσ] using hs
  change HEq ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs⟩) x
  subst hs'
  simp [fiber_of_localization_sigma_iso, e, hσ]
  cases X
  rfl

/-- Helper for Lemma 7.25.4: once the first sigma coordinate is identified with `X.hom`, the
whole sigma point is determined by the fibre equivalence. -/
theorem fiber_of_localization_sigma_eq_pair
    (𝒢 : Sheaf (J.over U) (Type (max u v))) (X : Over U)
    (s : (((Over.forget U).op.lan.obj 𝒢.obj).obj (op X.left)))
    (hs : ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 = X.hom) :
    (localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s =
      ⟨X.hom, (fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs⟩⟩ := by
  -- Package the first-coordinate identification with the explicit second-coordinate HEq.
  refine (Sigma.mk.inj_iff).2 ?_
  constructor
  · exact hs
  · exact (fiber_of_localization_sigma_iso_hom_eq_snd (J := J) (U := U) 𝒢 X s hs).symm

/-- Helper for Lemma 7.25.4: the explicit `Over.homMk` morphism appearing in the sigma-model map
formula is definitionally the original arrow in `(C/U)ᵒᵖ`. -/
theorem presheaf_map_over_homMk_op_eq
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : Over U} (f : op X ⟶ op Y)
    (x : 𝒢.obj.obj (op X)) :
    𝒢.obj.map ((show Over.mk Y.hom ⟶ Over.mk X.hom from
          Over.homMk f.unop.left (Over.w f.unop)).op) x =
      𝒢.obj.map f x := by
  -- Identify the displayed `Over.homMk` with `f` in `(Over U)ᵒᵖ`, then rewrite under `𝒢.obj.map`.
  have hMor :
      ((show Over.mk Y.hom ⟶ Over.mk X.hom from
            Over.homMk f.unop.left (Over.w f.unop)).op) = f := by
    apply Quiver.Hom.unop_inj
    rfl
  simpa using congrArg (fun m ↦ 𝒢.obj.map m x) hMor

/-- Helper for Lemma 7.25.4: after substituting the source fibre point into the sigma-model map
formula, the left Kan restriction lands in the expected raw summand over `f.left ≫ X.hom`. -/
theorem fiber_of_localization_inv_map_sigma_raw
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : Over U} (f : op X ⟶ op Y)
    (s : (((Over.forget U).op.lan.obj 𝒢.obj).obj (op X.left)))
    (hs : ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 = X.hom) :
    (localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y.left).hom
        (((Over.forget U).op.lan.obj 𝒢.obj).map f.unop.left.op s) =
      ⟨f.unop.left ≫ X.hom,
        𝒢.obj.map
          (representableLocalizationOverHomMk (U := U) (φ := X.hom) f.unop.left).op
          ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs⟩)⟩ := by
  -- This is the sigma-model map formula after substituting the source-side fibre description.
  have hmap_raw :=
    localization_leftKanExtension_objIsoSigma_hom_map (U := U) 𝒢.obj f.unop.left s
  rw [fiber_of_localization_sigma_eq_pair (J := J) (U := U) 𝒢 X s hs] at hmap_raw
  simpa using hmap_raw

/-- Helper for Lemma 7.25.4: applying the sigma-model on `Y.left` to the inverse fibre point
recovers the pair whose first coordinate is `Y.hom` and whose second coordinate is the restricted
section of `𝒢`. -/
theorem fiber_of_localization_inv_sigma_eq_pair
    (𝒢 : Sheaf (J.over U) (Type (max u v))) (Y : Over U)
    (y : 𝒢.obj.obj (op Y)) :
    (localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y.left).hom
        ↑((fiber_of_localization_sigma_iso (U := U) 𝒢.obj Y).inv y) =
      ⟨Y.hom, y⟩ := by
  -- The inverse fibre point is characterized by the sigma pair over `Y.hom`.
  simpa using
    (fiber_of_localization_sigma_eq_pair (J := J) (U := U) 𝒢 Y
      (((fiber_of_localization_sigma_iso (U := U) 𝒢.obj Y).inv y).1)
      (((fiber_of_localization_sigma_iso (U := U) 𝒢.obj Y).inv y).2))

/-- Helper for Lemma 7.25.4: transporting the displayed sigma-model restriction term along
`Over.w f.unop` identifies it with the literal presheaf map `𝒢.obj.map f`. -/
theorem fiber_of_localization_displayed_map_transport_homMk
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X : Over U} {Y' : C} {Yhom : Y' ⟶ U}
    (g : Y' ⟶ X.left) (hg : g ≫ X.hom = Yhom) (z : 𝒢.obj.obj (op X)) :
    Eq.ndrec
        (motive := fun a : Y' ⟶ U => 𝒢.obj.obj (op (Over.mk a)))
        (𝒢.obj.map
          (show Over.mk (g ≫ X.hom) ⟶ Over.mk X.hom from Over.homMk g).op
          z)
        hg =
      𝒢.obj.map (Over.homMk g hg).op z := by
  -- Eliminate the explicit triangle equality `hg`; the transport disappears and both displayed maps
  -- become definitional.
  cases hg
  rfl

/-- Helper for Lemma 7.25.4: transporting the displayed sigma-model restriction term along
`Over.w f.unop` identifies it with the literal presheaf map `𝒢.obj.map f`. -/
theorem fiber_of_localization_displayed_map_transport
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : Over U} (f : op X ⟶ op Y)
    (z : 𝒢.obj.obj (op X)) :
    Eq.ndrec
        (motive := fun a : Y.left ⟶ U => 𝒢.obj.obj (op (Over.mk a)))
        (𝒢.obj.map
          (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from Over.homMk f.unop.left).op
          z)
        (Over.w f.unop) =
      𝒢.obj.map f z := by
  -- Reduce the abstract target object `Y` to the concrete `Over.mk Y.hom` form and then invoke the
  -- explicit `Over.homMk` transport computation.
  rcases Over.mk_surjective Y with ⟨Y', Yhom, rfl⟩
  simpa using
    fiber_of_localization_displayed_map_transport_homMk (J := J) (U := U) 𝒢
      (X := X) (Y' := Y') (Yhom := Yhom) f.unop.left (Over.w f.unop) z

/-- Helper for Lemma 7.25.4: after aligning the first coordinates in the sigma-model map formula,
the two second coordinates are heterogeneously equal. -/
theorem fiber_of_localization_second_coordinate_heq
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : Over U} (f : op X ⟶ op Y)
    (x :
      (((fiber_presheaf_over_representable (U := U)).obj
          (localization_over_representable (J := J) (U := U) 𝒢)).obj (op X))) :
    𝒢.obj.map f
        ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom x) ≍
      𝒢.obj.map
        (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from Over.homMk f.unop.left).op
        ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom x) := by
  -- Rewrite the fibre point with the sigma-model fibre condition, then compose the ordinary
  -- transport equality with `eqRec_heq` to remove the displayed cast.
  rcases x with ⟨s, hs⟩
  have hs' : ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 = X.hom := by
    simpa [localization_over_representable_fibre_condition (J := J) (U := U) 𝒢 X s] using hs
  have hz :
      (fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs⟩ =
        (fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs'⟩ := by
    -- The fibre point depends only on the underlying section `s`; the proof field is irrelevant.
    apply congrArg ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom)
    apply Subtype.ext
    rfl
  let z := (fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs'⟩
  have htransport :
      Eq.ndrec
          (motive := fun a : Y.left ⟶ U => 𝒢.obj.obj (op (Over.mk a)))
          (𝒢.obj.map
            (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from Over.homMk f.unop.left).op z)
          (Over.w f.unop) =
        𝒢.obj.map f z :=
    fiber_of_localization_displayed_map_transport (J := J) (U := U) 𝒢 f z
  have hcast :
      cast
          (congrArg
            (fun a : Y.left ⟶ U => 𝒢.obj.obj (op (Over.mk a)))
            (Over.w f.unop))
          (𝒢.obj.map
            (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from Over.homMk f.unop.left).op z) =
        𝒢.obj.map f z := by
    -- Repackage the transport equality in cast form so `cast_eq_iff_heq` can read off the
    -- heterogeneous equality directly.
    simpa [eqRec_eq_cast] using htransport
  have hheq :
      𝒢.obj.map f z ≍
        𝒢.obj.map
          (show Over.mk (f.unop.left ≫ X.hom) ⟶ Over.mk X.hom from Over.homMk f.unop.left).op z := by
    exact ((cast_eq_iff_heq).1 hcast).symm
  simpa [z, hz] using hheq

/-- Helper for Lemma 7.25.4: after rewriting the sigma-model first coordinates to the endpoints of
the arrow `f`, the inverse fibre equivalence identifies the mapped section with the canonical
fibre point over `Y.hom`. -/
theorem fiber_of_localization_inv_map_eq
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : Over U} (f : op X ⟶ op Y)
    (s : (((Over.forget U).op.lan.obj 𝒢.obj).obj (op X.left)))
    (hs : ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 = X.hom)
    (hfst :
      ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y.left).hom
          (((Over.forget U).op.lan.obj 𝒢.obj).map f.unop.left.op s)).1 = Y.hom) :
    (fiber_of_localization_sigma_iso (U := U) 𝒢.obj Y).inv
        (𝒢.obj.map f ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs⟩)) =
      ⟨((Over.forget U).op.lan.obj 𝒢.obj).map f.unop.left.op s, hfst⟩ := by
  cases X
  rename_i X_left X_right X_hom
  cases Y
  rename_i Y_left Y_right Y_hom
  dsimp at hs hfst ⊢
  -- Route correction: the left sigma image is now explicit, and the remaining blocker is the
  -- raw sigma equality; after rewriting its first coordinate and displayed map, injectivity of the
  -- sigma-model identifies the underlying left-Kan-extension sections.
  have hleft :=
    fiber_of_localization_inv_sigma_eq_pair (J := J) (U := U) 𝒢
      { left := Y_left, right := Y_right, hom := Y_hom }
      (𝒢.obj.map f
        ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj
          { left := X_left, right := X_right, hom := X_hom }).hom ⟨s, hs⟩))
  have hright :=
    fiber_of_localization_inv_map_sigma_raw (J := J) (U := U) 𝒢
      (X := { left := X_left, right := X_right, hom := X_hom })
      (Y := { left := Y_left, right := Y_right, hom := Y_hom }) f s hs
  have hright' :
      (localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y_left).hom
          (((Over.forget U).op.lan.obj 𝒢.obj).map f.unop.left.op s) =
        ⟨Y_hom,
          𝒢.obj.map f
            ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj
              { left := X_left, right := X_right, hom := X_hom }).hom ⟨s, hs⟩)⟩ := by
    -- `convert` aligns the sigma target with the raw map formula, and `ext` reduces the remaining
    -- equality to the first-coordinate identity `Over.w f.unop`.
    convert hright using 1
    ext
    · exact (Over.w f.unop).symm
    · change
        (𝒢.obj.map f
            ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj
              { left := X_left, right := X_right, hom := X_hom }).hom ⟨s, hs⟩) ≍
          𝒢.obj.map
            (show Over.mk (f.unop.left ≫ X_hom) ⟶ Over.mk X_hom from Over.homMk f.unop.left).op
            ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj
              { left := X_left, right := X_right, hom := X_hom }).hom ⟨s, hs⟩))
      exact fiber_of_localization_second_coordinate_heq (J := J) (U := U) 𝒢
        (X := { left := X_left, right := X_right, hom := X_hom })
        (Y := { left := Y_left, right := Y_right, hom := Y_hom }) f ⟨s, hs⟩
  apply Subtype.ext
  -- Compare the underlying left-Kan-extension sections through the explicit sigma-model.
  apply (localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y_left).toEquiv.injective
  exact hleft.trans hright'.symm

/-- Helper for Lemma 7.25.4: after rewriting the sigma-model first coordinates to the endpoints of
the arrow `f`, the second-coordinate equality becomes the source-side fibre map formula. -/
theorem fiber_of_localization_second_coordinate_transport
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : Over U} (f : op X ⟶ op Y)
    (s : (((Over.forget U).op.lan.obj 𝒢.obj).obj (op X.left)))
    (hs : ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 = X.hom)
    (hfst :
      ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y.left).hom
          (((Over.forget U).op.lan.obj 𝒢.obj).map f.unop.left.op s)).1 = Y.hom) :
    (fiber_of_localization_sigma_iso (U := U) 𝒢.obj Y).hom
        ⟨((Over.forget U).op.lan.obj 𝒢.obj).map f.unop.left.op s, hfst⟩ =
      𝒢.obj.map f ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs⟩) := by
  -- Apply the forward fibre equivalence to the cast-free subtype equality proved just above.
  simpa using congrArg
    (fun t ↦ (fiber_of_localization_sigma_iso (U := U) 𝒢.obj Y).hom t)
    (fiber_of_localization_inv_map_eq (J := J) (U := U) 𝒢 f s hs hfst).symm

/-- Helper for Lemma 7.25.4: the textbook fibre identity
`(j_{U!}^{PSh} \mathcal{G})_\gamma = \mathcal{G}` is natural on `(C/U)^op`. -/
theorem fiber_of_localization_map_apply
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    (s :
      (((fiber_presheaf_over_representable (U := U)).obj
          (localization_over_representable (J := J) (U := U) 𝒢)).obj X)) :
    (fiber_of_localization_sigma_iso (U := U) 𝒢.obj Y.unop).hom
        ((((fiber_presheaf_over_representable (U := U)).obj
            (localization_over_representable (J := J) (U := U) 𝒢)).map f) s) =
      𝒢.obj.map f ((fiber_of_localization_sigma_iso (U := U) 𝒢.obj X.unop).hom s) := by
  -- Route correction: expand the fibre restriction once, then compare the second coordinates in the
  -- sigma-model for the left Kan extension.
  cases X using Opposite.rec
  rename_i X
  cases Y using Opposite.rec
  rename_i Y
  cases X
  rename_i X_left X_right X_hom
  cases Y
  rename_i Y_left Y_right Y_hom
  rcases s with ⟨s, hs⟩
  dsimp [fiber_presheaf_over_representable, fiber_presheaf_map]
  have hs' :
      ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X_left).hom s).1 = X_hom := by
    simpa using
      (localization_over_representable_fibre_condition (J := J) (U := U) 𝒢
        { left := X_left, right := X_right, hom := X_hom } s).1 hs
  have hfst :
      ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj Y_left).hom
          (((Over.forget U).op.lan.obj 𝒢.obj).map f.unop.left.op s)).1 =
        Y_hom := by
    -- The first coordinate is already controlled by the raw owner-map computation.
    simpa using fiber_of_localization_sigma_first_coordinate (J := J) (U := U) 𝒢 f s hs'
  -- Delegate the remaining dependent-transport step to the dedicated helper theorem.
  simpa using fiber_of_localization_second_coordinate_transport
    (J := J) (U := U) 𝒢 f s hs' hfst

/-- Helper for Lemma 7.25.4: the textbook fibre identity
`(j_{U!}^{PSh} \mathcal{G})_\gamma = \mathcal{G}` is natural on `(C/U)^op`. -/
theorem fiber_of_localization_naturality
    (𝒢 : Sheaf (J.over U) (Type (max u v))) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    ((fiber_presheaf_over_representable (U := U)).obj
        (localization_over_representable (J := J) (U := U) 𝒢)).map f ≫
      (fiber_of_localization_sigma_iso (U := U) 𝒢.obj Y.unop).hom =
    (fiber_of_localization_sigma_iso (U := U) 𝒢.obj X.unop).hom ≫ 𝒢.obj.map f := by
  -- Route correction: after evaluating both sides on a section `s`, the goal reduces to the
  -- second-coordinate computation inside `localization_leftKanExtension_objIsoSigma_hom_map`.
  ext s
  simpa using fiber_of_localization_map_apply (J := J) (U := U) 𝒢 f s

/-- Helper for Lemma 7.25.4: the source-side textbook identity
`(j_{U!}^{PSh} \mathcal{G})_\gamma = \mathcal{G}` packaged as a presheaf isomorphism. -/
noncomputable def fiber_of_localization_natIso
    (𝒢 : Sheaf (J.over U) (Type (max u v))) :
    (fiber_presheaf_over_representable (U := U)).obj
        (localization_over_representable (J := J) (U := U) 𝒢) ≅
      𝒢.obj :=
  NatIso.ofComponents
    (fun X ↦ fiber_of_localization_sigma_iso (U := U) 𝒢.obj X.unop)
    (fiber_of_localization_naturality (J := J) (U := U) 𝒢)

/-- Helper for Lemma 7.25.4: the raw fibre identity
`(j_{U!}^{PSh} \mathcal{G})_\gamma = \mathcal{G}` is natural in the sheaf
`\mathcal{G}`. -/
theorem fiber_of_localization_natIso_hom_naturality
    {𝒢 𝒢' : Sheaf (J.over U) (Type (max u v))} (η : 𝒢 ⟶ 𝒢') :
    (fiber_presheaf_over_representable (U := U)).map
        (localization_over_representable_map (J := J) (U := U) η) ≫
      (fiber_of_localization_natIso (J := J) (U := U) 𝒢').hom =
    (fiber_of_localization_natIso (J := J) (U := U) 𝒢).hom ≫ η.hom := by
  -- The sigma-model sends the map induced by `η` to the identity on first coordinates and `η` on
  -- second coordinates; the fibre equivalence then reads off exactly that second coordinate.
  ext X s
  cases X using Opposite.rec
  rename_i X
  rcases s with ⟨s, hs⟩
  dsimp [fiber_presheaf_over_representable, fiber_presheaf_hom,
    localization_over_representable_map]
  let t := (((Over.forget U).op.lan.map η.hom).app (op X.left) s)
  have hs' :
      ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢.obj X.left).hom s).1 =
        X.hom := by
    simpa using
      (localization_over_representable_fibre_condition (J := J) (U := U) 𝒢 X s).1 hs
  let y := (fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs⟩
  have hy :
      (fiber_of_localization_sigma_iso (U := U) 𝒢.obj X).hom ⟨s, hs'⟩ = y := by
    -- The source fibre point is independent of which proof of the fibre condition is used.
    simpa [y]
  have hmap :=
    localization_leftKanExtension_objIsoSigma_hom_natTrans (U := U) η.hom s
  have hsource :=
    fiber_of_localization_sigma_eq_pair (J := J) (U := U) 𝒢 X s hs'
  have ht_pair :
      (localization_leftKanExtension_objIsoSigma (U := U) 𝒢'.obj X.left).hom t =
        ⟨X.hom, η.hom.app (op X) y⟩ := by
    -- The natural transformation on the left Kan extension keeps the first sigma coordinate and
    -- applies `η` to the second one; substitute the source fibre description.
    rw [hmap, hsource]
    cases X
    rename_i X_left X_right X_hom
    cases X_right
    rename_i as
    cases as
    simpa [t, y, hy, Over.mk, CostructuredArrow.mk]
  have ht :
      ((localization_leftKanExtension_objIsoSigma (U := U) 𝒢'.obj X.left).hom t).1 =
        X.hom := by
    -- The first coordinate of the target fibre point is read from the displayed sigma equality.
    simpa [ht_pair]
  have htarget :=
    fiber_of_localization_sigma_eq_pair (J := J) (U := U) 𝒢' X t ht
  have hsection :
      (fiber_of_localization_sigma_iso (U := U) 𝒢'.obj X).hom ⟨t, ht⟩ =
        η.hom.app (op X) y := by
    -- Compare the two sigma descriptions of the same left-Kan-extension section and read off the
    -- second coordinate.
    exact eq_of_heq (Sigma.mk.inj_iff.mp (htarget.symm.trans ht_pair)).2
  change
    (fiber_of_localization_sigma_iso (U := U) 𝒢'.obj X).hom ⟨t, ?_⟩ =
      η.hom.app (op X) y
  -- The proof component of the target subtype is irrelevant.
  convert hsection using 1

/-- Helper for Lemma 7.25.4: functorial packaging of the raw fibre identity
`(j_{U!}^{PSh} \mathcal{G})_\gamma = \mathcal{G}`. -/
noncomputable def fiber_of_localization_natIso_natIso :
    localization_over_representableFunctor (J := J) (U := U) ⋙
        fiber_presheaf_over_representable (U := U) ≅
      sheafToPresheaf (J.over U) (Type (max u v)) :=
  NatIso.ofComponents
    (fun 𝒢 ↦ fiber_of_localization_natIso (J := J) (U := U) 𝒢)
    (fiber_of_localization_natIso_hom_naturality (J := J) (U := U))

/-- Helper for Lemma 7.25.4: after sheafification, the source-side raw fibre identity gives a
natural isomorphism from the localization-fibre construction back to the identity functor. -/
noncomputable def localization_fiber_sheafification_natIso :
    localization_over_representableFunctor (J := J) (U := U) ⋙
        fiber_presheaf_over_representable (U := U) ⋙
        presheafToSheaf (J.over U) (Type (max u v)) ≅
      𝟭 (Sheaf (J.over U) (Type (max u v))) :=
  Functor.isoWhiskerRight
      (fiber_of_localization_natIso_natIso (J := J) (U := U))
      (presheafToSheaf (J.over U) (Type (max u v))) ≪≫
    (sheafificationNatIso (J.over U) (Type (max u v))).symm

/-- Helper for Lemma 7.25.4: the inverse functor is obtained by sheafifying the fibre presheaf of
the raw pullback over `h_U`. -/
theorem comparison_inverse_obj_eq
    (T : Over h[U]^#[J]) :
    (comparison_inverse (J := J) (U := U)).obj T =
      (presheafToSheaf (J.over U) (Type (max u v))).obj
        ((fiber_presheaf_over_representable (U := U)).obj
          ((pullback_to_representable (J := J) (U := U)).obj T)) := rfl

/-- Helper for Lemma 7.25.4: the source-side composite `comparison_inverse ∘
representableLocalizationComparison` is obtained by sheafifying the fibre presheaf of the raw
pullback of the comparison object over `h_U`. -/
theorem comparison_unit_object_eq
    (𝒢 : Sheaf (J.over U) (Type (max u v))) :
    ((J.representableLocalizationComparison U ⋙ comparison_inverse (J := J) (U := U)).obj 𝒢) =
      (presheafToSheaf (J.over U) (Type (max u v))).obj
        ((fiber_presheaf_over_representable (U := U)).obj
          ((pullback_to_representable (J := J) (U := U)).obj
            ((J.representableLocalizationComparison U).obj 𝒢))) := by
  -- Unfold the composite once: it is exactly the source-side object that the final unit
  -- isomorphism must identify with `𝒢`.
  rfl

/-- Helper for Lemma 7.25.4: the comparison functor equips `comparison_inverse.obj T` with the
canonical structure map `representableLocalizationHom`. -/
theorem comparison_inverse_comparison_hom_eq
    (T : Over h[U]^#[J]) :
    ((J.representableLocalizationComparison U).obj
      ((comparison_inverse (J := J) (U := U)).obj T)).hom =
      J.representableLocalizationHom U ((comparison_inverse (J := J) (U := U)).obj T) := rfl

/-- Helper for Lemma 7.25.4: the lower-shriek/sheafification comparison from Lemma 7.25.2 is
natural in the presheaf over `C/U`. -/
theorem localization_lowerShriek_associatedSheafIso_naturality
    {G G' : (Over U)ᵒᵖ ⥤ Type (max u v)} (η : G ⟶ G') :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((presheafToSheaf (J.over U) (Type (max u v))).map η) ≫
      (localization_lowerShriek_associatedSheafIso J U G').hom =
    (localization_lowerShriek_associatedSheafIso J U G).hom ≫
      (presheafToSheaf J (Type (max u v))).map (((Over.forget U).op.lan).map η) := by
  let F := presheafToSheaf J (Type (max u v))
  let L :=
    Functor.sheafPullbackConstruction.sheafPullback
      (Over.forget U) (Type (max u v)) (J.over U) J
  have hsimpl :
      L.map ((presheafToSheaf (J.over U) (Type (max u v))).map η) ≫
          (asIso (F.map (((Over.forget U).op.lan).map
            (CategoryTheory.toSheafify (J.over U) G')))).inv =
        (asIso (F.map (((Over.forget U).op.lan).map
          (CategoryTheory.toSheafify (J.over U) G)))).inv ≫
          F.map (((Over.forget U).op.lan).map η) := by
    have hnat :
        F.map (((Over.forget U).op.lan).map η) ≫
            F.map (((Over.forget U).op.lan).map
              (CategoryTheory.toSheafify (J.over U) G')) =
          F.map (((Over.forget U).op.lan).map
              (CategoryTheory.toSheafify (J.over U) G)) ≫
            L.map ((presheafToSheaf (J.over U) (Type (max u v))).map η) := by
      -- The constructed lower shriek is `sheafToPresheaf ⋙ lan ⋙ presheafToSheaf`, so this is
      -- exactly the transported naturality of `toSheafify`.
      dsimp [F, L]
      simp [Functor.sheafPullbackConstruction.sheafPullback, ← Functor.map_comp]
    -- TODO: convert the raw transported square `hnat` into the inverse-on-the-right form needed
    -- for `localization_lowerShriek_associatedSheafIso`; the remaining gap is the categorical
    -- cancellation step against the two isomorphisms
    -- `F.map ((Over.forget U).op.lan.map (toSheafify ...))`.
    let i := asIso (F.map (((Over.forget U).op.lan).map
      (CategoryTheory.toSheafify (J.over U) G)))
    let i' := asIso (F.map (((Over.forget U).op.lan).map
      (CategoryTheory.toSheafify (J.over U) G')))
    have hrew :
        i.hom ≫ L.map ((presheafToSheaf (J.over U) (Type (max u v))).map η) =
          F.map (((Over.forget U).op.lan).map η) ≫ i'.hom := by
      simpa [i, i', Category.assoc] using hnat.symm
    have hrew' :
        L.map ((presheafToSheaf (J.over U) (Type (max u v))).map η) =
          i.inv ≫ F.map (((Over.forget U).op.lan).map η) ≫ i'.hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ i.inv ≫ k) hrew
    rw [hrew']
    change
      (((i.inv ≫ F.map (((Over.forget U).op.lan).map η)) ≫ i'.hom) ≫ i'.inv =
        i.inv ≫ F.map (((Over.forget U).op.lan).map η))
    simp [Category.assoc]
  -- Route correction: after unfolding Lemma 7.25.2, the only content is the cancellation step
  -- encoded in `hsimpl`; `sheafPullbackIso` and the intermediate `eqToIso rfl` are formal.
  -- The formal `sheafPullbackIso` and `eqToIso rfl` layers simplify away, leaving `hsimpl`.
  simpa [localization_lowerShriek_associatedSheafIso, Category.assoc] using hsimpl

/-- Helper for Lemma 7.25.4: the explicit sigma-model identification of the lower-shriek of the
identity representable is the inverse of the standard continuous-representable Lan comparison. -/
theorem localization_identity_leftKanExtension_eq_compULiftYoneda
    (U : C)
    [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F] :
    (localization_identity_leftKanExtension_iso_representable (U := U)).hom =
      ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max u v} (Over.forget U)).inv.app
        (Over.mk (𝟙 U))) := by
  let R : (Over U)ᵒᵖ ⥤ Type (max u v) :=
    ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
      (Over U)ᵒᵖ ⥤ Type (max u v))
  -- Both maps out of the left Kan extension are determined by their value on the Lan unit at the
  -- terminal object `U ⟶ U`.
  apply ((Over.forget U).op.lan.obj R).hom_ext_of_isLeftKanExtension
    ((Over.forget U).op.lanUnit.app R)
  change
    (show R ⟶ (Over.forget U).op ⋙ representable_presheaf (U := U) from
      (Over.forget U).op.lanUnit.app R ≫
        (Over.forget U).op.whiskerLeft
          (localization_identity_leftKanExtension_iso_representable (U := U)).hom) =
    (show R ⟶ (Over.forget U).op ⋙ representable_presheaf (U := U) from
      (Over.forget U).op.lanUnit.app R ≫
        (Over.forget U).op.whiskerLeft
          ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max u v} (Over.forget U)).inv.app
            (Over.mk (𝟙 U))))
  apply (CategoryTheory.uliftYonedaEquiv (X := Over.mk (𝟙 U))
    (F := (Over.forget U).op ⋙ representable_presheaf (U := U))).injective
  change
    (localization_identity_leftKanExtension_iso_representable (U := U)).hom.app (op U)
      (((Over.forget U).op.lanUnit.app R).app (op (Over.mk (𝟙 U)))
        (ULift.up (𝟙 (Over.mk (𝟙 U))))) =
    ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max u v} (Over.forget U)).inv.app
        (Over.mk (𝟙 U))).app (op U)
      (((Over.forget U).op.lanUnit.app R).app (op (Over.mk (𝟙 U)))
        (ULift.up (𝟙 (Over.mk (𝟙 U)))))
  have hleft :
      (localization_identity_leftKanExtension_iso_representable (U := U)).hom.app (op U)
        (((Over.forget U).op.lanUnit.app R).app (op (Over.mk (𝟙 U)))
          (ULift.up (𝟙 (Over.mk (𝟙 U))))) =
        (ULift.up (𝟙 U) : (representable_presheaf (U := U)).obj (op U)) := by
    change
      (identity_sigma_iso_representable (U := U) U).hom
        ((localization_leftKanExtension_objIsoSigma (U := U) R U).hom
          (((Over.forget U).op.lanUnit.app R).app (op (Over.mk (𝟙 U)))
            (ULift.up (𝟙 (Over.mk (𝟙 U)))))) =
        (ULift.up (𝟙 U) : (representable_presheaf (U := U)).obj (op U))
    have hσ := localization_leftKanExtension_objIsoSigma_hom_unit_app
      (U := U) R (𝟙 U) (ULift.up (𝟙 (Over.mk (𝟙 U))))
    rw [show (localization_leftKanExtension_objIsoSigma (U := U) R U).hom
          (((Over.forget U).op.lanUnit.app R).app (op (Over.mk (𝟙 U)))
            (ULift.up (𝟙 (Over.mk (𝟙 U))))) =
        ⟨𝟙 U, (ULift.up (𝟙 (Over.mk (𝟙 U))) : R.obj (op (Over.mk (𝟙 U))))⟩ by
      simpa [R, Functor.lanUnit] using hσ]
    rfl
  have hright :
      ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max u v} (Over.forget U)).inv.app
          (Over.mk (𝟙 U))).app (op U)
        (((Over.forget U).op.lanUnit.app R).app (op (Over.mk (𝟙 U)))
          (ULift.up (𝟙 (Over.mk (𝟙 U))))) =
        (ULift.up (𝟙 U) : (representable_presheaf (U := U)).obj (op U)) := by
    simpa [R, Functor.lanUnit] using
      (Presheaf.compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id
        (F := Over.forget U) (X := Over.mk (𝟙 U)))
  exact hleft.trans hright.symm

/-- Helper for Lemma 7.25.4: the inverse of an isomorphism after `presheafToSheaf` is the
corresponding inverse after rewriting through the `plusPlus` model of sheafification. -/
theorem presheafToSheaf_map_inv_hom_eq_plusPlus
    [HasWeakSheafify J (Type (max u v))]
    {P Q : Cᵒᵖ ⥤ Type (max u v)} (η : P ⟶ Q)
    [IsIso ((presheafToSheaf J (Type (max u v))).map η)]
    [IsIso (J.sheafifyMap η)] :
    (inv ((presheafToSheaf J (Type (max u v))).map η)).hom =
      (plusPlusIsoSheafify J (Type (max u v)) Q).inv ≫
        inv (J.sheafifyMap η) ≫
          (plusPlusIsoSheafify J (Type (max u v)) P).hom := by
  let F := presheafToSheaf J (Type (max u v))
  let βP := plusPlusIsoSheafify J (Type (max u v)) P
  let βQ := plusPlusIsoSheafify J (Type (max u v)) Q
  letI : IsIso (F.map η).hom := by
    change IsIso ((sheafToPresheaf J (Type (max u v))).map (F.map η))
    infer_instance
  have hnat :
      J.sheafifyMap η ≫ βQ.hom = βP.hom ≫ (F.map η).hom := by
    simpa [F, βP, βQ, GrothendieckTopology.sheafification_map, sheafification_map] using
      (plusPlusFunctorIsoSheafification J (Type (max u v))).hom.naturality η
  have hrew :
      (F.map η).hom = βP.inv ≫ J.sheafifyMap η ≫ βQ.hom := by
    simpa [Category.assoc] using congrArg (fun k ↦ βP.inv ≫ k) hnat.symm
  change (sheafToPresheaf J (Type (max u v))).map (inv (F.map η)) =
      βQ.inv ≫ inv (J.sheafifyMap η) ≫ βP.hom
  rw [Functor.map_inv]
  change inv (F.map η).hom = βQ.inv ≫ inv (J.sheafifyMap η) ≫ βP.hom
  apply IsIso.inv_eq_of_hom_inv_id
  rw [hrew]
  simp [Category.assoc]

/-- Helper for Lemma 7.25.4: for the terminal object of `C/U`, the lower-shriek identification
followed by the raw `h_U` identification is the inverse of the continuous-representable
comparison. -/
theorem identity_tail_eq_continuous_symm :
    let R : (Over U)ᵒᵖ ⥤ Type (max u v) :=
      ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
        (Over U)ᵒᵖ ⥤ Type (max u v))
    (localization_lowerShriek_associatedSheafIso J U R).hom ≫
        (presheafToSheaf J (Type (max u v))).map
          (localization_identity_leftKanExtension_iso_representable (U := U)).hom =
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).symm.hom := by
  let F := presheafToSheaf J (Type (max u v))
  let R : (Over U)ᵒᵖ ⥤ Type (max u v) :=
    ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
      (Over U)ᵒᵖ ⥤ Type (max u v))
  let A := Type (max u v)
  -- Normalize the two explicit constructions to the same `sheafPullbackIso` tail and compare the
  -- middle sheafification inverse through the `plusPlus` model.
  have hidentity :
      (localization_identity_leftKanExtension_iso_representable (U := U)).hom =
        ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{max u v} (Over.forget U)).inv.app
          (Over.mk (𝟙 U))) :=
    localization_identity_leftKanExtension_eq_compULiftYoneda (U := U)
  let η : ((Over.forget U).op.lan).obj R ⟶
      ((Over.forget U).op.lan).obj ((J.over U).sheafify R) :=
    ((Over.forget U).op.lan).map ((J.over U).toSheafify R)
  let invPlus : ((Over.forget U).op.lan).obj (CategoryTheory.sheafify (J.over U) R) ⟶
      ((Over.forget U).op.lan).obj ((J.over U).sheafify R) :=
    (Functor.mapIso ((Over.forget U).op.lan)
      (plusPlusIsoSheafify (J.over U) A R)).inv
  letI : IsIso (J.sheafifyMap η) :=
    continuous_pullback_sheafification_comparison_isIso
      (Over.forget U) (J.over U) J R
  have hηW : J.W η := by
    have hsource :
        (J.over U).W ((J.over U).toSheafify R) := by
      refine ((J.over U).W.cancel_right_of_respectsIso
        ((J.over U).toSheafify R) (plusPlusIsoSheafify (J.over U) A R).hom).1 ?_
      simpa [toSheafify_plusPlusIsoSheafify_hom (J.over U) A R] using
        ((J.over U).W_toSheafify R :
          (J.over U).W (CategoryTheory.toSheafify (J.over U) R))
    dsimp [η]
    exact (Over.forget U).W_map_of_adjunction_of_isContinuous (J.over U) J
      ((Over.forget U).op.lan) ((Over.forget U).op.lanAdjunction A)
      ((J.over U).toSheafify R) hsource
  letI : IsIso (F.map η) := (J.W_iff η).1 hηW
  have hgenericInv :
      (inv (F.map η)).hom =
        (plusPlusIsoSheafify J A
            (((Over.forget U).op.lan).obj ((J.over U).sheafify R))).inv ≫
          inv (J.sheafifyMap η) ≫
            (plusPlusIsoSheafify J A (((Over.forget U).op.lan).obj R)).hom := by
    exact presheafToSheaf_map_inv_hom_eq_plusPlus (J := J) η
  have hcanonicalInv :
      (inv (F.map (((Over.forget U).op.lan).map
        (CategoryTheory.toSheafify (J.over U) R)))).hom =
        (F.map invPlus).hom ≫ (inv (F.map η)).hom := by
    have hcanonicalInvSheaf :
        inv (F.map (((Over.forget U).op.lan).map
          (CategoryTheory.toSheafify (J.over U) R))) =
          F.map invPlus ≫ inv (F.map η) := by
      apply IsIso.inv_eq_of_hom_inv_id
      have hto := toSheafify_plusPlusIsoSheafify_hom (J.over U) A R
      have hlan :
          ((Over.forget U).op.lan).map (CategoryTheory.toSheafify (J.over U) R) =
            η ≫ ((Over.forget U).op.lan).map
              (plusPlusIsoSheafify (J.over U) A R).hom := by
        dsimp [η]
        rw [← Functor.map_comp]
        exact (congrArg (((Over.forget U).op.lan).map) hto).symm
      rw [hlan]
      dsimp [invPlus]
      simp [Category.assoc]
    exact congrArg (fun k ↦ k.hom) hcanonicalInvSheaf
  apply Sheaf.hom_ext
  dsimp [localization_lowerShriek_associatedSheafIso, continuous_sheafified_representable_iso,
    hidentity, F, R, A, η, invPlus]
  dsimp [η] at hgenericInv
  dsimp [invPlus] at hcanonicalInv
  rw [hcanonicalInv, hgenericInv, hidentity]
  simp only [F, R, A, GrothendieckTopology.uliftSheafifiedRepresentable,
    GrothendieckTopology.sheafifiedRepresentable]
  cat_disch

/-- Helper for Lemma 7.25.4: the sheafified first-coordinate map for a lower-shriek object is
the canonical structure morphism to the sheafified representable. -/
theorem lowerShriek_firstCoordinate_eq_representableLocalizationHom
    (G : (Over U)ᵒᵖ ⥤ Type (max u v)) :
    let firstMap : ((Over.forget U).op.lan.obj G) ⟶ representable_presheaf (U := U) :=
      { app := fun V x =>
          ULift.up
            (((localization_leftKanExtension_objIsoSigma (U := U) G (unop V)).hom x).1)
        naturality := by
          intro V Y f
          funext x
          apply ULift.ext
          simpa [representable_presheaf] using congrArg Sigma.fst
            (localization_leftKanExtension_objIsoSigma_hom_map (U := U) G f.unop x) }
    (localization_lowerShriek_associatedSheafIso J U G).hom ≫
      (presheafToSheaf J (Type (max u v))).map firstMap =
      J.representableLocalizationHom U
        ((presheafToSheaf (J.over U) (Type (max u v))).obj G) := by
  dsimp only
  rw [← localization_leftKanExtension_first_coordinate_eq_terminal (U := U) G]
  let R : (Over U)ᵒᵖ ⥤ Type (max u v) :=
    ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
      (Over U)ᵒᵖ ⥤ Type (max u v))
  let terminalMap : G ⟶ R :=
    (IsTerminal.isTerminalObj CategoryTheory.uliftYoneda.{max u v}
      (Over.mk (𝟙 U)) Over.mkIdTerminal).from G
  change
    (localization_lowerShriek_associatedSheafIso J U G).hom ≫
      (presheafToSheaf J (Type (max u v))).map
        (((Over.forget U).op.lan).map terminalMap ≫
          (localization_identity_leftKanExtension_iso_representable (U := U)).hom) =
      J.representableLocalizationHom U
        ((presheafToSheaf (J.over U) (Type (max u v))).obj G)
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc]
  rw [← localization_lowerShriek_associatedSheafIso_naturality
    (J := J) (U := U) (η := terminalMap)]
  have hterminalSheaf :
      (presheafToSheaf (J.over U) (Type (max u v))).map terminalMap =
        (localized_identity_sheafifiedRepresentable_isTerminal J U).from
          ((presheafToSheaf (J.over U) (Type (max u v))).obj G) := by
    exact (localized_identity_sheafifiedRepresentable_isTerminal J U).hom_ext _ _
  rw [hterminalSheaf, representableLocalizationHom]
  have htail := identity_tail_eq_continuous_symm (J := J) (U := U)
  dsimp at htail
  simpa [Category.assoc] using congrArg
    (fun k =>
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((localized_identity_sheafifiedRepresentable_isTerminal J U).from
          ((presheafToSheaf (J.over U) (Type (max u v))).obj G)) ≫ k)
    htail

/-- Helper for Lemma 7.25.4: sheafifying the raw localization object over `h_U` gives the
comparison object over `h_U^#`. -/
noncomputable def localization_over_representable_post_component
    (𝒢 : Sheaf (J.over U) (Type (max u v))) :
    (J.representableLocalizationComparison U).obj 𝒢 ≅
      (Over.post (X := representable_presheaf (U := U))
          (presheafToSheaf J (Type (max u v)))).obj
        (localization_over_representable (J := J) (U := U) 𝒢) := by
  let F := presheafToSheaf J (Type (max u v))
  let L := (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J
  let e𝒢 := (sheafificationNatIso (J.over U) (Type (max u v))).app 𝒢
  let eleft : L.obj 𝒢 ≅ F.obj ((Over.forget U).op.lan.obj 𝒢.obj) :=
    Functor.mapIso L e𝒢 ≪≫ localization_lowerShriek_associatedSheafIso J U 𝒢.obj
  refine Over.isoMk eleft ?_
  -- The structure map is the sheafified first-coordinate owner map; precomposing by
  -- sheafification of `𝒢.obj` is removed by naturality of `representableLocalizationHom`.
  change eleft.hom ≫ F.map (localization_over_representable (J := J) (U := U) 𝒢).hom =
    J.representableLocalizationHom U 𝒢
  dsimp [eleft]
  have hfirst :=
    lowerShriek_firstCoordinate_eq_representableLocalizationHom
      (J := J) (U := U) 𝒢.obj
  dsimp at hfirst
  have hfirst' :
      (localization_lowerShriek_associatedSheafIso J U 𝒢.obj).hom ≫
          F.map (localization_over_representable (J := J) (U := U) 𝒢).hom =
        J.representableLocalizationHom U
          ((presheafToSheaf (J.over U) (Type (max u v))).obj 𝒢.obj) := by
    simpa [F, localization_over_representable] using hfirst
  have hcomp := congrArg (fun k ↦ L.map e𝒢.hom ≫ k) hfirst'
  have hnat :=
    representableLocalizationHom_naturality
      (J := J) (U := U) (η := e𝒢.hom)
  simpa [Category.assoc] using hcomp.trans hnat

/-- Helper for Lemma 7.25.4: the previous source-side comparison is natural in sheaves on the
localized site. -/
theorem localization_over_representable_post_component_naturality
    {𝒢 𝒢' : Sheaf (J.over U) (Type (max u v))} (η : 𝒢 ⟶ 𝒢') :
    ((J.representableLocalizationComparison U).map η ≫
        (localization_over_representable_post_component (J := J) (U := U) 𝒢').hom).left =
      ((localization_over_representable_post_component (J := J) (U := U) 𝒢).hom ≫
        (Over.post (X := representable_presheaf (U := U))
          (presheafToSheaf J (Type (max u v)))).map
          (localization_over_representable_map (J := J) (U := U) η)).left := by
  let F := presheafToSheaf J (Type (max u v))
  let L := (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J
  let e𝒢 := (sheafificationNatIso (J.over U) (Type (max u v))).app 𝒢
  let e𝒢' := (sheafificationNatIso (J.over U) (Type (max u v))).app 𝒢'
  -- On left components this is the naturality square of `sheafificationNatIso`, followed by the
  -- naturality of the lower-shriek/sheafification comparison.
  rw [Over.comp_left, Over.comp_left]
  dsimp [localization_over_representable_post_component, localization_over_representable_map]
  have hsheaf :
      η ≫ e𝒢'.hom =
        e𝒢.hom ≫ (presheafToSheaf (J.over U) (Type (max u v))).map η.hom := by
    simpa [e𝒢, e𝒢'] using
      (sheafificationNatIso (J.over U) (Type (max u v))).hom.naturality η
  have hL :
      L.map η ≫ L.map e𝒢'.hom =
        L.map e𝒢.hom ≫ L.map ((presheafToSheaf (J.over U) (Type (max u v))).map η.hom) := by
    simpa [Functor.map_comp] using congrArg (fun k ↦ L.map k) hsheaf
  change
    (L.map η ≫ L.map e𝒢'.hom) ≫
        (localization_lowerShriek_associatedSheafIso J U 𝒢'.obj).hom =
      (L.map e𝒢.hom ≫
          (localization_lowerShriek_associatedSheafIso J U 𝒢.obj).hom) ≫
        F.map (((Over.forget U).op.lan).map η.hom)
  calc
    (L.map η ≫ L.map e𝒢'.hom) ≫
        (localization_lowerShriek_associatedSheafIso J U 𝒢'.obj).hom =
      (L.map e𝒢.hom ≫
          L.map ((presheafToSheaf (J.over U) (Type (max u v))).map η.hom)) ≫
        (localization_lowerShriek_associatedSheafIso J U 𝒢'.obj).hom := by
        exact congrArg
          (fun k ↦ k ≫ (localization_lowerShriek_associatedSheafIso J U 𝒢'.obj).hom)
          hL
    _ = L.map e𝒢.hom ≫
          (L.map ((presheafToSheaf (J.over U) (Type (max u v))).map η.hom) ≫
            (localization_lowerShriek_associatedSheafIso J U 𝒢'.obj).hom) := by
        rw [Category.assoc]
    _ = L.map e𝒢.hom ≫
          ((localization_lowerShriek_associatedSheafIso J U 𝒢.obj).hom ≫
            F.map (((Over.forget U).op.lan).map η.hom)) := by
        exact congrArg (fun k ↦ L.map e𝒢.hom ≫ k)
          (localization_lowerShriek_associatedSheafIso_naturality
            (J := J) (U := U) (η := η.hom))
    _ = (L.map e𝒢.hom ≫
          (localization_lowerShriek_associatedSheafIso J U 𝒢.obj).hom) ≫
        F.map (((Over.forget U).op.lan).map η.hom) := by
        rw [Category.assoc]

/-- Helper for Lemma 7.25.4: functorially, the comparison object is obtained by sheafifying the
raw localization object over the raw representable. -/
noncomputable def localization_over_representable_post_natIso :
    J.representableLocalizationComparison U ≅
      localization_over_representableFunctor (J := J) (U := U) ⋙
        Over.post (X := representable_presheaf (U := U))
          (presheafToSheaf J (Type (max u v))) := by
  -- The objectwise `Over`-isomorphisms above are natural because their left components are
  -- natural.
  refine NatIso.ofComponents
    (fun 𝒢 ↦ localization_over_representable_post_component (J := J) (U := U) 𝒢) ?_
  intro 𝒢 𝒢' η
  apply Over.OverMorphism.ext
  simpa using
    localization_over_representable_post_component_naturality (J := J) (U := U) η

/-- Helper for Lemma 7.25.4: the raw sigma-of-fibres comparison respects the structure map
over `h_U` for any raw slice object over the representable presheaf. -/
theorem raw_sigma_structure_map_compatibility
    (P : Over (representable_presheaf (U := U))) :
    let S := (presheafToSheaf (J.over U) (Type (max u v))).obj
      ((fiber_presheaf_over_representable (U := U)).obj P)
    let e :
        ((J.representableLocalizationComparison U).obj S).left ≅
          ((Over.post (X := representable_presheaf (U := U))
              (presheafToSheaf J (Type (max u v)))).obj P).left :=
      localization_lowerShriek_associatedSheafIso J U
          ((fiber_presheaf_over_representable (U := U)).obj P) ≪≫
        Functor.mapIso (presheafToSheaf J (Type (max u v)))
          (sigma_of_fibres_natIso (U := U) P)
    e.hom ≫ ((Over.post (X := representable_presheaf (U := U))
        (presheafToSheaf J (Type (max u v)))).obj P).hom =
      ((J.representableLocalizationComparison U).obj S).hom := by
  dsimp
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  change
    (localization_lowerShriek_associatedSheafIso J U
          ((fiber_presheaf_over_representable (U := U)).obj P)).hom ≫
      (presheafToSheaf J (Type (max u v))).map
        ((sigma_of_fibres_natIso (U := U) P).hom ≫ P.hom) =
    J.representableLocalizationHom U
      ((presheafToSheaf (J.over U) (Type (max u v))).obj
        ((fiber_presheaf_over_representable (U := U)).obj P))
  rw [sigma_of_fibres_natIso_owner (U := U) P]
  -- The owner map is precisely the sheafified first-coordinate map for the lower-shriek model.
  simpa using
    lowerShriek_firstCoordinate_eq_representableLocalizationHom
      (J := J) (U := U)
      ((fiber_presheaf_over_representable (U := U)).obj P)

/-- Helper for Lemma 7.25.4: the target-side raw presheaf identity
`j_{U!}^{PSh}(F_\varphi) = F` as a slice-level isomorphism after sheafification. -/
noncomputable def raw_sigma_over_component
    (P : Over (representable_presheaf (U := U))) :
    (J.representableLocalizationComparison U).obj
        ((presheafToSheaf (J.over U) (Type (max u v))).obj
          ((fiber_presheaf_over_representable (U := U)).obj P)) ≅
      (Over.post (X := representable_presheaf (U := U))
        (presheafToSheaf J (Type (max u v)))).obj P := by
  let S := (presheafToSheaf (J.over U) (Type (max u v))).obj
    ((fiber_presheaf_over_representable (U := U)).obj P)
  let e :
      ((J.representableLocalizationComparison U).obj S).left ≅
        ((Over.post (X := representable_presheaf (U := U))
            (presheafToSheaf J (Type (max u v)))).obj P).left :=
    localization_lowerShriek_associatedSheafIso J U
        ((fiber_presheaf_over_representable (U := U)).obj P) ≪≫
      Functor.mapIso (presheafToSheaf J (Type (max u v)))
        (sigma_of_fibres_natIso (U := U) P)
  refine Over.isoMk e ?_
  simpa [S, e] using raw_sigma_structure_map_compatibility (J := J) (U := U) P

/-- Helper for Lemma 7.25.4: the target-side sigma-of-fibres identification respects the structure
map to `h_U^#`. -/
theorem comparison_counit_structure_map_compatibility
    (T : Over h[U]^#[J]) :
    let P := (pullback_to_representable (J := J) (U := U)).obj T
    let e :
        ((comparison_inverse (J := J) (U := U) ⋙ J.representableLocalizationComparison U).obj T).left ≅
          ((pullback_to_representable (J := J) (U := U) ⋙
              Over.post (presheafToSheaf J (Type (max u v)))).obj T).left :=
      localization_lowerShriek_associatedSheafIso J U
          ((fiber_presheaf_over_representable (U := U)).obj P) ≪≫
        Functor.mapIso (presheafToSheaf J (Type (max u v)))
          (sigma_of_fibres_natIso (U := U) P)
    e.hom ≫ ((pullback_to_representable (J := J) (U := U) ⋙
        Over.post (presheafToSheaf J (Type (max u v)))).obj T).hom =
      ((comparison_inverse (J := J) (U := U) ⋙
        J.representableLocalizationComparison U).obj T).hom := by
  -- TODO: compare the sheafified sigma-of-fibres map with the terminal-arrow structure morphism
  -- defining `representableLocalizationHom`; this is the remaining target-side owner equality.
  dsimp
  rw [comparison_inverse_comparison_hom_eq]
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp]
  let P := (pullback_to_representable (J := J) (U := U)).obj T
  change
    (localization_lowerShriek_associatedSheafIso J U
          ((fiber_presheaf_over_representable (U := U)).obj P)).hom ≫
      (presheafToSheaf J (Type (max u v))).map
        ((sigma_of_fibres_natIso (U := U) P).hom ≫ P.hom) =
    J.representableLocalizationHom U ((comparison_inverse (J := J) (U := U)).obj T)
  rw [sigma_of_fibres_natIso_owner (U := U) P]
  -- The owner map is precisely the sheafified first-coordinate map for the lower-shriek model.
  simpa using
    lowerShriek_firstCoordinate_eq_representableLocalizationHom
      (J := J) (U := U)
      ((fiber_presheaf_over_representable (U := U)).obj P)

/-- Helper for Lemma 7.25.4: local injectivity of the underlying map over `h_U` restricts to
local injectivity on the fibre presheaves over the localized site. -/
theorem fiber_presheaf_hom_isLocallyInjective_of_left
    {P Q : Over (representable_presheaf (U := U))} (α : P ⟶ Q)
    [Presheaf.IsLocallyInjective J α.left] :
    Presheaf.IsLocallyInjective (J.over U)
      ((fiber_presheaf_over_representable (U := U)).map α) := by
  constructor
  intro X x y hxy
  cases X using Opposite.rec
  rename_i X
  have hleft : α.left.app (op X.left) x.1 = α.left.app (op X.left) y.1 := by
    exact congrArg Subtype.val hxy
  have hbase :
      Presheaf.equalizerSieve (F := P.left) (X := op X.left) x.1 y.1 ∈ J X.left := by
    exact Presheaf.equalizerSieve_mem J α.left x.1 y.1 hleft
  refine (J.over U).superset_covering ?_
    (J.overEquiv_symm_mem_over X
      (Presheaf.equalizerSieve (F := P.left) (X := op X.left) x.1 y.1) hbase)
  intro Y f hf
  apply Subtype.ext
  simpa [fiber_presheaf_over_representable, fiber_presheaf_map] using hf

/-- Helper for Lemma 7.25.4: local surjectivity of the underlying map over `h_U` restricts to
local surjectivity on the fibre presheaves over the localized site. -/
theorem fiber_presheaf_hom_isLocallySurjective_of_left
    {P Q : Over (representable_presheaf (U := U))} (α : P ⟶ Q)
    [Presheaf.IsLocallySurjective J α.left] :
    Presheaf.IsLocallySurjective (J.over U)
      ((fiber_presheaf_over_representable (U := U)).map α) := by
  constructor
  intro X z
  let S : Sieve X.left := Presheaf.imageSieve α.left z.1
  have hS : S ∈ J X.left := Presheaf.imageSieve_mem J α.left z.1
  refine (J.over U).superset_covering ?_ (J.overEquiv_symm_mem_over X S hS)
  intro Y f hf
  rcases hf with ⟨t, ht⟩
  have htbase : (P.hom.app (op Y.left) t).down = Y.hom := by
    have hαbase :=
      congrFun (NatTrans.congr_app (Over.w α) (op Y.left)) t
    dsimp at hαbase
    have hzbase :
        (Q.hom.app (op Y.left) (Q.left.map f.left.op z.1)).down = Y.hom := by
      have hnat := congrFun (Q.hom.naturality f.left.op) z.1
      dsimp at hnat
      rw [z.2] at hnat
      exact (congrArg ULift.down hnat).trans (Over.w f)
    have hval :
        P.hom.app (op Y.left) t =
          Q.hom.app (op Y.left) (Q.left.map f.left.op z.1) := by
      exact hαbase.symm.trans (congrArg (Q.hom.app (op Y.left)) ht)
    exact (congrArg ULift.down hval).trans hzbase
  refine ⟨⟨t, htbase⟩, ?_⟩
  apply Subtype.ext
  simpa [fiber_presheaf_over_representable, fiber_presheaf_hom, fiber_presheaf_map] using ht

/-- Helper for Lemma 7.25.4: a local weak equivalence over the raw representable remains a local
weak equivalence after taking the textbook fibre presheaves on `C/U`. -/
theorem fiber_presheaf_map_W_of_left_W
    {P Q : Over (representable_presheaf (U := U))} (α : P ⟶ Q) (hα : J.W α.left) :
    (J.over U).W ((fiber_presheaf_over_representable (U := U)).map α) := by
  letI : Presheaf.IsLocallyInjective J α.left := hα.isLocallyInjective
  letI : Presheaf.IsLocallySurjective J α.left := hα.isLocallySurjective
  exact ((J.over U).W_iff_isLocallyBijective
    ((fiber_presheaf_over_representable (U := U)).map α)).2
      ⟨fiber_presheaf_hom_isLocallyInjective_of_left (J := J) (U := U) α,
        fiber_presheaf_hom_isLocallySurjective_of_left (J := J) (U := U) α⟩

/-- Helper for Lemma 7.25.4: the explicit unit map from a raw object over `h_U` to the pullback
of its sheafification along `h_U ⟶ h_U^#`. -/
noncomputable def pullback_sheafification_unit_map
    (P : Over (representable_presheaf (U := U))) :
    P ⟶ (Over.post (X := representable_presheaf (U := U))
      (presheafToSheaf J (Type (max u v))) ⋙
      pullback_to_representable (J := J) (U := U)).obj P := by
  let ηP : P.left ⟶ (sheafToPresheaf J (Type (max u v))).obj
      ((presheafToSheaf J (Type (max u v))).obj P.left) :=
    CategoryTheory.toSheafify J P.left
  let w : ηP ≫ ((presheafToSheaf J (Type (max u v))).map P.hom).hom =
      P.hom ≫ CategoryTheory.toSheafify J (representable_presheaf (U := U)) := by
    simpa [ηP] using (CategoryTheory.toSheafify_naturality (J := J) P.hom).symm
  refine Over.homMk (pullback.lift ηP P.hom w) ?_
  · change pullback.lift ηP P.hom w ≫
        pullback.snd ((presheafToSheaf J (Type (max u v))).map P.hom).hom
          (CategoryTheory.toSheafify J (representable_presheaf (U := U))) = P.hom
    simpa using (pullback.lift_snd ηP P.hom w)

/-- Helper for Lemma 7.25.4: the first projection of the explicit unit pullback map is the
sheafification unit of the underlying presheaf. -/
theorem pullback_sheafification_unit_map_fst
    (P : Over (representable_presheaf (U := U))) :
    (pullback_sheafification_unit_map (J := J) (U := U) P).left ≫
        pullback.fst
          ((sheafToPresheaf J (Type (max u v))).map
            ((presheafToSheaf J (Type (max u v))).map P.hom))
          (CategoryTheory.toSheafify J (representable_presheaf (U := U))) =
      CategoryTheory.toSheafify J P.left := by
  let ηP : P.left ⟶ (sheafToPresheaf J (Type (max u v))).obj
      ((presheafToSheaf J (Type (max u v))).obj P.left) :=
    CategoryTheory.toSheafify J P.left
  let w : ηP ≫ ((presheafToSheaf J (Type (max u v))).map P.hom).hom =
      P.hom ≫ CategoryTheory.toSheafify J (representable_presheaf (U := U)) := by
    simpa [ηP] using (CategoryTheory.toSheafify_naturality (J := J) P.hom).symm
  simpa [pullback_sheafification_unit_map, ηP, w] using
    (pullback.lift_fst ηP P.hom w)

/-- Helper for Lemma 7.25.4: the second projection of the explicit unit pullback map is the
original structure morphism over `h_U`. -/
theorem pullback_sheafification_unit_map_snd
    (P : Over (representable_presheaf (U := U))) :
    (pullback_sheafification_unit_map (J := J) (U := U) P).left ≫
        pullback.snd
          ((sheafToPresheaf J (Type (max u v))).map
            ((presheafToSheaf J (Type (max u v))).map P.hom))
          (CategoryTheory.toSheafify J (representable_presheaf (U := U))) =
      P.hom := by
  simpa using Over.w (pullback_sheafification_unit_map (J := J) (U := U) P)

/-- Helper for Lemma 7.25.4: the explicit unit map is natural in raw objects over `h_U`. -/
theorem pullback_sheafification_unit_map_naturality
    {P Q : Over (representable_presheaf (U := U))} (α : P ⟶ Q) :
    α ≫ pullback_sheafification_unit_map (J := J) (U := U) Q =
      pullback_sheafification_unit_map (J := J) (U := U) P ≫
        (Over.post (X := representable_presheaf (U := U))
          (presheafToSheaf J (Type (max u v))) ⋙
          pullback_to_representable (J := J) (U := U)).map α := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left]
  apply pullback.hom_ext
  · let mapα :=
      ((Over.post (X := representable_presheaf (U := U))
        (presheafToSheaf J (Type (max u v))) ⋙
        pullback_to_representable (J := J) (U := U)).map α).left
    let fstP :=
      pullback.fst
        ((sheafToPresheaf J (Type (max u v))).map
          ((presheafToSheaf J (Type (max u v))).map P.hom))
        (CategoryTheory.toSheafify J (representable_presheaf (U := U)))
    let fstQ :=
      pullback.fst
        ((sheafToPresheaf J (Type (max u v))).map
          ((presheafToSheaf J (Type (max u v))).map Q.hom))
        (CategoryTheory.toSheafify J (representable_presheaf (U := U)))
    have h₁ :
        (α.left ≫ (pullback_sheafification_unit_map (J := J) (U := U) Q).left) ≫ fstQ =
          α.left ≫ CategoryTheory.toSheafify J Q.left := by
      simpa [fstQ, Category.assoc] using congrArg (fun f ↦ α.left ≫ f)
        (pullback_sheafification_unit_map_fst (J := J) (U := U) Q)
    have h₂ :
        α.left ≫ CategoryTheory.toSheafify J Q.left =
          CategoryTheory.toSheafify J P.left ≫
            ((presheafToSheaf J (Type (max u v))).map α.left).hom := by
      simpa using (CategoryTheory.toSheafify_naturality (J := J) α.left)
    have hmap : mapα ≫ fstQ =
        fstP ≫ ((presheafToSheaf J (Type (max u v))).map α.left).hom := by
      dsimp [mapα, fstP, fstQ, pullback_to_representable]
      rw [pullback.lift_fst]
    have h₃ :
        CategoryTheory.toSheafify J P.left ≫
            ((presheafToSheaf J (Type (max u v))).map α.left).hom =
          ((pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ mapα) ≫ fstQ := by
      calc
        CategoryTheory.toSheafify J P.left ≫
            ((presheafToSheaf J (Type (max u v))).map α.left).hom =
          ((pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ fstP) ≫
            ((presheafToSheaf J (Type (max u v))).map α.left).hom := by
            rw [pullback_sheafification_unit_map_fst]
            rfl
        _ = (pullback_sheafification_unit_map (J := J) (U := U) P).left ≫
            (fstP ≫ ((presheafToSheaf J (Type (max u v))).map α.left).hom) := by
            rw [Category.assoc]
        _ = (pullback_sheafification_unit_map (J := J) (U := U) P).left ≫
            (mapα ≫ fstQ) := by
            rw [hmap]
            rfl
        _ = ((pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ mapα) ≫
            fstQ := by
            rw [Category.assoc]
    exact h₁.trans (h₂.trans h₃)
  · let mapα :=
      ((Over.post (X := representable_presheaf (U := U))
        (presheafToSheaf J (Type (max u v))) ⋙
        pullback_to_representable (J := J) (U := U)).map α).left
    let sndP :=
      pullback.snd
        ((sheafToPresheaf J (Type (max u v))).map
          ((presheafToSheaf J (Type (max u v))).map P.hom))
        (CategoryTheory.toSheafify J (representable_presheaf (U := U)))
    let sndQ :=
      pullback.snd
        ((sheafToPresheaf J (Type (max u v))).map
          ((presheafToSheaf J (Type (max u v))).map Q.hom))
        (CategoryTheory.toSheafify J (representable_presheaf (U := U)))
    have h₁ :
        (α.left ≫ (pullback_sheafification_unit_map (J := J) (U := U) Q).left) ≫ sndQ =
          α.left ≫ Q.hom := by
      simpa [sndQ, Category.assoc] using congrArg (fun f ↦ α.left ≫ f)
        (pullback_sheafification_unit_map_snd (J := J) (U := U) Q)
    have h₂ : α.left ≫ Q.hom = P.hom := by
      simpa using Over.w α
    have hmap : mapα ≫ sndQ = sndP := by
      dsimp [mapα, sndP, sndQ, pullback_to_representable]
      rw [pullback.lift_snd]
    have h₃ :
        P.hom =
          ((pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ mapα) ≫ sndQ := by
      calc
        P.hom =
          (pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ sndP := by
          rw [pullback_sheafification_unit_map_snd]
        _ = (pullback_sheafification_unit_map (J := J) (U := U) P).left ≫
            (mapα ≫ sndQ) := by
          rw [hmap]
        _ = ((pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ mapα) ≫
            sndQ := by
          rw [Category.assoc]
    exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 7.25.4: the underlying map of the explicit unit is a local weak
equivalence. -/
theorem pullback_sheafification_unit_map_left_W
    (P : Over (representable_presheaf (U := U))) :
    J.W (pullback_sheafification_unit_map (J := J) (U := U) P).left := by
  let F := presheafToSheaf J (Type (max u v))
  let ηU := CategoryTheory.toSheafify J (representable_presheaf (U := U))
  let fstP :=
    pullback.fst
      ((sheafToPresheaf J (Type (max u v))).map (F.map P.hom))
      ηU
  have hfstIso : IsIso (F.map fstP) := by
    let T : Over h[U]^#[J] :=
      (Over.post (X := representable_presheaf (U := U)) F).obj P
    simpa [T, F, fstP, ηU, GrothendieckTopology.sheafifiedRepresentable,
      GrothendieckTopology.uliftSheafifiedRepresentable] using
      sheafified_pullback_projection_isIso (J := J) (U := U) T
  have hunitIso : IsIso (F.map (CategoryTheory.toSheafify J P.left)) := by
    exact (J.W_iff (CategoryTheory.toSheafify J P.left)).1 (J.W_toSheafify P.left)
  rw [J.W_iff]
  have hcomp :
      F.map ((pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ fstP) =
        F.map (CategoryTheory.toSheafify J P.left) := by
    simpa [F, fstP, ηU] using
      congrArg (fun f ↦ F.map f)
        (pullback_sheafification_unit_map_fst (J := J) (U := U) P)
  have hcompIso :
      IsIso (F.map ((pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ fstP)) := by
    rw [hcomp]
    exact hunitIso
  rw [Functor.map_comp] at hcompIso
  haveI : IsIso (F.map fstP) := hfstIso
  haveI : IsIso
      (F.map (pullback_sheafification_unit_map (J := J) (U := U) P).left ≫ F.map fstP) :=
    hcompIso
  exact @IsIso.of_isIso_comp_right (Sheaf J (Type (max u v))) _ _ _ _
    (F.map (pullback_sheafification_unit_map (J := J) (U := U) P).left) (F.map fstP)
    hfstIso hcompIso

/-- Helper for Lemma 7.25.4: after taking fibres and sheafifying on `C/U`, the explicit unit map
becomes an isomorphism. -/
theorem pullback_sheafification_unit_fiber_sheafification_isIso
    (P : Over (representable_presheaf (U := U))) :
    IsIso
      ((fiber_presheaf_over_representable (U := U) ⋙
          presheafToSheaf (J.over U) (Type (max u v))).map
        (pullback_sheafification_unit_map (J := J) (U := U) P)) := by
  let φ := (fiber_presheaf_over_representable (U := U)).map
    (pullback_sheafification_unit_map (J := J) (U := U) P)
  have hW : (J.over U).W φ :=
    fiber_presheaf_map_W_of_left_W (J := J) (U := U)
      (pullback_sheafification_unit_map (J := J) (U := U) P)
      (pullback_sheafification_unit_map_left_W (J := J) (U := U) P)
  simpa [φ] using ((J.over U).W_iff φ).1 hW

/-- Helper for Lemma 7.25.4: functorial form of the fact that inserting the sheafification-unit
pullback does not change the sheafified fibre of a raw localization object. -/
noncomputable def pullback_sheafification_unit_fiber_natIso :
    localization_over_representableFunctor (J := J) (U := U) ⋙
        fiber_presheaf_over_representable (U := U) ⋙
        presheafToSheaf (J.over U) (Type (max u v)) ≅
      localization_over_representableFunctor (J := J) (U := U) ⋙
        Over.post (X := representable_presheaf (U := U))
          (presheafToSheaf J (Type (max u v))) ⋙
        pullback_to_representable (J := J) (U := U) ⋙
        fiber_presheaf_over_representable (U := U) ⋙
        presheafToSheaf (J.over U) (Type (max u v)) := by
  let K := fiber_presheaf_over_representable (U := U) ⋙
      presheafToSheaf (J.over U) (Type (max u v))
  refine NatIso.ofComponents (fun 𝒢 ↦ ?_) ?_
  · have hIso : IsIso
        (K.map (pullback_sheafification_unit_map (J := J) (U := U)
          (localization_over_representable (J := J) (U := U) 𝒢))) := by
      dsimp [K]
      exact pullback_sheafification_unit_fiber_sheafification_isIso (J := J) (U := U)
        (localization_over_representable (J := J) (U := U) 𝒢)
    exact @asIso _ _ _ _
      (K.map (pullback_sheafification_unit_map (J := J) (U := U)
        (localization_over_representable (J := J) (U := U) 𝒢)))
      hIso
  · intro 𝒢 𝒢' η
    simp only [asIso_hom]
    change
      K.map ((localization_over_representableFunctor (J := J) (U := U)).map η) ≫
          K.map (pullback_sheafification_unit_map (J := J) (U := U)
            (localization_over_representable (J := J) (U := U) 𝒢')) =
        K.map (pullback_sheafification_unit_map (J := J) (U := U)
            (localization_over_representable (J := J) (U := U) 𝒢)) ≫
          K.map (((Over.post (X := representable_presheaf (U := U))
            (presheafToSheaf J (Type (max u v))) ⋙
            pullback_to_representable (J := J) (U := U)).map
              ((localization_over_representableFunctor (J := J) (U := U)).map η)))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun f ↦ K.map f)
      (pullback_sheafification_unit_map_naturality (J := J) (U := U)
        ((localization_over_representableFunctor (J := J) (U := U)).map η))

/-- Helper for Lemma 7.25.4: source-faithful unit comparison after applying the fibre construction
and sheafifying on the localized site.  This replaces the overly strong raw pullback
identification: the textbook proof only needs this sheafified fibre comparison. -/
noncomputable def comparison_unit_pullback_fiberNatIso :
    J.representableLocalizationComparison U ⋙ comparison_inverse (J := J) (U := U) ≅
      localization_over_representableFunctor (J := J) (U := U) ⋙
        fiber_presheaf_over_representable (U := U) ⋙
        presheafToSheaf (J.over U) (Type (max u v)) := by
  let K := fiber_presheaf_over_representable (U := U) ⋙
      presheafToSheaf (J.over U) (Type (max u v))
  let postF := Over.post (X := representable_presheaf (U := U))
      (presheafToSheaf J (Type (max u v)))
  let rawPull := pullback_to_representable (J := J) (U := U)
  let h₁ :
      J.representableLocalizationComparison U ⋙ rawPull ⋙ K ≅
        localization_over_representableFunctor (J := J) (U := U) ⋙ postF ⋙ rawPull ⋙ K :=
    Functor.isoWhiskerRight
      (localization_over_representable_post_natIso (J := J) (U := U))
      (rawPull ⋙ K)
  let h₂ :
      localization_over_representableFunctor (J := J) (U := U) ⋙ postF ⋙ rawPull ⋙ K ≅
        localization_over_representableFunctor (J := J) (U := U) ⋙ K :=
    (pullback_sheafification_unit_fiber_natIso (J := J) (U := U)).symm
  simpa [comparison_inverse, K, postF, rawPull, Category.assoc] using h₁ ≪≫ h₂

/-- Helper for Lemma 7.25.4: the objectwise `Over`-isomorphism implementing the raw target-side
sigma-of-fibres comparison. -/
noncomputable def comparison_counit_rawComponent
    (T : Over h[U]^#[J]) :
    ((comparison_inverse (J := J) (U := U) ⋙ J.representableLocalizationComparison U).obj T) ≅
      ((pullback_to_representable (J := J) (U := U) ⋙
          Over.post (presheafToSheaf J (Type (max u v)))).obj T) := by
  let P := (pullback_to_representable (J := J) (U := U)).obj T
  let e :
      ((comparison_inverse (J := J) (U := U) ⋙ J.representableLocalizationComparison U).obj T).left ≅
        ((pullback_to_representable (J := J) (U := U) ⋙
            Over.post (presheafToSheaf J (Type (max u v)))).obj T).left := by
    -- The left object is `j_{U!}` of the sheafified fibre presheaf; identify it with the
    -- sheafification of the sigma-model and then collapse the disjoint union of fibres.
    exact
      localization_lowerShriek_associatedSheafIso J U
          ((fiber_presheaf_over_representable (U := U)).obj P) ≪≫
        Functor.mapIso (presheafToSheaf J (Type (max u v)))
          (sigma_of_fibres_natIso (U := U) P)
  have hw :
      e.hom ≫ ((pullback_to_representable (J := J) (U := U) ⋙
          Over.post (presheafToSheaf J (Type (max u v)))).obj T).hom =
        ((comparison_inverse (J := J) (U := U) ⋙
          J.representableLocalizationComparison U).obj T).hom := by
    -- Reuse the explicit target-side structure-map compatibility proved just above.
    simpa using comparison_counit_structure_map_compatibility (J := J) (U := U) T
  exact Over.isoMk e hw

/-- Helper for Lemma 7.25.4: the left component of the raw target-side sigma-of-fibres
comparison is the expected composite of the lower-shriek/sheafification comparison with the
sheafified sigma-of-fibres isomorphism. -/
theorem comparison_counit_rawComponent_left_formula
    (T : Over h[U]^#[J]) :
    let P := (pullback_to_representable (J := J) (U := U)).obj T
    ((comparison_counit_rawComponent (J := J) (U := U) T).hom).left =
      (localization_lowerShriek_associatedSheafIso J U
          ((fiber_presheaf_over_representable (U := U)).obj P)).hom ≫
        (presheafToSheaf J (Type (max u v))).map (sigma_of_fibres_natIso (U := U) P).hom := by
  -- Unfold `comparison_counit_rawComponent` once: `Over.isoMk` stores exactly this left
  -- component.
  rfl

/-- Helper for Lemma 7.25.4: the left components of the raw target-side sigma-of-fibres
comparison are natural in slice morphisms over `h_U^#`. -/
theorem comparison_counit_rawComponent_left_naturality
    {X Y : Over h[U]^#[J]} (f : X ⟶ Y) :
    ((comparison_inverse (J := J) (U := U) ⋙ J.representableLocalizationComparison U).map f ≫
        (comparison_counit_rawComponent (J := J) (U := U) Y).hom).left =
      ((comparison_counit_rawComponent (J := J) (U := U) X).hom ≫
        (pullback_to_representable (J := J) (U := U) ⋙
          Over.post (presheafToSheaf J (Type (max u v)))).map f).left := by
  let α := (pullback_to_representable (J := J) (U := U)).map f
  -- The left-component square is the naturality of `localization_lowerShriek_associatedSheafIso`
  -- composed with the `sigma_of_fibres_natIso` compatibility over `α`.
  rw [Over.comp_left, Over.comp_left]
  rw [comparison_counit_rawComponent_left_formula, comparison_counit_rawComponent_left_formula]
  change
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((comparison_inverse (J := J) (U := U)).map f) ≫
      (localization_lowerShriek_associatedSheafIso J U
            ((fiber_presheaf_over_representable (U := U)).obj
              ((pullback_to_representable (J := J) (U := U)).obj Y))).hom ≫
        (presheafToSheaf J (Type (max u v))).map
          (sigma_of_fibres_natIso (U := U)
            ((pullback_to_representable (J := J) (U := U)).obj Y)).hom =
      ((localization_lowerShriek_associatedSheafIso J U
            ((fiber_presheaf_over_representable (U := U)).obj
              ((pullback_to_representable (J := J) (U := U)).obj X))).hom ≫
          (presheafToSheaf J (Type (max u v))).map
            (sigma_of_fibres_natIso (U := U)
              ((pullback_to_representable (J := J) (U := U)).obj X)).hom) ≫
        (presheafToSheaf J (Type (max u v))).map
          ((pullback_to_representable (J := J) (U := U)).map f).left
  dsimp [comparison_inverse, Functor.comp_map, α]
  rw [← Category.assoc]
  rw [localization_lowerShriek_associatedSheafIso_naturality
    (J := J) (U := U)
    (η := (fiber_presheaf_over_representable (U := U)).map
      ((pullback_to_representable (J := J) (U := U)).map f))]
  -- Collapse the middle two factors using the already-proved naturality of
  -- `sigma_of_fibres_natIso` over morphisms above `h_U`.
  simpa [Functor.map_comp, Category.assoc] using congrArg
    (fun k ↦
      (localization_lowerShriek_associatedSheafIso J U
            ((fiber_presheaf_over_representable (U := U)).obj
              ((pullback_to_representable (J := J) (U := U)).obj X))).hom ≫
        (presheafToSheaf J (Type (max u v))).map k)
    (sigma_of_fibres_natIso_over_hom
      (U := U) (α := (pullback_to_representable (J := J) (U := U)).map f))

/-- Helper for Lemma 7.25.4: the target-side textbook identity
`j_{U!}^{PSh}(F_φ) = F` packaged as a slice-level natural isomorphism before the final recovery
step to `Over h_U^#`. -/
noncomputable def comparison_counit_rawNatIso :
    comparison_inverse (J := J) (U := U) ⋙ J.representableLocalizationComparison U ≅
      pullback_to_representable (J := J) (U := U) ⋙
        Over.post (presheafToSheaf J (Type (max u v))) := by
  -- Package the source-proof sigma-of-fibres isomorphism objectwise in the slice category over
  -- `h_U^#`, then verify naturality on the left components.
  refine NatIso.ofComponents (fun T ↦ ?_) ?_
  · exact comparison_counit_rawComponent (J := J) (U := U) T
  · intro X Y f
    -- Route correction: after projecting to left components, the naturality square becomes the raw
    -- left-component equality for the composite
    -- `localization_lowerShriek_associatedSheafIso ≪≫ mapIso sigma_of_fibres_natIso`.
    apply Over.OverMorphism.ext
    simpa using
      comparison_counit_rawComponent_left_naturality (J := J) (U := U) f

/-- Helper for Lemma 7.25.4: the target-side counit natural isomorphism obtained by combining the
raw sigma-of-fibres identity with the recovery from the sheafified pullback. -/
noncomputable def comparison_counitIso :
    comparison_inverse (J := J) (U := U) ⋙ J.representableLocalizationComparison U ≅
      𝟭 (Over h[U]^#[J]) :=
  comparison_counit_rawNatIso (J := J) (U := U) ≪≫
    sheafified_pullback_recovery_natIso (J := J) (U := U)

/-- Helper for Lemma 7.25.4: the source-side textbook identity
`(j_{U!}^{PSh} \mathcal{G})_\gamma = \mathcal{G}` packaged as the unit isomorphism for the
comparison inverse. -/
noncomputable def comparison_unitIso :
    𝟭 (Sheaf (J.over U) (Type (max u v))) ≅
      J.representableLocalizationComparison U ⋙ comparison_inverse (J := J) (U := U) :=
  -- Route correction: the raw pullback identification is stronger than the source proof.  The
  -- source-side equality is instead used after taking fibres and sheafifying.
  (comparison_unit_pullback_fiberNatIso (J := J) (U := U) ≪≫
    localization_fiber_sheafification_natIso (J := J) (U := U)).symm

end RepresentableLocalizationComparison

-- Proof sketch: construct the inverse functor by sending a morphism `φ : ℱ ⟶ h[U]^#[J]` to the
-- sheaf
-- on `C/U` given by the fiber over each section `a : X ⟶ U`; the presheaf-level constructions in
-- the textbook are inverse to one another, and Lemmas 7.25.2 and 7.25.3 identify those
-- constructions with the chosen lower-shriek functor and the sheafified representable
-- `h[U]^#[J]`.
/-- Lemma 7.25.4: the canonical functor from sheaves on the localized site `(C/U, J.over U)` to
sheaves over `h[U]^#[J]`, sending `𝒢` to the canonical morphism
`j_{U!} 𝒢 ⟶ h[U]^#[J]`, is an equivalence. -/
theorem representableLocalizationComparison_isEquivalence
    :
    Functor.IsEquivalence (J.representableLocalizationComparison U) := by
  -- Route correction: the inverse now uses the canonical slice pullback along the sheafification
  -- unit of `h_U`, so the remaining work is to upgrade the adjunction counit on the slice over
  -- `h_U^#` and the sigma-model textbook identities to natural isomorphisms.
  refine Functor.IsEquivalence.mk'
    (RepresentableLocalizationComparison.comparison_inverse (J := J) (U := U))
    (RepresentableLocalizationComparison.comparison_unitIso (J := J) (U := U))
    (RepresentableLocalizationComparison.comparison_counitIso (J := J) (U := U))

end

end CategoryTheory.GrothendieckTopology
