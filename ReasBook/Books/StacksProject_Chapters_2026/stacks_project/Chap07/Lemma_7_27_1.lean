module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import stacks_project.Chap07.Lemma_7_25_2
public import stacks_project.Chap07.Remark_7_25_10

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [J.Subcanonical] (U : C)
variable (G : Sheaf (J.over U) (Type (max u v)))

/- Domain-style sampling for Lemma 7.27.1:
- primary domain: localization lower shriek on sheaves and its presheaf-level left-Kan-extension
  formula;
- sampled owner API:
  `(Over.forget U).sheafPullback`,
  `localization_lowerShriek_associatedSheafIso`,
  `localization_leftKanExtension_objIsoSigma`,
  `sheafificationIso`;
- source-facing layer: the Stacks Project identification of `j_{U!}(G)` with the presheaf
  `V ↦ ∐_{φ : V ⟶ U} G(V \xrightarrow{φ} U)`;
- core/canonical owner: the sheaf functor `(Over.forget U).sheafPullback (Type (max u v))
  (J.over U) J` and the presheaf functor `(Over.forget U).op.lan`;
- bridge/view: `localization_lowerShriek_associatedSheafIso` identifies `j_{U!}` with the
  sheafification of the left Kan extension, and subcanonicality upgrades that sheafification to the
  presheaf itself.

Primitive data are the site `J`, the localization object `U`, the sheaf `G`, and the standard
sheafification/Kan-extension hypotheses. The sheafified left Kan extension is derived API of the
canonical owners, so no separate wrapper sheaf is kept in the public surface.
-/


/-- Helper for Lemma 7.27.1: the sigma-model for the left Kan extension sends the canonical
generator from `leftKanExtensionUnit` to the corresponding summand. -/
theorem localization_leftKanExtension_objIsoSigma_hom_unit_app
    {V : C} (a : V ⟶ U) (s : G.obj.obj (op (Over.mk a))) :
    (localization_leftKanExtension_objIsoSigma U G.obj V).hom
        ((((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk a))) s) =
      ⟨a, s⟩ := by
  -- Expand the sigma comparison into the standard colimit presentation and evaluate each stage on
  -- the generator coming from `leftKanExtensionUnit`.
  let F₁ := LocalizationLeftKanExtension.indexFunctor U V
  let F₂ :=
    CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G.obj
  let F₃ :=
    Discrete.functor (fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ)))
  letI : Functor.Final F₁ := LocalizationLeftKanExtension.indexFunctor_final U V
  have h₀ :=
    congrFun
      (Functor.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom
        (L := (Over.forget U).op) (F := G.obj) (X := op (Over.mk a)))
      s
  have h₁ :=
    congrFun
      (Functor.Final.ι_colimitIso_inv
        (F := F₁) (G := F₂) (X := Discrete.mk a))
      s
  have h₂ :=
    congrFun
      (CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom
        (w := LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)
        (j := Discrete.mk a))
      s
  have h₃ :=
    congrFun
      (CategoryTheory.Limits.Types.coproductIso_ι_comp_hom
        (F := fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))) a)
      s
  calc
    (localization_leftKanExtension_objIsoSigma U G.obj V).hom
        ((((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk a))) s)
        =
          (CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom
            ((CategoryTheory.Limits.HasColimit.isoOfNatIso
                (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom
              ((Functor.Final.colimitIso F₁ F₂).inv
                (((Over.forget U).op.leftKanExtensionObjIsoColimit G.obj (op V)).hom
                  ((((Over.forget U).op.leftKanExtensionUnit G.obj).app
                    (op (Over.mk a))) s)))) := by
      rfl
    _ =
          (CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom
            ((CategoryTheory.Limits.HasColimit.isoOfNatIso
                (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom
              ((Functor.Final.colimitIso F₁ F₂).inv
                (CategoryTheory.Limits.colimit.ι F₂ (F₁.obj (Discrete.mk a)) s))) := by
      simpa [F₁, LocalizationLeftKanExtension.indexFunctor] using congrArg
        ((CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom ∘
          (CategoryTheory.Limits.HasColimit.isoOfNatIso
            (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom ∘
            (Functor.Final.colimitIso F₁ F₂).inv) h₀
    _ =
          (CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom
            ((CategoryTheory.Limits.HasColimit.isoOfNatIso
                (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom
              (CategoryTheory.Limits.colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s)) := by
      have h₁' :
          ((Functor.Final.colimitIso F₁ F₂).inv
              (CategoryTheory.Limits.colimit.ι F₂ (F₁.obj (Discrete.mk a)) s)) =
            CategoryTheory.Limits.colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s := by
        simpa [F₁, F₂, LocalizationLeftKanExtension.indexFunctor] using h₁
      exact congrArg
        ((CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom ∘
          (CategoryTheory.Limits.HasColimit.isoOfNatIso
            (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom) h₁'
    _ =
          (CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom
            (CategoryTheory.Limits.colimit.ι F₃ (Discrete.mk a) s) := by
      have h₂' :
          (CategoryTheory.Limits.HasColimit.isoOfNatIso
              (LocalizationLeftKanExtension.indexFunctorProjIso U G.obj V)).hom
              (CategoryTheory.Limits.colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s) =
            CategoryTheory.Limits.colimit.ι F₃ (Discrete.mk a) s := by
        simpa [F₁, F₂, F₃, LocalizationLeftKanExtension.indexFunctorProjIso] using h₂
      exact congrArg
        ((CategoryTheory.Limits.Types.coproductIso fun φ : V ⟶ U ↦ G.obj.obj (op (Over.mk φ))).hom) h₂'
    _ = ⟨a, s⟩ := by
      simpa [F₃] using h₃

/-- Helper for Lemma 7.27.1: the inverse sigma comparison sends a chosen summand back to the
canonical generator of the left Kan extension. -/
theorem localization_leftKanExtension_objIsoSigma_inv_mk
    {V : C} (a : V ⟶ U) (s : G.obj.obj (op (Over.mk a))) :
    (localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨a, s⟩ =
      (((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk a))) s := by
  -- Apply the sigma chart and cancel it against the generator formula proved just above.
  apply (localization_leftKanExtension_objIsoSigma U G.obj V).toEquiv.injective
  simp [localization_leftKanExtension_objIsoSigma_hom_unit_app]

/-- Helper for Lemma 7.27.1: the canonical map `Over.mk (f ≫ φ) ⟶ Over.mk φ` in the localized
site. -/
abbrev localization_leftKanExtension_over_homMk
    {V Y : C} {φ : V ⟶ U} (f : Y ⟶ V) :
    Over.mk (f ≫ φ) ⟶ Over.mk φ :=
  Over.homMk f

/-- Helper for Lemma 7.27.1: in sigma coordinates, restriction along `f : Y ⟶ V` sends the
summand indexed by `a : V ⟶ U` to the summand indexed by `f ≫ a`. -/
theorem localization_leftKanExtension_objIsoSigma_hom_map
    {V Y : C} (f : Y ⟶ V)
    (x : (((Over.forget U).op.lan.obj G.obj).obj (op V))) :
    (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
        (((Over.forget U).op.lan.obj G.obj).map f.op x) =
      ⟨f ≫ ((localization_leftKanExtension_objIsoSigma U G.obj V).hom x).1,
        G.obj.map
          (localization_leftKanExtension_over_homMk
            (U := U) (φ := ((localization_leftKanExtension_objIsoSigma U G.obj V).hom x).1) f).op
          ((localization_leftKanExtension_objIsoSigma U G.obj V).hom x).2⟩ := by
  -- Write `x` as the inverse image of its sigma coordinates, then use naturality of
  -- `leftKanExtensionUnit` along the canonical map `Over.mk (f ≫ a) ⟶ Over.mk a`.
  rcases hV : (localization_leftKanExtension_objIsoSigma U G.obj V).hom x with ⟨a, s⟩
  rw [← hV]
  have hx :
      x = (localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨a, s⟩ := by
    apply (localization_leftKanExtension_objIsoSigma U G.obj V).toEquiv.injective
    simp [hV]
  rw [hx]
  rw [localization_leftKanExtension_objIsoSigma_inv_mk (J := J) (U := U) (G := G) a s]
  let g : Over.mk (f ≫ a) ⟶ Over.mk a :=
    localization_leftKanExtension_over_homMk (U := U) (φ := a) f
  have hnat :=
    congrFun (((Over.forget U).op.leftKanExtensionUnit G.obj).naturality g.op) s
  dsimp at hnat
  have hnat' :
      (((Over.forget U).op.lan.obj G.obj).map f.op
          ((((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk a))) s)) =
        (((Over.forget U).op.leftKanExtensionUnit G.obj).app (op (Over.mk (f ≫ a))))
          (G.obj.map g.op s) := by
    simpa [g] using hnat.symm
  rw [hnat']
  rw [localization_leftKanExtension_objIsoSigma_hom_unit_app (J := J) (U := U) (G := G) a s]
  simpa using
    localization_leftKanExtension_objIsoSigma_hom_unit_app (J := J) (U := U) (G := G) (f ≫ a)
      (G.obj.map g.op s)

/-- Helper for Lemma 7.27.1: the raw representable presheaf `h_U`, raised to the ambient `Type`
universe used by the sigma model. -/
abbrev representable_presheaf : Cᵒᵖ ⥤ Type (max u v) :=
  ((CategoryTheory.uliftYoneda.{max u v}.obj U) : Cᵒᵖ ⥤ Type (max u v))

/-- Helper for Lemma 7.27.1: after gluing the first coordinates to `φ`, the local sigma first
coordinate over an arrow in the induced over-sieve equals the structural map of the source
over-object. -/
theorem localization_leftKanExtension_first_component_eq
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
        (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1 = Y.hom := by
  -- Compare the glued first coordinate with the defining triangle of `f`.
  exact (hφ f.left ((Sieve.overEquiv_symm_iff S f).1 hf)).symm.trans (Over.w f)

/-- Helper for Lemma 7.27.1: the sigma fibre indexed by the first coordinate is the given over
object. -/
theorem localization_leftKanExtension_overObj_eq
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    Over.mk
        (((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
          (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1) = Y := by
  -- The first-coordinate gluing identifies the sigma summand with the source over-object.
  cases Y with
  | mk leftY rightY homY =>
      cases rightY
      simpa using congrArg Over.mk
        (localization_leftKanExtension_first_component_eq
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))

/-- Helper for Lemma 7.27.1: transport along an equality of arrows `V ⟶ U` identifies the
corresponding sigma fibres in `G`. -/
theorem localization_leftKanExtension_sigma_type_eq
    {V : C} {a b : V ⟶ U} (h : a = b) :
    G.obj.obj (op (Over.mk a)) = G.obj.obj (op (Over.mk b)) := by
  cases h
  rfl

/-- Helper for Lemma 7.27.1: the transported sigma second coordinate can be viewed as a section of
`G` on the source over-object. -/
theorem localization_leftKanExtension_second_coordinate_type_eq
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    G.obj.obj
        (op
          (Over.mk
            (((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
              (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1))) =
      G.obj.obj (op Y) := by
  cases Y with
  | mk leftY rightY homY =>
      cases rightY
      simpa using localization_leftKanExtension_sigma_type_eq
        (J := J) (U := U) (G := G)
        (localization_leftKanExtension_first_component_eq
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))

/-- Helper for Lemma 7.27.1: after gluing the first coordinates to `φ`, each local section yields
the corresponding second coordinate in `G` on the induced over-sieve. -/
def localization_leftKanExtension_second_coordinate
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    G.obj.obj (op Y) :=
  cast
    (localization_leftKanExtension_second_coordinate_type_eq
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))
    (((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
      (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).2)

/-- Helper for Lemma 7.27.1: the direct second-coordinate assignment, packaged as a family on the
induced over-sieve. -/
def localization_leftKanExtension_second_coordinate_family
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1) :
    ((Sieve.overEquiv (Over.mk φ)).symm S).arrows.FamilyOfElements G.obj :=
  fun _ f hf ↦
    localization_leftKanExtension_second_coordinate
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)

/-- Helper for Lemma 7.27.1: the canonical over-arrow attached to `f : Y ⟶ V` lies in the induced
over-sieve. -/
theorem localization_leftKanExtension_over_homMk_mem
    {V : C} {S : Sieve V} {φ : V ⟶ U}
    {Y : C} (f : Y ⟶ V) (hf : S f) :
    ((Sieve.overEquiv (Over.mk φ)).symm S)
      (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f) := by
  simpa [localization_leftKanExtension_over_homMk] using
    (Sieve.overEquiv_symm_iff S
      (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)).2 hf

/-- Helper for Lemma 7.27.1: in sigma coordinates, the local section `x f hf` is described by the
glued first coordinate `f ≫ φ` and the direct second coordinate on the canonical over-arrow. -/
theorem localization_leftKanExtension_hom_eq_homMk
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : C} (f : Y ⟶ V) (hf : S f) :
    (localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf) =
      ⟨f ≫ φ,
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
          (hf := localization_leftKanExtension_over_homMk_mem
            (U := U) (φ := φ) f hf)⟩ := by
  -- Compare the sigma pair by first isolating the proof-irrelevant membership argument on the
  -- canonical over-arrow.
  let hf' : ((Sieve.overEquiv (Over.mk φ)).symm S).arrows
      (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f) :=
    localization_leftKanExtension_over_homMk_mem (U := U) (φ := φ) f hf
  have hpf :
      (Sieve.overEquiv_symm_iff S
          (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)).1 hf' = hf := by
    apply Subsingleton.elim
  -- Then rewrite the local section into explicit sigma coordinates and compare second components by
  -- `Sigma.mk.inj_iff`, finishing with the canonical cast/HEq bridge.
  rcases hsig : (localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf) with ⟨a, s⟩
  have ha : a = f ≫ φ := by
    simpa [hsig] using (hφ f hf).symm
  apply (Sigma.mk.inj_iff).2
  refine ⟨ha, ?_⟩
  cases ha
  have hsig' :
      (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
          (x (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).left
            ((Sieve.overEquiv_symm_iff S
              (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)).1 hf')) =
        ⟨f ≫ φ, s⟩ := by
    simpa [localization_leftKanExtension_over_homMk, hpf] using hsig
  dsimp [localization_leftKanExtension_second_coordinate]
  let p := localization_leftKanExtension_second_coordinate_type_eq
    (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
    (f := localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
    (hf := hf')
  let z := ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom
    (x (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).left
      ((Sieve.overEquiv_symm_iff S
        (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)).1 hf'))).2
  have hsnd : s ≍ z := ((Sigma.mk.inj_iff).1 hsig').2.symm
  exact HEq.trans hsnd (HEq.symm (cast_heq p z))

/-- Helper for Lemma 7.27.1: every over-arrow is equal to the canonical `homMk` built from its
underlying map. -/
theorem localization_leftKanExtension_over_homMk_eq
    {Y Z : Over U} (g : Z ⟶ Y) (w : g.left ≫ Y.hom = Z.hom) :
    Over.homMk g.left w = g := by
  -- Morphisms in `Over U` are determined by their underlying maps, so the proof field is
  -- irrelevant here.
  apply CommaMorphism.ext
  · rfl
  · rfl

/-- Helper for Lemma 7.27.1: every object of `Over U` is definitionally the canonical object built
from its structure map. -/
theorem localization_leftKanExtension_over_mk_hom_eq
    (Y : Over U) : Over.mk Y.hom = Y := by
  cases Y
  rfl

/-- Helper for Lemma 7.27.1: the canonical `homMk` restriction factors through the source-object
equality coming from `Over.w`. -/
theorem localization_leftKanExtension_over_homMk_eqToHom_comp
    {Y Z : Over U} (g : Z ⟶ Y) :
    localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left =
      eqToHom ((congrArg Over.mk (Over.w g)).trans
        (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)) ≫ g := by
  -- Morphisms in `Over U` are determined by their underlying arrows, so the factorization is
  -- proved by identifying the right-hand side with the canonical `homMk` for its underlying map.
  simpa [localization_leftKanExtension_over_homMk] using
    (localization_leftKanExtension_over_homMk_eq (U := U)
      (g := eqToHom ((congrArg Over.mk (Over.w g)).trans
        (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)) ≫ g)
      (w := by simp))

/-- Helper for Lemma 7.27.1: mapping an `eqToHom` in `Over U` through the `Type`-valued sheaf is
the same as transporting along the induced equality of fibres. -/
theorem localization_leftKanExtension_map_eqToHom_op_cast
    {A B : Over U} (h : A = B) (x : G.obj.obj (op B)) :
    cast (congrArg (fun T : Over U ↦ G.obj.obj (op T)) h)
      (G.obj.map (eqToHom h).op x) = x := by
  -- After reducing to the reflexive equality, the map is the identity and the cast disappears.
  cases h
  simp

/-- Helper for Lemma 7.27.1: the sigma coordinates of a local section over an arbitrary arrow in
the induced over-sieve are given by the structural map of the source over-object and the direct
second coordinate. -/
theorem localization_leftKanExtension_hom_eq_over
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) :
    (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
        (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf)) =
      ⟨Y.hom,
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)⟩ := by
  -- Compare the sigma pair by matching first coordinates, then identify the second coordinate by
  -- the transport already built into `localization_leftKanExtension_second_coordinate`.
  rcases hsig :
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
        (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf)) with ⟨a, s⟩
  have ha : a = Y.hom := by
    simpa [hsig] using
      localization_leftKanExtension_first_component_eq
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)
  cases ha
  apply (Sigma.mk.inj_iff).2
  refine ⟨rfl, ?_⟩
  have hsig' :
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
          (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf)) = ⟨Y.hom, s⟩ := by
    simpa using hsig
  dsimp [localization_leftKanExtension_second_coordinate]
  let z := ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
    (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).2
  have hsnd : z ≍ s := ((Sigma.mk.inj_iff).1 hsig').2
  exact HEq.trans (HEq.symm hsnd) (HEq.symm <|
    cast_heq
      (localization_leftKanExtension_second_coordinate_type_eq
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))
      z)

/-- Helper for Lemma 7.27.1: transporting the sigma-second-coordinate restriction along `Over.w`
identifies the canonical `homMk` restriction with the actual restriction map in `Over U`. -/
theorem localization_leftKanExtension_second_coordinate_transport_over_w
    {Y Z : Over U} (g : Z ⟶ Y) (s : G.obj.obj (op Y)) :
    cast
      (by
        simpa [localization_leftKanExtension_over_mk_hom_eq] using
          localization_leftKanExtension_sigma_type_eq
            (J := J) (U := U) (G := G) (Over.w g))
      (G.obj.map
        (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op s) =
      G.obj.map g.op s := by
  -- Route correction: factor the canonical `homMk` through the source-object equality, then
  -- collapse the induced `eqToHom` action on the `Type`-valued presheaf to an ordinary cast.
  let hZ : Over.mk (g.left ≫ Y.hom) = Z :=
    (congrArg Over.mk (Over.w g)).trans
      (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)
  change cast (congrArg (fun T : Over U ↦ G.obj.obj (op T)) hZ)
      (G.obj.map (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op s) =
    G.obj.map g.op s
  rw [localization_leftKanExtension_over_homMk_eqToHom_comp (U := U) g]
  calc
    cast (congrArg (fun T : Over U ↦ G.obj.obj (op T)) hZ)
        (G.obj.map (eqToHom hZ ≫ g).op s) =
      cast (congrArg (fun T : Over U ↦ G.obj.obj (op T)) hZ)
        (G.obj.map (eqToHom hZ).op (G.obj.map g.op s)) := by
          -- Rewrite the `Type`-valued functor on the opposite composite into successive maps.
          congr 1
          exact FunctorToTypes.map_comp_apply G.obj g.op (eqToHom hZ).op s
    _ = G.obj.map g.op s := by
      -- The `eqToHom` factor on the source object is exactly the transport cast on the fibre.
      have hcast :
          cast (congrArg (fun T : Over U ↦ G.obj.obj (op T))
              ((congrArg Over.mk (Over.w g)).trans
                (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)))
            (G.obj.map
              (eqToHom
                ((congrArg Over.mk (Over.w g)).trans
                  (localization_leftKanExtension_over_mk_hom_eq (U := U) Z))).op
              (G.obj.map g.op s)) =
            G.obj.map g.op s := by
        exact
          (show cast (congrArg (fun T : Over U ↦ G.obj.obj (op T))
              ((congrArg Over.mk (Over.w g)).trans
                (localization_leftKanExtension_over_mk_hom_eq (U := U) Z)))
              (G.obj.map
                (eqToHom ((congrArg Over.mk (Over.w g)).trans
                  (localization_leftKanExtension_over_mk_hom_eq (U := U) Z))).op
                (G.obj.map g.op s)) =
              G.obj.map g.op s from
            localization_leftKanExtension_map_eqToHom_op_cast
              (J := J) (U := U) (G := G)
              (h := (congrArg Over.mk (Over.w g)).trans
                (localization_leftKanExtension_over_mk_hom_eq (U := U) Z))
              (x := G.obj.map g.op s))
      simpa [hZ] using hcast

/-- Helper for Lemma 7.27.1: the direct second-coordinate family is compatible on the induced
over-sieve. -/
theorem localization_leftKanExtension_second_coordinate_map
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    (hx : x.Compatible) {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {Y Z : Over U} (f : Y ⟶ Over.mk φ)
    (hf : ((Sieve.overEquiv (Over.mk φ)).symm S) f) (g : Z ⟶ Y) :
    G.obj.map g.op
        (localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)) =
      localization_leftKanExtension_second_coordinate
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
        (f := g ≫ f)
        (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g) := by
  -- Compare the compatible family in sigma coordinates and then transport the second coordinate
  -- across the equality `Over.w g : g.left ≫ Y.hom = Z.hom`.
  rw [Presieve.compatible_iff_sieveCompatible] at hx
  have hpair :=
    congrArg
      (localization_leftKanExtension_objIsoSigma U G.obj Z.left).hom
      (hx f.left g.left ((Sieve.overEquiv_symm_iff S f).1 hf))
  have hleft :
      (localization_leftKanExtension_objIsoSigma U G.obj Z.left).hom
          (x (g ≫ f).left
            ((Sieve.overEquiv_symm_iff S (g ≫ f)).1
              (((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g))) =
        ⟨Z.hom,
          localization_leftKanExtension_second_coordinate
            (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
            (f := g ≫ f)
            (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g)⟩ := by
    -- The restricted section on `g ≫ f` is already in the normalized sigma form.
    simpa using
      localization_leftKanExtension_hom_eq_over
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
        (f := g ≫ f)
        (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g)
  have hright :
      (localization_leftKanExtension_objIsoSigma U G.obj Z.left).hom
          (((Over.forget U).op.lan.obj G.obj).map g.left.op
            (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))) =
        ⟨g.left ≫ Y.hom,
          G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op
            (localization_leftKanExtension_second_coordinate
              (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))⟩ := by
    -- Rewrite the source sigma coordinates first, then use the restriction formula for the chart.
    calc
      (localization_leftKanExtension_objIsoSigma U G.obj Z.left).hom
          (((Over.forget U).op.lan.obj G.obj).map g.left.op
            (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))) =
        ⟨g.left ≫
            ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
              (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1,
          G.obj.map
            (localization_leftKanExtension_over_homMk
              (U := U)
              (φ := ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
                (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).1)
              g.left).op
            ((localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
              (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))).2⟩ := by
        simpa [localization_leftKanExtension_over_homMk] using
          localization_leftKanExtension_objIsoSigma_hom_map
            (J := J) (U := U) (G := G) g.left
            (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf))
      _ = ⟨g.left ≫ Y.hom,
          G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op
            (localization_leftKanExtension_second_coordinate
              (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))⟩ := by
        let restrictSigma :
            (Σ a : Y.left ⟶ U, G.obj.obj (op (Over.mk a))) →
              Σ b : Z.left ⟶ U, G.obj.obj (op (Over.mk b)) :=
          fun p ↦
            ⟨g.left ≫ p.1,
              G.obj.map
                (localization_leftKanExtension_over_homMk (U := U) (φ := p.1) g.left).op p.2⟩
        have hsource :=
          localization_leftKanExtension_hom_eq_over
            (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)
        simpa [restrictSigma] using congrArg restrictSigma hsource
  have hcompare := hleft.symm.trans (hpair.trans hright)
  let p :
      G.obj.obj (op (Over.mk (g.left ≫ Y.hom))) = G.obj.obj (op Z) := by
    simpa [localization_leftKanExtension_over_mk_hom_eq] using
      localization_leftKanExtension_sigma_type_eq
        (J := J) (U := U) (G := G) (Over.w g)
  have hsnd :
      localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := g ≫ f)
          (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g) =
        cast p
          (G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := Y.hom) g.left).op
            (localization_leftKanExtension_second_coordinate
              (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))) := by
    -- `Sigma.mk.inj_iff` gives an `HEq`; casting puts both sides into the fibre over `Z`.
    exact eq_of_heq <|
      HEq.trans ((Sigma.mk.inj_iff).1 hcompare).2 (HEq.symm (cast_heq p _))
  have hsnd' :
      localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := g ≫ f)
          (hf := ((Sieve.overEquiv (Over.mk φ)).symm S).downward_closed hf g) =
        G.obj.map g.op
          (localization_leftKanExtension_second_coordinate
            (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)) := by
    simpa [p] using hsnd.trans <|
      localization_leftKanExtension_second_coordinate_transport_over_w
        (J := J) (U := U) (G := G) g
        (localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf))
  exact hsnd'.symm

/-- Helper for Lemma 7.27.1: the direct second-coordinate family on the induced over-sieve is
compatible. -/
theorem localization_leftKanExtension_second_coordinate_compatible
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    (hx : x.Compatible) {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1) :
    (localization_leftKanExtension_second_coordinate_family
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)).Compatible := by
  -- Compatibility is exactly the restriction formula proved for the direct second coordinates.
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z f g hf
  simpa using (localization_leftKanExtension_second_coordinate_map
    (J := J) (U := U) (G := G) (x := x) hx (hφ := hφ) (f := f) (hf := hf) g).symm

/-- Helper for Lemma 7.27.1: a glued second coordinate on the induced over-sieve yields an
amalgamation of the original family in the left Kan extension. -/
theorem localization_leftKanExtension_glued_pair_is_amalgamation
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {s : G.obj.obj (op (Over.mk φ))}
    (hs : (localization_leftKanExtension_second_coordinate_family
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)).IsAmalgamation s) :
    x.IsAmalgamation
      ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩) := by
  -- Apply the sigma chart after restricting the glued pair. The first coordinate is visibly
  -- `f ≫ φ`, and the second coordinate is the glued section prescribed by `hs`.
  intro Y f hf
  apply (localization_leftKanExtension_objIsoSigma U G.obj Y).toEquiv.injective
  have hmap :
      (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
          (((Over.forget U).op.lan.obj G.obj).map f.op
            ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩)) =
        ⟨f ≫ φ,
          G.obj.map (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).op s⟩ := by
    have hmap₀ :=
      localization_leftKanExtension_objIsoSigma_hom_map
        (J := J) (U := U) (G := G) f
        ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩)
    have hsigma :
        (localization_leftKanExtension_objIsoSigma U G.obj V).hom
            ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩) = ⟨φ, s⟩ := by
      simp
    rw [hsigma] at hmap₀
    simpa [localization_leftKanExtension_over_homMk] using hmap₀
  have hs' :
      G.obj.map (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).op s =
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
          (hf := localization_leftKanExtension_over_homMk_mem
            (U := U) (S := S) (φ := φ) f hf) := by
    exact hs
      (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
      (localization_leftKanExtension_over_homMk_mem (U := U) (S := S) (φ := φ) f hf)
  calc
    (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
        (((Over.forget U).op.lan.obj G.obj).map f.op
          ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩)) =
      ⟨f ≫ φ,
        G.obj.map (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f).op s⟩ := hmap
    _ =
      ⟨f ≫ φ,
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
          (f := localization_leftKanExtension_over_homMk (U := U) (φ := φ) f)
          (hf := localization_leftKanExtension_over_homMk_mem
            (U := U) (S := S) (φ := φ) f hf)⟩ := by
      rw [hs']
    _ = (localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf) := by
      symm
      exact localization_leftKanExtension_hom_eq_homMk
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) f hf

/-- Helper for Lemma 7.27.1: if a local section of the left Kan extension already amalgamates the
original family and its sigma first coordinate is `φ`, then its sigma second coordinate
amalgamates the induced family on the over-sieve of `φ`. -/
theorem localization_leftKanExtension_second_component_is_amalgamation
    {V : C} {S : Sieve V}
    (x : S.arrows.FamilyOfElements ((Over.forget U).op.lan.obj G.obj))
    {φ : V ⟶ U}
    (hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1)
    {t : ((Over.forget U).op.lan.obj G.obj).obj (op V)}
    {u : G.obj.obj (op (Over.mk φ))}
    (ht : x.IsAmalgamation t)
    (hsig : (localization_leftKanExtension_objIsoSigma U G.obj V).hom t = ⟨φ, u⟩) :
    (localization_leftKanExtension_second_coordinate_family
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)).IsAmalgamation u := by
  -- Apply the sigma chart to the amalgamation equation for `t`, then normalize the `Over.w f`
  -- transport exactly as in the compatibility proof above.
  intro Y f hf
  have hpair :=
    congrArg
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
      (ht f.left ((Sieve.overEquiv_symm_iff S f).1 hf))
  have hleft :
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
          (((Over.forget U).op.lan.obj G.obj).map f.left.op t) =
        ⟨f.left ≫ φ,
          G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f.left).op u⟩ := by
    -- The sigma chart on the restriction of `t` is computed by `objIsoSigma_hom_map`.
    have hmap :=
      localization_leftKanExtension_objIsoSigma_hom_map
        (J := J) (U := U) (G := G) f.left t
    let restrictSigma :
        (Σ a : V ⟶ U, G.obj.obj (op (Over.mk a))) →
          Σ b : Y.left ⟶ U, G.obj.obj (op (Over.mk b)) :=
      fun p ↦
        ⟨f.left ≫ p.1,
          G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := p.1) f.left).op p.2⟩
    simpa [restrictSigma] using congrArg restrictSigma hsig |> fun h => hmap.trans h
  have hright :
      (localization_leftKanExtension_objIsoSigma U G.obj Y.left).hom
          (x f.left ((Sieve.overEquiv_symm_iff S f).1 hf)) =
        ⟨Y.hom,
          localization_leftKanExtension_second_coordinate
            (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)⟩ := by
    -- The local family already has the normalized sigma description over the induced over-sieve.
    simpa using
      localization_leftKanExtension_hom_eq_over
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf)
  have hcompare := hleft.symm.trans (hpair.trans hright)
  let p :
      G.obj.obj (op (Over.mk (f.left ≫ φ))) = G.obj.obj (op Y) := by
    simpa [localization_leftKanExtension_over_mk_hom_eq] using
      localization_leftKanExtension_sigma_type_eq
        (J := J) (U := U) (G := G) (Over.w f)
  have hsnd :
      cast p
          (G.obj.map
            (localization_leftKanExtension_over_homMk (U := U) (φ := φ) f.left).op u) =
        localization_leftKanExtension_second_coordinate
          (J := J) (U := U) (G := G) (x := x) (hφ := hφ) (f := f) (hf := hf) := by
    -- Extract the second coordinates after transporting to the fibre over `Y`.
    exact eq_of_heq <|
      HEq.trans (cast_heq p _) ((Sigma.mk.inj_iff).1 hcompare).2
  simpa [p] using
    localization_leftKanExtension_second_coordinate_transport_over_w
      (J := J) (U := U) (G := G) f u |>.symm.trans hsnd

/-- Helper for Lemma 7.27.1: the left Kan extension presheaf is already a sheaf, so no additional
sheafification is required. -/
theorem localization_leftKanExtension_isSheaf :
    Presheaf.IsSheaf J ((Over.forget U).op.lan.obj G.obj) := by
  -- Route correction: glue the first coordinate in the representable sheaf `h_U`, then glue the
  -- transported second coordinates directly in `G` on the induced over-sieve.
  rw [isSheaf_iff_isSheaf_of_type]
  intro V S hS
  intro x hx
  let x₁ : S.arrows.FamilyOfElements (representable_presheaf (U := U)) :=
    fun _ f hf ↦
      ULift.up ((localization_leftKanExtension_objIsoSigma U G.obj _).hom (x f hf)).1
  have hx₁ : x₁.Compatible := by
    -- The first coordinates are compatible because restriction in sigma coordinates is by
    -- postcomposition with the base map.
    rw [Presieve.compatible_iff_sieveCompatible]
    rw [Presieve.compatible_iff_sieveCompatible] at hx
    intro Y Z f g hf
    have hpair :
        (localization_leftKanExtension_objIsoSigma U G.obj Z).hom
            (x (g ≫ f) (S.downward_closed hf g)) =
          (localization_leftKanExtension_objIsoSigma U G.obj Z).hom
            (((Over.forget U).op.lan.obj G.obj).map g.op (x f hf)) := by
      exact congrArg (localization_leftKanExtension_objIsoSigma U G.obj Z).hom (hx f g hf)
    apply ULift.ext
    simpa [x₁, localization_leftKanExtension_objIsoSigma_hom_map] using congrArg Sigma.fst hpair
  let hRep : Presieve.IsSheaf J (representable_presheaf (U := U)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := J) (representable_presheaf (U := U))
  let hRepS := hRep S hS
  let φu := hRepS.amalgamate x₁ hx₁
  let φ : V ⟶ U := φu.down
  have hφ : ∀ ⦃Y : C⦄ (f : Y ⟶ V) (hf : S f),
      f ≫ φ = ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1 := by
    intro Y f hf
    have hglue : (representable_presheaf (U := U)).map f.op φu = x₁ f hf :=
      hRepS.valid_glue hx₁ f hf
    simpa [x₁, φ] using hglue
  let T : Sieve (Over.mk φ) := (Sieve.overEquiv (Over.mk φ)).symm S
  have hT : T ∈ (J.over U) (Over.mk φ) :=
    J.overEquiv_symm_mem_over (Over.mk φ) S hS
  let x₂ : T.arrows.FamilyOfElements G.obj :=
    localization_leftKanExtension_second_coordinate_family
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
  have hx₂ : x₂.Compatible :=
    localization_leftKanExtension_second_coordinate_compatible
      (J := J) (U := U) (G := G) (x := x) hx (hφ := hφ)
  have hG : Presieve.IsSheaf (J.over U) G.obj :=
    (isSheaf_iff_isSheaf_of_type (J.over U) G.obj).1 G.property
  let hGS := hG T hT
  let s := hGS.amalgamate x₂ hx₂
  refine
    ⟨(localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩, ?_, ?_⟩
  · intro Y f hf
    -- The glued pair is an amalgamation because its first coordinate is `φ` and its second
    -- coordinate is the amalgamation of the direct family in `G`.
    exact localization_leftKanExtension_glued_pair_is_amalgamation
      (J := J) (U := U) (G := G) (x := x) (hφ := hφ)
      (hs := hGS.isAmalgamation (x := x₂) hx₂) f hf
  · intro t ht
    -- First compare first coordinates to force the same arrow `φ : V ⟶ U`. Then compare the
    -- resulting second coordinates by separatedness of `G` on the induced over-sieve.
    rcases hsig : (localization_leftKanExtension_objIsoSigma U G.obj V).hom t with ⟨ψ, u⟩
    have ht₁ :
        x₁.IsAmalgamation
          (ULift.up ψ) := by
      intro Y f hf
      have hpair :
          (localization_leftKanExtension_objIsoSigma U G.obj Y).hom
              (((Over.forget U).op.lan.obj G.obj).map f.op t) =
            (localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf) := by
        simpa [ht f hf]
      have hmap := localization_leftKanExtension_objIsoSigma_hom_map
        (J := J) (U := U) (G := G) f t
      have hfst :
          f ≫ ψ =
            ((localization_leftKanExtension_objIsoSigma U G.obj Y).hom (x f hf)).1 := by
        simpa [hsig] using (congrArg Sigma.fst hmap).symm.trans (congrArg Sigma.fst hpair)
      let e : (Y ⟶ U) → (representable_presheaf (U := U)).obj (op Y) := fun k ↦ ULift.up k
      simpa [representable_presheaf, x₁, e] using congrArg e hfst
    have hfirst_eq_u :
        ULift.up ψ = φu :=
      hRepS.isSeparatedFor x₁
        (ULift.up ψ)
        φu ht₁ (hRepS.isAmalgamation (x := x₁) hx₁)
    have hfirst :
        ψ = φ := by
      simpa [φ] using congrArg ULift.down hfirst_eq_u
    -- Rewrite the sigma first coordinate to `φ`, then compare second coordinates using
    -- separatedness of `G` on the induced over-sieve.
    cases hfirst
    have hu :
        x₂.IsAmalgamation u := by
      exact localization_leftKanExtension_second_component_is_amalgamation
        (J := J) (U := U) (G := G) (x := x) (hφ := hφ) ht hsig
    have hu_eq :
        u = s :=
      hGS.isSeparatedFor x₂ u s hu (hGS.isAmalgamation (x := x₂) hx₂)
    apply (localization_leftKanExtension_objIsoSigma U G.obj V).toEquiv.injective
    calc
      (localization_leftKanExtension_objIsoSigma U G.obj V).hom t = ⟨φ, u⟩ := hsig
      _ = ⟨φ, s⟩ := by rw [hu_eq]
      _ = (localization_leftKanExtension_objIsoSigma U G.obj V).hom
            ((localization_leftKanExtension_objIsoSigma U G.obj V).inv ⟨φ, s⟩) := by
          simp

/-- Lemma 7.27.1: if `J` is subcanonical and `G` is a sheaf on `C/U`, then the underlying
presheaf of `j_{U!}(G)` is canonically isomorphic to the left Kan extension of `G` along
`(Over.forget U).op`. -/
noncomputable def localization_lowerShriek_iso_leftKanExtension :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G).obj ≅
      (Over.forget U).op.lan.obj G.obj :=
  letI : HasWeakSheafify J (Type (max u v)) := inferInstance
  (sheafToPresheaf J (Type (max u v))).mapIso <|
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).mapIso
        (sheafificationIso G)) ≪≫
      localization_lowerShriek_associatedSheafIso J U G.obj ≪≫
        (sheafificationIso
          ⟨(Over.forget U).op.lan.obj G.obj, localization_leftKanExtension_isSheaf J U G⟩).symm

/-- Objectwise `Type`-valued form of Lemma 7.27.1. -/
noncomputable def localization_lowerShriek_objIsoSigma (V : C) :
    ((((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G).obj.obj (op V)) ≅
      Σ φ : V ⟶ U, G.obj.obj (op (Over.mk φ)) :=
  (localization_lowerShriek_iso_leftKanExtension J U G).app (op V) ≪≫
    localization_leftKanExtension_objIsoSigma U G.obj V

-- Proof sketch: unfold `localization_lowerShriek_objIsoSigma`; it is defined by evaluating the main
-- isomorphism of Lemma 7.27.1 at `V` and composing with the standard sigma-description of the left
-- Kan extension.
/-- The objectwise sigma-description is obtained by evaluating the canonical isomorphism of
Lemma 7.27.1 and then applying the standard left-Kan-extension formula. -/
theorem localization_lowerShriek_objIsoSigma_def (V : C) :
    localization_lowerShriek_objIsoSigma J U G V =
      (localization_lowerShriek_iso_leftKanExtension J U G).app (op V) ≪≫
        localization_leftKanExtension_objIsoSigma U G.obj V := by
  -- This is the defining equation of `localization_lowerShriek_objIsoSigma`.
  rfl

end
