module

public import «stacks_project».«Chap04».«4_27_7_1»
public import «stacks_project».«Chap04».«Lemma_4_19_2»

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

open MorphismProperty Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/-- Helper for Lemma 4.27.9: the denominator category indexing the left-fraction presentation of
`Hom(Q(-), Q(Y))`. -/
abbrev localization_denominator_category [W.HasLeftCalculusOfFractions] (Y : C) :=
  CategoryTheory.MorphismProperty.Under W ⊤ Y

/-- Helper for Lemma 4.27.9: the presheaf diagram of representables indexed by arrows
`Y ⟶ Y'` in `W`. -/
abbrev localization_denominator_diagram [W.HasLeftCalculusOfFractions] (Y : C) :
    localization_denominator_category W Y ⥤ Cᵒᵖ ⥤ Type (max u v) :=
  CategoryTheory.MorphismProperty.Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
    uliftYoneda.{u}

/-- Helper for Lemma 4.27.9: the filtered colimit of the denominator diagram preserves finite
limits, so any presheaf identified with that colimit is left exact. -/
lemma localization_presheaf_preservesFiniteLimits_of_iso [W.HasLeftCalculusOfFractions] (Y : C)
    (e : colimit (localization_denominator_diagram W Y) ≅
      W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u}) :
    PreservesFiniteLimits (W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u}) := by
  -- Each denominator object contributes a representable presheaf, hence a finite-limit-preserving
  -- functor; we combine those objectwise and then apply the filtered-colimit theorem in `Type`.
  have hflip : PreservesFiniteLimits (localization_denominator_diagram W Y).flip := by
    apply preservesFiniteLimits_of_evaluation
    intro s
    simpa [localization_denominator_diagram] using
      (show PreservesFiniteLimits (yoneda.obj s.right ⋙ uliftFunctor.{u}) from by
        letI : PreservesFiniteLimits (yoneda.obj s.right) := by infer_instance
        exact Limits.comp_preservesFiniteLimits _ _)
  have hcolim :
      PreservesFiniteLimits
        (colim :
          (localization_denominator_category W Y ⥤ Type (max u v)) ⥤ Type (max u v)) := by
    infer_instance
  have hcomp :
      PreservesFiniteLimits ((localization_denominator_diagram W Y).flip ⋙ colim) := by
    exact Limits.comp_preservesFiniteLimits _ _
  have hsource : PreservesFiniteLimits (colimit (localization_denominator_diagram W Y)) := by
    exact preservesFiniteLimits_of_natIso
      (colimitIsoFlipCompColim (localization_denominator_diagram W Y)).symm
  -- The comparison isomorphism transfers the finite-limit preservation to the localized Hom
  -- presheaf at the model object `Q(Y)`.
  exact preservesFiniteLimits_of_natIso e

/-- Helper for Lemma 4.27.9: the localized Hom-presheaf represented by `Q(Y)`. -/
noncomputable abbrev localization_target_presheaf [W.HasLeftCalculusOfFractions] (Y : C) :
    Cᵒᵖ ⥤ Type (max u v) :=
  W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u}

/-- Helper for Lemma 4.27.9: the underlying denominator map `Y ⟶ s.right` attached to an object
of the denominator category. -/
noncomputable abbrev localization_denominator_hom [W.HasLeftCalculusOfFractions] {Y : C}
    (s : localization_denominator_category W Y) :
    Y ⟶ s.right := by
  simpa using s.hom

/-- Helper for Lemma 4.27.9: the denominator map of an object of `Y / W` lies in `W`. -/
lemma localization_denominator_hom_mem [W.HasLeftCalculusOfFractions] {Y : C}
    (s : localization_denominator_category W Y) :
    W (localization_denominator_hom (W := W) s) := by
  simpa [localization_denominator_hom] using s.prop

/-- Helper for Lemma 4.27.9: the basic roof from `Q(s.right)` to `Q(Y)` indexed by `s : Y / W`. -/
noncomputable def localization_basic_fraction [W.HasLeftCalculusOfFractions] {Y : C}
    (s : localization_denominator_category W Y) :
    W.Q.obj s.right ⟶ W.Q.obj Y :=
  (MorphismProperty.LeftFraction.ofInv (localization_denominator_hom (W := W) s)
    (localization_denominator_hom_mem (W := W) s)).map W.Q (Localization.inverts W.Q W)

/-- Helper for Lemma 4.27.9: for a morphism in the denominator category, the basic roof
`Q(t.right) ⟶ Q(Y)` pulls back to the corresponding roof at the source. -/
lemma localization_basic_fraction_naturality [W.HasLeftCalculusOfFractions] {Y : C}
    {s t : localization_denominator_category W Y} (f : s ⟶ t) :
    W.Q.map f.right ≫ localization_basic_fraction (W := W) t =
      localization_basic_fraction (W := W) s := by
  -- Postcompose with `Q(s_t)` and use that the basic roofs are inverses to localized denominators.
  letI : IsIso (W.Q.map (localization_denominator_hom (W := W) t)) :=
    Localization.inverts W.Q W _ (localization_denominator_hom_mem (W := W) t)
  apply (cancel_mono (W.Q.map (localization_denominator_hom (W := W) t))).1
  rw [localization_basic_fraction, Category.assoc, MorphismProperty.LeftFraction.map_ofInv_hom_id]
  calc
    W.Q.map f.right = (𝟙 (W.Q.obj s.right)) ≫ W.Q.map f.right := by simp
    _ = localization_basic_fraction (W := W) s ≫
          W.Q.map (localization_denominator_hom (W := W) s) ≫ W.Q.map f.right := by
      simp [localization_basic_fraction]
    _ = localization_basic_fraction (W := W) s ≫
          W.Q.map (localization_denominator_hom (W := W) s ≫ f.right) := by
      rw [← W.Q.map_comp]
    _ = localization_basic_fraction (W := W) s ≫
          W.Q.map (localization_denominator_hom (W := W) t) := by
      simpa [localization_denominator_hom] using congrArg
        (fun k ↦ localization_basic_fraction (W := W) s ≫ W.Q.map k)
        (MorphismProperty.Under.w f)

/-- Helper for Lemma 4.27.9: the cocone leg indexed by a denominator `s : Y / W` is represented
by the basic roof `(𝟙, s)`. -/
noncomputable def localization_presheaf_cocone_app [W.HasLeftCalculusOfFractions] {Y : C}
    (s : localization_denominator_category W Y) :
    uliftYoneda.obj s.right ⟶ localization_target_presheaf W Y :=
  uliftYonedaEquiv.symm (ULift.up (localization_basic_fraction (W := W) s))

/-- Helper for Lemma 4.27.9: the cocone legs are natural in the denominator category. -/
lemma localization_presheaf_cocone_naturality [W.HasLeftCalculusOfFractions] {Y : C}
    {s t : localization_denominator_category W Y} (f : s ⟶ t) :
    (localization_denominator_diagram W Y).map f ≫
        localization_presheaf_cocone_app (W := W) t =
      localization_presheaf_cocone_app (W := W) s := by
  -- Check the equality objectwise: evaluating at `X` and `g : X ⟶ s.right` gives the same roof
  -- by `localization_basic_fraction_naturality`.
  ext X g
  cases X using Opposite.rec with
  | _ X =>
      cases g using ULift.rec with
      | _ g =>
          change
            ULift.up (W.Q.map (g ≫ f.right) ≫ localization_basic_fraction (W := W) t) =
              ULift.up (W.Q.map g ≫ localization_basic_fraction (W := W) s)
          rw [Functor.map_comp]
          simp [localization_basic_fraction_naturality (W := W) f]

/-- Helper for Lemma 4.27.9: the presheaf cocone whose point is the localized Hom-presheaf at
`Q(Y)`. -/
noncomputable def localization_presheaf_cocone [W.HasLeftCalculusOfFractions] (Y : C) :
    Cocone (localization_denominator_diagram W Y) :=
  { pt := localization_target_presheaf W Y
    ι :=
      { app := localization_presheaf_cocone_app (W := W)
        naturality := fun _ _ f ↦ localization_presheaf_cocone_naturality (W := W) f } }

/-- Helper for Lemma 4.27.9: evaluating the denominator diagram at `X` recovers the `Type`-valued
Hom-diagram used in the left-fraction presentation of `Hom(Q(X), Q(Y))`. -/
abbrev localization_evaluation_diagram [W.HasLeftCalculusOfFractions] (X Y : C) :
    localization_denominator_category W Y ⥤ Type (max u v) :=
  localization_denominator_diagram W Y ⋙ (evaluation Cᵒᵖ (Type (max u v))).obj (Opposite.op X)

/-- Helper for Lemma 4.27.9: the evaluated cocone leg at `s : Y / W` sends `g : X ⟶ s.right` to
the roof `(g, s)` in the localization. -/
noncomputable def localization_evaluation_cocone_app [W.HasLeftCalculusOfFractions] (X Y : C)
    (s : localization_denominator_category W Y) :
    (localization_evaluation_diagram W X Y).obj s →
      (localization_target_presheaf W Y).obj (Opposite.op X) :=
  fun g ↦ ULift.up (W.Q.map g.down ≫
    localization_basic_fraction (W := W) s)

/-- Helper for Lemma 4.27.9: evaluating the leg indexed by `s` at a numerator `g : X ⟶ s.right`
gives the image of the left fraction `(g, s)`. -/
lemma localization_evaluation_cocone_app_eq_map [W.HasLeftCalculusOfFractions] (X Y : C)
    (s : localization_denominator_category W Y) (g : X ⟶ s.right) :
    localization_evaluation_cocone_app (W := W) X Y s (ULift.up g) =
      ULift.up
        ((LeftFraction.mk g (localization_denominator_hom (W := W) s)
            (localization_denominator_hom_mem (W := W) s)).map W.Q
          (Localization.inverts W.Q W)) := by
  -- The fraction `(g, s)` factors as `ofHom g` followed by the basic inverse roof for `s`.
  change ULift.up (W.Q.map g ≫ localization_basic_fraction (W := W) s) = _
  apply congrArg ULift.up
  simpa [localization_basic_fraction, LeftFraction.comp₀, Category.assoc,
    MorphismProperty.LeftFraction.map_ofHom] using
    (MorphismProperty.LeftFraction.map_comp_map_eq_map
      (MorphismProperty.LeftFraction.ofHom W g)
      (MorphismProperty.LeftFraction.ofInv (localization_denominator_hom (W := W) s)
        (localization_denominator_hom_mem (W := W) s))
      (MorphismProperty.LeftFraction.ofHom W (𝟙 s.right)) (by simp) W.Q)

/-- Helper for Lemma 4.27.9: the evaluated cocone legs are natural in the denominator category. -/
lemma localization_evaluation_cocone_naturality [W.HasLeftCalculusOfFractions] (X Y : C)
    {s t : localization_denominator_category W Y} (f : s ⟶ t) :
    (localization_evaluation_diagram W X Y).map f ≫
        localization_evaluation_cocone_app (W := W) X Y t =
      localization_evaluation_cocone_app (W := W) X Y s := by
  funext g
  -- After evaluating at `X`, naturality is the same roof identity as above, now postcomposed by
  -- the numerator `g`.
  change
    ULift.up (W.Q.map (g.down ≫ f.right) ≫
      localization_basic_fraction (W := W) t) =
      ULift.up (W.Q.map g.down ≫ localization_basic_fraction (W := W) s)
  rw [Functor.map_comp]
  simp [Category.assoc, localization_basic_fraction_naturality (W := W) f]

/-- Helper for Lemma 4.27.9: the explicit evaluated roof cocone in `Type`. -/
noncomputable def localization_evaluation_cocone [W.HasLeftCalculusOfFractions] (X Y : C) :
    Cocone (localization_evaluation_diagram W X Y) :=
  { pt := (localization_target_presheaf W Y).obj (Opposite.op X)
    ι :=
      { app := localization_evaluation_cocone_app (W := W) X Y
        naturality := fun _ _ f ↦ localization_evaluation_cocone_naturality (W := W) X Y f } }

/-- Helper for Lemma 4.27.9: the explicit evaluated roof cocone is colimiting. -/
theorem localization_evaluation_coconeTypes_isColimit
    [W.HasLeftCalculusOfFractions] (X Y : C) :
    let F : localization_denominator_category W Y ⥤ Type (max u v) :=
      localization_evaluation_diagram W X Y
    let c : F.CoconeTypes := F.coconeTypesEquiv.symm (localization_evaluation_cocone (W := W) X Y)
    c.IsColimit := by
  let F : localization_denominator_category W Y ⥤ Type (max u v) :=
    localization_evaluation_diagram W X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (localization_evaluation_cocone (W := W) X Y)
  refine ⟨?_⟩
  constructor
  · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered]
    intro s t f g hfg
    let φ : W.LeftFraction X Y := LeftFraction.mk f.down
      (localization_denominator_hom (W := W) s) (localization_denominator_hom_mem (W := W) s)
    let ψ : W.LeftFraction X Y := LeftFraction.mk g.down
      (localization_denominator_hom (W := W) t) (localization_denominator_hom_mem (W := W) t)
    change localization_evaluation_cocone_app (W := W) X Y s f =
        localization_evaluation_cocone_app (W := W) X Y t g at hfg
    have hmap :
        φ.map W.Q (Localization.inverts W.Q W) =
          ψ.map W.Q (Localization.inverts W.Q W) := by
      have hmapUp :
          ULift.up (φ.map W.Q (Localization.inverts W.Q W)) =
            ULift.up (ψ.map W.Q (Localization.inverts W.Q W)) := by
        have hsEq :
            ULift.up (φ.map W.Q (Localization.inverts W.Q W)) =
              localization_evaluation_cocone_app (W := W) X Y s (ULift.up f.down) := by
          symm
          simpa [φ, localization_denominator_hom] using
            localization_evaluation_cocone_app_eq_map (W := W) X Y s f.down
        have hfgEq :
            localization_evaluation_cocone_app (W := W) X Y s (ULift.up f.down) =
              localization_evaluation_cocone_app (W := W) X Y t (ULift.up g.down) := by
          simpa using hfg
        have htEq :
            localization_evaluation_cocone_app (W := W) X Y t (ULift.up g.down) =
              ULift.up (ψ.map W.Q (Localization.inverts W.Q W)) := by
          simpa [ψ, localization_denominator_hom] using
            localization_evaluation_cocone_app_eq_map (W := W) X Y t g.down
        exact hsEq.trans (hfgEq.trans htEq)
      exact congrArg ULift.down hmapUp
    obtain ⟨Z, a, b, hab, hfg', hW⟩ :=
      (MorphismProperty.LeftFraction.map_eq_iff (L := W.Q) (W := W) φ ψ).mp hmap
    let u : localization_denominator_category W Y :=
      MorphismProperty.Under.mk (⊤ : MorphismProperty C)
        (localization_denominator_hom (W := W) s ≫ a) hW
    refine ⟨u, ?_, ?_, ?_⟩
    · exact MorphismProperty.Under.homMk a rfl
    · exact MorphismProperty.Under.homMk b (by simpa [u, localization_denominator_hom] using hab.symm)
    change ULift.up (f.down ≫ a) = ULift.up (g.down ≫ b)
    simpa using hfg'
  · rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    change ∀ z : (localization_target_presheaf W Y).obj (Opposite.op X),
        ∃ s x, localization_evaluation_cocone_app (W := W) X Y s x = z
    intro z
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction W.Q W z.down
    let s : localization_denominator_category W Y :=
      MorphismProperty.Under.mk (⊤ : MorphismProperty C) φ.s φ.hs
    refine ⟨s, ULift.up φ.f, ?_⟩
    -- Every localized morphism is represented by some left fraction, so it lies in the image of
    -- the leg indexed by that denominator.
    have hsEq :
        localization_evaluation_cocone_app (W := W) X Y s (ULift.up φ.f) =
          ULift.up (φ.map W.Q (Localization.inverts W.Q W)) := by
      simpa [s, localization_denominator_hom] using
        localization_evaluation_cocone_app_eq_map (W := W) X Y s φ.f
    have hzEq : ULift.up (φ.map W.Q (Localization.inverts W.Q W)) = ULift.up z.down :=
      congrArg ULift.up hφ.symm
    have hzRefl : ULift.up z.down = z := by
      cases z
      rfl
    exact hsEq.trans (hzEq.trans hzRefl)

/-- Helper for Lemma 4.27.9: each evaluated roof cocone is colimiting. -/
noncomputable def localization_evaluation_cocone_isColimit
    [W.HasLeftCalculusOfFractions] (X Y : C) :
    IsColimit (localization_evaluation_cocone (W := W) X Y) := by
  let F : localization_denominator_category W Y ⥤ Type (max u v) :=
    localization_evaluation_diagram W X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (localization_evaluation_cocone (W := W) X Y)
  have hc : c.IsColimit := by
    simpa [F, c] using localization_evaluation_coconeTypes_isColimit (W := W) X Y
  exact Nonempty.some <| by
    simpa [c] using (Functor.CoconeTypes.isColimit_iff c).mp hc

/-- Helper for Lemma 4.27.9: evaluating the presheaf cocone at `X` produces the explicit roof
cocone. -/
noncomputable def localization_presheaf_cocone_eval_iso [W.HasLeftCalculusOfFractions] (X Y : C) :
    ((evaluation Cᵒᵖ (Type (max u v))).obj (Opposite.op X)).mapCocone
        (localization_presheaf_cocone (W := W) Y) ≅
      localization_evaluation_cocone (W := W) X Y := by
  refine Cocone.ext (Iso.refl _) ?_
  intro s
  ext g
  cases g using ULift.rec with
  | _ g =>
      rfl

/-- Helper for Lemma 4.27.9: each evaluation of the presheaf cocone is a colimit cocone. -/
noncomputable def localization_presheaf_cocone_eval_isColimit [W.HasLeftCalculusOfFractions] (Y : C)
    (X : Cᵒᵖ) :
    IsColimit (((evaluation Cᵒᵖ (Type (max u v))).obj X).mapCocone
      (localization_presheaf_cocone (W := W) Y)) := by
  -- Evaluate at `X`, replace the result by the explicit roof cocone, and use the `Type`-valued
  -- left-fraction colimit argument.
  refine IsColimit.ofIsoColimit
    (localization_evaluation_cocone_isColimit (W := W) X.unop Y) ?_
  simpa using (localization_presheaf_cocone_eval_iso (W := W) X.unop Y).symm

/-- Helper for Lemma 4.27.9: the explicit presheaf roof cocone is colimiting. -/
noncomputable def localization_presheaf_colimitCocone [W.HasLeftCalculusOfFractions] (Y : C) :
    ColimitCocone (localization_denominator_diagram W Y) :=
  { cocone := localization_presheaf_cocone (W := W) Y
    isColimit := Limits.evaluationJointlyReflectsColimits _
      (fun X ↦ localization_presheaf_cocone_eval_isColimit (W := W) Y X) }

/-- Helper for Lemma 4.27.9: the localized Hom-presheaf at `Q(Y)` is the filtered colimit of the
representables indexed by the denominator category `Y / W`. -/
noncomputable def localization_presheaf_iso_of_left_fractions [W.HasLeftCalculusOfFractions]
    (Y : C) :
    colimit (localization_denominator_diagram W Y) ≅
      W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u} :=
  colimit.isoColimitCocone (localization_presheaf_colimitCocone (W := W) Y)

/-- Helper for Lemma 4.27.9: for a model object `Q(Y)`, the Yoneda presheaf of localized morphisms
sends the chosen colimit cocone of `K` to a limit cone. -/
noncomputable def localized_yoneda_limit_at_model_obj [W.HasLeftCalculusOfFractions]
    {J : Type w} [SmallCategory J] [FinCategory J] (K : J ⥤ C)
    (c : Cocone K) (hc : IsColimit c) (Y : C) :
    IsLimit ((yoneda.obj (W.Q.obj Y)).mapCone (W.Q.mapCocone c).op) := by
  -- First show the ulifted localized Hom-presheaf is left exact by expressing it as the filtered
  -- colimit over `Y / W` of representables.
  have hpresULift :
      PreservesFiniteLimits (W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u}) := by
    exact localization_presheaf_preservesFiniteLimits_of_iso (W := W) Y
      (localization_presheaf_iso_of_left_fractions (W := W) Y)
  have hpres :
      PreservesFiniteLimits (W.Q.op ⋙ yoneda.obj (W.Q.obj Y)) := by
    have hpresAssoc :
        PreservesFiniteLimits (((W.Q.op ⋙ yoneda.obj (W.Q.obj Y)) ⋙ uliftFunctor.{u})) := by
      simpa [Functor.assoc] using hpresULift
    letI :
        PreservesFiniteLimits (((W.Q.op ⋙ yoneda.obj (W.Q.obj Y)) ⋙ uliftFunctor.{u})) :=
      hpresAssoc
    exact preservesFiniteLimits_of_reflects_of_preserves _ uliftFunctor.{u}
  -- Applying that presheaf to the opposite of a colimit cocone yields a limit cone.
  have hlimit :
      IsLimit ((W.Q.op ⋙ yoneda.obj (W.Q.obj Y)).mapCone c.op) := by
    exact isLimitOfPreserves (W.Q.op ⋙ yoneda.obj (W.Q.obj Y)) hc.op
  have hmap :
      IsLimit ((yoneda.obj (W.Q.obj Y)).mapCone ((W.Q.op).mapCone c.op)) := by
    exact IsLimit.ofIsoLimit hlimit
      (Functor.mapConeMapCone (H := W.Q.op) (H' := yoneda.obj (W.Q.obj Y)) c.op).symm
  -- The opposite of `W.Q.mapCocone` is definitionally the same cone up to the canonical cone iso.
  exact IsLimit.ofIsoLimit hmap (Cone.ext (Iso.refl _) (by simp))

/-- Helper for Lemma 4.27.9: essential surjectivity transports the model-object Yoneda limit
statement to every object of the localization. -/
noncomputable def localized_yoneda_limit_at_any_obj [W.HasLeftCalculusOfFractions]
    {J : Type w} [SmallCategory J] [FinCategory J] (K : J ⥤ C)
    (c : Cocone K) (hc : IsColimit c) (X : W.Localization) :
    IsLimit ((yoneda.obj X).mapCone (W.Q.mapCocone c).op) := by
  -- Every localization object is isomorphic to some `Q(Y)`, so we transport the limit statement
  -- across the induced Yoneda isomorphism.
  let Y := W.Q.objPreimage X
  let e : W.Q.obj Y ≅ X := W.Q.objObjPreimageIso X
  exact IsLimit.mapConeEquiv (yoneda.mapIso e)
    (localized_yoneda_limit_at_model_obj (W := W) K c hc Y)

/-- Helper for Lemma 4.27.9: the image under `W.Q` of the chosen colimit cocone of `K` is again a
colimit cocone. -/
noncomputable def localization_mapCocone_isColimit [W.HasLeftCalculusOfFractions]
    {J : Type w} [SmallCategory J] [FinCategory J] (K : J ⥤ C)
    (c : Cocone K) (hc : IsColimit c) :
    IsColimit (W.Q.mapCocone c) := by
  -- Yoneda detects colimits, so it is enough to verify the corresponding limit statement for all
  -- representable presheaves on the localization.
  exact (Limits.Cocone.isColimitYonedaEquiv (W.Q.mapCocone c)).2
    (localized_yoneda_limit_at_any_obj (W := W) K c hc)

/- Domain-style sampling for Lemma 4.27.9:
- primary domain: localization of morphism properties and finite-colimit preservation;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `Functor.q_isLocalization`,
  `Functor.IsLocalization.pi`,
  `Localization.equivalenceFromModel`,
  `Localization.qCompEquivalenceFromModelFunctorIso`;
- best owner abstraction: `Functor.IsLocalization`, with `PreservesFiniteColimits L` as derived API
  for a localization functor `L`, transported from the canonical model `W.Q` along the owner
  equivalence `equivalenceFromModel`.

Primitive-vs-derived split:
- primitive data: the morphism property `W` and a localization functor `L`;
- derived API: the instance `PreservesFiniteColimits L`, transported from the canonical owner
  functor `W.Q`.

Source/core/bridge triage:
- source-facing: the instance `PreservesFiniteColimits W.Q`;
- core/canonical: `Functor.IsLocalization`;
- bridge/view: `Functor.IsLocalization.preservesFiniteColimits`, which transports the owner
  instance along `equivalenceFromModel` and `qCompEquivalenceFromModelFunctorIso`. -/

-- Proof sketch: for each object `Y`, represent `Hom_{W.Localization}(W.Q.obj -, W.Q.obj Y)` as a
-- filtered colimit of representable functors using `4.27.7.1`; then filtered colimits commute
-- with finite limits in `Type`, so these hom-functors send finite colimits in `C` to limits, which
-- is exactly the universal property that `W.Q` preserves finite colimits.
/-- Lemma 4.27.9: if `W` is a left multiplicative system in `C`, then the localization functor
`W.Q : C ⥤ W.Localization` commutes with finite colimits. -/
instance localization_Q_preservesFiniteColimits [W.HasLeftCalculusOfFractions] :
    PreservesFiniteColimits W.Q where
  -- Route correction: package the left-fraction comparison as one presheaf colimit, deduce that
  -- each localized Hom-presheaf preserves finite limits, and conclude via Yoneda detection.
  preservesFiniteColimits J _ _ := by
    constructor
    intro K
    constructor
    intro c hc
    exact ⟨localization_mapCocone_isColimit (W := W) K c hc⟩

namespace Functor.IsLocalization

-- Proof sketch: transport finite-colimit preservation from the canonical localization functor
-- `W.Q` across the equivalence `equivalenceFromModel L W`, using the natural isomorphism
-- `qCompEquivalenceFromModelFunctorIso L W`.
/-- Any localization functor of a left multiplicative system is canonically identified with
`W.Q`, so it also preserves finite colimits. -/
theorem preservesFiniteColimits
    {D : Type w} [Category.{v} D] (L : C ⥤ D) [W.HasLeftCalculusOfFractions]
    [L.IsLocalization W] : PreservesFiniteColimits L := by
  -- Transport the canonical finite-colimit preservation of `W.Q` across the chosen equivalence
  -- from the localization model `W.Localization` to the target category `D`.
  let e := Localization.equivalenceFromModel L W
  letI : PreservesFiniteColimits W.Q := localization_Q_preservesFiniteColimits W
  letI : PreservesFiniteColimits e.functor := by infer_instance
  letI : PreservesFiniteColimits (W.Q ⋙ e.functor) :=
    Limits.comp_preservesFiniteColimits W.Q e.functor
  exact
    preservesFiniteColimits_of_natIso
      (Localization.qCompEquivalenceFromModelFunctorIso L W)

end Functor.IsLocalization

end CategoryTheory
