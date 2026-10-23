module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import stacks_project.Chap04.Lemma_4_19_9
public import stacks_project.Chap07.Lemma_7_5_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe w w' t v₁ v₂ u₁ u₂

noncomputable section

section PresheafPart

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)
variable [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasLeftKanExtension P]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-
Domain-style sampling for Lemma 7.21.6:
- primary domain: the presheaf-level left Kan extension `u.op.lan`;
- sampled owner API:
  `Functor.lanCompIsoOfPreserves`,
  `structuredArrowOpEquivalence`,
  `Functor.Final.colimIso`,
  `CategoryTheory.Limits.colimit_preserves_finite_connected_limits_of_types`;
- source/core/bridge triage:
  `source-facing`: the indexing categories `(𝓘_V^u)ᵒᵖ`;
  `core/canonical`: evaluation of `u.op.lan`;
  `bridge/view`: transport to a large enough universe so those indexing categories are small.
-/

-- Proof sketch: enlarge the target universe of sets, use Lemmas `7.5.1` and `4.19.9` on the
-- resulting small indexing categories, and then descend back along the universe-lift functor.
/-- Helper for Lemma 7.21.6: enlarge the universe of sets just enough that the structured-arrow
indexing categories become small. -/
abbrev type_lift_functor :
    Type t ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂)) :=
  CategoryTheory.uliftFunctor.{max (max (max u₁ u₂) v₁) v₂, t}

/-- Helper for Lemma 7.21.6: the pointwise colimit formula for `u.op.lan` is natural in the
presheaf argument in any target universe. -/
private theorem leftKanExtensionObjIsoColimit_naturality_univ
    [∀ F : Cᵒᵖ ⥤ Type w', u.op.HasPointwiseLeftKanExtension F]
    {P Q : Cᵒᵖ ⥤ Type w'} (η : P ⟶ Q) (V : D) :
    (((show ((Cᵒᵖ ⥤ Type w') ⥤ Dᵒᵖ ⥤ Type w') from u.op.lan) ⋙
          (evaluation Dᵒᵖ (Type w')).obj (op V)).map η) ≫
      (u.op.leftKanExtensionObjIsoColimit Q (op V)).hom =
    (u.op.leftKanExtensionObjIsoColimit P (op V)).hom ≫
      colimMap ((CostructuredArrow.proj u.op (op V)).whiskerLeft η) := by
  let eP := u.op.leftKanExtensionObjIsoColimit P (op V)
  let eQ := u.op.leftKanExtensionObjIsoColimit Q (op V)
  let FP : CostructuredArrow u.op (op V) ⥤ Type w' :=
    CostructuredArrow.proj u.op (op V) ⋙ P
  let FQ : CostructuredArrow u.op (op V) ⥤ Type w' :=
    CostructuredArrow.proj u.op (op V) ⋙ Q
  -- Compare the two maps after precomposing with the inverse of the colimit comparison.
  exact (Iso.cancel_iso_inv_left eP _ _).1 <| by
    apply colimit.hom_ext
    intro A
    ext x
    simp [Functor.comp_map, Functor.lan]
    -- Rewrite the source colimit class using the owner-level inverse formula.
    have hP :
        eP.inv ((colimit.ι FP A) x) =
          ((((u.op.leftKanExtensionUnit P).app A.left) ≫
              ((u.op.leftKanExtension P).map A.hom)) x) := by
      simpa [eP, FP, Functor.lan] using
        congrArg (fun k ↦ k x)
          (u.op.ι_leftKanExtensionObjIsoColimit_inv (F := P) (X := op V) A)
    -- Move the comparison map past the restriction map in the lifted Kan extension.
    have hNat :
        ((u.op.leftKanExtensionUnit P).app A.left ≫
              (u.op.leftKanExtension P).map A.hom ≫
              (u.op.lan.map η).app (op V)) x =
          ((u.op.leftKanExtensionUnit P).app A.left ≫
              (u.op.lan.map η).app (u.op.obj A.left) ≫
              (u.op.leftKanExtension Q).map A.hom) x := by
      exact
        congrArg (fun k ↦ k (((u.op.leftKanExtensionUnit P).app A.left) x))
          ((u.op.lan.map η).naturality A.hom)
    -- Identify the lifted Kan-extension map with the defining descent from `η`.
    have hDesc :
        ((u.op.leftKanExtensionUnit P).app A.left ≫
              (u.op.lan.map η).app (u.op.obj A.left)) x =
          (η.app A.left ≫ (u.op.leftKanExtensionUnit Q).app A.left) x := by
      simpa [Functor.lan] using
        congrArg (fun k ↦ k x)
          (Functor.descOfIsLeftKanExtension_fac_app
            (F' := u.op.leftKanExtension P)
            (α := u.op.leftKanExtensionUnit P)
            (G := u.op.leftKanExtension Q)
            (β := η ≫ u.op.leftKanExtensionUnit Q)
            A.left)
    have hDesc' :
        ((u.op.leftKanExtensionUnit P).app A.left ≫
              (u.op.lan.map η).app (u.op.obj A.left) ≫
              (u.op.leftKanExtension Q).map A.hom) x =
          ((η.app A.left) ≫
              (u.op.leftKanExtensionUnit Q).app A.left ≫
              (u.op.leftKanExtension Q).map A.hom) x := by
      exact congrArg (fun y ↦ ((u.op.leftKanExtension Q).map A.hom) y) hDesc
    -- Rewrite the target colimit class using the owner-level forward formula.
    have hQ :
        eQ.hom
            ((((u.op.leftKanExtensionUnit Q).app A.left) ≫
                ((u.op.leftKanExtension Q).map A.hom))
              (((η.app A.left) x))) =
          ((colimit.ι FQ A) ((η.app A.left) x)) := by
      simpa [eQ, FQ, Functor.lan] using
        congrArg (fun k ↦ k ((η.app A.left) x))
          (u.op.ι_leftKanExtensionObjIsoColimit_hom (F := Q) (X := op V) A)
    -- The colimit map on the indexing diagram acts by applying `η` at the left object.
    have hMap :
        colimMap ((CostructuredArrow.proj u.op (op V)).whiskerLeft η) ((colimit.ι FP A) x) =
          ((colimit.ι FQ A) ((η.app A.left) x)) := by
      simpa [FP, FQ] using
        congrArg (fun k ↦ k x)
          (ι_colimMap ((CostructuredArrow.proj u.op (op V)).whiskerLeft η) A)
    have hP_hom :
        eP.hom
            ((((u.op.leftKanExtensionUnit P).app A.left) ≫
                ((u.op.leftKanExtension P).map A.hom)) x) =
          ((colimit.ι FP A) x) := by
      rw [← hP]
      simp
    rw [hP]
    change
      eQ.hom
          (((((u.op.leftKanExtensionUnit P).app A.left) ≫
              (u.op.leftKanExtension P).map A.hom ≫
              (u.op.lan.map η).app (op V)) x)) =
        _
    rw [hNat]
    rw [hDesc']
    rw [hP_hom]
    rw [hMap]
    exact hQ

/-- Helper for Lemma 7.21.6: the objectwise colimit description of the Kan extension is natural
in the presheaf variable in the enlarged universe used later in the proof. -/
theorem leftKanExtensionObjIsoColimit_naturality
    {P Q : Cᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))} (η : P ⟶ Q) (V : D) :
    (((show (Cᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
            Dᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂)) from u.op.lan) ⋙
          (evaluation Dᵒᵖ (Type (max t (max (max (max u₁ u₂) v₁) v₂)))).obj (op V)).map η) ≫
      (u.op.leftKanExtensionObjIsoColimit Q (op V)).hom =
    (u.op.leftKanExtensionObjIsoColimit P (op V)).hom ≫
      colimMap ((CostructuredArrow.proj u.op (op V)).whiskerLeft η) := by
  -- Specialize the universe-polymorphic normalization to the enlarged universe used below.
  simpa using leftKanExtensionObjIsoColimit_naturality_univ (u := u) (η := η) (V := V)

/-- Helper for Lemma 7.21.6: span cocones transport across the canonical `AsSmall`
equivalence. -/
private theorem asSmall_hasSpanCocones
    (I : Type _) [Category I] [HasSpanCocones I] :
    HasSpanCocones (AsSmall I) where
  span f g := by
    -- Shrink the span problem back to the original category, solve it there, and lift the apex.
    obtain ⟨w, fy, gz, hfg⟩ := HasSpanCocones.span f.down g.down
    refine ⟨AsSmall.up.obj w, AsSmall.up.map fy, AsSmall.up.map gz, ?_⟩
    simpa using congrArg (fun k => AsSmall.up.map k) hfg

/-- Helper for Lemma 7.21.6: after shrinking the structured-arrow indexing category with
`AsSmall`, Lemma 4.19.9 applies to the lifted colimit functor. -/
private theorem structuredArrow_op_colimit_preserves_finite_connected_limits_lifted
    (K : Type w) [SmallCategory K] [FinCategory K] [IsConnected K] (V : D) :
    PreservesLimitsOfShape K
      (colim :
        ((StructuredArrow V u)ᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
          Type (max t (max (max (max u₁ u₂) v₁) v₂))) := by
  let S := (StructuredArrow V u)ᵒᵖ
  have hStructured := structuredArrow_op_has_span_cocones_and_postcomposition_equalizers u V
  let e : AsSmall S ≌ S := AsSmall.equiv.symm
  let _ : HasSpanCocones (AsSmall S) := asSmall_hasSpanCocones S
  have hMap :
      ∀ ⦃X Y : AsSmall S⦄ (f g : X ⟶ Y),
        ∃ (Z : AsSmall S) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
    intro X Y f g
    -- The postcomposition equalizer data transports through `AsSmall.down` for the same reason.
    obtain ⟨Z, h, hfg⟩ := hStructured.2 f.down g.down
    refine ⟨AsSmall.up.obj Z, AsSmall.up.map h, ?_⟩
    simpa using congrArg (fun k => AsSmall.up.map k) hfg
  let _ :
      PreservesLimitsOfShape K
        (colim :
          (AsSmall S ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
            Type (max t (max (max (max u₁ u₂) v₁) v₂))) :=
    CategoryTheory.Limits.colimit_preserves_finite_connected_limits_of_types
      (I := AsSmall S) (J := K) hMap
  let _ :
      PreservesLimitsOfShape K
        (((Functor.whiskeringLeft _ _ _).obj e.functor) ⋙
          (colim :
            (AsSmall S ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
              Type (max t (max (max (max u₁ u₂) v₁) v₂)))) := by
    -- Precomposition along the equivalence functor preserves all limits.
    infer_instance
  -- Finality of the equivalence functor identifies the transported colimit with the original one.
  exact preservesLimitsOfShape_of_natIso (J := K) (Functor.Final.colimIso e.functor)

/-- Helper for Lemma 7.21.6: the structured-arrow/costructured-arrow equivalence transports the
lifted colimit theorem to the indexing category used by the Kan extension formula. -/
private theorem costructuredArrow_colimit_preserves_finite_connected_limits_lifted
    (K : Type w) [SmallCategory K] [FinCategory K] [IsConnected K] (V : D) :
    PreservesLimitsOfShape K
      (colim :
        (CostructuredArrow u.op (op V) ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
          Type (max t (max (max (max u₁ u₂) v₁) v₂))) := by
  let e := structuredArrowOpEquivalence u V
  let _ :
      PreservesLimitsOfShape K
        (colim :
          ((StructuredArrow V u)ᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
            Type (max t (max (max (max u₁ u₂) v₁) v₂))) :=
    structuredArrow_op_colimit_preserves_finite_connected_limits_lifted
      (u := u) (K := K) V
  let _ :
      PreservesLimitsOfShape K
        (((Functor.whiskeringLeft _ _ _).obj e.functor) ⋙
          (colim :
            ((StructuredArrow V u)ᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
              Type (max t (max (max (max u₁ u₂) v₁) v₂)))) := by
    -- Transport the structured-arrow result across the standard equivalence of indexing categories.
    infer_instance
  exact preservesLimitsOfShape_of_natIso (J := K) (Functor.Final.colimIso e.functor)

/-- Helper for Lemma 7.21.6: evaluating `u.op.lan` at `V` preserves finite connected limits. -/
private theorem lan_evaluation_preserves_finite_connected_limits_lifted
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] (V : D) :
    PreservesLimitsOfShape I
      (((u.op.lan :
            (Cᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
              Dᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂)))) ⋙
          (evaluation Dᵒᵖ (Type (max t (max (max (max u₁ u₂) v₁) v₂)))).obj (op V)) := by
  let Tl := Type (max t (max (max (max u₁ u₂) v₁) v₂))
  let eColim :
      (((u.op.lan : (Cᵒᵖ ⥤ Tl) ⥤ Dᵒᵖ ⥤ Tl)) ⋙ (evaluation Dᵒᵖ Tl).obj (op V)) ≅
        ((Functor.whiskeringLeft _ _ Tl).obj (CostructuredArrow.proj u.op (op V)) ⋙ colim) :=
    NatIso.ofComponents
      (fun P ↦ u.op.leftKanExtensionObjIsoColimit P (op V))
      (fun {P Q} η ↦ leftKanExtensionObjIsoColimit_naturality (u := u) (η := η) (V := V))
  -- The lifted Kan extension is exactly the structured-arrow colimit from the source proof.
  let _ :
      PreservesLimitsOfShape I
      (colim : (CostructuredArrow u.op (op V) ⥤ Tl) ⥤ Tl) :=
    costructuredArrow_colimit_preserves_finite_connected_limits_lifted
      (u := u) (K := I) V
  exact preservesLimitsOfShape_of_natIso (J := I) eColim.symm

/-- Helper for Lemma 7.21.6: once every evaluation of the lifted Kan extension preserves
finite connected limits, the lifted Kan extension itself does as well. -/
private theorem lan_preserves_finite_connected_limits_lifted
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I
      (u.op.lan :
        (Cᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) ⥤
          Dᵒᵖ ⥤ Type (max t (max (max (max u₁ u₂) v₁) v₂))) := by
  -- Evaluation detects limits in a functor category, so reuse the lifted objectwise theorem.
  apply preservesLimitsOfShape_of_evaluation
  intro V
  simpa using
    lan_evaluation_preserves_finite_connected_limits_lifted
      (u := u) (I := I) (V := unop V)

/-- Helper for Lemma 7.21.6: the presheaf left Kan extension `u.op.lan` preserves finite
connected limits after reflecting the lifted source proof across `ULift`. -/
private theorem lan_preserves_finite_connected_limits_of_hasLeftKanExtension
    [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseLeftKanExtension P]
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) := by
  let Tl := Type (max t (max (max (max u₁ u₂) v₁) v₂))
  let U : Type t ⥤ Tl := type_lift_functor.{t, v₁, v₂, u₁, u₂}
  let WRD := (Functor.whiskeringRight Dᵒᵖ (Type t) Tl).obj U
  let WRC := (Functor.whiskeringRight Cᵒᵖ (Type t) Tl).obj U
  let e :
      ((u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) ⋙ WRD) ≅
        (WRC ⋙
          (u.op.lan : (Cᵒᵖ ⥤ Tl) ⥤ Dᵒᵖ ⥤ Tl)) := by
    simpa [U, WRD, WRC, type_lift_functor] using U.lanCompIsoOfPreserves u.op
  let _ :
      PreservesLimitsOfShape I
        (u.op.lan : (Cᵒᵖ ⥤ Tl) ⥤ Dᵒᵖ ⥤ Tl) :=
    lan_preserves_finite_connected_limits_lifted (u := u) (I := I)
  let _ : PreservesLimitsOfShape I (WRC ⋙
      (u.op.lan : (Cᵒᵖ ⥤ Tl) ⥤ Dᵒᵖ ⥤ Tl)) := by
    infer_instance
  let _ :
      PreservesLimitsOfShape I
        ((u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) ⋙ WRD) :=
    preservesLimitsOfShape_of_natIso (J := I) e.symm
  let _ : ReflectsLimitsOfShape I WRD := by
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) WRD

/-- Helper for Lemma 7.21.6: evaluating `u.op.lan` at `V` preserves finite connected limits
provided the small-universe Kan extensions are pointwise. -/
private theorem lan_evaluation_preserves_finite_connected_limits
    [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseLeftKanExtension P]
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] (V : D) :
    PreservesLimitsOfShape I
      (((u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t)) ⋙
        (evaluation Dᵒᵖ (Type t)).obj (op V)) := by
  let _ :
      PreservesLimitsOfShape I
        (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) :=
    lan_preserves_finite_connected_limits_of_hasLeftKanExtension (u := u) (I := I)
  infer_instance

end PresheafPart

/-- Helper for Lemma 7.21.6: the presheaf left Kan extension `u.op.lan` preserves finite
connected limits after reflecting the lifted source proof across `ULift`. -/
theorem lan_preserves_finite_connected_limits
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (u : C ⥤ D)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseLeftKanExtension P]
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) := by
  let _ : ∀ P : Cᵒᵖ ⥤ Type t, u.op.HasLeftKanExtension P := fun P => inferInstance
  exact lan_preserves_finite_connected_limits_of_hasLeftKanExtension (u := u) (I := I)

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasSheafify K (Type t)]
variable [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasPointwiseLeftKanExtension P]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

-- Proof sketch: realize `g_!` as the sheafified left Kan extension along `u.op` from
-- Lemma `7.21.5`. Limits of sheaves are computed on the underlying presheaves, and the presheaf
-- Kan-extension part is already settled in the preceding section.
/-- Helper for Lemma 7.21.6: postcomposing a sheaf of small types with the relevant ULift functor
still yields a sheaf. -/
  private theorem isSheaf_comp_type_lift
    (P : Dᵒᵖ ⥤ Type t) (hP : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf K
      (P ⋙ (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂)))) := by
  -- The ULift functor does not change the sheaf condition on type-valued presheaves.
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_comp_uliftFunctor K ((isSheaf_iff_isSheaf_of_type K P).mp hP)

/-- Helper for Lemma 7.21.6: whiskering a locally injective map of type-valued presheaves by the
relevant ULift functor stays locally injective. -/
private theorem isLocallyInjective_whisker_ulift
    {P Q : Dᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective K η] :
    Presheaf.IsLocallyInjective K
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))) where
  equalizerSieve_mem {X} x y h := by
    -- The ULift comparison is pointwise, so the equalizer sieve is literally the unlifted one.
    have hDown : η.app X x.down = η.app X y.down := by
      change ULift.up (η.app X x.down) = ULift.up (η.app X y.down) at h
      exact ULift.up.inj h
    have hSieve :
        Presheaf.equalizerSieve
            (F := P ⋙
              (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
                Type t ⥤ Type (max t (max u₂ v₂))))
            x y =
          Presheaf.equalizerSieve (F := P) x.down y.down := by
      ext Y f
      constructor
      · intro hEq
        change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down) at hEq
        exact ULift.up.inj hEq
      · intro hEq
        change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down)
        exact congrArg ULift.up hEq
    rw [hSieve]
    exact Presheaf.equalizerSieve_mem K η x.down y.down hDown

/-- Helper for Lemma 7.21.6: the image sieve of a whiskered ULift map is the same as the
underlying image sieve before whiskering. -/
private theorem imageSieve_whisker_ulift
    {P Q : Dᵒᵖ ⥤ Type t} (η : P ⟶ Q) {X : D}
    (x : ULift.{max u₂ v₂} (Q.obj (op X))) :
    Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))) x =
      Presheaf.imageSieve η x.down := by
  ext Y f
  constructor
  · rintro ⟨y, hy⟩
    -- Any lifted local preimage descends to an ordinary local preimage by `ULift.down`.
    refine ⟨y.down, ?_⟩
    exact congrArg ULift.down hy
  · rintro ⟨y, hy⟩
    -- Conversely, any ordinary local preimage lifts back via `ULift.up`.
    refine ⟨ULift.up y, ?_⟩
    change ULift.up (η.app (op Y) y) = ULift.up (Q.map f.op x.down)
    exact congrArg ULift.up hy

/-- Helper for Lemma 7.21.6: whiskering a locally surjective map of type-valued presheaves by the
relevant ULift functor stays locally surjective. -/
private theorem isLocallySurjective_whisker_ulift
    {P Q : Dᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective K η] :
    Presheaf.IsLocallySurjective K
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))) where
  imageSieve_mem {X} x := by
  -- After identifying the image sieve with the unlifted one, use local surjectivity of `η`.
    simpa [imageSieve_whisker_ulift (η := η) x] using
      (Presheaf.imageSieve_mem K η x.down)

/-- Helper for Lemma 7.21.6: the identity functor on any `Type` universe preserves
sheafification tautologically. -/
private instance preservesSheafification_id_type
    {E : Type _} [Category E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (𝟭 (Type t)) where
  le P Q f hf := by
    -- Whiskering by the identity functor leaves the `W`-morphism unchanged.
    simpa using hf

/-- Helper for Lemma 7.21.6: the concrete `Plus` map is locally injective for type-valued
presheaves in any universe. -/
private theorem toPlus_isLocallyInjective_type
    [∀ X : D, Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ (Type w')]
    [∀ P' : Dᵒᵖ ⥤ Type w', ∀ X : D, ∀ S : K.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : D, Limits.PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget (Type w'))]
    (P : Dᵒᵖ ⥤ Type w') :
    Presheaf.IsLocallyInjective K (K.toPlus P) := by
  letI : Presheaf.IsLocallyInjective K (K.toPlus P) := {
    equalizerSieve_mem := by
      intro X x y h
      open GrothendieckTopology.Plus in
      rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
      obtain ⟨W, h₁, h₂, eq⟩ := h
      exact K.superset_covering (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2 }
  infer_instance

/-- Helper for Lemma 7.21.6: the concrete `Plus` map is locally surjective for type-valued
presheaves in any universe. -/
private theorem toPlus_isLocallySurjective_type
    [∀ X : D, Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ (Type w')]
    [∀ P' : Dᵒᵖ ⥤ Type w', ∀ X : D, ∀ S : K.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : D, Limits.PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget (Type w'))]
    (P : Dᵒᵖ ⥤ Type w') :
    Presheaf.IsLocallySurjective K (K.toPlus P) := by
  letI : Presheaf.IsLocallySurjective K (K.toPlus P) := {
    imageSieve_mem := by
      intro X x
      open GrothendieckTopology.Plus in
      obtain ⟨S, x, rfl⟩ := exists_rep x
      refine K.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
      rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
      refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
      ext ⟨Z, g, hg⟩
      simpa using
        x.2
          { fst.hf := hf
            snd.hf := S.1.downward_closed hf g
            r.g₁ := g
            r.g₂ := 𝟙 Z
            .. } }
  infer_instance

/-- Helper for Lemma 7.21.6: the concrete `Plus` model of sheafification is locally injective for
type-valued presheaves in any universe. -/
private theorem concrete_toSheafify_isLocallyInjective_type
    [∀ X : D, Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ (Type w')]
    [∀ P' : Dᵒᵖ ⥤ Type w', ∀ X : D, ∀ S : K.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : D, Limits.PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget (Type w'))]
    (P : Dᵒᵖ ⥤ Type w') :
    Presheaf.IsLocallyInjective K (K.toSheafify P) := by
  letI : Presheaf.IsLocallyInjective K (K.toPlus P) :=
    toPlus_isLocallyInjective_type (K := K) P
  letI : Presheaf.IsLocallyInjective K (K.toPlus (K.plusObj P)) :=
    toPlus_isLocallyInjective_type (K := K) (K.plusObj P)
  -- Rewrite the concrete sheafification unit as a composite of two `toPlus` maps.
  change Presheaf.IsLocallyInjective K (K.toPlus P ≫ K.plusMap (K.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.21.6: the concrete `Plus` model of sheafification is locally surjective for
type-valued presheaves in any universe. -/
private theorem concrete_toSheafify_isLocallySurjective_type
    [∀ X : D, Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ (Type w')]
    [∀ P' : Dᵒᵖ ⥤ Type w', ∀ X : D, ∀ S : K.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : D, Limits.PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget (Type w'))]
    (P : Dᵒᵖ ⥤ Type w') :
    Presheaf.IsLocallySurjective K (K.toSheafify P) := by
  letI : Presheaf.IsLocallySurjective K (K.toPlus P) :=
    toPlus_isLocallySurjective_type (K := K) P
  letI : Presheaf.IsLocallySurjective K (K.toPlus (K.plusObj P)) :=
    toPlus_isLocallySurjective_type (K := K) (K.plusObj P)
  -- The same concrete `Plus` factorization gives local surjectivity of `K.toSheafify`.
  change Presheaf.IsLocallySurjective K (K.toPlus P ≫ K.plusMap (K.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.21.6: once the target universe is large enough for the concrete `Plus`
construction, the abstract sheafification unit is locally injective. -/
private theorem large_toSheafify_isLocallyInjective_type
    [HasWeakSheafify K (Type (max w' (max u₂ v₂)))]
    (P : Dᵒᵖ ⥤ Type (max w' (max u₂ v₂))) :
    Presheaf.IsLocallyInjective K (toSheafify K P) := by
  let T := Type (max w' (max u₂ v₂))
  let _ : Presheaf.IsLocallyInjective K (K.toSheafify (P ⋙ forget T)) :=
    concrete_toSheafify_isLocallyInjective_type (K := K) (P := P ⋙ forget T)
  -- Compare the concrete `Plus` model with the abstract sheafification in the large universe.
  rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso ((plusPlusIsoSheafify K T (P ⋙ forget T)).hom) := by
    infer_instance
  let _ : IsIso ((sheafifyComposeIso K (forget T) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.21.6: once the target universe is large enough for the concrete `Plus`
construction, the abstract sheafification unit is locally surjective. -/
private theorem large_toSheafify_isLocallySurjective_type
    [HasWeakSheafify K (Type (max w' (max u₂ v₂)))]
    (P : Dᵒᵖ ⥤ Type (max w' (max u₂ v₂))) :
    Presheaf.IsLocallySurjective K (toSheafify K P) := by
  let T := Type (max w' (max u₂ v₂))
  let _ : Presheaf.IsLocallySurjective K (K.toSheafify (P ⋙ forget T)) :=
    concrete_toSheafify_isLocallySurjective_type (K := K) (P := P ⋙ forget T)
  -- The same large-universe comparison transfers local surjectivity from the concrete model.
  rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso ((plusPlusIsoSheafify K T (P ⋙ forget T)).hom) := by
    infer_instance
  let _ : IsIso ((sheafifyComposeIso K (forget T) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.21.6: any left exact sheafification functor already preserves the finite
connected limits that appear in the source proof. -/
private theorem presheafToSheaf_preserves_finite_connected_limits_of_hasSheafify
    {A : Type w'} [Category A] [HasSheafify K A]
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (presheafToSheaf K A) := by
  -- Once `presheafToSheaf` is left exact, the finite connected case is immediate by the owner
  -- finite-limit instance.
  let _ : PreservesFiniteLimits (presheafToSheaf K A) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.21.6: sheafification should preserve finite connected limits; this is the
remaining universe-descent step from the standard large-universe left exactness theorem. -/
private theorem presheafToSheaf_preserves_finite_connected_limits_large
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (presheafToSheaf K (Type (max t (max u₂ v₂)))) := by
  -- In the large target universe, `HasSheafify` is available outright, so the source sheafification
  -- step reduces to the generic left exactness helper above.
  simpa using
    (presheafToSheaf_preserves_finite_connected_limits_of_hasSheafify
      (K := K) (A := Type (max t (max u₂ v₂))) (I := I))

/-- Helper for Lemma 7.21.6: `sheafCompose` followed by `sheafToPresheaf` is definitionally the
underlying whiskering functor on presheaves. -/
private noncomputable def sheafCompose_comp_sheafToPresheaf_iso
    {Ts : Type _} [Category Ts] (F : Type t ⥤ Ts) [K.HasSheafCompose F] :
    sheafCompose K F ⋙ sheafToPresheaf K Ts ≅
      sheafToPresheaf K (Type t) ⋙ (Functor.whiskeringRight Dᵒᵖ (Type t) Ts).obj F :=
  Iso.refl _

/-- Helper for Lemma 7.21.6: composing a sheaf of small types with the relevant ULift functor
still yields a sheaf. -/
private instance uliftFunctor_hasSheafCompose_type :
    K.HasSheafCompose
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂))) where
  isSheaf P hP := by
    -- Convert to the type-valued sheaf condition and use stability under `ULift`.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := K)
      ((isSheaf_iff_isSheaf_of_type K P).1 hP)

/-- Helper for Lemma 7.21.6: local injectivity reflects across whiskering by the relevant
`ULift` functor. -/
private theorem locallyInjective_of_whisker_ulift
    {P Q : Dᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective K
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂))))] :
    Presheaf.IsLocallyInjective K η where
  equalizerSieve_mem {X} x y h := by
    -- Apply local injectivity to the lifted equality and then descend the equalizer sieve.
    let x' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))).obj X := ULift.up x
    let y' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))).obj X := ULift.up y
    have hUp :
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))).app X x' =
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
              Type t ⥤ Type (max t (max u₂ v₂)))).app X y' := by
      change ULift.up (η.app X x) = ULift.up (η.app X y)
      exact congrArg ULift.up h
    let S : Sieve X.unop :=
      Presheaf.equalizerSieve
        (F := P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))))
        x' y'
    have hS : S ∈ K X.unop := by
      exact
        Presheaf.equalizerSieve_mem K
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
              Type t ⥤ Type (max t (max u₂ v₂))))
          x' y' hUp
    refine K.superset_covering ?_ hS
    intro Y f hf
    change ULift.up ((P.map f.op) x) = ULift.up ((P.map f.op) y) at hf
    change (P.map f.op) x = (P.map f.op) y
    exact ULift.up.inj hf

/-- Helper for Lemma 7.21.6: local surjectivity reflects across whiskering by the relevant
`ULift` functor. -/
private theorem locallySurjective_of_whisker_ulift
    {P Q : Dᵒᵖ ⥤ Type t} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective K
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂))))] :
    Presheaf.IsLocallySurjective K η where
  imageSieve_mem {X} x := by
    -- Identify the lifted image sieve with the original one and descend the covering statement.
    let x' :
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))).obj (op X) := ULift.up x
    let S : Sieve X :=
      Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))))
        x'
    have hS : S ∈ K X := by
      exact
        Presheaf.imageSieve_mem K
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
              Type t ⥤ Type (max t (max u₂ v₂))))
          x'
    refine K.superset_covering ?_ hS
    intro Y f hf
    change ∃ t : (P ⋙
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))).obj (op Y),
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))).app (op Y) t =
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))).map f.op x' at hf
    rcases hf with ⟨y, hy⟩
    refine ⟨y.down, ?_⟩
    change ULift.up (η.app (op Y) y.down) = ULift.up (Q.map f.op x) at hy
    exact ULift.up.inj hy

/-- Helper for Lemma 7.21.6: the underlying presheaf map of the sheafification comparison for the
relevant ULift functor. -/
private noncomputable def ulift_sheafCompose_comparison_hom
    (P : Dᵒᵖ ⥤ Type t) :
    sheafify K
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))) ⟶
      sheafify K P ⋙
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂))) :=
  (sheafToPresheaf K (Type (max t (max u₂ v₂)))).map
    ((sheafComposeNatTrans K
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂)))
      (sheafificationAdjunction K (Type t))
      (sheafificationAdjunction K (Type (max t (max u₂ v₂))))).app P)

/-- Helper for Lemma 7.21.6: the concrete presheaf comparison satisfies the standard
`toSheafify` factorization. -/
private theorem ulift_sheafCompose_comparison_hom_fac
    (P : Dᵒᵖ ⥤ Type t) :
    toSheafify K
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))) ≫
      ulift_sheafCompose_comparison_hom (K := K) P =
        Functor.whiskerRight (toSheafify K P)
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))) := by
  -- Unfold the named comparison back to the standard sheafification comparison component.
  simpa [ulift_sheafCompose_comparison_hom] using
    sheafComposeNatTrans_fac K
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂)))
      (sheafificationAdjunction K (Type t))
      (sheafificationAdjunction K (Type (max t (max u₂ v₂)))) P

/-- Helper for Lemma 7.21.6: the remaining ULift sheafification comparison is an isomorphism
exactly when the whiskered small sheafification unit is a `W`-morphism in the large universe. -/
private theorem ulift_sheafComposeNatTrans_app_isIso_iff_whiskered_toSheafify_W
    (P : Dᵒᵖ ⥤ Type t) :
    IsIso
      ((sheafComposeNatTrans K
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))
          (sheafificationAdjunction K (Type t))
          (sheafificationAdjunction K (Type (max t (max u₂ v₂))))).app P) ↔
      K.W
        (Functor.whiskerRight (toSheafify K P)
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))) := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  let adj₁ := sheafificationAdjunction K (Type t)
  let adj₂ := sheafificationAdjunction K Ts
  let η := (sheafComposeNatTrans K F adj₁ adj₂).app P
  have hW :
      K.W (ulift_sheafCompose_comparison_hom (K := K) P) ↔ IsIso η := by
    -- Unfold the named presheaf comparison back to the sheaf morphism component.
    simpa [ulift_sheafCompose_comparison_hom, η] using
      (K.W_sheafToPresheaf_map_iff_isIso η)
  -- Reduce the componentwise isomorphism to a `W`-statement for its underlying presheaf map.
  change IsIso η ↔ K.W (Functor.whiskerRight (toSheafify K P) F)
  rw [← hW, ← ulift_sheafCompose_comparison_hom_fac (K := K) (P := P)]
  -- Precomposition by the large-universe sheafification unit does not change membership in `W`.
  exact
    (((GrothendieckTopology.W (J := K) (A := Ts)).precomp_iff
      (W' := GrothendieckTopology.W (J := K) (A := Ts))
      (toSheafify K (P ⋙ F))
      (ulift_sheafCompose_comparison_hom (K := K) P)
      (K.W_toSheafify (P ⋙ F))).symm)

/-- Helper for Lemma 7.21.6: if the small sheafification unit is already locally injective, then
whiskering it by the relevant `ULift` functor preserves that local injectivity. -/
private theorem whiskered_toSheafify_isLocallyInjective_of
    (P : Dᵒᵖ ⥤ Type t)
    [Presheaf.IsLocallyInjective K (toSheafify K P)] :
    Presheaf.IsLocallyInjective K
      (Functor.whiskerRight (toSheafify K P)
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))) := by
  -- This is exactly the forward `ULift` transport for local injectivity.
  exact isLocallyInjective_whisker_ulift (K := K) (η := toSheafify K P)

/-- Helper for Lemma 7.21.6: if the small sheafification unit is already locally surjective, then
whiskering it by the relevant `ULift` functor preserves that local surjectivity. -/
private theorem whiskered_toSheafify_isLocallySurjective_of
    (P : Dᵒᵖ ⥤ Type t)
    [Presheaf.IsLocallySurjective K (toSheafify K P)] :
    Presheaf.IsLocallySurjective K
      (Functor.whiskerRight (toSheafify K P)
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))) := by
  -- This is exactly the forward `ULift` transport for local surjectivity.
  exact isLocallySurjective_whisker_ulift (K := K) (η := toSheafify K P)

/-- Helper for Lemma 7.21.6: the underlying comparison map for ULift sheafification is locally
surjective. -/
private theorem ulift_sheafCompose_comparison_hom_isLocallySurjective_of_whiskered_toSheafify
    (P : Dᵒᵖ ⥤ Type t)
    [Presheaf.IsLocallySurjective K
      (Functor.whiskerRight (toSheafify K P)
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂))))] :
    Presheaf.IsLocallySurjective K (ulift_sheafCompose_comparison_hom (K := K) P) := by
  -- Then descend along the standard factorization of the comparison map.
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac K
    (ulift_sheafCompose_comparison_hom_fac (K := K) P)

/-- Helper for Lemma 7.21.6: the underlying comparison map for ULift sheafification is locally
injective. -/
private theorem ulift_sheafCompose_comparison_hom_isLocallyInjective_of_whiskered_toSheafify
    (P : Dᵒᵖ ⥤ Type t)
    [Presheaf.IsLocallyInjective K
      (Functor.whiskerRight (toSheafify K P)
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂))))]
    [Presheaf.IsLocallySurjective K
      (toSheafify K
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))))] :
    Presheaf.IsLocallyInjective K (ulift_sheafCompose_comparison_hom (K := K) P) := by
  -- The factorization identifies the comparison as the second map in a composite whose first map
  -- is locally surjective and whose total composite is locally injective.
  exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac K
    (Functor.whiskerRight (toSheafify K P)
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂))))
    (ulift_sheafCompose_comparison_hom_fac (K := K) P)

/-- Helper for Lemma 7.21.6: once ULift is known to preserve sheafification on the site `K`, the
whiskered small sheafification unit is automatically a `W`-morphism. -/
private theorem whiskered_toSheafify_W_of_preservesSheafification
    (P : Dᵒᵖ ⥤ Type t)
    [K.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂)))] :
    K.W
      (Functor.whiskerRight (toSheafify K P)
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))) := by
  let F : Type t ⥤ Type (max t (max u₂ v₂)) :=
    CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  -- The ULift functor preserves sheafification, so it carries the sheafification unit's `W`
  -- property to the whiskered unit.
  exact K.W_of_preservesSheafification F (toSheafify K P) (K.W_toSheafify P)

/-- Helper for Lemma 7.21.6: in the large universe of types used for the ULift comparison, `W`
coincides with local bijectivity because the large-universe sheafification unit is already
locally bijective. -/
private theorem large_type_WEqualsLocallyBijective :
    K.WEqualsLocallyBijective (Type (max t (max u₂ v₂))) := by
  let T := Type (max t (max u₂ v₂))
  let _ : HasWeakSheafify K T := by
    infer_instance
  let _ :
      ∀ P : Dᵒᵖ ⥤ T,
        Presheaf.IsLocallyInjective K (toSheafify K P) := by
    intro P
    let _ : Presheaf.IsLocallyInjective K (K.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallyInjective_type (K := K) (P := P ⋙ forget T)
    -- Rewrite the abstract large-universe unit as the concrete one followed by comparison
    -- isomorphisms that preserve local injectivity.
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify K T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso K (forget T) P).hom) := by
      infer_instance
    infer_instance
  let _ :
      ∀ P : Dᵒᵖ ⥤ T,
        Presheaf.IsLocallySurjective K (toSheafify K P) := by
    intro P
    let _ : Presheaf.IsLocallySurjective K (K.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallySurjective_type (K := K) (P := P ⋙ forget T)
    -- The same large-universe comparison transfers local surjectivity to the abstract unit.
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify K T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso K (forget T) P).hom) := by
      infer_instance
    infer_instance
  exact
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := K) (A := T)

/-- Helper for Lemma 7.21.6: once local bijectivity of the small sheafification unit is known,
its ULift-whiskering is already a `W`-morphism in the large target universe. -/
private theorem whiskered_toSheafify_W_of_small_local_bijectivity
    (P : Dᵒᵖ ⥤ Type t)
    [Presheaf.IsLocallyInjective K (toSheafify K P)]
    [Presheaf.IsLocallySurjective K (toSheafify K P)] :
    K.W
      (Functor.whiskerRight (toSheafify K P)
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))) := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  let _ : K.WEqualsLocallyBijective Ts := large_type_WEqualsLocallyBijective (K := K)
  let _ : Presheaf.IsLocallyInjective K (Functor.whiskerRight (toSheafify K P) F) :=
    whiskered_toSheafify_isLocallyInjective_of (K := K) P
  let _ : Presheaf.IsLocallySurjective K (Functor.whiskerRight (toSheafify K P) F) :=
    whiskered_toSheafify_isLocallySurjective_of (K := K) P
  -- The sheaf-side source route is now reduced to obtaining the small-unit local bijectivity.
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := K) (f := Functor.whiskerRight (toSheafify K P) F))

/-- Helper for Lemma 7.21.6: the whiskered small-universe sheafification unit is already a
`W`-morphism because it identifies with the large-universe sheafification unit. -/
private theorem ulifted_toSheafify_W
    (P : Dᵒᵖ ⥤ Type t) :
    K.W
      (toSheafify K
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))))) := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  let _ : K.WEqualsLocallyBijective Ts := large_type_WEqualsLocallyBijective (K := K)
  -- The large-universe sheafification unit is in `W` once `W` is identified with local
  -- bijectivity in that universe.
  simpa [F] using (K.W_toSheafify (P ⋙ F))

/-- Helper for Lemma 7.21.6: the large-universe sheafification unit obtained from `P` by
whiskering with `ULift` is locally bijective. -/
private theorem ulifted_toSheafify_isLocallyBijective
    (P : Dᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective K
        (toSheafify K
          (P ⋙
            (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
              Type t ⥤ Type (max t (max u₂ v₂))))) ∧
      Presheaf.IsLocallySurjective K
        (toSheafify K
          (P ⋙
            (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
              Type t ⥤ Type (max t (max u₂ v₂))))) := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  let _ : K.WEqualsLocallyBijective Ts := large_type_WEqualsLocallyBijective (K := K)
  -- The already proved large-unit `W`-statement converts immediately into the two local
  -- properties needed for the remaining sheafification comparison.
  exact
    (GrothendieckTopology.W_iff_isLocallyBijective
      (J := K) (f := toSheafify K (P ⋙ F))).1
      (ulifted_toSheafify_W (K := K) (P := P))

/-- Helper for Lemma 7.21.6: the `ULift`-enlarged sheafification unit is locally injective. -/
private theorem ulifted_toSheafify_isLocallyInjective
    (P : Dᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective K
      (toSheafify K
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))))) :=
  (ulifted_toSheafify_isLocallyBijective (K := K) P).1

/-- Helper for Lemma 7.21.6: the `ULift`-enlarged sheafification unit is locally surjective. -/
private theorem ulifted_toSheafify_isLocallySurjective
    (P : Dᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective K
      (toSheafify K
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))))) :=
  (ulifted_toSheafify_isLocallyBijective (K := K) P).2

/-- Helper for Lemma 7.21.6: preserving sheafification for the relevant `ULift` functor is
equivalent to invertibility of the canonical comparison against the concrete `plus-plus`
adjunction. -/
private theorem uliftFunctor_preservesSheafification_type_iff :
    K.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂))) ↔
      IsIso
        (sheafComposeNatTrans K
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))
          (sheafificationAdjunction K (Type t))
          (plusPlusAdjunction K (Type (max t (max u₂ v₂))))) := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  -- Rewrite preservation into the owner comparison for the chosen adjunctions.
  change K.PreservesSheafification F ↔
    IsIso (sheafComposeNatTrans K F
      (sheafificationAdjunction K (Type t))
      (plusPlusAdjunction K Ts))
  rw [GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose
    (J := K) (F := F)
    (adj₁ := sheafificationAdjunction K (Type t))
    (adj₂ := plusPlusAdjunction K Ts)]


/-- Helper for Lemma 7.21.6: the sheaf-level `plus-plus` comparison followed by the large
sheafification comparison is exactly the owner comparison against `plusPlusAdjunction`. -/
private theorem ulift_plusPlus_sheafComposeNatTrans_app
    (P : Dᵒᵖ ⥤ Type t) :
    (((plusPlusSheafIsoPresheafToSheaf K (Type (max t (max u₂ v₂)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))))).hom ≫
      (sheafComposeNatTrans K
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))
        (sheafificationAdjunction K (Type t))
        (sheafificationAdjunction K (Type (max t (max u₂ v₂))))).app P) =
      (sheafComposeNatTrans K
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))
        (sheafificationAdjunction K (Type t))
        (plusPlusAdjunction K (Type (max t (max u₂ v₂))))).app P := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  let α :
      (plusPlusSheaf K Ts).obj (P ⋙ F) ⟶
        (sheafCompose K F).obj ((presheafToSheaf K (Type t)).obj P) :=
    ((plusPlusSheafIsoPresheafToSheaf K Ts).app (P ⋙ F)).hom ≫
      (sheafComposeNatTrans K F
        (sheafificationAdjunction K (Type t))
        (sheafificationAdjunction K Ts)).app P
  apply sheafComposeNatTrans_app_uniq
  -- First rewrite the owner `plus-plus` unit through the comparison to the abstract sheafify
  -- model, then finish with the standard sheafification comparison factorization.
  change
    (plusPlusAdjunction K Ts).unit.app (P ⋙ F) ≫
        (sheafToPresheaf K Ts).map α =
      Functor.whiskerRight ((sheafificationAdjunction K (Type t)).unit.app P) F
  simp only [α, Functor.map_comp, Category.assoc, plusPlusIsoSheafify]
  change
    K.toSheafify (P ⋙ F) ≫
        (sheafToPresheaf K Ts).map ((plusPlusSheafIsoPresheafToSheaf K Ts).app (P ⋙ F)).hom ≫
          (sheafToPresheaf K Ts).map
            ((sheafComposeNatTrans K F
              (sheafificationAdjunction K (Type t))
              (sheafificationAdjunction K Ts)).app P) =
      Functor.whiskerRight ((sheafificationAdjunction K (Type t)).unit.app P) F
  have hplus :
      K.toSheafify (P ⋙ F) ≫
          (sheafToPresheaf K Ts).map ((plusPlusSheafIsoPresheafToSheaf K Ts).app (P ⋙ F)).hom =
        toSheafify K (P ⋙ F) := by
    simpa [plusPlusIsoSheafify] using
      (toSheafify_plusPlusIsoSheafify_hom (J := K) (D := Ts) (P := P ⋙ F))
  have hplus' :
      K.toSheafify (P ⋙ F) ≫
          (sheafToPresheaf K Ts).map ((plusPlusSheafIsoPresheafToSheaf K Ts).app (P ⋙ F)).hom ≫
            (sheafToPresheaf K Ts).map
              ((sheafComposeNatTrans K F
                (sheafificationAdjunction K (Type t))
                (sheafificationAdjunction K Ts)).app P) =
        toSheafify K (P ⋙ F) ≫
          (sheafToPresheaf K Ts).map
            ((sheafComposeNatTrans K F
              (sheafificationAdjunction K (Type t))
              (sheafificationAdjunction K Ts)).app P) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ (sheafToPresheaf K Ts).map
            ((sheafComposeNatTrans K F
              (sheafificationAdjunction K (Type t))
              (sheafificationAdjunction K Ts)).app P))
        hplus
  rw [hplus']
  simpa [Ts, F] using
    sheafComposeNatTrans_fac K F
      (sheafificationAdjunction K (Type t))
      (sheafificationAdjunction K Ts) P

/-- Helper for Lemma 7.21.6: after cancelling the `plusPlusSheafIsoPresheafToSheaf`
comparison on the left, the owner comparison against `plusPlusAdjunction` reduces to the
large sheafification comparison. -/
private theorem ulift_plusPlus_sheafComposeNatTrans_app_cancel_left
    (P : Dᵒᵖ ⥤ Type t) :
    (((plusPlusSheafIsoPresheafToSheaf K (Type (max t (max u₂ v₂)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))))).inv ≫
      (sheafComposeNatTrans K
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))
        (sheafificationAdjunction K (Type t))
        (plusPlusAdjunction K (Type (max t (max u₂ v₂))))).app P) =
      (sheafComposeNatTrans K
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))
        (sheafificationAdjunction K (Type t))
        (sheafificationAdjunction K (Type (max t (max u₂ v₂))))).app P := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  let e := (plusPlusSheafIsoPresheafToSheaf K Ts).app (P ⋙ F)
  have h :=
    ulift_plusPlus_sheafComposeNatTrans_app (K := K) (P := P)
  have h' := congrArg (fun k ↦ e.inv ≫ k) h
  simpa [e, Ts, F, Category.assoc] using h'.symm

/-- Helper for Lemma 7.21.6: after re-expanding the cancelled comparison, the owner comparison
against `plusPlusAdjunction` is the `plusPlusSheafIsoPresheafToSheaf` isomorphism followed by the
large sheafification comparison. -/
private theorem ulift_plusPlus_sheafComposeNatTrans_app_eq_large_comparison
    (P : Dᵒᵖ ⥤ Type t) :
    (sheafComposeNatTrans K
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂)))
      (sheafificationAdjunction K (Type t))
      (plusPlusAdjunction K (Type (max t (max u₂ v₂))))).app P =
      ((plusPlusSheafIsoPresheafToSheaf K (Type (max t (max u₂ v₂)))).app
        (P ⋙
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂))))).hom ≫
        (sheafComposeNatTrans K
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))
          (sheafificationAdjunction K (Type t))
          (sheafificationAdjunction K (Type (max t (max u₂ v₂))))).app P := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  have hcancel :=
    ulift_plusPlus_sheafComposeNatTrans_app_cancel_left (K := K) (P := P)
  have h' := congrArg
    (fun k ↦
      ((plusPlusSheafIsoPresheafToSheaf K Ts).app (P ⋙ F)).hom ≫ k)
    hcancel
  -- Cancel the inverse comparison on the left to recover the owner comparison itself.
  simpa [Ts, F, Category.assoc] using h'

/-- Helper for Lemma 7.21.6: to show the owner comparison against `plusPlusAdjunction` is an
isomorphism, it is enough to show the large sheafification comparison is an isomorphism
componentwise. -/
private theorem ulift_plusPlus_sheafComposeNatTrans_app_isIso_of_large_comparison
    (P : Dᵒᵖ ⥤ Type t)
    [IsIso
      ((sheafComposeNatTrans K
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))
          (sheafificationAdjunction K (Type t))
          (sheafificationAdjunction K (Type (max t (max u₂ v₂))))).app P)] :
    IsIso
      ((sheafComposeNatTrans K
          (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
            Type t ⥤ Type (max t (max u₂ v₂)))
          (sheafificationAdjunction K (Type t))
          (plusPlusAdjunction K (Type (max t (max u₂ v₂))))).app P) := by
  -- The remaining sheaf-side work is to prove the large comparison is invertible at `P`.
  rw [ulift_plusPlus_sheafComposeNatTrans_app_eq_large_comparison (K := K) (P := P)]
  let _ :
      IsIso
        (((plusPlusSheafIsoPresheafToSheaf K (Type (max t (max u₂ v₂)))).app
            (P ⋙
              (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
                Type t ⥤ Type (max t (max u₂ v₂))))).hom) := by
    infer_instance
  let hLarge :
      IsIso
        ((sheafComposeNatTrans K
            (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
              Type t ⥤ Type (max t (max u₂ v₂)))
            (sheafificationAdjunction K (Type t))
            (sheafificationAdjunction K (Type (max t (max u₂ v₂))))).app P) :=
    inferInstance
  exact IsIso.comp_isIso' inferInstance hLarge

/-- Helper for Lemma 7.21.6: whenever the compatible sheafification comparison
`sheafifyCompIso` is available for a functor `F`, membership in `W` transports from the
large-universe sheafification unit to the whiskered small-universe unit. -/
private theorem whiskered_toSheafify_W_of_sheafifyCompIso
    {Ts : Type*} [Category Ts] (F : Type t ⥤ Ts) [HasWeakSheafify K Ts] [K.HasSheafCompose F]
    [∀ (J' : MulticospanShape.{max v₂ u₂, max v₂ u₂}),
      HasLimitsOfShape (WalkingMulticospan J') (Type t)]
    [∀ (J' : MulticospanShape.{max v₂ u₂, max v₂ u₂}),
      HasLimitsOfShape (WalkingMulticospan J') Ts]
    [∀ X : D, HasColimitsOfShape (K.Cover X)ᵒᵖ (Type t)]
    [∀ X : D, HasColimitsOfShape (K.Cover X)ᵒᵖ Ts]
    [∀ X : D, PreservesColimitsOfShape (K.Cover X)ᵒᵖ F]
    [∀ (X : D) (S : K.Cover X) (P' : Dᵒᵖ ⥤ Type t),
      PreservesLimit (S.index P').multicospan F]
    (P : Dᵒᵖ ⥤ Type t) (hP : K.W (K.toSheafify (P ⋙ F))) :
    K.W (Functor.whiskerRight (K.toSheafify P) F) := by
  have hfac :
      K.toSheafify (P ⋙ F) ≫ (K.sheafifyCompIso F P).inv =
        Functor.whiskerRight (K.toSheafify P) F := by
    simpa using K.toSheafify_comp_sheafifyCompIso_inv (F := F) (P := P)
  have hIso :
      MorphismProperty.isomorphisms _ ((K.sheafifyCompIso F P).inv) := by
    infer_instance
  -- Rewrite the whiskered unit as the large sheafification unit followed by the compatible
  -- sheafification comparison isomorphism, then transport `W` across that isomorphism.
  rw [← hfac]
  exact
    (((GrothendieckTopology.W (J := K) (A := Ts)).postcomp_iff
      (W' := MorphismProperty.isomorphisms _)
      (K.toSheafify (P ⋙ F)) ((K.sheafifyCompIso F P).inv) hIso).2 hP)

/-- Helper for Lemma 7.21.6: if the small universe `Type t` had the extra multicospan-limit and
cover-colimit instances needed by `sheafifyCompIso`, then the whiskered concrete `plus-plus`
sheafification unit would already be in `W` by the general transport theorem. -/
private theorem whiskered_concrete_toSheafify_W_of_sheafifyCompIso_ulift
    [∀ (J' : MulticospanShape.{max v₂ u₂, max v₂ u₂}),
      HasLimitsOfShape (WalkingMulticospan J') (Type t)]
    [∀ X : D, HasColimitsOfShape (K.Cover X)ᵒᵖ (Type t)]
    (P : Dᵒᵖ ⥤ Type t) :
    K.W
      (Functor.whiskerRight (K.toSheafify P)
        (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
          Type t ⥤ Type (max t (max u₂ v₂)))) := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  let _ : HasWeakSheafify K Ts := by
    infer_instance
  let _ : K.HasSheafCompose F := by
    infer_instance
  let _ :
      ∀ (J' : MulticospanShape.{max v₂ u₂, max v₂ u₂}),
        HasLimitsOfShape (WalkingMulticospan J') Ts := by
    intro J'
    infer_instance
  let _ : ∀ X : D, HasColimitsOfShape (K.Cover X)ᵒᵖ Ts := by
    intro X
    infer_instance
  let _ : ∀ X : D, PreservesColimitsOfShape (K.Cover X)ᵒᵖ F := by
    intro X
    infer_instance
  let _ :
      ∀ (X : D) (S : K.Cover X) (P' : Dᵒᵖ ⥤ Type t),
        PreservesLimit (S.index P').multicospan F := by
    intro X S P'
    infer_instance
  have hW : K.W (K.toSheafify (P ⋙ F)) := by
    let _ : Presheaf.IsLocallyInjective K (K.toSheafify (P ⋙ F)) :=
      concrete_toSheafify_isLocallyInjective_type (K := K) (P := P ⋙ F)
    let _ : Presheaf.IsLocallySurjective K (K.toSheafify (P ⋙ F)) :=
      concrete_toSheafify_isLocallySurjective_type (K := K) (P := P ⋙ F)
    let _ : K.WEqualsLocallyBijective Ts := large_type_WEqualsLocallyBijective (K := K)
    -- In the large target universe, `W` is exactly local bijectivity, so the concrete unit is in
    -- `W` once its local injectivity and surjectivity are known.
    exact GrothendieckTopology.W_of_isLocallyBijective (J := K) (f := K.toSheafify (P ⋙ F))
  -- Route correction: once the owner-level `sheafifyCompIso` hypotheses are available in the
  -- small universe, the ULift specialization is immediate.
  simpa [F] using
    whiskered_toSheafify_W_of_sheafifyCompIso (K := K) (F := F) P
      hW

/-- Helper for Lemma 7.21.6: if the small universe `Type t` had the extra multicospan-limit and
cover-colimit owners used by the concrete sheafification theorem, then the relevant `ULift`
functor would preserve sheafification by the generic concrete-category criterion. -/
private theorem uliftFunctor_preservesSheafification_type_of_small_owners
    [∀ (J' : MulticospanShape.{max v₂ u₂, max v₂ u₂}),
      HasLimitsOfShape (WalkingMulticospan J') (Type t)]
    [∀ X : D, HasColimitsOfShape (K.Cover X)ᵒᵖ (Type t)] :
    K.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂))) := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts := CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  -- Supply the small-owner hypotheses explicitly so the generic concrete-category theorem applies
  -- without the global instance-search timeout seen in the unconditional goal.
  let _ :
      ∀ (J' : MulticospanShape.{max v₂ u₂, max v₂ u₂}),
        HasLimitsOfShape (WalkingMulticospan J') Ts := by
    intro J'
    infer_instance
  let _ : ∀ X : D, HasColimitsOfShape (K.Cover X)ᵒᵖ Ts := by
    intro X
    infer_instance
  let _ : ∀ X : D, PreservesColimitsOfShape (K.Cover X)ᵒᵖ F := by
    intro X
    infer_instance
  let _ :
      ∀ (X : D) (S : K.Cover X) (P : Dᵒᵖ ⥤ Type t),
        PreservesLimit (S.index P).multicospan F := by
    intro X S P
    infer_instance
  let _ : PreservesLimitsOfSize.{max v₂ u₂, max v₂ u₂} (forget (Type t)) := by
    infer_instance
  let _ : PreservesLimitsOfSize.{max v₂ u₂, max v₂ u₂} (forget Ts) := by
    infer_instance
  let _ : (forget (Type t)).ReflectsIsomorphisms := by
    infer_instance
  let _ : (forget Ts).ReflectsIsomorphisms := by
    infer_instance
  simpa [F] using
    (CategoryTheory.GrothendieckTopology.instPreservesSheafification
      (J := K) (F := F))

/-- Helper for Lemma 7.21.6: the remaining sheafification-preservation blocker is purely
componentwise for the owner comparison against `plusPlusAdjunction`. -/
private theorem uliftFunctor_preservesSheafification_type_iff_isIso_app :
    K.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂))) ↔
      ∀ P : Dᵒᵖ ⥤ Type t,
        IsIso
          ((sheafComposeNatTrans K
              (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
                Type t ⥤ Type (max t (max u₂ v₂)))
              (sheafificationAdjunction K (Type t))
              (plusPlusAdjunction K (Type (max t (max u₂ v₂))))).app P) := by
  rw [uliftFunctor_preservesSheafification_type_iff]
  rw [NatTrans.isIso_iff_isIso_app]

/-- Helper for Lemma 7.21.6: once the small-universe sheafification unit is known to be locally
bijective for every presheaf, `W` agrees with local bijectivity on `Type t`. -/
private theorem small_type_WEqualsLocallyBijective_of_toSheafify_locally_bijective
    [∀ P : Dᵒᵖ ⥤ Type t, Presheaf.IsLocallyInjective K (toSheafify K P)]
    [∀ P : Dᵒᵖ ⥤ Type t, Presheaf.IsLocallySurjective K (toSheafify K P)] :
    K.WEqualsLocallyBijective (Type t) := by
  -- Package the small-universe `toSheafify` local bijectivity into the standard owner theorem
  -- characterizing `W` by local injectivity and surjectivity.
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' (J := K) (A := Type t)

/-- Helper for Lemma 7.21.6: if the concrete `plus-plus` sheafification owners already exist in
`Type t`, then the abstract small sheafification unit is locally injective. -/
private theorem toSheafify_isLocallyInjective_small_type_of_small_owners
    [∀ X : D, Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Dᵒᵖ ⥤ Type t, ∀ X : D, ∀ S : K.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : D, Limits.PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget (Type t))]
    (P : Dᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective K (toSheafify K P) := by
  let T := Type t
  let _ : K.PreservesSheafification (forget T) := by
    exact ⟨fun _ _ _ hf ↦ by simpa using hf⟩
  let _ : Presheaf.IsLocallyInjective K (K.toSheafify (P ⋙ forget T)) :=
    concrete_toSheafify_isLocallyInjective_type (K := K) (P := P ⋙ forget T)
  -- The concrete `plus-plus` model compares to the abstract sheafification unit by isomorphisms,
  -- so local injectivity transports across that comparison.
  rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso ((plusPlusIsoSheafify K T (P ⋙ forget T)).hom) := by
    infer_instance
  let _ : IsIso ((sheafifyComposeIso K (forget T) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.21.6: under the same concrete small-owner hypotheses, the abstract small
sheafification unit is locally surjective. -/
private theorem toSheafify_isLocallySurjective_small_type_of_small_owners
    [∀ X : D, Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ (Type t)]
    [∀ P' : Dᵒᵖ ⥤ Type t, ∀ X : D, ∀ S : K.Cover X, Limits.HasMultiequalizer (S.index P')]
    [∀ X : D, Limits.PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget (Type t))]
    (P : Dᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective K (toSheafify K P) := by
  let T := Type t
  let _ : K.PreservesSheafification (forget T) := by
    exact ⟨fun _ _ _ hf ↦ by simpa using hf⟩
  let _ : Presheaf.IsLocallySurjective K (K.toSheafify (P ⋙ forget T)) :=
    concrete_toSheafify_isLocallySurjective_type (K := K) (P := P ⋙ forget T)
  -- The same concrete comparison transports local surjectivity to the abstract small unit.
  rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  let _ : IsIso ((plusPlusIsoSheafify K T (P ⋙ forget T)).hom) := by
    infer_instance
  let _ : IsIso ((sheafifyComposeIso K (forget T) P).hom) := by
    infer_instance
  infer_instance

/-- Helper for Lemma 7.21.6: once `W` agrees with local bijectivity in both the small and large
type universes, the relevant `ULift` functor preserves sheafification. -/
private theorem uliftFunctor_preservesSheafification_type_of_WEqualsLocallyBijective
    [HasWeakSheafify K (Type (max t (max u₂ v₂)))]
    [K.WEqualsLocallyBijective (Type t)]
    [K.WEqualsLocallyBijective (Type (max t (max u₂ v₂)))] :
    K.PreservesSheafification
      (CategoryTheory.uliftFunctor.{max u₂ v₂, t} :
        Type t ⥤ Type (max t (max u₂ v₂))) := by
  let Ts := Type (max t (max u₂ v₂))
  let F : Type t ⥤ Ts :=
    CategoryTheory.uliftFunctor.{max u₂ v₂, t}
  refine ⟨?_⟩
  intro P Q f hf
  let _ : Presheaf.IsLocallyInjective K f :=
    (K.W_iff_isLocallyBijective f).1 hf |>.1
  let _ : Presheaf.IsLocallySurjective K f :=
    (K.W_iff_isLocallyBijective f).1 hf |>.2
  -- `ULift` leaves the local equalizer and image sieves unchanged, so local bijectivity
  -- transports directly across whiskering.
  let _ : Presheaf.IsLocallyInjective K (Functor.whiskerRight f F) :=
    isLocallyInjective_whisker_ulift (K := K) (η := f)
  let _ : Presheaf.IsLocallySurjective K (Functor.whiskerRight f F) :=
    isLocallySurjective_whisker_ulift (K := K) (η := f)
  simpa [F] using
    (GrothendieckTopology.W_of_isLocallyBijective
      (J := K) (f := Functor.whiskerRight f F))

/-- Helper for Lemma 7.21.6: the abstract sheafification unit is locally surjective.  This
uses only the reflector universal property: the image of the unit sheafifies to the whole
target sheaf. -/
private theorem toSheafify_isLocallySurjective_small_type
    (P : Dᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective K (toSheafify K P) := by
  let η : P ⟶ sheafify K P := toSheafify K P
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  let Rsub : Subfunctor (sheafify K P) := (Subfunctor.range η).sheafify K
  change Rsub = ⊤
  rw [Subfunctor.eq_top_iff_isIso]
  let hS : Presheaf.IsSheaf K (sheafify K P) :=
    ((presheafToSheaf K (Type t)).obj P).property
  have hR : Presheaf.IsSheaf K Rsub.toFunctor := by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact hS
  let r : sheafify K P ⟶ Rsub.toFunctor :=
    sheafifyLift K (Subfunctor.toRangeSheafify K η) hR
  have hfac : Subfunctor.toRangeSheafify K η ≫ Rsub.ι = η := by
    dsimp [Subfunctor.toRangeSheafify, Rsub]
    rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
  have hret : r ≫ Rsub.ι = 𝟙 (sheafify K P) := by
    apply sheafify_hom_ext K
    · exact hS
    · change (toSheafify K P ≫ r) ≫ Rsub.ι =
        toSheafify K P ≫ 𝟙 (sheafify K P)
      dsimp [r]
      rw [toSheafify_sheafifyLift, hfac]
      simp [η]
  refine ⟨r, ?_, hret⟩
  apply (cancel_mono Rsub.ι).1
  simp [Category.assoc, hret]

/-- Helper for Lemma 7.21.6: sheafification preserves finite connected limits by the
left-exactness packaged in `HasSheafify`. -/
theorem presheafToSheaf_preserves_finite_connected_limits
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (presheafToSheaf K (Type t)) := by
  exact
    presheafToSheaf_preserves_finite_connected_limits_of_hasSheafify
      (K := K) (A := Type t) (I := I)

/-- Helper for Lemma 7.21.6: the concrete sheaf pullback construction preserves finite connected
limits by composing the forgetful functor to presheaves, the Kan extension, and sheafification. -/
theorem sheafPullbackConstruction_preserves_finite_connected_limits
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (Functor.sheafPullbackConstruction.sheafPullback u (Type t) J K) := by
  -- Assemble the source proof literally on the concrete model
  -- `sheafToPresheaf ⋙ u.op.lan ⋙ presheafToSheaf`.
  let _ : PreservesLimitsOfShape I (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) :=
    lan_preserves_finite_connected_limits (u := u) (I := I)
  let _ : PreservesLimitsOfShape I (presheafToSheaf K (Type t)) :=
    presheafToSheaf_preserves_finite_connected_limits (K := K) (I := I)
  simpa [Functor.sheafPullbackConstruction.sheafPullback] using
    (inferInstance :
      PreservesLimitsOfShape I
        (sheafToPresheaf J (Type t) ⋙
          (u.op.lan : (Cᵒᵖ ⥤ Type t) ⥤ Dᵒᵖ ⥤ Type t) ⋙ presheafToSheaf K (Type t)))

-- Proof sketch: transport the concrete statement along `sheafPullbackIso`.
/-- Lemma 7.21.6: if `u : C ⥤ D` is continuous, `C` has fibre products and equalizers, and `u`
commutes with them, then the lower shriek `g_!`, realized by
`u.sheafPullback (Type t) J K`, commutes with finite connected limits. -/
theorem sheafPullback_preserves_finite_connected_limits
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (u.sheafPullback (Type t) J K) := by
  -- First prove the statement for the concrete Kan-extension-plus-sheafification model.
  let _ :
      PreservesLimitsOfShape I
        (Functor.sheafPullbackConstruction.sheafPullback u (Type t) J K) :=
    sheafPullbackConstruction_preserves_finite_connected_limits
      (u := u) (J := J) (K := K) (I := I)
  -- Then transport along the canonical comparison isomorphism to the chosen owner
  -- `u.sheafPullback`.
  exact preservesLimitsOfShape_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso u (Type t) J K).symm

-- Proof sketch: specialize the finite-connected-limit statement to the walking cospan.
/-- The canonical lower shriek `u.sheafPullback (Type t) J K` preserves fibre products. -/
theorem sheafPullback_preserves_pullbacks :
    PreservesLimitsOfShape WalkingCospan (u.sheafPullback (Type t) J K) := by
  -- Pullbacks are the `WalkingCospan` case of the finite connected limit statement.
  simpa using sheafPullback_preserves_finite_connected_limits
    (u := u) (J := J) (K := K) WalkingCospan

-- Proof sketch: specialize the finite-connected-limit statement to the walking parallel pair.
/-- The canonical lower shriek `u.sheafPullback (Type t) J K` preserves equalizers. -/
theorem sheafPullback_preserves_equalizers :
    PreservesLimitsOfShape WalkingParallelPair (u.sheafPullback (Type t) J K) := by
  -- Equalizers are the `WalkingParallelPair` case of the finite connected limit statement.
  simpa using sheafPullback_preserves_finite_connected_limits
    (u := u) (J := J) (K := K) WalkingParallelPair

end

end
