module

public import stacks_project.Chap07.Lemma_7_26_4.PullbackRestriction

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: after normalizing the direct pullback cover over
`((Over.map I.f).obj T)`, the direct source-compatible-family subtype is exactly the already
constructed iterated/source-compatible-family subtype. This is the objectwise bridge Agent C
requested before the glued presheaf is packaged into a natural isomorphism. -/
noncomputable def localized_cover_descent_glue_restrict_obj_equiv_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_direct_source_over
      (J := J) (U := U) 𝒰 D I T ≃
      localized_cover_descent_glue_component_source_over
        (J := J) (U := U) 𝒰 D I T where
  toFun s :=
    ⟨localized_cover_descent_glue_direct_family_equiv
      (J := J) (U := U) 𝒰 D I T s.1, s.2⟩
  invFun t :=
    ⟨(localized_cover_descent_glue_direct_family_equiv
      (J := J) (U := U) 𝒰 D I T).symm t.1, by
        -- The direct compatibility predicate is defined by transporting to the component side, so
        -- the inverse family inherits compatibility from `t` verbatim.
        have ht :
            localized_cover_descent_glue_direct_family_equiv
                (J := J) (U := U) 𝒰 D I T
                ((localized_cover_descent_glue_direct_family_equiv
                  (J := J) (U := U) 𝒰 D I T).symm t.1) = t.1 :=
          (localized_cover_descent_glue_direct_family_equiv
            (J := J) (U := U) 𝒰 D I T).right_inv t.1
        exact (congrArg (Presieve.Arrows.Compatible _ _) ht).mpr t.2⟩
  left_inv s := by
    -- The subtype equality reduces to the pointwise inverse for the direct-family equivalence.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_glue_direct_family_equiv
        (J := J) (U := U) 𝒰 D I T).left_inv s.1) K
  right_inv t := by
    -- The transported direct compatible family on the component side is recovered verbatim.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_glue_direct_family_equiv
        (J := J) (U := U) 𝒰 D I T).right_inv t.1) K

/-- Helper for Lemma 7.26.4: these are the source-side terminal sections on the iterated pullback
cover over `I` and then `T`. They are the arbitrary-`T` precursor to the future glued presheaf
value restricted to `I`. -/
abbrev localized_cover_descent_pullback_over_family
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :=
  ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
    (((localized_cover_descent_pullbackDatum_over_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))

/-- Helper for Lemma 7.26.4: the source-compatible-family condition on terminal sections of the
iterated pullback datum over `I` and `T` is defined by transporting each section to the ordinary
pulled-back component sheaf. This keeps the remaining arbitrary-`T` compatibility check at the
stable sheaf level from Agent C's plan. -/
def localized_cover_descent_pullback_over_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_pullback_over_family (J := J) (U := U) 𝒰 D I T) : Prop :=
  Presieve.Arrows.Compatible
    (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
    (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
      (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f))
    (fun K ↦
      localized_cover_descent_pullbackDatum_over_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K (s K))

/-- Helper for Lemma 7.26.4: the pointwise arbitrary-`T` section comparison upgrades to an
equivalence of the underlying families on the iterated pullback cover over `I` and then `T`. -/
noncomputable def localized_cover_descent_pullback_over_family_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_pullback_over_family (J := J) (U := U) 𝒰 D I T ≃
      (∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
        ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
          (Opposite.op (Over.mk K.f)))) where
  toFun s K :=
    localized_cover_descent_pullbackDatum_over_section_equiv_component
      (J := J) (U := U) 𝒰 D I T K (s K)
  invFun t K :=
    (localized_cover_descent_pullbackDatum_over_section_equiv_component
      (J := J) (U := U) 𝒰 D I T K).symm (t K)
  left_inv s := by
    -- Each arbitrary-`T` component is inverted by the corresponding section-level equivalence.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_over_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K).left_inv (s K)
  right_inv t := by
    -- The same pointwise inverse shows that the transported arbitrary-`T` family is unchanged.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_over_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K).right_inv (t K)

/-- Helper for Lemma 7.26.4: after rewriting each arbitrary-`T` component section by the
iterated-pullback comparison, the source-side subtype of compatible families is exactly the
standard subtype of compatible sections of the pulled-back component sheaf. This is the stable
arbitrary-`T` bridge that remains after the earlier transport block. -/
noncomputable def localized_cover_descent_pullback_over_compatible_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    { s : localized_cover_descent_pullback_over_family (J := J) (U := U) 𝒰 D I T //
        localized_cover_descent_pullback_over_compatible
          (J := J) (U := U) 𝒰 D I T s } ≃
      localized_cover_descent_glue_component_source_over
        (J := J) (U := U) 𝒰 D I T where
  toFun s :=
    ⟨localized_cover_descent_pullback_over_family_equiv
      (J := J) (U := U) 𝒰 D I T s.1, s.2⟩
  invFun t :=
    ⟨(localized_cover_descent_pullback_over_family_equiv
      (J := J) (U := U) 𝒰 D I T).symm t.1, by
        -- The source-side compatibility predicate is defined by transporting to the component
        -- side, so the inverse family inherits compatibility from `t` verbatim.
        have ht :
            localized_cover_descent_pullback_over_family_equiv
                (J := J) (U := U) 𝒰 D I T
                ((localized_cover_descent_pullback_over_family_equiv
                  (J := J) (U := U) 𝒰 D I T).symm t.1) = t.1 :=
          (localized_cover_descent_pullback_over_family_equiv
            (J := J) (U := U) 𝒰 D I T).right_inv t.1
        exact (congrArg (Presieve.Arrows.Compatible _ _) ht).mpr t.2⟩
  left_inv s := by
    -- The subtype equality reduces to the pointwise inverse for the arbitrary-`T` family
    -- equivalence.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_pullback_over_family_equiv
        (J := J) (U := U) 𝒰 D I T).left_inv s.1) K
  right_inv t := by
    -- The transported arbitrary-`T` compatible family on the component side is recovered
    -- verbatim.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_pullback_over_family_equiv
        (J := J) (U := U) 𝒰 D I T).right_inv t.1) K

/-- Helper for Lemma 7.26.4: this is the source-proof family
`V/U ↦ ∏ₖ Fₖ(K ×ᵤ V)` before imposing the overlap equations. Each component is a section of the
pulled-back descent datum over the terminal object of the localized slice above `K.Y`. -/
abbrev localized_cover_descent_glue_family
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U) :=
  ∀ K : (𝒰.pullback V.hom).Arrow,
    (((localized_cover_descent_pullbackDatum
      (J := J) (U := U) 𝒰 D V).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))

/-- Helper for Lemma 7.26.4: this is the textbook overlap condition for a family of local sections
over the pullback cover of `V/U`. We first restrict both sections to the overlap object `R.r.Z`,
then compare them using the descent transition map of the pulled-back datum. -/
def localized_cover_descent_glue_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D V) : Prop :=
  let P := localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V
  ∀ R : (𝒰.pullback V.hom).Relation,
    (P.hom (R.r.g₁ ≫ R.fst.f) R.r.g₁ R.r.g₂ rfl R.r.w.symm).hom.app
        (Opposite.op (Over.mk (𝟙 R.r.Z)))
        (cast
          (localized_cover_descent_pullbackDatum_section_eq
            (J := J) (U := U) 𝒰 D V R.fst R.r.g₁).symm
          (((P.obj R.fst).1.map (Over.homMk R.r.g₁).op) (s R.fst))) =
      cast
        (localized_cover_descent_pullbackDatum_section_eq
          (J := J) (U := U) 𝒰 D V R.snd R.r.g₂).symm
        (((P.obj R.snd).1.map (Over.homMk R.r.g₂).op) (s R.snd))

/-- Helper for Lemma 7.26.4: this packages the source-proof compatible family on the pullback
cover of `V/U`. The remaining presheaf step is to show that reindexing along `g : V ⟶ W`
preserves this predicate. -/
abbrev localized_cover_descent_glue_value
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U) :=
  { s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D V //
      localized_cover_descent_glue_compatible
        (J := J) (U := U) 𝒰 D V s }

/-- Helper for Lemma 7.26.4: if the site-sized indexing types are `w`-small, then the
source-style glued compatible-family value over `V/U` is also `w`-small. This is the precise
resizing bridge needed to regard the textbook compatible-family construction as a
`Type w`-valued presheaf. -/
theorem localized_cover_descent_glue_value_small
    [UnivLE.{max u v, w}]
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (V : Over U) :
    Small.{w} (localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V) := by
  infer_instance

/-- Helper for Lemma 7.26.4: when `V = Uᵢ/U`, the underlying family in
`localized_cover_descent_glue_value` is literally the terminal-section family used by the fixed
component comparison over `I`. This identifies the main controlled source object without yet
repackaging its compatibility predicate. -/
theorem localized_cover_descent_glue_family_over_arrow
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D (Over.mk I.f) =
      (∀ K : (𝒰.pullback I.f).Arrow,
        (((localized_cover_descent_pullbackDatum
          (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K).1.obj
            (Opposite.op (Over.mk (𝟙 K.Y))))) := rfl

/-- Helper for Lemma 7.26.4: the textbook family of terminal sections for the pullback datum over
`I` is identified pointwise with the family of sections of the fixed component sheaf `D.obj I`
over the overlap objects `Over.mk K.f`. -/
abbrev localized_cover_descent_pullback_terminal_family
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :=
  ∀ K : (𝒰.pullback I.f).Arrow,
    (((localized_cover_descent_pullbackDatum
      (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))

/-- Helper for Lemma 7.26.4: this is the fixed-component family on the pullback cover over `I`
that the textbook compatible-family formula should recover after reindexing. -/
abbrev localized_cover_descent_component_terminal_family
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :=
  ∀ K : (𝒰.pullback I.f).Arrow,
    ((D.obj I).1.obj (Opposite.op (Over.mk K.f)))

/-- Helper for Lemma 7.26.4: the pullback-cover arrows over a chosen member `I` are the induced
arrows into the terminal object `I.Y / I.Y` of the localized site. -/
abbrev localized_cover_descent_component_terminal_arrow
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    Over.mk K.f ⟶ Over.mk (𝟙 I.Y) :=
  Over.homMk K.f

/-- Helper for Lemma 7.26.4: the source-compatible-family condition on terminal sections of the
pullback datum over `I` is just the ordinary compatibility condition after translating each
component section to the fixed sheaf `D.obj I`. -/
def localized_cover_descent_pullback_terminal_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (s : localized_cover_descent_pullback_terminal_family (J := J) (U := U) 𝒰 D I) : Prop :=
  Presieve.Arrows.Compatible ((D.obj I).1)
    (fun K : (𝒰.pullback I.f).Arrow ↦
      localized_cover_descent_component_terminal_arrow (J := J) (U := U) 𝒰 I K)
    (fun K ↦
      localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K (s K))

/-- Helper for Lemma 7.26.4: the pointwise section comparison over a chosen cover member `I`
upgrades to an equivalence of the underlying families indexed by `𝒰.pullback I.f`. -/
noncomputable def localized_cover_descent_pullback_component_family_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_pullback_terminal_family (J := J) (U := U) 𝒰 D I ≃
      localized_cover_descent_component_terminal_family (J := J) (U := U) 𝒰 D I where
  toFun s K :=
    localized_cover_descent_pullbackDatum_section_equiv_component
      (J := J) (U := U) 𝒰 D I K (s K)
  invFun t K :=
    (localized_cover_descent_pullbackDatum_section_equiv_component
      (J := J) (U := U) 𝒰 D I K).symm (t K)
  left_inv s := by
    -- Each component is inverted by the corresponding section-level equivalence.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K).left_inv (s K)
  right_inv t := by
    -- The same pointwise inverse shows that the transported component family is unchanged.
    funext K
    exact
      (localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K).right_inv (t K)

/-- Helper for Lemma 7.26.4: after rewriting each component section by the pullback-datum
comparison, compatible families on the source side and on the fixed component side are the same
subtype. This isolates the terminal-object comparison already proved in the file. -/
noncomputable def localized_cover_descent_pullback_terminal_compatible_equiv
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    { s : localized_cover_descent_pullback_terminal_family (J := J) (U := U) 𝒰 D I //
        localized_cover_descent_pullback_terminal_compatible
          (J := J) (U := U) 𝒰 D I s } ≃
      { t : localized_cover_descent_component_terminal_family (J := J) (U := U) 𝒰 D I //
          Presieve.Arrows.Compatible ((D.obj I).1)
            (fun K : (𝒰.pullback I.f).Arrow ↦
              localized_cover_descent_component_terminal_arrow (J := J) (U := U) 𝒰 I K)
            t } where
  toFun s :=
    ⟨localized_cover_descent_pullback_component_family_equiv
      (J := J) (U := U) 𝒰 D I s.1, s.2⟩
  invFun t :=
    ⟨(localized_cover_descent_pullback_component_family_equiv
      (J := J) (U := U) 𝒰 D I).symm t.1, by
        -- The left-hand compatibility predicate is defined by transporting to the component side.
        have ht :
            localized_cover_descent_pullback_component_family_equiv
                (J := J) (U := U) 𝒰 D I
                ((localized_cover_descent_pullback_component_family_equiv
                  (J := J) (U := U) 𝒰 D I).symm t.1) = t.1 :=
          (localized_cover_descent_pullback_component_family_equiv
            (J := J) (U := U) 𝒰 D I).right_inv t.1
        simpa [localized_cover_descent_pullback_terminal_compatible,
          localized_cover_descent_pullback_component_family_equiv, ht] using t.2⟩
  left_inv s := by
    -- The subtype equality reduces to the pointwise inverse for the family equivalence.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_pullback_component_family_equiv
        (J := J) (U := U) 𝒰 D I).left_inv s.1) K
  right_inv t := by
    -- The transported compatible family on the fixed component side is recovered verbatim.
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_pullback_component_family_equiv
        (J := J) (U := U) 𝒰 D I).right_inv t.1) K

/-- Helper for Lemma 7.26.4: on a source-compatible family over the pullback cover above `I`,
the forward subtype equivalence simply applies the pointwise section comparison on each component.
This is the explicit component formula needed when the future glued presheaf is restricted to `I`.
-/
theorem localized_cover_descent_pullback_terminal_compatible_equiv_apply_val
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (s :
      { s : localized_cover_descent_pullback_terminal_family (J := J) (U := U) 𝒰 D I //
          localized_cover_descent_pullback_terminal_compatible
            (J := J) (U := U) 𝒰 D I s })
    (K : (𝒰.pullback I.f).Arrow) :
    ((localized_cover_descent_pullback_terminal_compatible_equiv
      (J := J) (U := U) 𝒰 D I s).1 K) =
      localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K (s.1 K) := by
  -- The forward subtype equivalence is defined by the pointwise family equivalence.
  rfl

/-- Helper for Lemma 7.26.4: on a compatible family of sections of the fixed component sheaf
`D.obj I`, the inverse subtype equivalence simply applies the inverse pointwise section
comparison on each overlap component. This is the explicit reconstruction formula for the source
family that the future glued presheaf will use.
-/
theorem localized_cover_descent_pullback_terminal_compatible_equiv_symm_val
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (t :
      { t : localized_cover_descent_component_terminal_family (J := J) (U := U) 𝒰 D I //
          Presieve.Arrows.Compatible ((D.obj I).1)
            (fun K : (𝒰.pullback I.f).Arrow ↦
              localized_cover_descent_component_terminal_arrow (J := J) (U := U) 𝒰 I K)
            t })
    (K : (𝒰.pullback I.f).Arrow) :
    (((localized_cover_descent_pullback_terminal_compatible_equiv
      (J := J) (U := U) 𝒰 D I).symm t).1 K) =
      (localized_cover_descent_pullbackDatum_section_equiv_component
        (J := J) (U := U) 𝒰 D I K).symm (t.1 K) := by
  -- The inverse subtype equivalence is defined by the inverse pointwise family equivalence.
  rfl

/-- Helper for Lemma 7.26.4: the ordinary Hom sheaf on `J.over U` is a sheaf for the induced
terminal cover coming from `𝒰`. This isolates the slice-site input needed by the fixed-cover
fully-faithfulness route. -/
theorem localized_cover_descent_sheafHom_isSheafFor_terminal_cover
    (𝒰 : J.Cover U)
    (M N : Sheaf (J.over U) (Type w)) :
    Presieve.IsSheafFor
      ((CategoryTheory.sheafHom (J := J.over U) M N).1)
      ((localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰 : (J.over U).Cover
        (Over.mk (𝟙 U))).1.arrows) := by
  -- The ordinary internal Hom on the slice site is already a sheaf, so it satisfies the sheaf
  -- condition for every covering sieve in `J.over U`, in particular for the induced terminal cover.
  exact Presheaf.IsSheaf.isSheafFor
    ((CategoryTheory.sheafHom (J := J.over U) M N).2)
    (localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰).1
    (localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰).condition

/- Helper for Lemma 7.26.4: restricting a global section of the ordinary slice-site Hom sheaf
along a terminal-cover arrow matches the corresponding component of the owner-side descent datum
map after transporting through the canonical objectwise Hom equivalences. -/
/-
theorem localized_cover_descent_terminal_component_restrict_eq
    (𝒰 : J.Cover U)
    {M N : Sheaf (J.over U) (Type w)}
    (ψ : M ⟶ N)
    (I : (localized_cover_descent_terminal_cover (J := J) (U := U) 𝒰).Arrow) :
    localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U) I.Y M N
      (((CategoryTheory.sheafHom (J := J.over U) M N).1).map I.f.op
        ((localized_pseudofunctorOver_presheafHom_base_equiv
          (J := J) (U := U) M N).symm ψ)) =
      (((J.pseudofunctorOver (Type w)).presheafHom M N).map I.f.op
        (localized_pseudofunctorOver_presheafHom_obj_equiv (J := J) (U := U)
          (Over.mk (𝟙 U)) M N
          ((localized_pseudofunctorOver_presheafHom_base_equiv
            (J := J) (U := U) M N).symm ψ))) := by
  -- The fixed-cover restriction identity is the terminal-object specialization of the presheaf
  -- comparison naturality, after normalizing the base section on the owner side.
  simpa [localized_pseudofunctorOver_presheafHom_base_equiv_apply
    (J := J) (U := U) (ψ := ψ)] using
    congrFun
      ((localized_pseudofunctorOver_presheafHom_iso
        (J := J) (U := U) M N).hom.naturality I.f.op)
      ((localized_pseudofunctorOver_presheafHom_base_equiv
        (J := J) (U := U) M N).symm ψ)
-/

-- Before comparing with the owner-side `pullHom`, first expose the ordinary `sheafHom`
-- restriction map in its concrete localized-pullback form.
/-- Helper for Lemma 7.26.4: descent for morphisms on the fixed cover `𝒰` is already covered by
the slice-site Hom-sheaf theorem from Lemma `7.26.1`, so the associated descent-data functor is
fully faithful without using any object-level gluing. -/
noncomputable def localized_cover_descent_fullyFaithful
    (𝒰 : J.Cover U) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).FullyFaithful := by
  -- The owner-side Hom presheaf is definitionally the ordinary slice-site Hom sheaf, so the
  -- generic morphism-descent criterion only needs the terminal-cover sheaf condition.
  exact ((Functor.FullyFaithful.nonempty_iff_map_bijective
    (F := (J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f))).2 (fun M N ↦ by
        -- The generic descent criterion reduces bijectivity to the sheaf condition for the
        -- owner-side Hom presheaf on the induced terminal cover of `U/U`. Transport the sheaf
        -- condition across the Hom-presheaf comparison before invoking the slice-site result.
        rw [Pseudofunctor.bijective_toDescentData_map_iff]
        let R :
            Presieve (Over.mk (𝟙 U)) :=
          Presieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
            (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)
        have hsheaf_generate :
            Presieve.IsSheafFor
              ((CategoryTheory.sheafHom (J := J.over U) M N).1)
              (Sieve.generate R).arrows := by
          simpa [R, localized_cover_descent_terminal_cover, Sieve.ofArrows] using
            localized_cover_descent_sheafHom_isSheafFor_terminal_cover
              (J := J) (U := U) 𝒰 M N
        have hsheaf :
            Presieve.IsSheafFor
              ((CategoryTheory.sheafHom (J := J.over U) M N).1) R :=
          (Presieve.isSheafFor_iff_generate R).2 hsheaf_generate
        exact
          (Presieve.isSheafFor_iff_of_iso
            (localized_pseudofunctorOver_presheafHom_iso
              (J := J) (U := U) M N)).1
            hsheaf)).some

/-- Helper for Lemma 7.26.4: morphism descent on the fixed cover `𝒰` is already settled by the
fully faithful descent-data functor, so the remaining work in this file is purely object-level
gluing. -/
theorem localized_cover_descent_isPrestackFor
    (𝒰 : J.Cover U) :
    (J.pseudofunctorOver (Type w)).IsPrestackFor
      (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f)) := by
  -- Package the fully faithful descent-data functor as the owner-side prestack statement.
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff]
  exact ⟨localized_cover_descent_fullyFaithful (J := J) (U := U) 𝒰⟩

/-- Helper for Lemma 7.26.4: once the future glued presheaf is restricted to a fixed cover member
`I`, its objectwise comparison with the given component sheaf is exactly the composite of the
direct-source normalization and the already-proved component gluing equivalence. -/
noncomputable def localized_cover_descent_glue_component_obj_equiv_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_direct_source_over
      (J := J) (U := U) 𝒰 D I T ≃
      ((D.obj I).1.obj (Opposite.op T)) :=
  -- First rewrite the restricted glued value into the stable component-side subtype, then glue
  -- that compatible family inside the sheaf `D.obj I`.
  (localized_cover_descent_glue_restrict_obj_equiv_over
    (J := J) (U := U) 𝒰 D I T).trans
    (localized_cover_descent_glue_component_equiv_over
      (J := J) (U := U) 𝒰 D I T)

/-- Helper for Lemma 7.26.4: applying the new objectwise comparison after the direct-source
normalization is definitionally the same composite that will later become the component of the
restriction `NatIso`. -/
theorem localized_cover_descent_glue_component_obj_equiv_over_apply
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s :
      localized_cover_descent_glue_direct_source_over
        (J := J) (U := U) 𝒰 D I T) :
    localized_cover_descent_glue_component_obj_equiv_over
        (J := J) (U := U) 𝒰 D I T s =
      localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T
        (localized_cover_descent_glue_restrict_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T s) := by
  -- The objectwise comparison is defined as this composite equivalence.
  rfl

/-- Helper for Lemma 7.26.4: the objectwise comparison over `T` is a genuine equivalence, so
transporting a section of `D.obj I` back to the direct-source compatible family and then forward
again recovers the original section. -/
theorem localized_cover_descent_glue_component_obj_equiv_over_apply_symm
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : (D.obj I).1.obj (Opposite.op T)) :
    localized_cover_descent_glue_component_obj_equiv_over
        (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_component_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T).symm t) =
      t := by
  -- This is the right-inverse identity for the explicit composite equivalence above.
  exact Equiv.apply_symm_apply
    (localized_cover_descent_glue_component_obj_equiv_over
      (J := J) (U := U) 𝒰 D I T)
    t

/-- Helper for Lemma 7.26.4: after moving a section of `D.obj I` back through the objectwise
comparison, applying the direct-source normalization alone recovers exactly the inverse of the
component-side gluing equivalence. This isolates the normalization half of the future naturality
square. -/
theorem localized_cover_descent_glue_component_obj_equiv_over_symm_restrict
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : (D.obj I).1.obj (Opposite.op T)) :
    localized_cover_descent_glue_restrict_obj_equiv_over
        (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_component_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T).symm t) =
      (localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T).symm t := by
  -- Compare both candidates after applying the component-side gluing equivalence; this avoids
  -- reopening the transport-heavy definition of the composite objectwise equivalence.
  apply
    (localized_cover_descent_glue_component_equiv_over
      (J := J) (U := U) 𝒰 D I T).injective
  calc
    localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T
        (localized_cover_descent_glue_restrict_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T
          ((localized_cover_descent_glue_component_obj_equiv_over
            (J := J) (U := U) 𝒰 D I T).symm t)) =
      localized_cover_descent_glue_component_obj_equiv_over
        (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_component_obj_equiv_over
          (J := J) (U := U) 𝒰 D I T).symm t) := by
        rfl
    _ = t := localized_cover_descent_glue_component_obj_equiv_over_apply_symm
      (J := J) (U := U) 𝒰 D I T t
    _ =
      localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_component_equiv_over
          (J := J) (U := U) 𝒰 D I T).symm t) := by
        symm
        exact Equiv.apply_symm_apply
          (localized_cover_descent_glue_component_equiv_over
            (J := J) (U := U) 𝒰 D I T)
          t

end

end GrothendieckTopology
end CategoryTheory
