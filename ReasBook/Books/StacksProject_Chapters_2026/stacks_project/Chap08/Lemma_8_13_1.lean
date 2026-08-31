module

public import stacks_project.Chap04.Example_4_38_7
public import stacks_project.Chap08.Lemma_8_4_4
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

namespace RepresentablePresheaf

scoped notation:max "h[" U "]" => yoneda.obj U

end RepresentablePresheaf

open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

section OverDescent

/-- Helper for Lemma 8.13.1: an object of the fiber of the slice projection `Over.forget U` over
`V` is canonically determined by its underlying arrow `V ⟶ U`. -/
private def over_fiber_to_hom (U V : C) :
    ((Over.forget U).Fiber V) → (V ⟶ U) :=
  fun a ↦ eqToHom a.2.symm ≫ a.1.hom

/-- Helper for Lemma 8.13.1: the fiber of `Over.forget U` over `V` is in bijection with
the hom-set `V ⟶ U`. -/
private theorem over_fiber_to_hom_bijective (U V : C) :
    Function.Bijective (over_fiber_to_hom U V) := by
  constructor
  · intro a b h
    cases a with
    | mk a ha =>
        cases b with
        | mk b hb =>
            dsimp [over_fiber_to_hom] at h ⊢
            cases a with
            | mk la ra ha' =>
                cases b with
                | mk lb rb hb' =>
                    cases ha
                    cases hb
                    cases ra
                    cases rb
                    have h' : ha' = hb' := by
                      simpa [Over.forget_obj] using h
                    subst h'
                    rfl
  · intro f
    refine ⟨⟨Over.mk f, rfl⟩, ?_⟩
    simp [over_fiber_to_hom]

/-- Helper for Lemma 8.13.1: equality of the underlying arrows to `U` identifies fiber objects in
the slice projection. -/
private theorem over_fiber_eq_of_hom_eq
    {U V : C} {a b : (Over.forget U).Fiber V}
    (h : over_fiber_to_hom U V a = over_fiber_to_hom U V b) :
    a = b :=
  (over_fiber_to_hom_bijective U V).1 h

/-- Helper for Lemma 8.13.1: the fiber object built from `f : V ⟶ U` has underlying arrow `f`
when viewed through `over_fiber_to_hom`. -/
private theorem over_fiber_to_hom_fiber_mk_over_mk
    {U V : C} (f : V ⟶ U) :
    over_fiber_to_hom U V (Functor.Fiber.mk (a := Over.mk f) rfl) = f := by
  change eqToHom rfl.symm ≫ (Over.mk f).hom = f
  simp

/-- Helper for Lemma 8.13.1: any morphism in a slice fiber preserves the underlying arrow to
the terminal object `U`. -/
private theorem over_fiber_to_hom_eq_of_hom
    {U V : C} {a b : (Over.forget U).Fiber V} (h : a ⟶ b) :
    over_fiber_to_hom U V a = over_fiber_to_hom U V b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with ⟨la, ra, fa⟩
  rcases b with ⟨lb, rb, fb⟩
  dsimp at ha hb
  cases ha
  cases hb
  simp [over_fiber_to_hom]
  have hw : (Functor.Fiber.fiberInclusion.map h).left ≫ fb = fa := by
    simpa using Over.w (Functor.Fiber.fiberInclusion.map h)
  have hleft : (Functor.Fiber.fiberInclusion.map h).left = 𝟙 V := by
    simpa using
      (@IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
        (Functor.Fiber.fiberInclusion.map h) h.2)
  rw [hleft] at hw
  simpa using (show fa = 𝟙 V ≫ fb from hw.symm)

/-- Helper for Lemma 8.13.1: every hom-set in a fiber of the slice projection `Over.forget U`
is a subsingleton. -/
private theorem over_fiber_hom_subsingleton
    {U V : C} (a b : (Over.forget U).Fiber V) :
    Subsingleton (a ⟶ b) := by
  refine ⟨fun φ ψ ↦ ?_⟩
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  have hφ := @IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
    (Functor.Fiber.fiberInclusion.map φ) φ.2
  have hψ := @IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
    (Functor.Fiber.fiberInclusion.map ψ) ψ.2
  simpa using hφ.trans hψ.symm

/-- Helper for Lemma 8.13.1: a lift in the slice projection over `f : Y ⟶ Z` records that the
underlying map to `U` on the source is `f` followed by the underlying map on the target. -/
private theorem over_fiber_to_hom_eq_comp_of_isHomLift
    {U Y Z : C} {a : (Over.forget U).Fiber Y} {b : (Over.forget U).Fiber Z}
    {f : Y ⟶ Z} {h : a.1 ⟶ b.1} (hh : Functor.IsHomLift (Over.forget U) f h) :
    over_fiber_to_hom U Y a = f ≫ over_fiber_to_hom U Z b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with ⟨la, ra, fa⟩
  rcases b with ⟨lb, rb, fb⟩
  dsimp at ha hb
  cases ha
  cases hb
  have hfac : (Over.forget U).map h = f := by
    simpa using (@IsHomLift.fac' _ _ _ _ (Over.forget U) Y Z _ _ f h hh)
  have hw : h.left ≫ fb = fa := by
    simpa using Over.w h
  have hw' : fa = f ≫ fb := by
    rw [← hfac]
    simpa using hw.symm
  simpa [over_fiber_to_hom] using hw'

/-- Helper for Lemma 8.13.1: the chosen pullback object in the slice fiber over `Y` represents
precomposition of the underlying arrow to `U` by `f : Y ⟶ Z`. -/
private theorem over_pseudofunctor_map_obj_hom_eq_comp
    {U Y Z : C} (f : Y ⟶ Z) (a : (Over.forget U).Fiber Z) :
    over_fiber_to_hom U Y
        (((canonicalFiberPseudofunctor (Over.forget U)).map f.op.toLoc).toFunctor.obj a) =
      f ≫ over_fiber_to_hom U Z a := by
  let hc := canonicalPullbackChoice (Over.forget U)
  let φ := hc.map f a
  simpa using
    (over_fiber_to_hom_eq_comp_of_isHomLift
      (U := U) (a := ((hc.pullbackFunctor f).obj a)) (b := a) (f := f) (h := φ)
      ((hc.isStronglyCartesian f a).toIsHomLift))

/-- Helper for Lemma 8.13.1: for a functor between discrete categories, equivalence is exactly
bijectivity on objects. -/
private theorem isEquivalence_iff_bijective_obj_of_isDiscrete
    {A B : Type*} [Category A] [Category B] [IsDiscrete A] [IsDiscrete B]
    (G : A ⥤ B) :
    G.IsEquivalence ↔ Function.Bijective G.obj := by
  constructor
  · intro h
    let _ : G.IsEquivalence := h
    refine ⟨?_, ?_⟩
    · intro X Y hXY
      exact obj_ext_of_isDiscrete (G.preimage (eqToHom hXY))
    · intro Y
      rcases Functor.EssSurj.mem_essImage (F := G) Y with ⟨X, ⟨e⟩⟩
      exact ⟨X, obj_ext_of_isDiscrete e.hom⟩
  · intro hG
    let faithfulG : G.Faithful := ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
    let fullG : G.Full := ⟨fun {X Y} f ↦
      ⟨eqToHom (hG.1 (obj_ext_of_isDiscrete f)), Subsingleton.elim _ _⟩⟩
    let essSurjG : G.EssSurj := Functor.essSurj_of_surj hG.2
    exact { faithful := faithfulG, full := fullG, essSurj := essSurjG }

/-- Helper for Lemma 8.13.1: for a cover `S` of `V`, the canonical descent functor for the slice
projection `Over.forget U` is an equivalence exactly when the representable presheaf `h[U]`
satisfies the sheaf condition for the covering sieve of `S`. -/
private theorem over_cover_toDescentData_isEquivalence_iff_isSheafFor
    (J : GrothendieckTopology C) (U V : C) (S : J.Cover V) :
    ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
      (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
      Presieve.IsSheafFor (yoneda.obj U) ((S : Sieve V).arrows) := by
  let DD :=
    (canonicalFiberPseudofunctor (Over.forget U)).DescentData
      (fun I : S.Arrow ↦ I.f)
  let compat :=
    Subtype (Presieve.Arrows.Compatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
  let compatOfDescent : DD → compat := fun D ↦
    ⟨fun I ↦ over_fiber_to_hom U I.Y (D.obj I), by
      intro I₁ I₂ Y g₁ g₂ h
      let q : Y ⟶ V := g₁ ≫ I₁.f
      have hg₁ : g₁ ≫ I₁.f = q := rfl
      have hg₂ : g₂ ≫ I₂.f = q := by
        simpa [q] using h.symm
      have hEq :
          over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₁.op.toLoc).toFunctor.obj
                (D.obj I₁)) =
            over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₂.op.toLoc).toFunctor.obj
                (D.obj I₂)) := by
        exact over_fiber_to_hom_eq_of_hom (D.hom q g₁ g₂ hg₁ hg₂)
      have hg₁' :
          (yoneda.obj U).map g₁.op (over_fiber_to_hom U I₁.Y (D.obj I₁)) =
            over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₁.op.toLoc).toFunctor.obj
                (D.obj I₁)) := by
        simpa using
          (over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := g₁) (a := D.obj I₁)).symm
      have hg₂' :
          over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₂.op.toLoc).toFunctor.obj
                (D.obj I₂)) =
            (yoneda.obj U).map g₂.op (over_fiber_to_hom U I₂.Y (D.obj I₂)) := by
        simpa using
          over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := g₂) (a := D.obj I₂)
      exact hg₁'.trans (hEq.trans hg₂')⟩
  have hHomSub :
      ∀ D₁ D₂ : DD, Subsingleton (D₁ ⟶ D₂) := by
    intro D₁ D₂
    refine ⟨fun φ ψ ↦ Pseudofunctor.DescentData.hom_ext (fun I ↦ ?_)⟩
    exact (over_fiber_hom_subsingleton (D₁.obj I) (D₂.obj I)).elim _ _
  have hCompatMap :
      ∀ {D₁ D₂ : DD} (φ : D₁ ⟶ D₂), compatOfDescent D₁ = compatOfDescent D₂ := by
    intro D₁ D₂ φ
    apply Subtype.ext
    funext I
    exact over_fiber_to_hom_eq_of_hom (φ.hom I)
  let G : DD ⥤ Discrete compat := by
    refine
      { obj := fun D ↦ Discrete.mk (compatOfDescent D)
        map := fun {D₁ D₂} φ ↦ ?_
        map_id := ?_
        map_comp := ?_ }
    exact eqToHom (congrArg Discrete.mk (hCompatMap φ))
    · intro D
      exact Subsingleton.elim _ _
    · intro D₁ D₂ D₃ φ ψ
      exact Subsingleton.elim _ _
  let descentOfCompat : compat → DD := fun s ↦
    { obj := fun I ↦ Functor.Fiber.mk (a := Over.mk (s.1 I)) rfl
      hom := fun {Y} q {I₁ I₂} f₁ f₂ hf₁ hf₂ ↦ by
        have h₁ :
            over_fiber_to_hom U Y
                (((canonicalFiberPseudofunctor (Over.forget U)).map f₁.op.toLoc).toFunctor.obj
                  (Functor.Fiber.mk (a := Over.mk (s.1 I₁)) rfl)) =
              (yoneda.obj U).map f₁.op (s.1 I₁) := by
          simpa [over_fiber_to_hom_fiber_mk_over_mk] using
            over_pseudofunctor_map_obj_hom_eq_comp
              (U := U) (f := f₁) (a := Functor.Fiber.mk (a := Over.mk (s.1 I₁)) rfl)
        have h₂ :
            (yoneda.obj U).map f₁.op (s.1 I₁) =
              (yoneda.obj U).map f₂.op (s.1 I₂) := by
          simpa [hf₁, hf₂] using s.2 I₁ I₂ _ f₁ f₂ (by rw [hf₁, hf₂])
        have h₃ :
            (yoneda.obj U).map f₂.op (s.1 I₂) =
              over_fiber_to_hom U Y
                (((canonicalFiberPseudofunctor (Over.forget U)).map f₂.op.toLoc).toFunctor.obj
                  (Functor.Fiber.mk (a := Over.mk (s.1 I₂)) rfl)) := by
          simpa [over_fiber_to_hom_fiber_mk_over_mk] using
            (over_pseudofunctor_map_obj_hom_eq_comp
              (U := U) (f := f₂) (a := Functor.Fiber.mk (a := Over.mk (s.1 I₂)) rfl)).symm
        apply eqToHom
        apply over_fiber_eq_of_hom_eq (U := U)
        exact h₁.trans (h₂.trans h₃)
      pullHom_hom := by
        intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        exact (over_fiber_hom_subsingleton _ _).elim _ _
      hom_self := by
        intro Y q I g hg
        exact (over_fiber_hom_subsingleton _ _).elim _ _
      hom_comp := by
        intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        exact (over_fiber_hom_subsingleton _ _).elim _ _ }
  have hInverse : ∀ s : compat, compatOfDescent (descentOfCompat s) = s := by
    intro s
    apply Subtype.ext
    funext I
    simp [compatOfDescent, descentOfCompat, over_fiber_to_hom_fiber_mk_over_mk]
  have hObjEq :
      ∀ (D : DD) (I : S.Arrow),
        D.obj I = (descentOfCompat (compatOfDescent D)).obj I := by
    intro D I
    apply over_fiber_eq_of_hom_eq (U := U)
    simp [compatOfDescent, descentOfCompat, over_fiber_to_hom_fiber_mk_over_mk]
  let H : Discrete compat ⥤ DD := by
    refine
      { obj := fun s ↦ descentOfCompat s.as
        map := fun {s t} φ ↦
          eqToHom
            (congrArg (fun x : Discrete compat ↦ descentOfCompat x.as)
              (obj_ext_of_isDiscrete φ))
        map_id := ?_
        map_comp := ?_ }
    · intro s
      exact (hHomSub _ _).elim _ _
    · intro s t u φ ψ
      exact (hHomSub _ _).elim _ _
  let E : DD ≌ Discrete compat :=
    { functor := G
      inverse := H
      unitIso := by
        refine NatIso.ofComponents (fun D ↦ ?_) ?_
        · refine Pseudofunctor.DescentData.isoMk (fun I ↦ ?_) ?_
          · exact eqToIso (hObjEq D I)
          · intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
            exact (over_fiber_hom_subsingleton _ _).elim _ _
        · intro D₁ D₂ φ
          exact (hHomSub _ _).elim _ _
      counitIso := by
        refine Discrete.natIso ?_
        intro s
        apply eqToIso
        simp [G, H, hInverse] }
  let K : ((Over.forget U).Fiber V) ⥤ Discrete compat := by
    refine
      { obj := fun a ↦
          Discrete.mk (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)
            (over_fiber_to_hom U V a))
        map := fun {a b} φ ↦ ?_
        map_id := ?_
        map_comp := ?_ }
    apply eqToHom
    apply congrArg Discrete.mk
    apply congrArg (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
    exact over_fiber_to_hom_eq_of_hom φ
    · intro a
      exact Subsingleton.elim _ _
    · intro a b c φ ψ
      exact Subsingleton.elim _ _
  letI : IsDiscrete ((Over.forget U).Fiber V) :=
    { subsingleton := fun a b ↦ over_fiber_hom_subsingleton a b
      eq_of_hom := fun φ ↦ over_fiber_eq_of_hom_eq (over_fiber_to_hom_eq_of_hom φ) }
  have hIso :
      (((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙ G) ≅ K := by
    refine NatIso.ofComponents (fun a ↦ ?_) ?_
    · apply eqToIso
      apply congrArg Discrete.mk
      apply Subtype.ext
      funext I
      simpa [compatOfDescent] using
        over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := I.f) (a := a)
    · intro a b φ
      exact Subsingleton.elim _ _
  let Kobj' : ((Over.forget U).Fiber V) → compat := fun a ↦
    Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f) (over_fiber_to_hom U V a)
  have hDiscreteMk :
      Function.Bijective (fun s : compat ↦ (Discrete.mk s : Discrete compat)) := by
    constructor
    · intro s t hst
      cases hst
      rfl
    · intro s
      exact ⟨s.as, by cases s; rfl⟩
  have hObjBijDiscrete :
      Function.Bijective K.obj ↔ Function.Bijective Kobj' := by
    simpa [K, Kobj', Function.comp] using
      (Function.Bijective.of_comp_iff' hDiscreteMk Kobj')
  have hObjBijFiber :
      Function.Bijective Kobj' ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) := by
    convert
      (Function.Bijective.of_comp_iff
        (f := Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
        (g := over_fiber_to_hom U V)
        (over_fiber_to_hom_bijective U V)) using 1
  have hObjBij :
      Function.Bijective K.obj ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) :=
    hObjBijDiscrete.trans hObjBijFiber
  have hDiscrete :
      K.IsEquivalence ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) := by
    rw [isEquivalence_iff_bijective_obj_of_isDiscrete (G := K), hObjBij]
  have hCompare :
      ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
        K.IsEquivalence := by
    constructor
    · intro hΦ
      let _ :
          ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
            (fun I : S.Arrow ↦ I.f)).IsEquivalence := hΦ
      let _ : G.IsEquivalence := E.isEquivalence_functor
      have hComp :
          ((((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
              (fun I : S.Arrow ↦ I.f))) ⋙ G).IsEquivalence :=
        by infer_instance
      exact (Functor.isEquivalence_iff_of_iso hIso).1 hComp
    · intro hK
      let _ : K.IsEquivalence := hK
      have hComp :
          ((((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
              (fun I : S.Arrow ↦ I.f))) ⋙ G).IsEquivalence :=
        (Functor.isEquivalence_iff_of_iso hIso).2 hK
      let _ : G.IsEquivalence := E.isEquivalence_functor
      exact Functor.isEquivalence_of_comp_right
        ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)) G
  rw [hCompare, hDiscrete]
  rw [← S.ofArrows_eq, ← Presieve.isSheafFor_iff_generate]
  exact
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := yoneda.obj U) (π := fun I : S.Arrow ↦ I.f)).symm

end OverDescent

/- Domain-style sampling for Lemma 8.13.1:
- primary domain: stacks on a site, specialized to representable presheaves and the slice
  projection `Over.forget U`.
- inspected owner-level declarations:
  `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`,
  `representableElementsOpToOver_isEquivalenceOverBase`,
  `IsStackOnSite`,
  `Over.forget`.
- best owner abstraction: the core owner is
  `IsStackOnSite J ((CategoryOfElements.π F).leftOp)` for a presheaf `F`; the slice projection
  `Over.forget U` is reached from that owner by the canonical over-base equivalence for the
  representable presheaf `h[U]`.
- primitive data: the object `U : C` and the representable presheaf `h[U]`.
- derived API: the slice-category reformulation obtained by transporting the stack condition
  across `representableElementsOpToOver_isEquivalenceOverBase U`.

Source/core/bridge triage:
- `source-facing`: `over_forget_isStackOnSite_iff_representable_isSheaf`.
- `core/canonical`: `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`.
- `bridge/view`: `representableElementsOpToOver_isEquivalenceOverBase U`. -/

-- Proof sketch: the canonical owner theorem `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`
-- identifies the sheaf condition on a presheaf with the stack condition on its category of
-- elements. For the representable presheaf `h[U]`, Example `4.38.7` gives the canonical
-- over-base equivalence between that category of elements and the slice projection `Over.forget U`,
-- so transport the stack condition across that equivalence.
/-- Lemma 8.13.1: for an object `U` of a site `(C, J)`, the localization functor
`j_U : C/U ⥤ C`, written in Lean as `Over.forget U`, is a stack over `(C, J)` if and only if the
representable presheaf `h_U`, written canonically as `h[U]`, is a sheaf. This is the canonical
chapter-facing form of the source statement. -/
theorem over_forget_isStackOnSite_iff_representable_isSheaf
    (J : GrothendieckTopology C) (U : C) :
    IsStackOnSite J (Over.forget U) ↔ Presheaf.IsSheaf J (yoneda.obj U) := by
  rw [isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence]
  constructor
  · intro h
    rw [isSheaf_iff_isSheaf_of_type]
    intro V R hR
    let S : J.Cover V := ⟨R, hR⟩
    -- Reduce the target sheaf condition for this covering sieve to the explicit descent comparison.
    exact
      (over_cover_toDescentData_isEquivalence_iff_isSheafFor
        (J := J) (U := U) (V := V) S).1 (h V S)
  · intro h V S
    have hS : Presieve.IsSheafFor (yoneda.obj U) ((S : Sieve V).arrows) := by
      -- Convert the global sheaf hypothesis into the cover-specific sheaf condition.
      exact h.isSheafFor (S : Sieve V) S.condition
    -- Apply the explicit comparison for this fixed cover.
    exact
      (over_cover_toDescentData_isEquivalence_iff_isSheafFor
        (J := J) (U := U) (V := V) S).2 hS

end CategoryTheory
