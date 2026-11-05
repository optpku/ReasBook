module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Types.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v w

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

section

variable {C : Type u} [Category.{v} C] {U : C}

/-- Helper for Lemma 7.28.1: the discrete family of terminal indexing objects for the
objectwise left Kan extension formula along `(Over.forget U).op`. -/
abbrev uliftLocalizationIndexFunctor
    (V : C) : Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (op V) :=
  Discrete.functor fun φ ↦
    CostructuredArrow.mk
      (show (Over.forget U).op.obj (op (Over.mk φ)) ⟶ op V from 𝟙 (op V))

/-- Helper for Lemma 7.28.1: the underlying slice object of a costructured arrow over
`(Over.forget U).op`. -/
abbrev uliftLocalizationOverObj
    {V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Over U :=
  X.left.unop

/-- Helper for Lemma 7.28.1: the leg `V ⟶ A` in the triangle represented by a costructured
arrow over `(Over.forget U).op`. -/
abbrev uliftLocalizationLeg
    {V : C} (X : CostructuredArrow (Over.forget U).op (op V)) :
    V ⟶ (uliftLocalizationOverObj (U := U) X).left :=
  X.hom.unop

/-- Helper for Lemma 7.28.1: the composite `V ⟶ U` remembered by a costructured arrow. -/
abbrev uliftLocalizationComposite
    {V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : V ⟶ U :=
  uliftLocalizationLeg (U := U) X ≫ (uliftLocalizationOverObj (U := U) X).hom

/-- Helper for Lemma 7.28.1: the discrete index determined by the composite of a triangle. -/
abbrev uliftLocalizationIndex
    {V : C} (X : CostructuredArrow (Over.forget U).op (op V)) : Discrete (V ⟶ U) :=
  Discrete.mk (uliftLocalizationComposite (U := U) X)

/-- Helper for Lemma 7.28.1: the canonical morphism from a costructured-arrow index to its
chosen terminal representative. -/
abbrev uliftLocalizationTerminalHom
    (V : C) {X : CostructuredArrow (Over.forget U).op (op V)} :
    X ⟶ (uliftLocalizationIndexFunctor (U := U) V).obj
        (uliftLocalizationIndex (U := U) X) :=
  CostructuredArrow.homMk
    ((show Over.mk (uliftLocalizationComposite (U := U) X) ⟶
        uliftLocalizationOverObj (U := U) X from
        Over.homMk (uliftLocalizationLeg (U := U) X)).op)
    (by
      simp [uliftLocalizationIndexFunctor, uliftLocalizationIndex,
        uliftLocalizationLeg])

/-- Helper for Lemma 7.28.1: morphisms in the indexing category preserve the composite
`V ⟶ U`. -/
lemma uliftLocalizationComposite_eq_of_map
    (V : C) {X Y : CostructuredArrow (Over.forget U).op (op V)} (hom : X ⟶ Y) :
    uliftLocalizationComposite (U := U) X =
      uliftLocalizationComposite (U := U) Y := by
  -- Project the costructured-arrow square to the underlying triangle in `C`.
  let triangle : uliftLocalizationOverObj (U := U) Y ⟶
      uliftLocalizationOverObj (U := U) X := hom.left.unop
  have hleg :
      uliftLocalizationLeg (U := U) Y ≫ triangle.left =
        uliftLocalizationLeg (U := U) X := by
    have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
    simpa [triangle] using h
  have hw :
      triangle.left ≫ (uliftLocalizationOverObj (U := U) X).hom =
        (uliftLocalizationOverObj (U := U) Y).hom := Over.w triangle
  dsimp [uliftLocalizationComposite]
  calc
    uliftLocalizationLeg (U := U) X ≫ (uliftLocalizationOverObj (U := U) X).hom =
        (uliftLocalizationLeg (U := U) Y ≫ triangle.left) ≫
          (uliftLocalizationOverObj (U := U) X).hom := by
      rw [hleg]
    _ = uliftLocalizationLeg (U := U) Y ≫
          (triangle.left ≫ (uliftLocalizationOverObj (U := U) X).hom) := by
      rw [Category.assoc]
    _ = uliftLocalizationLeg (U := U) Y ≫
          (uliftLocalizationOverObj (U := U) Y).hom := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ uliftLocalizationLeg (U := U) Y ≫ k) hw

/-- Helper for Lemma 7.28.1: a morphism into a chosen indexed terminal object records exactly
the source composite. -/
lemma uliftLocalizationComposite_eq_of_hom
    (V : C) {X : CostructuredArrow (Over.forget U).op (op V)}
    {φ : V ⟶ U}
    (hom : X ⟶ (uliftLocalizationIndexFunctor (U := U) V).obj (Discrete.mk φ)) :
    uliftLocalizationComposite (U := U) X = φ := by
  simpa [uliftLocalizationIndexFunctor, uliftLocalizationComposite,
    uliftLocalizationLeg, uliftLocalizationOverObj] using
    uliftLocalizationComposite_eq_of_map (U := U) V hom

/-- Helper for Lemma 7.28.1: reindex a costructured arrow by an identified composite
`V ⟶ U`. -/
def uliftLocalizationHomToIndex
    (V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : uliftLocalizationComposite (U := U) X = φ) :
    X ⟶ (uliftLocalizationIndexFunctor (U := U) V).obj (Discrete.mk φ) := by
  cases hφ
  exact uliftLocalizationTerminalHom (U := U) V

/-- Helper for Lemma 7.28.1: a morphism into the chosen terminal representative is unique. -/
lemma uliftLocalizationHom_eq_terminalHom
    (V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (hom : X ⟶ (uliftLocalizationIndexFunctor (U := U) V).obj
        (uliftLocalizationIndex (U := U) X)) :
    hom = uliftLocalizationTerminalHom (U := U) V := by
  ext
  exact by
    apply Quiver.Hom.unop_inj
    apply CommaMorphism.ext
    · have h := congrArg Quiver.Hom.unop (CostructuredArrow.w hom)
      simpa [uliftLocalizationIndexFunctor] using h
    · simp [Over.homMk]

/-- Helper for Lemma 7.28.1: the canonical morphism to an explicitly indexed terminal object is
unique. -/
lemma uliftLocalizationHom_eq_homToIndex
    (V : C) (X : CostructuredArrow (Over.forget U).op (op V))
    (φ : V ⟶ U) (hφ : uliftLocalizationComposite (U := U) X = φ)
    (hom : X ⟶ (uliftLocalizationIndexFunctor (U := U) V).obj (Discrete.mk φ)) :
    hom = uliftLocalizationHomToIndex (U := U) V X φ hφ := by
  cases hφ
  simpa [uliftLocalizationHomToIndex] using
    uliftLocalizationHom_eq_terminalHom (U := U) V X hom

/-- Helper for Lemma 7.28.1: the indexing category remembers only the composite map `V ⟶ U`.
-/
abbrev uliftLocalizationCompositeFunctor
    (V : C) :
    CostructuredArrow (Over.forget U).op (op V) ⥤ Discrete (V ⟶ U) where
  obj X := Discrete.mk (uliftLocalizationComposite (U := U) X)
  map hom := Discrete.eqToHom (uliftLocalizationComposite_eq_of_map (U := U) V hom)

/-- Helper for Lemma 7.28.1: the discrete inclusion of chosen terminal indices is right adjoint
to the composite-index functor. -/
def uliftLocalizationCompositeIndexAdjunction
    (V : C) :
    uliftLocalizationCompositeFunctor (U := U) V ⊣
      uliftLocalizationIndexFunctor (U := U) V :=
  Adjunction.mkOfHomEquiv
    { homEquiv := by
        intro X φ
        cases φ with
        | mk ψ =>
            refine
              { toFun := fun hom ↦
                  uliftLocalizationHomToIndex (U := U) V X ψ (Discrete.eq_of_hom hom)
                invFun := fun hom ↦
                  Discrete.eqToHom
                    (uliftLocalizationComposite_eq_of_hom (U := U) V hom)
                left_inv := ?_
                right_inv := ?_ }
            · intro hom
              apply Subsingleton.elim
            · intro hom
              simpa using
                (uliftLocalizationHom_eq_homToIndex (U := U) V X ψ
                  (uliftLocalizationComposite_eq_of_hom (U := U) V hom) hom).symm
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
                  (uliftLocalizationHom_eq_homToIndex (U := U) V X ψ'
                    (by simpa using Discrete.eq_of_hom (hom ≫ g))
                    (uliftLocalizationHomToIndex (U := U) V X ψ
                        (Discrete.eq_of_hom hom) ≫
                      (uliftLocalizationIndexFunctor (U := U) V).map g)).symm
                simpa [uliftLocalizationHomToIndex] using congrArg CommaMorphism.left h }

/-- Helper for Lemma 7.28.1: the discrete inclusion of chosen terminal indexing objects is final.
-/
theorem uliftLocalizationIndexFunctor_final
    (V : C) :
    Functor.Final (uliftLocalizationIndexFunctor (U := U) V) := by
  let _ : (uliftLocalizationIndexFunctor (U := U) V).IsRightAdjoint :=
    ⟨⟨uliftLocalizationCompositeFunctor (U := U) V,
      ⟨uliftLocalizationCompositeIndexAdjunction (U := U) V⟩⟩⟩
  infer_instance

/-- Helper for Lemma 7.28.1: the restricted costructured-arrow diagram is the discrete family
`φ ↦ G(V ⟶ U via φ)`. -/
abbrev uliftLocalizationIndexFunctorProjIso
    (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) (V : C) :
    uliftLocalizationIndexFunctor (U := U) V ⋙
        CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G ≅
      Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) := by
  refine Discrete.natIso ?_
  intro φ
  exact Iso.refl _

/-- Helper for Lemma 7.28.1: the objectwise left Kan extension along `(Over.forget U).op` is the
sigma type of all fibres over arrows `V ⟶ U` in the enlarged type universe. -/
noncomputable def uliftLocalizationLeftKanExtensionObjIsoSigma
    (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) (V : C) :
    (((Over.forget U).op.lan.obj G).obj (op V)) ≅
      Σ φ : V ⟶ U, G.obj (op (Over.mk φ)) :=
  letI : Functor.Final (uliftLocalizationIndexFunctor (U := U) V) :=
    uliftLocalizationIndexFunctor_final (U := U) V
  (Over.forget U).op.leftKanExtensionObjIsoColimit G (op V) ≪≫
    (Functor.Final.colimitIso
      (uliftLocalizationIndexFunctor (U := U) V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso (uliftLocalizationIndexFunctorProjIso (U := U) G V) ≪≫
    Types.coproductIso.{v, max w u} (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))

/-- Helper for Lemma 7.28.1: the sigma model sends a canonical left-Kan-extension generator to
the corresponding summand. -/
theorem uliftLocalizationLeftKanExtensionObjIsoSigma_hom_unit_app
    (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {V : C} (a : V ⟶ U)
    (s : G.obj (op (Over.mk a))) :
    (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).hom
        ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s) =
      ⟨a, s⟩ := by
  -- Follow the definition of the sigma model through the colimit comparison, the final functor
  -- comparison, the discrete-family comparison, and finally the coproduct sigma comparison.
  let F₁ := uliftLocalizationIndexFunctor (U := U) V
  let F₂ := CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G
  let F₃ := Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))
  letI : Functor.Final F₁ := uliftLocalizationIndexFunctor_final (U := U) V
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
        (w := uliftLocalizationIndexFunctorProjIso (U := U) G V) (j := Discrete.mk a))
      s
  have h₃ :=
    congrFun
      (Types.coproductIso_ι_comp_hom.{v, max w u}
        (F := fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) a)
      s
  calc
    (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).hom
        ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s)
        =
          (Types.coproductIso.{v, max w u}
              (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom
            ((HasColimit.isoOfNatIso
                (uliftLocalizationIndexFunctorProjIso (U := U) G V)).hom
              ((Functor.Final.colimitIso F₁ F₂).inv
                (((Over.forget U).op.leftKanExtensionObjIsoColimit G (op V)).hom
                  ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s)))) := by
      rfl
    _ =
          (Types.coproductIso.{v, max w u}
              (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom
            ((HasColimit.isoOfNatIso
                (uliftLocalizationIndexFunctorProjIso (U := U) G V)).hom
              ((Functor.Final.colimitIso F₁ F₂).inv
                (colimit.ι F₂ (F₁.obj (Discrete.mk a)) s))) := by
      simpa [F₁, uliftLocalizationIndexFunctor] using congrArg
        ((Types.coproductIso.{v, max w u}
              (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom ∘
          (HasColimit.isoOfNatIso
            (uliftLocalizationIndexFunctorProjIso (U := U) G V)).hom ∘
            (Functor.Final.colimitIso F₁ F₂).inv) h₀
    _ =
          (Types.coproductIso.{v, max w u}
              (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom
            ((HasColimit.isoOfNatIso
                (uliftLocalizationIndexFunctorProjIso (U := U) G V)).hom
              (colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s)) := by
      have h₁' :
          ((Functor.Final.colimitIso F₁ F₂).inv
              (colimit.ι F₂ (F₁.obj (Discrete.mk a)) s)) =
            colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s := by
        simpa [F₁, F₂, uliftLocalizationIndexFunctor] using h₁
      exact congrArg
        ((Types.coproductIso.{v, max w u}
              (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom ∘
          (HasColimit.isoOfNatIso
            (uliftLocalizationIndexFunctorProjIso (U := U) G V)).hom) h₁'
    _ =
          (Types.coproductIso.{v, max w u}
              (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom
            (colimit.ι F₃ (Discrete.mk a) s) := by
      have h₂' :
          (HasColimit.isoOfNatIso
              (uliftLocalizationIndexFunctorProjIso (U := U) G V)).hom
              (colimit.ι (F₁ ⋙ F₂) (Discrete.mk a) s) =
            colimit.ι F₃ (Discrete.mk a) s := by
        simpa [F₁, F₂, F₃, uliftLocalizationIndexFunctorProjIso] using h₂
      exact congrArg
        ((Types.coproductIso.{v, max w u}
          (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))).hom) h₂'
    _ = ⟨a, s⟩ := by
      simpa [F₃] using h₃

/-- Helper for Lemma 7.28.1: the inverse sigma model sends a summand back to the canonical
left-Kan-extension generator. -/
theorem uliftLocalizationLeftKanExtensionObjIsoSigma_inv_mk
    (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {V : C} (a : V ⟶ U)
    (s : G.obj (op (Over.mk a))) :
    (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).inv ⟨a, s⟩ =
      (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s := by
  -- Cancel the sigma model against the explicit generator computation.
  apply (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).toEquiv.injective
  simp [uliftLocalizationLeftKanExtensionObjIsoSigma_hom_unit_app]

/-- Helper for Lemma 7.28.1: the canonical over-arrow induced by `f : Y ⟶ V`. -/
abbrev uliftLocalizationOverHomMk {V Y : C} {φ : V ⟶ U} (f : Y ⟶ V) :
    Over.mk (f ≫ φ) ⟶ Over.mk φ :=
  Over.homMk f

/-- Helper for Lemma 7.28.1: in the sigma model, restriction along `f : Y ⟶ V` sends the summand
indexed by `a : V ⟶ U` to the summand indexed by `f ≫ a`. -/
theorem uliftLocalizationLeftKanExtensionObjIsoSigma_hom_map
    (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) {V Y : C} (f : Y ⟶ V)
    (x : (((Over.forget U).op.lan.obj G).obj (op V))) :
    (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G Y).hom
        (((Over.forget U).op.lan.obj G).map f.op x) =
      ⟨f ≫ ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).hom x).1,
        G.map
          (uliftLocalizationOverHomMk
            (U := U) (φ := ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).hom x).1)
            f).op
          ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).hom x).2⟩ := by
  -- Rewrite `x` as the canonical generator for its sigma coordinates, then use naturality of the
  -- left-Kan-extension unit along the evident morphism in `Over U`.
  rcases hV : (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).hom x with ⟨a, s⟩
  rw [← hV]
  have hx :
      x =
        (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).inv ⟨a, s⟩ := by
    apply (uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G V).toEquiv.injective
    simp [hV]
  rw [hx, uliftLocalizationLeftKanExtensionObjIsoSigma_inv_mk (U := U) G a s]
  let g : Over.mk (f ≫ a) ⟶ Over.mk a :=
    uliftLocalizationOverHomMk (U := U) (φ := a) f
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
  rw [uliftLocalizationLeftKanExtensionObjIsoSigma_hom_unit_app (U := U) G a s]
  simpa using
    uliftLocalizationLeftKanExtensionObjIsoSigma_hom_unit_app (U := U) G (f ≫ a)
      (G.map g.op s)

/-- Helper for Lemma 7.28.1: in the enlarged sigma model, the fibre over `X.hom` is exactly
evaluation at the slice object `X`. -/
noncomputable def uliftLocalizationFiberSigmaIso
    (G : (Over U)ᵒᵖ ⥤ Type (max w u v)) (X : Over U) :
    { s : (((Over.forget U).op.lan.obj G).obj (op X.left)) //
        ((uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left).hom s).1 =
          X.hom } ≅
      G.obj (op X) := by
  -- Transfer the fibre through the sigma-model equivalence, then substitute the first coordinate.
  let e := uliftLocalizationLeftKanExtensionObjIsoSigma (U := U) G X.left
  let e₁ :
      { s : (((Over.forget U).op.lan.obj G).obj (op X.left)) //
          (e.hom s).1 = X.hom } ≃
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

end

end CategoryTheory
