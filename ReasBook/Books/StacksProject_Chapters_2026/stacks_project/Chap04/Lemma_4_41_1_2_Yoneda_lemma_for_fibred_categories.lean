module

public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Lemma_4_33_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u₁ u₂

namespace CategoryTheory

open Functor
open Functor.Fiber
open FibredCategoryMor

variable {C : Type u₁} [Category.{v} C]

namespace FibredCategoryOver

variable (X : FibredCategoryOver C)

/- Domain-style sampling for Lemma 4.41.1 (2):
- primary domain: fibred categories over a fixed base and evaluation of the hom-category
  `Mor_{Fib/C}(C/U, X)` at the identity slice object `id_U : U/U`.
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids (Over.forget U)`,
  `FibredCategoryOver.ofFunctor`,
  `FibredCategoryMor.toFunctor`,
  `FibredCategoryMor.comm`,
  `Fiber.inducedFunctor`,
  `Fiber.fiberInclusion_comp_eq_const`.
- best owner abstraction: the public owner here is the evaluation functor from the hom-category of
  fibred-category morphisms out of the canonical slice owner
  `FibredCategoryOver.ofFunctor (Over.forget U) inferInstance` to the standard
  fibre `X.p.Fiber U`; its construction should factor through the canonical fiber owner
  `Fiber.inducedFunctor`.
- primitive data: the underlying evaluation functor to the total category `X.S` together with the
  proof that its composite with `X.p` is constant at `U`.
- derived API: the fibre-valued evaluation functor and its equivalence instance.

Source/core/bridge triage:
- `source-facing`: `yonedaEvaluationFunctor` and `yonedaEvaluationFunctor_isEquivalence`.
- `core/canonical`: `FibredCategoryOver.ofFunctor`, the ambient owner homs `X ⟶ Y`, and
  `Fiber.inducedFunctor`.
- `bridge/view`: the fibred-in-groupoids specialization in
  `Lemma_4_41_2_2_Yoneda_lemma`. -/

noncomputable def yonedaEvaluationToTotal (U : C) :
    (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) ⥤ X.S :=
  ((fibredCategoryOverSubTwoCategory C).hom (FibredCategoryOver.ofFunctor (Over.forget U)) X).inclusion ⋙
    BasedNatTrans.forgetful _ _ ⋙ (evaluation (Over U) X.S).obj (Over.mk (𝟙 U))

theorem yonedaEvaluationToTotal_comp_eq_const (U : C) :
    X.yonedaEvaluationToTotal U ⋙ X.p =
      (Functor.const (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X)).obj U := by
  let hobj :
      ∀ F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X,
        (X.yonedaEvaluationToTotal U ⋙ X.p).obj F = U :=
    fun F ↦ congrArg (fun q ↦ q.obj (Over.mk (𝟙 U))) (FibredCategoryMor.comm F)
  refine Functor.ext hobj ?_
  intro F G τ
  let _ : X.p.IsHomLift (𝟙 U) ((X.yonedaEvaluationToTotal U).map τ) := by
    change X.p.IsHomLift (𝟙 U) ((τ.hom.hom).toNatTrans.app (Over.mk (𝟙 U)))
    exact fibredCategoryMor_hom_isHomLift_id τ (Over.mk (𝟙 U))
  change X.p.map ((X.yonedaEvaluationToTotal U).map τ) =
      eqToHom (hobj F) ≫ 𝟙 U ≫ eqToHom (hobj G).symm
  simpa using IsHomLift.fac' X.p (𝟙 U) ((X.yonedaEvaluationToTotal U).map τ)

/-- Evaluation at the identity object `id_U : U/U` on morphisms of fibred categories
`C/U ⟶ X` over `C`. -/
noncomputable def yonedaEvaluationFunctor (U : C) :
    (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) ⥤ X.p.Fiber U :=
  Fiber.inducedFunctor (X.yonedaEvaluationToTotal_comp_eq_const U)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the base relation recorded by
an arrow in the slice category `C/U`. -/
private theorem over_hom_left_comp_hom
    {U : C} {a b : Over U} (φ : a ⟶ b) :
    φ.left ≫ b.hom = a.hom := by
  simpa using φ.w

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the chosen arrow in the
canonical pullback system is a lift over its defining base morphism. -/
private theorem canonicalPullbackChoice_map_isHomLift
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    X.p.IsHomLift f ((canonicalPullbackChoice X.p).map f x) := by
  let _ : X.p.IsStronglyCartesian f ((canonicalPullbackChoice X.p).map f x) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian f x
  infer_instance

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the chosen pullback arrow of
`b.hom` satisfies the expected universal property with respect to the chosen pullback arrow of
`a.hom`. -/
private theorem yonedaPullbackLiftMap_existsUnique
    {U : C} (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    ∃! χ : (a.hom ^*[canonicalPullbackChoice X.p] x).1 ⟶
        (b.hom ^*[canonicalPullbackChoice X.p] x).1,
      X.p.IsHomLift φ.left χ ∧
        χ ≫ (canonicalPullbackChoice X.p).map b.hom x =
          (canonicalPullbackChoice X.p).map a.hom x := by
  -- Use the universal property of the chosen pullback arrow of `b.hom`.
  let hs : X.p.IsStronglyCartesian b.hom ((canonicalPullbackChoice X.p).map b.hom x) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian b.hom x
  let hsA : X.p.IsStronglyCartesian a.hom ((canonicalPullbackChoice X.p).map a.hom x) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian a.hom x
  let hl : X.p.IsHomLift a.hom ((canonicalPullbackChoice X.p).map a.hom x) := hsA.toIsHomLift
  refine ⟨?_, ?_, ?_⟩
  · exact
      @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _ b.hom
        ((canonicalPullbackChoice X.p).map b.hom x) hs _ _ φ.left a.hom
        (over_hom_left_comp_hom φ).symm ((canonicalPullbackChoice X.p).map a.hom x) hl
  · constructor
    · exact
        @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _ b.hom
          ((canonicalPullbackChoice X.p).map b.hom x) hs _ _ φ.left a.hom
          (over_hom_left_comp_hom φ).symm ((canonicalPullbackChoice X.p).map a.hom x) hl
    · exact
        @IsStronglyCartesian.fac _ _ _ _ X.p _ _ _ _ b.hom
          ((canonicalPullbackChoice X.p).map b.hom x) hs _ _ φ.left a.hom
          (over_hom_left_comp_hom φ).symm ((canonicalPullbackChoice X.p).map a.hom x) hl
  · intro ψ hψ
    let hψlift : X.p.IsHomLift φ.left ψ := hψ.1
    exact
      @IsStronglyCartesian.map_uniq _ _ _ _ X.p _ _ _ _ b.hom
        ((canonicalPullbackChoice X.p).map b.hom x) hs _ _ φ.left a.hom
        (over_hom_left_comp_hom φ).symm ((canonicalPullbackChoice X.p).map a.hom x) hl
        ψ hψlift hψ.2

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the textbook arrow attached to
`φ : a ⟶ b` in `C/U`, characterized as the unique lift over `φ.left` whose composite with the
chosen pullback arrow of `b.hom` recovers the chosen pullback arrow of `a.hom`. -/
private noncomputable def yonedaPullbackLiftMap
    {U : C} (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    (a.hom ^*[canonicalPullbackChoice X.p] x).1 ⟶
      (b.hom ^*[canonicalPullbackChoice X.p] x).1 :=
  -- Route correction: package the transition arrow from the explicit universal-property witness.
  Classical.choose (X.yonedaPullbackLiftMap_existsUnique x φ)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the universal-property map
postcomposes with the chosen pullback arrow of `b.hom` to the chosen pullback arrow of `a.hom`. -/
@[reassoc]
private theorem yonedaPullbackLiftMap_fac
    {U : C} (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    X.yonedaPullbackLiftMap x φ ≫ (canonicalPullbackChoice X.p).map b.hom x =
      (canonicalPullbackChoice X.p).map a.hom x := by
  -- Read off the defining factorization from the chosen universal-property witness.
  exact (Classical.choose_spec (X.yonedaPullbackLiftMap_existsUnique x φ)).1.2

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the pullback transition map is
strongly cartesian over the underlying arrow in `C`. -/
private theorem yonedaPullbackLiftMap_isStronglyCartesian
    {U : C} (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    X.p.IsStronglyCartesian φ.left (X.yonedaPullbackLiftMap x φ) := by
  -- The composite with the chosen pullback of `b.hom` is the chosen pullback of `a.hom`,
  -- hence strongly cartesian; cancel the second strongly cartesian factor.
  let hComp :
      X.p.IsStronglyCartesian (φ.left ≫ b.hom)
        (X.yonedaPullbackLiftMap x φ ≫ (canonicalPullbackChoice X.p).map b.hom x) := by
    rw [X.yonedaPullbackLiftMap_fac x φ]
    letI : X.p.IsStronglyCartesian a.hom ((canonicalPullbackChoice X.p).map a.hom x) :=
      (canonicalPullbackChoice X.p).isStronglyCartesian a.hom x
    simpa [(over_hom_left_comp_hom φ).symm] using
      (show X.p.IsStronglyCartesian a.hom ((canonicalPullbackChoice X.p).map a.hom x) from
        inferInstance)
  letI : X.p.IsStronglyCartesian (φ.left ≫ b.hom)
      (X.yonedaPullbackLiftMap x φ ≫ (canonicalPullbackChoice X.p).map b.hom x) := hComp
  let hLift : X.p.IsHomLift φ.left (X.yonedaPullbackLiftMap x φ) :=
    (Classical.choose_spec (X.yonedaPullbackLiftMap_existsUnique x φ)).1.1
  letI : X.p.IsHomLift φ.left (X.yonedaPullbackLiftMap x φ) := hLift
  exact
    @Functor.IsStronglyCartesian.of_comp
      _ _ _ _ X.p _ _ _ _ _ _ _ _ _ _
      ((canonicalPullbackChoice X.p).isStronglyCartesian b.hom x)
      hComp hLift

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the universal-property map is
the expected lift over the underlying slice morphism. -/
private theorem yonedaPullbackLiftMap_isHomLift
    {U : C} (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    X.p.IsHomLift φ.left (X.yonedaPullbackLiftMap x φ) := by
  -- The chosen witness already comes equipped with the required lifting property.
  exact (Classical.choose_spec (X.yonedaPullbackLiftMap_existsUnique x φ)).1.1

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the transition morphism maps to
the underlying arrow in the slice category, up to the standard fiber object equalities. -/
private theorem yonedaPullbackLiftMap_base
    {U : C} (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    X.p.map (X.yonedaPullbackLiftMap x φ) =
      eqToHom (show X.p.obj ((a.hom ^*[canonicalPullbackChoice X.p] x).1) = a.left from
        (a.hom ^*[canonicalPullbackChoice X.p] x).2) ≫
        φ.left ≫
          eqToHom (show X.p.obj ((b.hom ^*[canonicalPullbackChoice X.p] x).1) = b.left from
            (b.hom ^*[canonicalPullbackChoice X.p] x).2).symm := by
  -- Read off the base map from the fact that the transition arrow is a lift over `φ.left`.
  letI : X.p.IsHomLift φ.left (X.yonedaPullbackLiftMap x φ) :=
    X.yonedaPullbackLiftMap_isHomLift x φ
  exact IsHomLift.fac' X.p φ.left (X.yonedaPullbackLiftMap x φ)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the chosen pullback
transition arrow attached to the identity slice morphism is the identity. -/
private theorem yonedaPullbackLiftMap_id
    {U : C} (x : X.p.Fiber U) (a : Over U) :
    X.yonedaPullbackLiftMap x (𝟙 a) = 𝟙 ((a.hom ^*[canonicalPullbackChoice X.p] x).1) := by
  -- Uniqueness against the identity candidate packages the identity law for the pullback lift.
  rcases X.yonedaPullbackLiftMap_existsUnique x (𝟙 a) with ⟨χ, hχ, hχuniq⟩
  have hChosen : X.yonedaPullbackLiftMap x (𝟙 a) = χ := by
    simpa [yonedaPullbackLiftMap] using
      hχuniq
        (Classical.choose (X.yonedaPullbackLiftMap_existsUnique x (𝟙 a)))
        (Classical.choose_spec (X.yonedaPullbackLiftMap_existsUnique x (𝟙 a))).1
  have hId : 𝟙 ((a.hom ^*[canonicalPullbackChoice X.p] x).1) = χ := by
    apply hχuniq
    constructor
    · change X.p.IsHomLift (𝟙 a.left) (𝟙 ((a.hom ^*[canonicalPullbackChoice X.p] x).1))
      exact IsHomLift.id (a.hom ^*[canonicalPullbackChoice X.p] x).2
    · simp
  exact hChosen.trans hId.symm

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the chosen pullback
transition arrows compose as expected along composable slice morphisms. -/
private theorem yonedaPullbackLiftMap_comp
    {U : C} (x : X.p.Fiber U) {a b c : Over U} (φ : a ⟶ b) (ψ : b ⟶ c) :
    X.yonedaPullbackLiftMap x (φ ≫ ψ) =
      X.yonedaPullbackLiftMap x φ ≫ X.yonedaPullbackLiftMap x ψ := by
  -- The composite arrow has the same universal property as the chosen lift of `φ ≫ ψ`.
  rcases X.yonedaPullbackLiftMap_existsUnique x (φ ≫ ψ) with ⟨χ, hχ, hχuniq⟩
  have hChosen : X.yonedaPullbackLiftMap x (φ ≫ ψ) = χ := by
    simpa [yonedaPullbackLiftMap] using
      hχuniq
        (Classical.choose (X.yonedaPullbackLiftMap_existsUnique x (φ ≫ ψ)))
        (Classical.choose_spec (X.yonedaPullbackLiftMap_existsUnique x (φ ≫ ψ))).1
  have hComp : X.yonedaPullbackLiftMap x φ ≫ X.yonedaPullbackLiftMap x ψ = χ := by
    apply hχuniq
    constructor
    · change X.p.IsHomLift (φ.left ≫ ψ.left)
        (X.yonedaPullbackLiftMap x φ ≫ X.yonedaPullbackLiftMap x ψ)
      letI : X.p.IsHomLift φ.left (X.yonedaPullbackLiftMap x φ) :=
        X.yonedaPullbackLiftMap_isHomLift x φ
      letI : X.p.IsHomLift ψ.left (X.yonedaPullbackLiftMap x ψ) :=
        X.yonedaPullbackLiftMap_isHomLift x ψ
      infer_instance
    · calc
        (X.yonedaPullbackLiftMap x φ ≫ X.yonedaPullbackLiftMap x ψ) ≫
            (canonicalPullbackChoice X.p).map c.hom x
            = X.yonedaPullbackLiftMap x φ ≫
                (X.yonedaPullbackLiftMap x ψ ≫ (canonicalPullbackChoice X.p).map c.hom x) := by
                  simp [Category.assoc]
        _ = X.yonedaPullbackLiftMap x φ ≫ (canonicalPullbackChoice X.p).map b.hom x := by
              rw [X.yonedaPullbackLiftMap_fac x ψ]
        _ = (canonicalPullbackChoice X.p).map a.hom x := by
              exact X.yonedaPullbackLiftMap_fac x φ
  exact hChosen.trans hComp.symm

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the textbook pullback
construction packaged as an ordinary functor to the total category. -/
private noncomputable def yonedaPullbackLiftToTotal
    {U : C} (x : X.p.Fiber U) :
    Over U ⥤ X.S where
  obj a := (a.hom ^*[canonicalPullbackChoice X.p] x).1
  map φ := X.yonedaPullbackLiftMap x φ
  map_id a := X.yonedaPullbackLiftMap_id x a
  map_comp φ ψ := X.yonedaPullbackLiftMap_comp x φ ψ

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the ordinary pullback functor
lies over the slice forgetful functor. -/
private theorem yonedaPullbackLiftToTotal_comp_eq_forget
    {U : C} (x : X.p.Fiber U) :
    X.yonedaPullbackLiftToTotal x ⋙ X.p = Over.forget U := by
  -- The chosen pullback objects and maps already record the needed base equalities.
  let hobj :
      ∀ a : Over U, (X.yonedaPullbackLiftToTotal x ⋙ X.p).obj a = (Over.forget U).obj a :=
    fun a ↦ (a.hom ^*[canonicalPullbackChoice X.p] x).2
  refine Functor.ext hobj ?_
  intro a b φ
  change X.p.map (X.yonedaPullbackLiftMap x φ) =
      eqToHom (hobj a) ≫ φ.left ≫ eqToHom (hobj b).symm
  simpa using X.yonedaPullbackLiftMap_base x φ

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the quasi-inverse object
attached to a fiber object, following the textbook pullback construction. -/
private noncomputable def yonedaPullbackLiftBasedFunctor
    {U : C} (x : X.p.Fiber U) :
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.toBasedCategory :=
  -- Package the already verified pullback transport functor together with its over-base equation.
  show BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.toBasedCategory from
    { toFunctor := X.yonedaPullbackLiftToTotal x
      w := X.yonedaPullbackLiftToTotal_comp_eq_forget x }

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): a morphism of fibred
categories sends a lift over `f` to a lift over the same base arrow `f`. -/
private theorem fibredCategoryMor_map_isHomLift_over_base
    {Y Z : FibredCategoryOver C} (F : Y ⟶ Z)
    {U V : C} {a b : Y.S} {f : U ⟶ V} {ψ : a ⟶ b}
    (hψ : Y.p.IsHomLift f ψ) :
    Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map ψ) := by
  -- The based-functor compatibility already transports the lifting equation along `F`.
  letI : Y.p.IsHomLift f ψ := hψ
  exact (show Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map ψ) from inferInstance)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): a morphism of fibred
categories sends a strongly cartesian morphism over `f` to a strongly cartesian morphism over the
same arrow `f`. -/
private theorem fibredCategoryMor_map_stronglyCartesian_over_base
    {Y Z : FibredCategoryOver C} (F : Y ⟶ Z)
    {U V : C} {a b : Y.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : Y.p.IsStronglyCartesian f φ) :
    Z.p.IsStronglyCartesian f ((FibredCategoryMor.toFunctor F).map φ) := by
  -- First rewrite the source owner statement to the owner-selected base map.
  have hφ' : Y.p.IsStronglyCartesian (Y.p.map φ) φ := by
    letI : Y.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift Y.p f φ
    simpa using hφ
  have hmap :
      Z.p.IsStronglyCartesian (Z.p.map ((FibredCategoryMor.toFunctor F).map φ))
        ((FibredCategoryMor.toFunctor F).map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  have hLift :
      Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) :=
    fibredCategoryMor_map_isHomLift_over_base (F := F) hφ.toIsHomLift
  letI : Z.p.IsHomLift f ((FibredCategoryMor.toFunctor F).map φ) := hLift
  -- Then rebase the target strong-cartesian structure back to the external arrow `f`.
  subst_hom_lift Z.p f ((FibredCategoryMor.toFunctor F).map φ)
  simpa using hmap

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the pullback-based functor
really preserves strongly cartesian arrows, so it packages to an owner morphism in `Fib/C`. -/
private theorem yonedaPullbackLiftBasedFunctor_preserves_strongly_cartesian
    {U : C} (x : X.p.Fiber U) :
    (X.yonedaPullbackLiftBasedFunctor x).PreservesStronglyCartesian := by
  intro a b φ _
  -- Route correction: first rebase the proved strong-cartesianness to the actual projected base
  -- map of the pullback-lift arrow, then forget the packaging of the based functor.
  have hstrong :
      X.p.IsStronglyCartesian φ.left (X.yonedaPullbackLiftMap x φ) :=
    X.yonedaPullbackLiftMap_isStronglyCartesian x φ
  have ha : X.p.obj ((a.hom ^*[canonicalPullbackChoice X.p] x).1) = a.left :=
    IsHomLift.domain_eq X.p φ.left (X.yonedaPullbackLiftMap x φ)
  have hb : X.p.obj ((b.hom ^*[canonicalPullbackChoice X.p] x).1) = b.left :=
    IsHomLift.codomain_eq X.p φ.left (X.yonedaPullbackLiftMap x φ)
  change X.p.IsStronglyCartesian (X.p.map (X.yonedaPullbackLiftMap x φ))
    (X.yonedaPullbackLiftMap x φ)
  rw [X.yonedaPullbackLiftMap_base x φ]
  refine
    { toIsHomLift := by
        refine IsHomLift.of_fac' X.p (eqToHom ha ≫ φ.left ≫ eqToHom hb.symm)
          (X.yonedaPullbackLiftMap x φ) rfl rfl ?_
        simpa [Category.assoc] using X.yonedaPullbackLiftMap_base x φ
      universal_property' := ?_ }
  intro z g ψ hψ
  have hψext :
      X.p.IsHomLift ((g ≫ eqToHom ha) ≫ φ.left) ψ := by
    refine IsHomLift.of_fac' X.p (((g ≫ eqToHom ha) ≫ φ.left)) ψ rfl hb ?_
    letI : X.p.IsHomLift (g ≫ (eqToHom ha ≫ φ.left ≫ eqToHom hb.symm)) ψ := hψ
    calc
      X.p.map ψ
          = eqToHom rfl ≫ (g ≫ (eqToHom ha ≫ φ.left ≫ eqToHom hb.symm)) ≫ eqToHom rfl.symm := by
              simpa using IsHomLift.fac' X.p
                (g ≫ (eqToHom ha ≫ φ.left ≫ eqToHom hb.symm)) ψ
      _ = eqToHom rfl ≫ (((g ≫ eqToHom ha) ≫ φ.left)) ≫ eqToHom hb.symm := by
            simp [Category.assoc]
  letI : X.p.IsHomLift ((g ≫ eqToHom ha) ≫ φ.left) ψ := hψext
  obtain ⟨χ, hχ, hχuniq⟩ :=
    IsStronglyCartesian.universal_property X.p φ.left (X.yonedaPullbackLiftMap x φ)
      (g ≫ eqToHom ha) (((g ≫ eqToHom ha) ≫ φ.left)) rfl ψ
  refine ⟨χ, ?_, ?_⟩
  · constructor
    · refine IsHomLift.of_fac' X.p g χ rfl rfl ?_
      letI : X.p.IsHomLift (g ≫ eqToHom ha) χ := hχ.1
      calc
        X.p.map χ
            = eqToHom rfl ≫ (g ≫ eqToHom ha) ≫ eqToHom ha.symm := by
                simpa using IsHomLift.fac' X.p (g ≫ eqToHom ha) χ
        _ = eqToHom rfl ≫ g ≫ eqToHom rfl.symm := by
              simp [Category.assoc]
    · exact hχ.2
  · intro τ hτ
    have hτext : X.p.IsHomLift (g ≫ eqToHom ha) τ := by
      refine IsHomLift.of_fac' X.p (g ≫ eqToHom ha) τ rfl ha ?_
      letI : X.p.IsHomLift g τ := hτ.1
      calc
        X.p.map τ
            = eqToHom rfl ≫ g ≫ eqToHom rfl.symm := by
                simpa using IsHomLift.fac' X.p g τ
        _ = eqToHom rfl ≫ (g ≫ eqToHom ha) ≫ eqToHom ha.symm := by
              simp [Category.assoc]
    exact hχuniq τ ⟨hτext, hτ.2⟩

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the textbook quasi-inverse on
objects of the fiber, packaged as a morphism of fibred categories over `C`. -/
private noncomputable def yonedaPullbackLiftObject
    {U : C} (x : X.p.Fiber U) :
    FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X :=
  -- The owner morphism is exactly the pullback functor once preservation of strongly cartesian
  -- arrows has been isolated in the adapter lemma above.
  FibredCategoryMor.ofBasedFunctor
    (X.yonedaPullbackLiftBasedFunctor x)
    (X.yonedaPullbackLiftBasedFunctor_preserves_strongly_cartesian x)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): convert a based natural
transformation into the corresponding morphism in the owner hom-category of fibred categories. -/
private abbrev fibredCategoryMorHomOfBasedNatTrans
    {Y Z : FibredCategoryOver C}
    {F G : Y ⟶ Z}
    (η : FibredCategoryMor.toBasedFunctor F ⟶ FibredCategoryMor.toBasedFunctor G) :
    F ⟶ G :=
  ⟨ObjectProperty.homMk η, trivial⟩

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): forgetting the owner wrapper
around a morphism built from a based natural transformation recovers the original transformation. -/
@[simp] private theorem fibredCategoryMorHomOfBasedNatTrans_hom_hom
    {Y Z : FibredCategoryOver C}
    {F G : Y ⟶ Z}
    (η : FibredCategoryMor.toBasedFunctor F ⟶ FibredCategoryMor.toBasedFunctor G) :
    (fibredCategoryMorHomOfBasedNatTrans η).hom.hom = η :=
  rfl

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): an isomorphism of underlying
based functors yields the corresponding owner isomorphism of fibred-category morphisms. -/
private noncomputable def fibredCategoryMorIsoOfBasedFunctorIso
    {Y Z : FibredCategoryOver C}
    {F G : Y ⟶ Z}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the map induced by the chosen
pullback functor factors through the chosen pullback arrow in the expected way. -/
private theorem canonicalPullbackFunctor_map_fac
    {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U} (α : x ⟶ y) :
    (((canonicalPullbackChoice X.p).pullbackFunctor f).map α).1 ≫
        (canonicalPullbackChoice X.p).map f y =
      (canonicalPullbackChoice X.p).map f x ≫ α.1 := by
  -- Unfold the pullback map as the universal arrow induced by strong cartesianness.
  letI : X.p.IsHomLift (𝟙 U) α.1 := α.2
  letI : X.p.IsHomLift f ((canonicalPullbackChoice X.p).map f x) :=
    X.canonicalPullbackChoice_map_isHomLift f x
  letI : X.p.IsHomLift f ((canonicalPullbackChoice X.p).map f x ≫ α.1) :=
    IsHomLift.comp_lift_id_right' X.p f ((canonicalPullbackChoice X.p).map f x) U α.1
  letI : X.p.IsStronglyCartesian f ((canonicalPullbackChoice X.p).map f y) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian f y
  change
      IsStronglyCartesian.map X.p f ((canonicalPullbackChoice X.p).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice X.p).map f x ≫ α.1) ≫
          (canonicalPullbackChoice X.p).map f y =
        (canonicalPullbackChoice X.p).map f x ≫ α.1
  simpa using
    (IsStronglyCartesian.fac X.p f ((canonicalPullbackChoice X.p).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice X.p).map f x ≫ α.1))

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the pullback maps attached to
`α : x ⟶ y` are natural with respect to the slice-transition maps used in the reconstruction
functor. -/
private theorem yonedaReconstructionBasedNatTrans_naturality
    {U : C} {x y : X.p.Fiber U} (α : x ⟶ y)
    {a b : Over U} (φ : a ⟶ b) :
    X.yonedaPullbackLiftMap x φ ≫
        (((canonicalPullbackChoice X.p).pullbackFunctor b.hom).map α).1 =
      (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫
        X.yonedaPullbackLiftMap y φ := by
  -- Compare the two candidate morphisms only after postcomposing with the chosen strongly
  -- cartesian pullback arrow of `b.hom`.
  let ψ :=
    X.yonedaPullbackLiftMap x φ ≫
      (((canonicalPullbackChoice X.p).pullbackFunctor b.hom).map α).1
  let ψ' :=
    (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫
      X.yonedaPullbackLiftMap y φ
  have hψ :
      X.p.IsHomLift φ.left ψ := by
    dsimp [ψ]
    letI : X.p.IsHomLift φ.left (X.yonedaPullbackLiftMap x φ) :=
      X.yonedaPullbackLiftMap_isHomLift x φ
    letI : X.p.IsHomLift (𝟙 b.left)
        (((canonicalPullbackChoice X.p).pullbackFunctor b.hom).map α).1 :=
      (((canonicalPullbackChoice X.p).pullbackFunctor b.hom).map α).2
    let hcomp :
        X.p.IsHomLift φ.left
          (X.yonedaPullbackLiftMap x φ ≫
            (((canonicalPullbackChoice X.p).pullbackFunctor b.hom).map α).1) := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        φ.left (X.yonedaPullbackLiftMap x φ)
        (X.yonedaPullbackLiftMap_isHomLift x φ)
        b.left (((canonicalPullbackChoice X.p).pullbackFunctor b.hom).map α).1
        (((canonicalPullbackChoice X.p).pullbackFunctor b.hom).map α).2
    simpa using hcomp
  have hψ' :
      X.p.IsHomLift φ.left ψ' := by
    dsimp [ψ']
    letI : X.p.IsHomLift (𝟙 a.left)
        (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 :=
      (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).2
    letI : X.p.IsHomLift φ.left (X.yonedaPullbackLiftMap y φ) :=
      X.yonedaPullbackLiftMap_isHomLift y φ
    let hcomp :
        X.p.IsHomLift φ.left
          ((((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫
            X.yonedaPullbackLiftMap y φ) := by
      exact @IsHomLift.comp_lift_id_left' _ _ _ _ X.p _ _ _
        a.left (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1
        (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).2
        _ _ φ.left (X.yonedaPullbackLiftMap y φ)
        (X.yonedaPullbackLiftMap_isHomLift y φ)
    simpa using hcomp
  refine
    @IsStronglyCartesian.ext _ _ _ _ X.p _ _ _ _
      b.hom ((canonicalPullbackChoice X.p).map b.hom y)
      ((canonicalPullbackChoice X.p).isStronglyCartesian b.hom y)
      _ _ φ.left ψ ψ' hψ hψ' ?_
  calc
    ψ ≫ (canonicalPullbackChoice X.p).map b.hom y
        = X.yonedaPullbackLiftMap x φ ≫
            ((((canonicalPullbackChoice X.p).pullbackFunctor b.hom).map α).1 ≫
              (canonicalPullbackChoice X.p).map b.hom y) := by
              dsimp [ψ]
              simp [Category.assoc]
    _ = X.yonedaPullbackLiftMap x φ ≫
          ((canonicalPullbackChoice X.p).map b.hom x ≫ α.1) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ X.yonedaPullbackLiftMap x φ ≫ k)
                (X.canonicalPullbackFunctor_map_fac b.hom α)
    _ = (X.yonedaPullbackLiftMap x φ ≫ (canonicalPullbackChoice X.p).map b.hom x) ≫ α.1 := by
          simp [Category.assoc]
    _ = (canonicalPullbackChoice X.p).map a.hom x ≫ α.1 := by
          rw [X.yonedaPullbackLiftMap_fac x φ]
    _ = (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫
          (canonicalPullbackChoice X.p).map a.hom y := by
            exact (X.canonicalPullbackFunctor_map_fac a.hom α).symm
    _ = ψ' ≫ (canonicalPullbackChoice X.p).map b.hom y := by
          calc
            (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫
                (canonicalPullbackChoice X.p).map a.hom y
                = (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫
                    (X.yonedaPullbackLiftMap y φ ≫
                      (canonicalPullbackChoice X.p).map b.hom y) := by
                        exact congrArg
                          (fun k ↦ (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫ k)
                          (X.yonedaPullbackLiftMap_fac y φ).symm
            _ = ψ' ≫ (canonicalPullbackChoice X.p).map b.hom y := by
                  dsimp [ψ']
                  simp [Category.assoc]

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the morphism part of the
textbook pullback reconstruction, packaged as a based natural transformation. -/
private noncomputable def yonedaReconstructionBasedNatTrans
    {U : C} {x y : X.p.Fiber U} (α : x ⟶ y) :
    FibredCategoryMor.toBasedFunctor (X.yonedaPullbackLiftObject x) ⟶
      FibredCategoryMor.toBasedFunctor (X.yonedaPullbackLiftObject y) where
  toNatTrans :=
    { app := fun a ↦ (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1
      naturality := by
        intro a b φ
        -- The naturality square is the pullback-functoriality square proved just above.
        exact X.yonedaReconstructionBasedNatTrans_naturality α φ }
  isHomLift' := fun a ↦ by
    -- Each pullback-functor component stays inside the fiber over `a.left`.
    change X.p.IsHomLift (𝟙 a.left)
      ((((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1)
    exact (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).2

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the textbook quasi-inverse
functor from the fiber `X_U` back to morphisms `C/U ⟶ X`. -/
private noncomputable def yonedaReconstructionFunctor (U : C) :
    X.p.Fiber U ⥤ (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) where
  obj x := X.yonedaPullbackLiftObject x
  map := fun {x y} α ↦
    ⟨ObjectProperty.homMk (X.yonedaReconstructionBasedNatTrans α), trivial⟩
  map_id x := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply BasedNatTrans.ext
    ext a
    -- Fiberwise, pullback along `a.hom` is functorial on identities.
    change ((((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map (𝟙 x)).1) =
      𝟙 (((a.hom ^*[canonicalPullbackChoice X.p] x).1))
    exact congrArg (fun k ↦ k.1) (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map_id x)
  map_comp α β := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply BasedNatTrans.ext
    ext a
    -- Fiberwise, pullback along `a.hom` is functorial on composition.
    change ((((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map (α ≫ β)).1) =
      ((((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫
        (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map β).1)
    exact congrArg (fun k ↦ k.1)
      (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map_comp α β)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): every morphism in the slice
category `C/U` is strongly cartesian for the projection `Over.forget U`. -/
private theorem over_hom_isStronglyCartesian
    {U : C} {a b : Over U} (φ : a ⟶ b) :
    (Over.forget U).IsStronglyCartesian φ.left φ := by
  -- The slice projection is fibred in groupoids, so every morphism is strongly cartesian.
  simpa using (show (Over.forget U).IsStronglyCartesian ((Over.forget U).map φ) φ from
    (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map φ)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the actual value of a morphism
`F : C/U ⟶ X` at `a : Over U`, regarded as an object of the fiber over `a.left`. -/
private noncomputable def yonedaReconstructionActualFiberObject
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    X.p.Fiber a.left :=
  ⟨(FibredCategoryMor.toFunctor F).obj a,
    congrArg (fun q ↦ q.obj a) (FibredCategoryMor.comm F)⟩

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the original object `F(a)` is
canonically isomorphic to the chosen pullback of `F(id_U)` along `a.hom`. -/
private noncomputable def yonedaReconstructionComponentIso
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    X.yonedaReconstructionActualFiberObject F a ≅
      (a.hom ^*[canonicalPullbackChoice X.p] ((X.yonedaEvaluationFunctor U).obj F)) := by
  -- Compare the actual map `F(a) ⟶ F(id_U)` with the chosen pullback arrow of `F(id_U)` along
  -- `a.hom`; both are strongly cartesian over the same base arrow.
  let φa : a ⟶ Over.mk (𝟙 U) := Over.homMk a.hom
  let hActual :
      X.p.IsStronglyCartesian a.hom
        ((FibredCategoryMor.toFunctor F).map φa) := by
    exact fibredCategoryMor_map_stronglyCartesian_over_base
      (Y := FibredCategoryOver.ofFunctor (Over.forget U))
      (Z := X)
      (F := F)
      (over_hom_isStronglyCartesian φa)
  let hChosen :
      X.p.IsStronglyCartesian a.hom
        ((canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F)) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian a.hom ((X.yonedaEvaluationFunctor U).obj F)
  let hActualCart :
      X.p.IsCartesian a.hom
        ((FibredCategoryMor.toFunctor F).map φa) :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := X.p) (f := a.hom) (φ := (FibredCategoryMor.toFunctor F).map φa)
  let hChosenCart :
      X.p.IsCartesian a.hom
        ((canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F)) :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := X.p) (f := a.hom)
      (φ := (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F))
  let e :=
    @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _ X.p _ _ _ _ a.hom
      ((canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F))
      hChosenCart
      _
      ((FibredCategoryMor.toFunctor F).map φa)
      hActualCart
  have hHomLift :
      X.p.IsHomLift (𝟙 a.left) e.hom := by
    simpa [e] using
      (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _
        X.p _ _ _ _ a.hom
        ((canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F))
        hChosenCart
        _
        ((FibredCategoryMor.toFunctor F).map φa)
        hActualCart)
  have hInvLift :
      X.p.IsHomLift (𝟙 a.left) e.inv := by
    simpa [e] using
      (@Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _
        X.p _ _ _ _ a.hom
        ((canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F))
        hChosenCart
        _
        ((FibredCategoryMor.toFunctor F).map φa)
        hActualCart)
  exact
    { hom := ⟨e.hom, hHomLift⟩
      inv := ⟨e.inv, hInvLift⟩
      hom_inv_id := by
        apply Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the hom of the comparison
isomorphism factors through the chosen pullback arrow exactly as the actual value of `F` on the
canonical map `a ⟶ id_U`. -/
@[reassoc]
private theorem yonedaReconstructionComponentIso_hom_fac
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    ((X.yonedaReconstructionComponentIso F a).hom).1 ≫
      (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F) =
        (FibredCategoryMor.toFunctor F).map (Over.homMk a.hom) := by
  -- Rebuild the comparison isomorphism from the two cartesian arrows whose domains it compares,
  -- then read off the defining factorization of its hom.
  let φa : a ⟶ Over.mk (𝟙 U) := Over.homMk a.hom
  let hActual :
      X.p.IsStronglyCartesian a.hom
        ((FibredCategoryMor.toFunctor F).map φa) := by
    exact fibredCategoryMor_map_stronglyCartesian_over_base
      (Y := FibredCategoryOver.ofFunctor (Over.forget U))
      (Z := X)
      (F := F)
      (over_hom_isStronglyCartesian φa)
  let hChosen :
      X.p.IsStronglyCartesian a.hom
        ((canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F)) :=
    (canonicalPullbackChoice X.p).isStronglyCartesian a.hom ((X.yonedaEvaluationFunctor U).obj F)
  let hActualCart :
      X.p.IsCartesian a.hom
        ((FibredCategoryMor.toFunctor F).map φa) :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := X.p) (f := a.hom) (φ := (FibredCategoryMor.toFunctor F).map φa)
  let hChosenCart :
      X.p.IsCartesian a.hom
        ((canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F)) :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := X.p) (f := a.hom)
      (φ := (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F))
  let e :=
    @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _ X.p _ _ _ _ a.hom
      ((canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F))
      hChosenCart
      _
      ((FibredCategoryMor.toFunctor F).map φa)
      hActualCart
  change e.hom ≫
      (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F) =
        (FibredCategoryMor.toFunctor F).map φa
  simpa [e] using
    (IsCartesian.fac (p := X.p) (f := a.hom)
      (φ := (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F))
      (φ' := (FibredCategoryMor.toFunctor F).map φa))

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the hom components of the
comparison isomorphisms are natural with respect to slice morphisms. -/
private theorem yonedaReconstructionComponentIso_hom_naturality
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X)
    {a b : Over U} (φ : a ⟶ b) :
    (FibredCategoryMor.toFunctor F).map φ ≫ ((X.yonedaReconstructionComponentIso F b).hom).1 =
      ((X.yonedaReconstructionComponentIso F a).hom).1 ≫
        X.yonedaPullbackLiftMap ((X.yonedaEvaluationFunctor U).obj F) φ := by
  -- Compare both candidate lifts only after postcomposing with the chosen pullback arrow of
  -- `b.hom`; the two resulting composites are both `F.map (a ⟶ id_U)`.
  let φa : a ⟶ Over.mk (𝟙 U) := Over.homMk a.hom
  let φb : b ⟶ Over.mk (𝟙 U) := Over.homMk b.hom
  have hφcomp : φ ≫ φb = φa := by
    apply Over.OverMorphism.ext
    simpa [φa, φb] using over_hom_left_comp_hom φ
  have hleft :
      X.p.IsHomLift φ.left
        ((FibredCategoryMor.toFunctor F).map φ ≫
          ((X.yonedaReconstructionComponentIso F b).hom).1) := by
    have hFφ : X.p.IsHomLift φ.left ((FibredCategoryMor.toFunctor F).map φ) := by
      exact fibredCategoryMor_map_isHomLift_over_base
        (F := F) (over_hom_isStronglyCartesian φ).toIsHomLift
    have hcomp :
        X.p.IsHomLift φ.left
          ((FibredCategoryMor.toFunctor F).map φ ≫
            ((X.yonedaReconstructionComponentIso F b).hom).1) := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        φ.left ((FibredCategoryMor.toFunctor F).map φ) hFφ
        b.left (((X.yonedaReconstructionComponentIso F b).hom).1)
        ((X.yonedaReconstructionComponentIso F b).hom).2
    simpa using hcomp
  have hright :
      X.p.IsHomLift φ.left
        (((X.yonedaReconstructionComponentIso F a).hom).1 ≫
          X.yonedaPullbackLiftMap ((X.yonedaEvaluationFunctor U).obj F) φ) := by
    have hcomp :
        X.p.IsHomLift φ.left
          (((X.yonedaReconstructionComponentIso F a).hom).1 ≫
            X.yonedaPullbackLiftMap ((X.yonedaEvaluationFunctor U).obj F) φ) := by
      exact @IsHomLift.comp_lift_id_left' _ _ _ _ X.p _ _ _
        a.left (((X.yonedaReconstructionComponentIso F a).hom).1)
        ((X.yonedaReconstructionComponentIso F a).hom).2
        _ _ φ.left
        (X.yonedaPullbackLiftMap ((X.yonedaEvaluationFunctor U).obj F) φ)
        (X.yonedaPullbackLiftMap_isHomLift ((X.yonedaEvaluationFunctor U).obj F) φ)
    simpa using hcomp
  refine
    @IsStronglyCartesian.ext _ _ _ _ X.p _ _ _ _
      b.hom
      ((canonicalPullbackChoice X.p).map b.hom ((X.yonedaEvaluationFunctor U).obj F))
      ((canonicalPullbackChoice X.p).isStronglyCartesian b.hom ((X.yonedaEvaluationFunctor U).obj F))
      _ _ φ.left
      ((FibredCategoryMor.toFunctor F).map φ ≫ ((X.yonedaReconstructionComponentIso F b).hom).1)
      (((X.yonedaReconstructionComponentIso F a).hom).1 ≫
        X.yonedaPullbackLiftMap ((X.yonedaEvaluationFunctor U).obj F) φ)
      hleft hright ?_
  let lhs :=
    (FibredCategoryMor.toFunctor F).map φ ≫ ((X.yonedaReconstructionComponentIso F b).hom).1
  let rhs :=
    ((X.yonedaReconstructionComponentIso F a).hom).1 ≫
      X.yonedaPullbackLiftMap ((X.yonedaEvaluationFunctor U).obj F) φ
  let chosenB := (canonicalPullbackChoice X.p).map b.hom ((X.yonedaEvaluationFunctor U).obj F)
  let chosenA := (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F)
  have hpost₁ : lhs ≫ chosenB =
      (FibredCategoryMor.toFunctor F).map φ ≫ (FibredCategoryMor.toFunctor F).map φb := by
    dsimp [lhs, chosenB]
    simpa [Category.assoc] using
      congrArg (fun k ↦ (FibredCategoryMor.toFunctor F).map φ ≫ k)
        (X.yonedaReconstructionComponentIso_hom_fac F b)
  have hpost₂ :
      (FibredCategoryMor.toFunctor F).map φ ≫ (FibredCategoryMor.toFunctor F).map φb =
        (FibredCategoryMor.toFunctor F).map φa := by
    exact
      (Functor.map_comp (FibredCategoryMor.toFunctor F) φ φb).symm.trans
        (congrArg (fun k ↦ (FibredCategoryMor.toFunctor F).map k) hφcomp)
  have hpost₃ :
      (FibredCategoryMor.toFunctor F).map φa =
        ((X.yonedaReconstructionComponentIso F a).hom).1 ≫ chosenA := by
    simpa [chosenA] using (X.yonedaReconstructionComponentIso_hom_fac F a).symm
  have hpost₄ :
      ((X.yonedaReconstructionComponentIso F a).hom).1 ≫ chosenA = rhs ≫ chosenB := by
    dsimp [rhs, chosenA, chosenB]
    calc
      ((X.yonedaReconstructionComponentIso F a).hom).1 ≫
          (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F)
          = ((X.yonedaReconstructionComponentIso F a).hom).1 ≫
              (X.yonedaPullbackLiftMap ((X.yonedaEvaluationFunctor U).obj F) φ ≫
                (canonicalPullbackChoice X.p).map b.hom ((X.yonedaEvaluationFunctor U).obj F)) := by
                  exact congrArg
                    (fun k ↦ ((X.yonedaReconstructionComponentIso F a).hom).1 ≫ k)
                    (X.yonedaPullbackLiftMap_fac ((X.yonedaEvaluationFunctor U).obj F) φ).symm
      _ = (((X.yonedaReconstructionComponentIso F a).hom).1 ≫
            X.yonedaPullbackLiftMap ((X.yonedaEvaluationFunctor U).obj F) φ) ≫
              (canonicalPullbackChoice X.p).map b.hom ((X.yonedaEvaluationFunctor U).obj F) := by
            simp [Category.assoc]
  exact hpost₁.trans (hpost₂.trans (hpost₃.trans hpost₄))

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the component comparison
isomorphisms are also natural with respect to owner morphisms `τ : F ⟶ G`. -/
private theorem yonedaReconstruction_unit_component_naturality
    {U : C}
    {F G : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X}
    (τ : F ⟶ G) (a : Over U) :
    τ.hom.hom.app a ≫ ((X.yonedaReconstructionComponentIso G a).hom).1 =
      ((X.yonedaReconstructionComponentIso F a).hom).1 ≫
        (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map
          ((X.yonedaEvaluationFunctor U).map τ)).1 := by
  -- Compare the two vertical candidates only after postcomposing with the chosen pullback arrow
  -- of `a.hom`; then both sides become the naturality square of `τ` at `a ⟶ id_U`.
  let φa : a ⟶ Over.mk (𝟙 U) := Over.homMk a.hom
  let α : (X.yonedaEvaluationFunctor U).obj F ⟶ (X.yonedaEvaluationFunctor U).obj G :=
    (X.yonedaEvaluationFunctor U).map τ
  let lhs := τ.hom.hom.app a ≫ ((X.yonedaReconstructionComponentIso G a).hom).1
  let rhs :=
    ((X.yonedaReconstructionComponentIso F a).hom).1 ≫
      (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1
  let chosenG := (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj G)
  let chosenF := (canonicalPullbackChoice X.p).map a.hom ((X.yonedaEvaluationFunctor U).obj F)
  have hleft :
      X.p.IsHomLift (𝟙 a.left) lhs := by
    have hτ :
        X.p.IsHomLift (𝟙 a.left) (τ.hom.hom.app a) := by
      exact fibredCategoryMor_hom_isHomLift_id τ a
    have hcomp :
        X.p.IsHomLift (𝟙 a.left)
          (τ.hom.hom.app a ≫ ((X.yonedaReconstructionComponentIso G a).hom).1) := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        (𝟙 a.left) (τ.hom.hom.app a) hτ
        a.left (((X.yonedaReconstructionComponentIso G a).hom).1)
        ((X.yonedaReconstructionComponentIso G a).hom).2
    change
      X.p.IsHomLift (𝟙 a.left)
        (τ.hom.hom.app a ≫ ((X.yonedaReconstructionComponentIso G a).hom).1)
    exact hcomp
  have hright :
      X.p.IsHomLift (𝟙 a.left) rhs := by
    have hcomp :
        X.p.IsHomLift (𝟙 a.left)
          (((X.yonedaReconstructionComponentIso F a).hom).1 ≫
            (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1) := by
      exact @IsHomLift.comp_lift_id_left' _ _ _ _ X.p _ _ _
        a.left (((X.yonedaReconstructionComponentIso F a).hom).1)
        ((X.yonedaReconstructionComponentIso F a).hom).2
        _ _ (𝟙 a.left)
        (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1
        (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).2
    change
      X.p.IsHomLift (𝟙 a.left)
        (((X.yonedaReconstructionComponentIso F a).hom).1 ≫
          (((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1)
    exact hcomp
  refine
    @IsStronglyCartesian.ext _ _ _ _ X.p _ _ _ _
      a.hom chosenG
      ((canonicalPullbackChoice X.p).isStronglyCartesian a.hom ((X.yonedaEvaluationFunctor U).obj G))
      _ _ (𝟙 a.left) lhs rhs hleft hright ?_
  have hpost₁ :
      lhs ≫ chosenG = τ.hom.hom.app a ≫ (FibredCategoryMor.toFunctor G).map φa := by
    calc
      lhs ≫ chosenG
          = τ.hom.hom.app a ≫ (((X.yonedaReconstructionComponentIso G a).hom).1 ≫ chosenG) := by
              show
                (τ.hom.hom.app a ≫ ((X.yonedaReconstructionComponentIso G a).hom).1) ≫ chosenG =
                  τ.hom.hom.app a ≫
                    (((X.yonedaReconstructionComponentIso G a).hom).1 ≫ chosenG)
              rw [Category.assoc]
      _ = τ.hom.hom.app a ≫ (FibredCategoryMor.toFunctor G).map φa := by
            exact congrArg (fun k ↦ τ.hom.hom.app a ≫ k)
              (X.yonedaReconstructionComponentIso_hom_fac G a)
  have hEval :
      α.1 = τ.hom.hom.app (Over.mk (𝟙 U)) := by
    rfl
  have hpost₂ :
      τ.hom.hom.app a ≫ (FibredCategoryMor.toFunctor G).map φa =
        (FibredCategoryMor.toFunctor F).map φa ≫ α.1 := by
    simpa only [hEval] using ((τ.hom.hom).naturality φa).symm
  have hpost₃ :
      (FibredCategoryMor.toFunctor F).map φa ≫ α.1 = rhs ≫ chosenG := by
    calc
      (FibredCategoryMor.toFunctor F).map φa ≫ α.1
          = (((X.yonedaReconstructionComponentIso F a).hom).1 ≫ chosenF) ≫ α.1 := by
              exact congrArg (fun k ↦ k ≫ α.1)
                (X.yonedaReconstructionComponentIso_hom_fac F a).symm
      _ = ((X.yonedaReconstructionComponentIso F a).hom).1 ≫ (chosenF ≫ α.1) := by
            simp [Category.assoc]
      _ = ((X.yonedaReconstructionComponentIso F a).hom).1 ≫
            ((((canonicalPullbackChoice X.p).pullbackFunctor a.hom).map α).1 ≫ chosenG) := by
              exact congrArg
                (fun k ↦ ((X.yonedaReconstructionComponentIso F a).hom).1 ≫ k)
                (X.canonicalPullbackFunctor_map_fac a.hom α).symm
      _ = rhs ≫ chosenG := by
            simp [rhs, Category.assoc]
  exact hpost₁.trans (hpost₂.trans hpost₃)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the fiber comparison
isomorphism viewed in the total based category. -/
private noncomputable def yonedaReconstructionComponentBasedIso
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (FibredCategoryMor.toBasedFunctor F).obj a ≅
      (FibredCategoryMor.toBasedFunctor
        ((X.yonedaReconstructionFunctor U).obj ((X.yonedaEvaluationFunctor U).obj F))).obj a :=
  Functor.mapIso (Functor.Fiber.fiberInclusion :
    X.p.Fiber a.left ⥤ X.S) (X.yonedaReconstructionComponentIso F a)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the component comparison
isomorphisms are natural as morphisms in the total based category. -/
private theorem yonedaReconstruction_unitBasedFunctorIso_naturality
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X)
    {a b : Over U} (φ : a ⟶ b) :
    (FibredCategoryMor.toBasedFunctor F).map φ ≫
        (X.yonedaReconstructionComponentBasedIso F b).hom =
      (X.yonedaReconstructionComponentBasedIso F a).hom ≫
        (FibredCategoryMor.toBasedFunctor
          ((X.yonedaReconstructionFunctor U).obj ((X.yonedaEvaluationFunctor U).obj F))).map φ := by
  -- This is the same raw-arrow equality as the slice-object naturality proved above.
  simpa only [yonedaReconstructionComponentBasedIso, yonedaReconstructionFunctor,
    yonedaPullbackLiftObject, yonedaPullbackLiftBasedFunctor, yonedaPullbackLiftToTotal] using
    X.yonedaReconstructionComponentIso_hom_naturality F φ

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): each based-unit component lies
over the identity on the source object of the slice. -/
private theorem yonedaReconstructionComponentBasedIso_isHomLift
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    X.p.IsHomLift (𝟙 a.left) (X.yonedaReconstructionComponentBasedIso F a).hom := by
  change X.p.IsHomLift (𝟙 a.left) ((X.yonedaReconstructionComponentIso F a).hom).1
  exact ((X.yonedaReconstructionComponentIso F a).hom).2

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the objectwise comparison
isomorphisms package into an isomorphism of the underlying based functors. -/
private noncomputable def yonedaReconstruction_unitBasedFunctorIso
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    FibredCategoryMor.toBasedFunctor F ≅
      FibredCategoryMor.toBasedFunctor
        ((X.yonedaReconstructionFunctor U).obj ((X.yonedaEvaluationFunctor U).obj F)) := by
  -- The slice-object naturality already proved above is exactly the naturality needed for the
  -- based-functor comparison.
  refine BasedNatIso.mkNatIso ?_ ?_
  · refine NatIso.ofComponents (fun a ↦ X.yonedaReconstructionComponentBasedIso F a) ?_
    intro a b φ
    exact X.yonedaReconstruction_unitBasedFunctorIso_naturality F φ
  · intro a
    exact X.yonedaReconstructionComponentBasedIso_isHomLift F a

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the unit component on the
owner hom-category is obtained by lifting the based-functor comparison. -/
private noncomputable def yonedaReconstruction_unitIso_app
    {U : C} (F : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    F ≅ (X.yonedaEvaluationFunctor U ⋙ X.yonedaReconstructionFunctor U).obj F :=
  fibredCategoryMorIsoOfBasedFunctorIso
    (F := F)
    (G := (X.yonedaReconstructionFunctor U).obj ((X.yonedaEvaluationFunctor U).obj F))
    (X.yonedaReconstruction_unitBasedFunctorIso F)

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the owner-level unit
comparison is natural in morphisms `τ : F ⟶ G`. -/
private theorem yonedaReconstruction_unitIso_naturality
    {U : C} {F G : FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X} (τ : F ⟶ G) :
    (𝟭 (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X)).map τ ≫
        (X.yonedaReconstruction_unitIso_app G).hom =
      (X.yonedaReconstruction_unitIso_app F).hom ≫
        (X.yonedaEvaluationFunctor U ⋙ X.yonedaReconstructionFunctor U).map τ := by
  -- The owner category equality is detected on the underlying based natural transformations.
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply BasedNatTrans.ext
  ext a
  simpa only [yonedaReconstruction_unitIso_app, fibredCategoryMorIsoOfBasedFunctorIso,
    yonedaReconstruction_unitBasedFunctorIso, yonedaReconstructionComponentBasedIso,
    yonedaReconstructionFunctor, yonedaReconstructionBasedNatTrans, yonedaPullbackLiftObject,
    yonedaPullbackLiftBasedFunctor, yonedaPullbackLiftToTotal] using
    X.yonedaReconstruction_unit_component_naturality τ a

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the reconstruction functor is
left inverse to evaluation at `id_U` on the owner hom-category. -/
private noncomputable def yonedaReconstruction_unitIso
    (U : C) :
    𝟭 (FibredCategoryOver.ofFunctor (Over.forget U) ⟶ X) ≅
      X.yonedaEvaluationFunctor U ⋙ X.yonedaReconstructionFunctor U := by
  -- Route correction: instead of trying to package owner-level data first, build the based-functor
  -- isomorphism objectwise and then lift it through the owner wrapper.
  refine NatIso.ofComponents (fun F ↦ X.yonedaReconstruction_unitIso_app F) ?_
  intro F G τ
  exact X.yonedaReconstruction_unitIso_naturality τ

/-- Helper for Lemma 4.41.1 (2-Yoneda lemma for fibred categories): on the fiber side, evaluating
the reconstructed morphism at `id_U` is exactly the chosen identity pullback, so the counit is the
standard `pullbackIdIso`. -/
private noncomputable def yonedaEvaluation_counitIso
    (U : C) :
    X.yonedaReconstructionFunctor U ⋙ X.yonedaEvaluationFunctor U ≅ 𝟭 (X.p.Fiber U) := by
  -- The reconstruction sends `x` to pullback along each map into `U`, hence evaluation at `id_U`
  -- is just pullback along `𝟙 U`.
  simpa [yonedaReconstructionFunctor, yonedaEvaluationFunctor, yonedaPullbackLiftObject,
    yonedaPullbackLiftBasedFunctor, yonedaPullbackLiftToTotal] using
      ((canonicalPullbackChoice X.p).pullbackIdIso U).symm

-- Proof sketch: choose pullbacks for `X.p` as in Definition 4.33.6. For `x : X_U`, send an
-- object `f : V ⟶ U` of `C/U` to the chosen pullback `f^*x`; Lemma 4.33.7 supplies the
-- comparison isomorphisms needed for functoriality. One then checks that this construction is
-- inverse, up to natural isomorphism, to evaluation at `id_U`.
/-- Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the evaluation functor
`Mor_{Fib/C}(C/U, X) ⥤ X_U`, sending `G` to `G(id_U)`, is an equivalence. -/
noncomputable instance yonedaEvaluationFunctor_isEquivalence (U : C) :
    (X.yonedaEvaluationFunctor U).IsEquivalence := by
  -- The unit comes from the objectwise comparison `F(a) ≅ a.hom^*F(id_U)`, and the counit is the
  -- identity-pullback comparison on the fiber over `U`.
  exact Functor.IsEquivalence.mk'
    (X.yonedaReconstructionFunctor U)
    (yonedaReconstruction_unitIso (X := X) U)
    (X.yonedaEvaluation_counitIso U)

end FibredCategoryOver

end CategoryTheory
