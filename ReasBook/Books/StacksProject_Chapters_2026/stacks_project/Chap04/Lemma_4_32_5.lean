module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import stacks_project.Chap04.Definition_4_32_1
public import stacks_project.Chap04.Definition_4_32_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback

universe u v uX uY uS

namespace CategoryTheory
namespace CategoryOver

/- Domain-style sampling for Lemma 4.32.5:
- primary domain: categories over a fixed base, standard fibres, and the source-facing `2`-fibre
  product over `C`;
- sampled owner-level declarations:
  `BasedCategory`,
  `BasedFunctor.fiberFunctor`,
  `Functor.Fiber`,
  `CategoricalPullback`,
  `CategoricalPullback.CatCommSqOver`;
- best owner abstraction: the source-facing over-`C` pullback is the explicit category whose
  objects are base points `U : C` together with fibrewise pullback objects
  `CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)`;
- primitive data: the based functors `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S`;
- derived API: the bundled category over `C`, its two projection functors, its comparison
  isomorphism over `S`, and the fibrewise equivalence over a fixed `U`.

Source/core/bridge triage:
- `source-facing`: `ExplicitTwoFibreProductObject`, `ExplicitTwoFibreProductHom`, and
  `explicitTwoFibreProduct`;
- `core/canonical`: `Functor.Fiber`, `BasedFunctor.fiberFunctor`, and `CategoricalPullback`;
- `bridge/view`: `explicitTwoFibreProductSquareOver` and
  `fibreOfPullback_equiv_pullbackOfFibres`. -/

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{v, uX} C}
variable {Y : BasedCategory.{v, uY} C}
variable {S : BasedCategory.{v, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

/-- An object of the explicit `2`-fibre product over `C` is a base object `U : C` together with
an object of the fibrewise categorical pullback `X_U ×_{S_U} Y_U`. -/
structure ExplicitTwoFibreProductObject where
  /-- The chosen base object `U` of `C`. -/
  U : C
  /-- The canonical pullback object `(x, y, f)` in the fibre categories over `U`. -/
  obj : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)

namespace ExplicitTwoFibreProductObject

/-- The canonical comparison morphism in `S` carried by an object of the explicit `2`-fibre
product. -/
abbrev comparison
    (P : ExplicitTwoFibreProductObject F G) :
    F.obj P.obj.fst.1 ⟶ G.obj P.obj.snd.1 :=
  match P with
  | ⟨_, ⟨_, _, i⟩⟩ => i.hom.1

/-- The canonical comparison morphism of an explicit `2`-fibre-product object lies over the
identity of the chosen base object. -/
theorem comparison_over
    (P : ExplicitTwoFibreProductObject F G) :
    S.p.IsHomLift (𝟙 P.U) P.comparison :=
  match P with
  | ⟨_, ⟨_, _, i⟩⟩ => i.hom.2

end ExplicitTwoFibreProductObject

/-- A morphism in the explicit `2`-fibre product is a pair of morphisms in `X` and `Y`
lying over a common base morphism in `C` and compatible with the comparison isomorphisms in `S`. -/
structure ExplicitTwoFibreProductHom
    (P Q : ExplicitTwoFibreProductObject F G) where
  /-- The common base morphism in `C`. -/
  base : P.U ⟶ Q.U
  /-- The morphism on the `X`-component. -/
  a : P.obj.fst.1 ⟶ Q.obj.fst.1
  /-- The `X`-component lies over the common base morphism. -/
  a_over : X.p.IsHomLift base a
  /-- The morphism on the `Y`-component. -/
  b : P.obj.snd.1 ⟶ Q.obj.snd.1
  /-- The `Y`-component lies over the same common base morphism. -/
  b_over : Y.p.IsHomLift base b
  /-- The square relating `F(a)` and `G(b)` commutes. -/
  comm : CommSq (F.toFunctor.map a) P.comparison Q.comparison (G.toFunctor.map b)

attribute [instance] ExplicitTwoFibreProductHom.a_over ExplicitTwoFibreProductHom.b_over

namespace ExplicitTwoFibreProductHom

/-- Morphisms in the explicit `2`-fibre product are determined by their two fibrewise
components. The common base arrow is forced by either lift condition. -/
@[ext] theorem ext
    {P Q : ExplicitTwoFibreProductObject F G}
    (φ ψ : ExplicitTwoFibreProductHom F G P Q)
    (ha : φ.a = ψ.a) (hb : φ.b = ψ.b) :
    φ = ψ := by
  have hbase : φ.base = ψ.base := by
    calc
      φ.base =
          eqToHom P.obj.fst.2.symm ≫ X.p.map φ.a ≫ eqToHom Q.obj.fst.2 :=
        IsHomLift.fac X.p φ.base φ.a
      _ = eqToHom P.obj.fst.2.symm ≫ X.p.map ψ.a ≫ eqToHom Q.obj.fst.2 := by
          simp [ha]
      _ = ψ.base := by simpa using (IsHomLift.fac X.p ψ.base ψ.a).symm
  cases φ
  cases ψ
  cases hbase
  cases ha
  cases hb
  rfl

end ExplicitTwoFibreProductHom

/-- The defining square for the identity morphism in the explicit `2`-fibre product commutes. -/
theorem explicitTwoFibreProductHom_id_comm
    (P : ExplicitTwoFibreProductObject F G) :
    CommSq
      (F.toFunctor.map (𝟙 P.obj.fst.1))
      P.comparison
      P.comparison
      (G.toFunctor.map (𝟙 P.obj.snd.1)) := by
  refine ⟨?_⟩
  simp [ExplicitTwoFibreProductObject.comparison]

/-- The identity morphism in the explicit `2`-fibre product. -/
def explicitTwoFibreProductHom_id
    (P : ExplicitTwoFibreProductObject F G) :
    ExplicitTwoFibreProductHom F G P P :=
  { base := 𝟙 P.U
    a := 𝟙 P.obj.fst.1
    a_over := IsHomLift.id P.obj.fst.2
    b := 𝟙 P.obj.snd.1
    b_over := IsHomLift.id P.obj.snd.2
    comm := explicitTwoFibreProductHom_id_comm F G P }

/-- The defining square remains commutative after composing two morphisms in the explicit
`2`-fibre product. -/
theorem explicitTwoFibreProductHom_comp_comm
    {P Q R : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q)
    (ψ : ExplicitTwoFibreProductHom F G Q R) :
    CommSq (F.toFunctor.map (φ.a ≫ ψ.a)) P.comparison R.comparison
      (G.toFunctor.map (φ.b ≫ ψ.b)) := by
  simpa [Functor.map_comp] using CommSq.horiz_comp φ.comm ψ.comm

/-- Composition in the explicit `2`-fibre product. -/
def explicitTwoFibreProductHom_comp
    {P Q R : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q)
    (ψ : ExplicitTwoFibreProductHom F G Q R) :
    ExplicitTwoFibreProductHom F G P R :=
  { base := φ.base ≫ ψ.base
    a := φ.a ≫ ψ.a
    a_over := by infer_instance
    b := φ.b ≫ ψ.b
    b_over := by infer_instance
    comm := explicitTwoFibreProductHom_comp_comm F G φ ψ }

/-- Left identity for the explicit `2`-fibre-product composition law. -/
theorem explicitTwoFibreProductHom_id_comp
    {P Q : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q) :
    explicitTwoFibreProductHom_comp F G (explicitTwoFibreProductHom_id F G P) φ = φ := by
  apply ExplicitTwoFibreProductHom.ext
  · simp [explicitTwoFibreProductHom_comp, explicitTwoFibreProductHom_id]
  · simp [explicitTwoFibreProductHom_comp, explicitTwoFibreProductHom_id]

/-- Right identity for the explicit `2`-fibre-product composition law. -/
theorem explicitTwoFibreProductHom_comp_id
    {P Q : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q) :
    explicitTwoFibreProductHom_comp F G φ (explicitTwoFibreProductHom_id F G Q) = φ := by
  apply ExplicitTwoFibreProductHom.ext
  · simp [explicitTwoFibreProductHom_comp, explicitTwoFibreProductHom_id]
  · simp [explicitTwoFibreProductHom_comp, explicitTwoFibreProductHom_id]

/-- Associativity for the explicit `2`-fibre-product composition law. -/
theorem explicitTwoFibreProductHom_assoc
    {P Q R T : ExplicitTwoFibreProductObject F G}
    (φ : ExplicitTwoFibreProductHom F G P Q)
    (ψ : ExplicitTwoFibreProductHom F G Q R)
    (χ : ExplicitTwoFibreProductHom F G R T) :
    explicitTwoFibreProductHom_comp F G (explicitTwoFibreProductHom_comp F G φ ψ) χ =
      explicitTwoFibreProductHom_comp F G φ (explicitTwoFibreProductHom_comp F G ψ χ) := by
  apply ExplicitTwoFibreProductHom.ext
  · simp [explicitTwoFibreProductHom_comp]
  · simp [explicitTwoFibreProductHom_comp]

/-- The objects and morphisms described in Lemma 4.32.5 form a category. -/
instance explicitTwoFibreProductCategory :
    Category (ExplicitTwoFibreProductObject F G) where
  Hom P Q := ExplicitTwoFibreProductHom F G P Q
  id := explicitTwoFibreProductHom_id F G
  comp φ ψ := explicitTwoFibreProductHom_comp F G φ ψ
  id_comp := explicitTwoFibreProductHom_id_comp F G
  comp_id := explicitTwoFibreProductHom_comp_id F G
  assoc φ ψ χ := explicitTwoFibreProductHom_assoc F G φ ψ χ

/-- The projection from the explicit `2`-fibre product to the base category `C`. -/
abbrev explicitTwoFibreProductBaseFunctor :
    ExplicitTwoFibreProductObject F G ⥤ C :=
  { obj := fun P ↦ P.U
    map := fun φ ↦ φ.base
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The projection from the explicit `2`-fibre product to the left total category. -/
abbrev explicitTwoFibreProductLeftFunctor :
    ExplicitTwoFibreProductObject F G ⥤ X.obj :=
  { obj := fun P ↦ P.obj.fst.1
    map := fun φ ↦ φ.a
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The projection from the explicit `2`-fibre product to the right total category. -/
abbrev explicitTwoFibreProductRightFunctor :
    ExplicitTwoFibreProductObject F G ⥤ Y.obj :=
  { obj := fun P ↦ P.obj.snd.1
    map := fun φ ↦ φ.b
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The left projection composed with the structure map to `C` recovers the base projection of
the explicit `2`-fibre product. -/
theorem explicitTwoFibreProductLeftFunctor_comm :
    explicitTwoFibreProductLeftFunctor F G ⋙ X.p =
      explicitTwoFibreProductBaseFunctor F G := by
  exact Functor.ext (fun P ↦ P.obj.fst.2) (fun P Q φ ↦ by
    simpa using (IsHomLift.fac' X.p φ.base φ.a))

/-- The right projection composed with the structure map to `C` recovers the base projection of
the explicit `2`-fibre product. -/
theorem explicitTwoFibreProductRightFunctor_comm :
    explicitTwoFibreProductRightFunctor F G ⋙ Y.p =
      explicitTwoFibreProductBaseFunctor F G := by
  exact Functor.ext (fun P ↦ P.obj.snd.2) (fun P Q φ ↦ by
    simpa using (IsHomLift.fac' Y.p φ.base φ.b))

/-- The canonical comparison isomorphism `F ∘ p ≅ G ∘ q` on the explicit `2`-fibre product. -/
def explicitTwoFibreProductComparisonNatIso :
    explicitTwoFibreProductLeftFunctor F G ⋙ F.toFunctor ≅
      explicitTwoFibreProductRightFunctor F G ⋙ G.toFunctor :=
  NatIso.ofComponents
    (fun P ↦
      (fiberInclusion : Functor.Fiber S.p P.U ⥤ S.obj).mapIso P.obj.iso)
    (fun {_ _} φ ↦ φ.comm.w)

/-- The explicit `2`-fibre product over `C`, with objects given by a base point `U` and an object
of the pullback of the fibre categories over `U`. -/
abbrev explicitTwoFibreProduct
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :=
  BasedCategory.ofFunctor (explicitTwoFibreProductBaseFunctor F G)

/-- The left projection from the explicit `2`-fibre product in `Cat/C`. -/
abbrev explicitTwoFibreProductLeftProjection
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    explicitTwoFibreProduct F G ⥤ᵇ X :=
  { toFunctor := explicitTwoFibreProductLeftFunctor F G
    w := explicitTwoFibreProductLeftFunctor_comm F G }

/-- The right projection from the explicit `2`-fibre product in `Cat/C`. -/
abbrev explicitTwoFibreProductRightProjection
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    explicitTwoFibreProduct F G ⥤ᵇ Y :=
  { toFunctor := explicitTwoFibreProductRightFunctor F G
    w := explicitTwoFibreProductRightFunctor_comm F G }

noncomputable section

/-- The canonical comparison isomorphism over `C` on the explicit `2`-fibre product. -/
def explicitTwoFibreProductComparisonIsoOver :
    explicitTwoFibreProductLeftProjection F G ⋙ F ≅
      explicitTwoFibreProductRightProjection F G ⋙ G :=
  BasedNatIso.mkNatIso
    (explicitTwoFibreProductComparisonNatIso F G)
    (fun P ↦ by
      simpa [explicitTwoFibreProduct] using P.comparison_over)

/-- The ordinary categorical square underlying the explicit `2`-fibre product over `C`. This is
the canonical bridge from the source-facing based pullback owner to the chapter's categorical
pullback-square owner `CategoricalPullback.CatCommSqOver`. -/
abbrev explicitTwoFibreProductSquareOver :
    CategoricalPullback.CatCommSqOver F.toFunctor G.toFunctor (explicitTwoFibreProduct F G).obj
    where
  fst := (explicitTwoFibreProductLeftProjection F G).toFunctor
  snd := (explicitTwoFibreProductRightProjection F G).toFunctor
  iso := (BasedNatTrans.forgetful _ _).mapIso (explicitTwoFibreProductComparisonIsoOver F G)

/-- The compatibility square in `S` induced by a morphism in the pullback of fibres. -/
theorem pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comm
    {U : C} {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)}
    (φ : P ⟶ Q) :
    CommSq (F.toFunctor.map φ.fst.1) P.iso.hom.1 Q.iso.hom.1 (G.toFunctor.map φ.snd.1) := by
  refine ⟨?_⟩
  convert congrArg Subtype.val φ.w using 1

/-- The pullback of the fibres over `U`, viewed in the total explicit `2`-fibre product over
`C`. -/
def pullbackOfFibres_to_explicitTwoFibreProduct
    (U : C) :
    (F.fiberFunctor U) ⊡ (G.fiberFunctor U) ⥤ (explicitTwoFibreProduct F G).obj where
  obj P := { U := U, obj := P }
  map φ :=
    { base := 𝟙 U
      a := φ.fst.1
      a_over := φ.fst.2
      b := φ.snd.1
      b_over := φ.snd.2
      comm := pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comm F G φ }
  map_id P := by
    apply ExplicitTwoFibreProductHom.ext
    · rfl
    · rfl
  map_comp φ ψ := by
    apply ExplicitTwoFibreProductHom.ext
    · rfl
    · rfl

/-- The canonical comparison functor from the pullback of the fibres over `U` to the fibre over
`U` of the explicit `2`-fibre product over `C`. -/
abbrev pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct
    (U : C) :
    (F.fiberFunctor U) ⊡ (G.fiberFunctor U) ⥤
      Functor.Fiber (explicitTwoFibreProduct F G).p U :=
  let H := pullbackOfFibres_to_explicitTwoFibreProduct F G U
  have hH :
      H ⋙ (explicitTwoFibreProduct F G).p =
        (Functor.const ((F.fiberFunctor U) ⊡ (G.fiberFunctor U))).obj U := rfl
  Functor.Fiber.inducedFunctor hH

/-- Helper for Lemma 4.32.5: an object of the fibre of the explicit pullback over `U` already
stores an object of the pullback of the fibre categories over `U`. -/
def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj
    (U : C) :
    Functor.Fiber (explicitTwoFibreProduct F G).p U →
      ((F.fiberFunctor U) ⊡ (G.fiberFunctor U))
  | ⟨⟨_, P⟩, rfl⟩ => P

/-- Helper for Lemma 4.32.5: the left component of a fibre morphism in the explicit pullback lies
over the identity of `U`. -/
theorem fibreOfExplicitTwoFibreProduct_left_over_id
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    X.p.IsHomLift (𝟙 U) φ.1.a := by
  -- After normalizing the objects of the outer fibre, the lift over `𝟙 U` becomes definitional.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (explicitTwoFibreProduct F G).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [explicitTwoFibreProduct] using
                      (IsHomLift.fac' ((explicitTwoFibreProduct F G).p) (𝟙 UP) φ.1)
                  simpa [hbase, explicitTwoFibreProduct] using φ.1.a_over

/-- Helper for Lemma 4.32.5: the right component of a fibre morphism in the explicit pullback
lies over the identity of `U`. -/
theorem fibreOfExplicitTwoFibreProduct_right_over_id
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    Y.p.IsHomLift (𝟙 U) φ.1.b := by
  -- The right component is handled by the same outer-fibre normalization.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (explicitTwoFibreProduct F G).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [explicitTwoFibreProduct] using
                      (IsHomLift.fac' ((explicitTwoFibreProduct F G).p) (𝟙 UP) φ.1)
                  simpa [hbase, explicitTwoFibreProduct] using φ.1.b_over

/-- Helper for Lemma 4.32.5: the left component of a fibre morphism gives the left morphism in
the pullback of fibres. -/
def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_fst
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P).fst ⟶
      (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U Q).fst :=
  match P, Q, φ with
  | ⟨⟨_, P⟩, rfl⟩, ⟨⟨_, Q⟩, rfl⟩, φ =>
      ⟨φ.1.a, fibreOfExplicitTwoFibreProduct_left_over_id F G φ⟩

/-- Helper for Lemma 4.32.5: the right component of a fibre morphism gives the right morphism in
the pullback of fibres. -/
def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_snd
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P).snd ⟶
      (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U Q).snd :=
  match P, Q, φ with
  | ⟨⟨_, P⟩, rfl⟩, ⟨⟨_, Q⟩, rfl⟩, φ =>
      ⟨φ.1.b, fibreOfExplicitTwoFibreProduct_right_over_id F G φ⟩

/-- Helper for Lemma 4.32.5: the two induced fibre morphisms still satisfy the pullback
compatibility equation. -/
theorem fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_w
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    (F.fiberFunctor U).map (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_fst F G φ) ≫
        (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U Q).iso.hom =
      (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P).iso.hom ≫
        (G.fiberFunctor U).map (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_snd F G φ) := by
  -- After normalizing the outer fibre equalities, this is exactly the compatibility square of
  -- the explicit pullback morphism.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  apply Functor.Fiber.hom_ext
                  simpa using φ.1.comm.w

/-- Helper for Lemma 4.32.5: a fibre morphism in the explicit pullback induces a morphism in the
pullback of the fibre categories over `U`. -/
def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) :
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P ⟶
      fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U Q :=
  match P, Q, φ with
  | ⟨⟨_, P⟩, rfl⟩, ⟨⟨_, Q⟩, rfl⟩, φ =>
      { fst := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_fst F G φ
        snd := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_snd F G φ
        w := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_w F G φ }

/-- Helper for Lemma 4.32.5: the inverse functor on fibres preserves identities. -/
theorem fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_id
    {U : C} (P : Functor.Fiber (explicitTwoFibreProduct F G).p U) :
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G (𝟙 P) =
      𝟙 (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U P) := by
  -- After normalizing the outer fibre equality, the induced morphism is definitionally the
  -- identity on each fibre component.
  cases P with
  | mk P hP =>
      cases P with
      | mk UP Pobj =>
          cases hP
          apply CategoricalPullback.hom_ext
          · apply Functor.Fiber.hom_ext
            rfl
          · apply Functor.Fiber.hom_ext
            rfl

/-- Helper for Lemma 4.32.5: the inverse functor on fibres preserves composition. -/
theorem fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_comp
    {U : C}
    {P Q R : Functor.Fiber (explicitTwoFibreProduct F G).p U}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G (φ ≫ ψ) =
      fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G φ ≫
        fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G ψ := by
  -- After reducing the outer fibre equalities, composition is componentwise in the pullback.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases R with
          | mk R hR =>
              cases P with
              | mk UP Pobj =>
                  cases Q with
                  | mk UQ Qobj =>
                      cases R with
                      | mk UR Robj =>
                          cases hP
                          cases hQ
                          cases hR
                          apply CategoricalPullback.hom_ext
                          · apply Functor.Fiber.hom_ext
                            rfl
                          · apply Functor.Fiber.hom_ext
                            rfl

/-- Helper for Lemma 4.32.5: forgetting the redundant outer fibre equality gives the concrete
quasi-inverse from the fibre of the explicit pullback to the pullback of fibres. -/
def fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres
    (U : C) :
    Functor.Fiber (explicitTwoFibreProduct F G).p U ⥤
      ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) where
  obj := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_obj F G U
  map := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map F G
  map_id := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_id F G
  map_comp := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_map_comp F G

/-- Helper for Lemma 4.32.5: the canonical functor from the pullback of fibres and the concrete
quasi-inverse compose to the identity on the pullback of fibres. -/
theorem pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comp_inverse
    (U : C) :
    pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U ⋙
        fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U =
      𝟭 ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) := by
  -- Route correction: use heterogeneous functor extensionality to avoid all `eqToHom`
  -- transports in the morphism clause.
  refine Functor.hext (fun P ↦ rfl) ?_
  intro P Q φ
  cases P
  cases Q
  rfl

/-- Helper for Lemma 4.32.5: the concrete quasi-inverse followed by the canonical functor back to
the outer fibre is the identity on that fibre. -/
theorem fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_comp_forward
    (U : C) :
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U ⋙
        pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U =
      𝟭 (Functor.Fiber (explicitTwoFibreProduct F G).p U) := by
  refine Functor.hext
    (fun P ↦ by
      cases P with
      | mk P hP =>
          cases P with
          | mk UP Pobj =>
              cases hP
              rfl)
    ?_
  intro P Q φ
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  cases Pobj with
                  | mk Pfst Psnd Piso =>
                      cases Qobj with
                      | mk Qfst Qsnd Qiso =>
                          cases Pfst with
                          | mk PX hPX =>
                              cases Psnd with
                              | mk PY hPY =>
                                  cases Qfst with
                                  | mk QX hQX =>
                                      cases Qsnd with
                                      | mk QY hQY =>
                                          have hmap :
                                              (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G
                                                      ((explicitTwoFibreProduct F G).p.obj
                                                        { U := UP
                                                          obj := { fst := ⟨PX, hPX⟩
                                                                   snd := ⟨PY, hPY⟩
                                                                   iso := Piso } }) ⋙
                                                    pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G
                                                      ((explicitTwoFibreProduct F G).p.obj
                                                        { U := UP
                                                          obj := { fst := ⟨PX, hPX⟩
                                                                   snd := ⟨PY, hPY⟩
                                                                   iso := Piso } })).map φ =
                                                (𝟭
                                                      ((explicitTwoFibreProduct F G).p.Fiber
                                                        ((explicitTwoFibreProduct F G).p.obj
                                                          { U := UP
                                                            obj := { fst := ⟨PX, hPX⟩
                                                                     snd := ⟨PY, hPY⟩
                                                                     iso := Piso } }))).map φ := by
                                            apply Functor.Fiber.hom_ext
                                            apply ExplicitTwoFibreProductHom.ext
                                            · rfl
                                            · rfl
                                          exact hmap ▸ HEq.rfl

private theorem pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_isEquivalence
    (U : C) :
    (pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U).IsEquivalence := by
  -- The concrete quasi-inverse is obtained by deleting the redundant outer fibre equality.
  let H := fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U
  have hη :
      pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U ⋙ H =
        𝟭 ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :=
    pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comp_inverse F G U
  have hε :
      H ⋙ pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U =
        𝟭 (Functor.Fiber (explicitTwoFibreProduct F G).p U) :=
    fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_comp_forward F G U
  exact
    Functor.IsEquivalence.mk'
      H
      (eqToIso hη.symm)
      (eqToIso hε)

/-- Lemma 4.32.5: for morphisms of categories over `C`, the fibre over `U` of the explicit
`2`-fibre product category over `C` is canonically equivalent to the pullback of the fibre
categories `X_U ×_{S_U} Y_U`. -/
noncomputable def fibreOfPullback_equiv_pullbackOfFibres
    (U : C) :
    Functor.Fiber (explicitTwoFibreProduct F G).p U ≌
      ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :=
  Equivalence.mk
    (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U)
    (pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct F G U)
    (eqToIso (fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres_comp_forward F G U).symm)
    (eqToIso (pullbackOfFibres_to_fibreOfExplicitTwoFibreProduct_comp_inverse F G U))

/-- Helper for Lemma 4.32.5: the forward functor of the packaged equivalence is the concrete
quasi-inverse obtained by forgetting the redundant outer fibre equality. -/
private theorem fibreOfPullback_equiv_pullbackOfFibres_functor
    (U : C) :
    (fibreOfPullback_equiv_pullbackOfFibres F G U).functor =
      fibreOfExplicitTwoFibreProduct_to_pullbackOfFibres F G U := by
  -- Unfolding the packaged equivalence exposes the chosen quasi-inverse as its forward functor.
  rfl

-- Proof sketch: the equivalence is the quasi-inverse of the canonical functor from the pullback
-- of fibres into the fibre of the explicit pullback. Its forward functor therefore recovers the
-- left pullback projection on the nose, which matches the fibre functor induced by the left
-- projection `explicitTwoFibreProductLeftProjection F G`.
/-- The forward functor of `fibreOfPullback_equiv_pullbackOfFibres` composed with the left
projection `π₁` is the fibre functor induced by the left projection of the explicit
`2`-fibre product. -/
theorem fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
    (U : C) :
    (fibreOfPullback_equiv_pullbackOfFibres F G U).functor ⋙
        π₁ (F.fiberFunctor U) (G.fiberFunctor U) =
      (explicitTwoFibreProductLeftProjection F G).fiberFunctor U := by
  -- The forward functor is the concrete quasi-inverse defined above.
  rw [fibreOfPullback_equiv_pullbackOfFibres_functor F G U]
  refine Functor.hext
    (fun P ↦ by
      cases P with
      | mk P hP =>
          cases P with
          | mk UP Pobj =>
              cases hP
              rfl)
    ?_
  intro P Q φ
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  rfl

-- Proof sketch: this is the right-hand analogue of
-- `fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁`. The forward functor of the
-- equivalence forgets to the `Y`-component exactly as the fibre functor induced by the right
-- projection `explicitTwoFibreProductRightProjection F G`.
/-- The forward functor of `fibreOfPullback_equiv_pullbackOfFibres` composed with the right
projection `π₂` is the fibre functor induced by the right projection of the explicit
`2`-fibre product. -/
theorem fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
    (U : C) :
    (fibreOfPullback_equiv_pullbackOfFibres F G U).functor ⋙
        π₂ (F.fiberFunctor U) (G.fiberFunctor U) =
      (explicitTwoFibreProductRightProjection F G).fiberFunctor U := by
  -- The same concrete quasi-inverse forgets to the right fibre component.
  rw [fibreOfPullback_equiv_pullbackOfFibres_functor F G U]
  refine Functor.hext
    (fun P ↦ by
      cases P with
      | mk P hP =>
          cases P with
          | mk UP Pobj =>
              cases hP
              rfl)
    ?_
  intro P Q φ
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  rfl

end

end CategoryOver
end CategoryTheory
