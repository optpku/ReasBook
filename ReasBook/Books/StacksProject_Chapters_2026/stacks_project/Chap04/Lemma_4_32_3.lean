module

public import stacks_project.Chap04.Definition_4_31_2
public import stacks_project.Chap04.Lemma_4_32_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped Bicategory
open scoped CategoricalPullback

universe u v

namespace CategoryTheory
namespace CategoryOver

/- Domain-style sampling for Lemma 4.32.3:
- primary domain: bicategorical `2`-fibre products in `Cat/C`;
- sampled owner-level declarations:
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductSquareOver`,
  `explicitTwoFibreProductLeftProjection`,
  `explicitTwoFibreProductRightProjection`,
  `CatCommSqOver.toBicategoricalSquare`,
  `Bicategory.IsFinal`;
-- best owner abstraction: the source-facing over-`C` pullback owner is the
  `BicategoricalTwoCommutativeSquare` in the bicategory `BasedCategory C` whose apex is
  `explicitTwoFibreProduct F G`, already defined in Lemma 4.32.5 from the fibrewise pullback
  construction;
- primitive data: owned upstream by the explicit over-`C` pullback construction and its canonical
  categorical square;
-- derived API kept here: only the bicategorical `2`-fibre-product property of the canonical
  over-`C` square.  The ordinary `Cat` square obtained by forgetting the base is not the statement
  of Lemma 4.32.3 and is false in general.

Source/core/bridge triage:
-- `source-facing`: `explicitTwoFibreProductSquare F G`;
-- `core/canonical`: `Bicategory.IsFinal (explicitTwoFibreProductSquare F G)`;
-- `bridge/view`: the forgotten ordinary `Cat` square `explicitTwoFibreProductSquareOver F G`,
  which is useful for some constructions but does not carry the universal property by itself. -/

variable {C : Type u} [Category.{v} C]

section

variable {X Y S : BasedCategory C}
variable (F : X ⟶ S) (G : Y ⟶ S)

/-- Helper for Lemma 4.32.3: the canonical comparison functor from the explicit pullback over `C`
to the ordinary categorical pullback forgets only the common-base witness. -/
private abbrev explicitTwoFibreProductToCategoricalPullback :
    (explicitTwoFibreProduct F G).obj ⥤ F.toFunctor ⊡ G.toFunctor :=
  (toFunctorToCategoricalPullback F.toFunctor G.toFunctor
    (explicitTwoFibreProduct F G).obj).obj (explicitTwoFibreProductSquareOver F G)

/-- Helper for Lemma 4.32.3: every object in the image of the canonical comparison functor comes
from a genuine common base object, so its two components lie over equal objects of `C`. -/
private theorem explicitTwoFibreProduct_comparison_obj_base_eq
    (P : (explicitTwoFibreProduct F G).obj) :
    X.p.obj ((explicitTwoFibreProductToCategoricalPullback F G).obj P).fst =
      Y.p.obj ((explicitTwoFibreProductToCategoricalPullback F G).obj P).snd := by
  -- Unpack the explicit pullback object and read off the two fibre conditions.
  cases P with
  | mk U P =>
      simpa [explicitTwoFibreProductToCategoricalPullback, explicitTwoFibreProductSquareOver,
        explicitTwoFibreProductLeftProjection, explicitTwoFibreProductRightProjection] using
        P.fst.2.trans P.snd.2.symm

/-- Helper for Lemma 4.32.3: the left component of an ordinary pullback object has the expected
base in `C` after applying the structure identity of the based functor `F`. -/
private theorem categoricalPullback_left_base_eq
    (Q : F.toFunctor ⊡ G.toFunctor) :
    S.p.obj (F.obj Q.fst) = X.p.obj Q.fst := by
  -- This is the object part of the defining equality `F ⋙ S.p = X.p`.
  exact congrArg (fun H : X.obj ⥤ C => H.obj Q.fst) F.w

/-- Helper for Lemma 4.32.3: the right component of an ordinary pullback object has the expected
base in `C` after applying the structure identity of the based functor `G`. -/
private theorem categoricalPullback_right_base_eq
    (Q : F.toFunctor ⊡ G.toFunctor) :
    S.p.obj (G.obj Q.snd) = Y.p.obj Q.snd := by
  -- This is the object part of the defining equality `G ⋙ S.p = Y.p`.
  exact congrArg (fun H : Y.obj ⥤ C => H.obj Q.snd) G.w

/-- Helper for Lemma 4.32.3: an arbitrary object of the ordinary categorical pullback canonically
produces an isomorphism between the two base objects in `C`. -/
private def categoricalPullback_obj_base_iso
    (Q : F.toFunctor ⊡ G.toFunctor) :
    X.p.obj Q.fst ≅ Y.p.obj Q.snd :=
  eqToIso (categoricalPullback_left_base_eq F G Q).symm ≪≫
    S.p.mapIso Q.iso ≪≫
    eqToIso (categoricalPullback_right_base_eq F G Q)

/-- Helper for Lemma 4.32.3: if the induced base isomorphism of an ordinary pullback object is
represented by an actual equality of base objects, then its comparison arrow already lies over
the identity of that common base. -/
private theorem categoricalPullback_comparison_isHomLift_of_eqToIso
    (Q : F.toFunctor ⊡ G.toFunctor)
    (hbase : X.p.obj Q.fst = Y.p.obj Q.snd)
    (hcompat : categoricalPullback_obj_base_iso F G Q = eqToIso hbase) :
    S.p.IsHomLift (𝟙 (X.p.obj Q.fst)) Q.iso.hom := by
  let ha : S.p.obj (F.obj Q.fst) = X.p.obj Q.fst :=
    categoricalPullback_left_base_eq F G Q
  let hb : S.p.obj (G.obj Q.snd) = X.p.obj Q.fst :=
    (categoricalPullback_right_base_eq F G Q).trans hbase.symm
  -- Rewrite the transported base isomorphism as the chosen equality and then solve the lift
  -- condition by the standard `of_fac` criterion.
  have hhom : (categoricalPullback_obj_base_iso F G Q).hom = eqToHom hbase := by
    exact congrArg Iso.hom hcompat
  exact IsHomLift.of_fac S.p (𝟙 (X.p.obj Q.fst)) Q.iso.hom ha hb <| by
    dsimp [categoricalPullback_obj_base_iso] at hhom
    symm
    simpa [ha, hb, Category.assoc] using
      congrArg (fun k ↦ k ≫ eqToHom hbase.symm) hhom

/-- Helper for Lemma 4.32.3: an ordinary pullback object strictifies to the explicit pullback over
`C` once its induced base isomorphism is identified with an equality. -/
private theorem categoricalPullback_strictified_comparison_exists
    (Q : F.toFunctor ⊡ G.toFunctor)
    (hbase : X.p.obj Q.fst = Y.p.obj Q.snd)
    (hcompat : categoricalPullback_obj_base_iso F G Q = eqToIso hbase) :
    Nonempty
      (((F.fiberFunctor (X.p.obj Q.fst)).obj (Functor.Fiber.mk rfl)) ≅
        ((G.fiberFunctor (X.p.obj Q.fst)).obj (Functor.Fiber.mk hbase.symm))) := by
  letI : S.p.IsHomLift (𝟙 (X.p.obj Q.fst)) Q.iso.hom :=
    categoricalPullback_comparison_isHomLift_of_eqToIso F G Q hbase hcompat
  letI : S.p.IsHomLift (𝟙 (X.p.obj Q.fst)) Q.iso.inv := by
    infer_instance
  -- The strictified comparison is just the original pullback comparison, reinterpreted in the
  -- fibre over the common base.
  refine ⟨{ hom := Functor.Fiber.homMk S.p (X.p.obj Q.fst) Q.iso.hom
            inv := Functor.Fiber.homMk S.p (X.p.obj Q.fst) Q.iso.inv
            hom_inv_id := by
              apply Functor.Fiber.hom_ext
              change Q.iso.hom ≫ Q.iso.inv = 𝟙 _
              exact Q.iso.hom_inv_id
            inv_hom_id := by
              apply Functor.Fiber.hom_ext
              change Q.iso.inv ≫ Q.iso.hom = 𝟙 _
              exact Q.iso.inv_hom_id }⟩

/-- Helper for Lemma 4.32.3: an ordinary pullback object with equality-compatible base transport
canonically determines an object of the explicit pullback over `C`. -/
private noncomputable def categoricalPullback_strictified_comparison
    (Q : F.toFunctor ⊡ G.toFunctor)
    (hbase : X.p.obj Q.fst = Y.p.obj Q.snd)
    (hcompat : categoricalPullback_obj_base_iso F G Q = eqToIso hbase) :
    ((F.fiberFunctor (X.p.obj Q.fst)).obj (Functor.Fiber.mk rfl)) ≅
      ((G.fiberFunctor (X.p.obj Q.fst)).obj (Functor.Fiber.mk hbase.symm)) :=
  Classical.choice (categoricalPullback_strictified_comparison_exists F G Q hbase hcompat)

/-- Helper for Lemma 4.32.3: an ordinary pullback object with equality-compatible base transport
canonically determines an object of the explicit pullback over `C`. -/
private noncomputable def categoricalPullback_to_explicitTwoFibreProduct
    (Q : F.toFunctor ⊡ G.toFunctor)
    (hbase : X.p.obj Q.fst = Y.p.obj Q.snd)
    (hcompat : categoricalPullback_obj_base_iso F G Q = eqToIso hbase) :
    (explicitTwoFibreProduct F G).obj :=
  { U := X.p.obj Q.fst
    obj :=
      { fst := Functor.Fiber.mk rfl
        snd := Functor.Fiber.mk hbase.symm
        iso := categoricalPullback_strictified_comparison F G Q hbase hcompat } }

/-- The canonical `2`-commutative square in `Cat/C` carried by the explicit fibrewise pullback
model of Lemma 4.32.3. -/
noncomputable def explicitTwoFibreProductSquare :
    BicategoricalTwoCommutativeSquare F G where
  obj := explicitTwoFibreProduct F G
  p := explicitTwoFibreProductLeftProjection F G
  q := explicitTwoFibreProductRightProjection F G
  ψ := explicitTwoFibreProductComparisonIsoOver F G

/-- Helper for Lemma 4.32.3: equality of based natural transformations is detected on the
underlying ordinary natural transformations. -/
private theorem basedNatTrans_ext_toNatTrans
    {A B : BasedCategory C}
    {H K : A ⥤ᵇ B}
    (η θ : H ⟶ K)
    (h : η.toNatTrans = θ.toNatTrans) :
    η = θ := by
  exact BasedNatTrans.ext η θ h

/-- Helper for Lemma 4.32.3: whiskering a based natural transformation into the left projection of
the explicit pullback reads off its `a`-component objectwise. -/
private theorem explicitTwoFibreProduct_left_projection_whisker_app
    {A : BasedCategory C}
    {H K : A ⥤ᵇ explicitTwoFibreProduct F G}
    (τ : H ⟶ K)
    (T : A.obj) :
    ((τ ▷ (explicitTwoFibreProductSquare F G).p).app T) = (τ.app T).a := by
  rfl

/-- Helper for Lemma 4.32.3: whiskering a based natural transformation into the right projection
of the explicit pullback reads off its `b`-component objectwise. -/
private theorem explicitTwoFibreProduct_right_projection_whisker_app
    {A : BasedCategory C}
    {H K : A ⥤ᵇ explicitTwoFibreProduct F G}
    (τ : H ⟶ K)
    (T : A.obj) :
    ((τ ▷ (explicitTwoFibreProductSquare F G).q).app T) = (τ.app T).b := by
  rfl

/-- Helper for Lemma 4.32.3: the base projection of a morphism in the explicit pullback is its
stored `base` field. -/
private theorem explicitTwoFibreProduct_base_projection_map
    {P Q : (explicitTwoFibreProduct F G).obj}
    (φ : P ⟶ Q) :
    (explicitTwoFibreProduct F G).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 4.32.3: whiskering a based functor into the comparison isomorphism of the
explicit pullback returns the stored comparison of its image object. -/
private theorem explicitTwoFibreProduct_comparison_whisker_app
    {A : BasedCategory C}
    (H : A ⥤ᵇ explicitTwoFibreProduct F G)
    (T : A.obj) :
    ((H ◁ (explicitTwoFibreProductSquare F G).ψ.hom).app T) = (H.obj T).comparison := by
  rfl

/-- Helper for Lemma 4.32.3: the forward square comparison is vertical over the common base of
the textbook factorization object. -/
private theorem explicitTwoFibreProduct_terminalLift_obj_hom_isHomLift
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    S.p.IsHomLift (𝟙 (P.obj.p.obj T)) (P.ψ.hom.app T) := by
  -- Each component of a based natural transformation is vertical over the identity base map.
  exact BasedNatTrans.isHomLift P.ψ.hom (rfl : P.obj.p.obj T = P.obj.p.obj T)

/-- Helper for Lemma 4.32.3: the inverse square comparison is vertical over the same common base
object. -/
private theorem explicitTwoFibreProduct_terminalLift_obj_inv_isHomLift
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    S.p.IsHomLift (𝟙 (P.obj.p.obj T)) (P.ψ.inv.app T) := by
  -- The inverse comparison is also a component of a based natural transformation over `C`.
  exact BasedNatTrans.isHomLift P.ψ.inv (rfl : P.obj.p.obj T = P.obj.p.obj T)

/-- Helper for Lemma 4.32.3: the lifted forward and inverse comparison maps compose to the
identity in the fibre over the chosen base object. -/
private theorem explicitTwoFibreProduct_terminalLift_obj_iso_hom_inv_id
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    @Functor.Fiber.homMk _ _ _ _ S.p (P.obj.p.obj T) _ _ (P.ψ.hom.app T)
        (explicitTwoFibreProduct_terminalLift_obj_hom_isHomLift F G P T) ≫
      @Functor.Fiber.homMk _ _ _ _ S.p (P.obj.p.obj T) _ _ (P.ψ.inv.app T)
        (explicitTwoFibreProduct_terminalLift_obj_inv_isHomLift F G P T) =
      𝟙 ((F.fiberFunctor (P.obj.p.obj T)).obj (Functor.Fiber.mk (P.p.w_obj T))) := by
  -- Forget to the total category `S` and use the objectwise inverse law of the square
  -- isomorphism.
  apply Functor.Fiber.hom_ext
  let τ := (BasedNatTrans.forgetful P.obj S).mapIso P.ψ
  change (τ.app T).hom ≫ (τ.app T).inv = 𝟙 _
  exact Iso.hom_inv_id (τ.app T)

/-- Helper for Lemma 4.32.3: the inverse and forward comparison maps also compose to the identity
in the fibre over the chosen base object. -/
private theorem explicitTwoFibreProduct_terminalLift_obj_iso_inv_hom_id
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    @Functor.Fiber.homMk _ _ _ _ S.p (P.obj.p.obj T) _ _ (P.ψ.inv.app T)
        (explicitTwoFibreProduct_terminalLift_obj_inv_isHomLift F G P T) ≫
      @Functor.Fiber.homMk _ _ _ _ S.p (P.obj.p.obj T) _ _ (P.ψ.hom.app T)
        (explicitTwoFibreProduct_terminalLift_obj_hom_isHomLift F G P T) =
      𝟙 ((G.fiberFunctor (P.obj.p.obj T)).obj (Functor.Fiber.mk (P.q.w_obj T))) := by
  -- The second inverse law is proved by the same forgetful-fibre argument.
  apply Functor.Fiber.hom_ext
  let τ := (BasedNatTrans.forgetful P.obj S).mapIso P.ψ
  change (τ.app T).inv ≫ (τ.app T).hom = 𝟙 _
  exact Iso.inv_hom_id (τ.app T)

/-- Helper for Lemma 4.32.3: the objectwise comparison isomorphism of the canonical factorization
is the given component `ψ_T`, viewed inside the fibre over `p(T)`. -/
private noncomputable def explicitTwoFibreProduct_terminalLift_obj_iso
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    (F.fiberFunctor (P.obj.p.obj T)).obj (Functor.Fiber.mk (P.p.w_obj T)) ≅
      (G.fiberFunctor (P.obj.p.obj T)).obj (Functor.Fiber.mk (P.q.w_obj T)) :=
  { hom := @Functor.Fiber.homMk _ _ _ _ S.p (P.obj.p.obj T) _ _ (P.ψ.hom.app T)
      (explicitTwoFibreProduct_terminalLift_obj_hom_isHomLift F G P T)
    inv := @Functor.Fiber.homMk _ _ _ _ S.p (P.obj.p.obj T) _ _ (P.ψ.inv.app T)
      (explicitTwoFibreProduct_terminalLift_obj_inv_isHomLift F G P T)
    hom_inv_id := explicitTwoFibreProduct_terminalLift_obj_iso_hom_inv_id F G P T
    inv_hom_id := explicitTwoFibreProduct_terminalLift_obj_iso_inv_hom_id F G P T }

/-- Helper for Lemma 4.32.3: the canonical factorization sends `T` to the explicit pullback
object `(p(T), P.p(T), P.q(T), ψ_T)`. -/
private noncomputable def explicitTwoFibreProduct_terminalLift_obj
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    (explicitTwoFibreProduct F G).obj :=
  { U := P.obj.p.obj T
    obj :=
      { fst := Functor.Fiber.mk (P.p.w_obj T)
        snd := Functor.Fiber.mk (P.q.w_obj T)
        iso := explicitTwoFibreProduct_terminalLift_obj_iso F G P T } }

/-- Helper for Lemma 4.32.3: the comparison of the canonical factorization object is literally
the component `ψ_T`. -/
private theorem explicitTwoFibreProduct_terminalLift_obj_comparison
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    (explicitTwoFibreProduct_terminalLift_obj F G P T).comparison = P.ψ.hom.app T := by
  rfl

/-- Helper for Lemma 4.32.3: the morphism part of the textbook factorization is compatible with
the comparison isomorphisms by naturality of `ψ`. -/
private theorem explicitTwoFibreProduct_terminalLift_map_comm
    (P : BicategoricalTwoCommutativeSquare F G)
    {T T' : P.obj.obj}
    (f : T ⟶ T') :
    CommSq (F.map (P.p.map f))
      (explicitTwoFibreProduct_terminalLift_obj F G P T).comparison
      (explicitTwoFibreProduct_terminalLift_obj F G P T').comparison
      (G.map (P.q.map f)) := by
  -- The defining square is exactly the naturality square of `P.ψ.hom`.
  refine ⟨?_⟩
  simpa [Functor.comp_map, explicitTwoFibreProduct_terminalLift_obj_comparison] using
    P.ψ.hom.toNatTrans.naturality f

/-- Helper for Lemma 4.32.3: the morphism part of the textbook factorization uses the original
maps on the left and right legs. -/
private theorem explicitTwoFibreProduct_terminalLift_map_left_isHomLift
    (P : BicategoricalTwoCommutativeSquare F G)
    {T T' : P.obj.obj}
    (f : T ⟶ T') :
    X.p.IsHomLift (P.obj.p.map f) (P.p.map f) := by
  exact inferInstance

/-- Helper for Lemma 4.32.3: the right leg of the textbook factorization lies over the same base
morphism as the left leg. -/
private theorem explicitTwoFibreProduct_terminalLift_map_right_isHomLift
    (P : BicategoricalTwoCommutativeSquare F G)
    {T T' : P.obj.obj}
    (f : T ⟶ T') :
    Y.p.IsHomLift (P.obj.p.map f) (P.q.map f) := by
  exact inferInstance

/-- Helper for Lemma 4.32.3: the morphism part of the textbook factorization uses the original
maps on the left and right legs. -/
private noncomputable def explicitTwoFibreProduct_terminalLift_map
    (P : BicategoricalTwoCommutativeSquare F G)
    {T T' : P.obj.obj}
    (f : T ⟶ T') :
    explicitTwoFibreProduct_terminalLift_obj F G P T ⟶
      explicitTwoFibreProduct_terminalLift_obj F G P T' :=
  { base := P.obj.p.map f
    a := P.p.map f
    a_over := explicitTwoFibreProduct_terminalLift_map_left_isHomLift F G P f
    b := P.q.map f
    b_over := explicitTwoFibreProduct_terminalLift_map_right_isHomLift F G P f
    comm := explicitTwoFibreProduct_terminalLift_map_comm F G P f }

/-- Helper for Lemma 4.32.3: the textbook factorization preserves identity morphisms. -/
private theorem explicitTwoFibreProduct_terminalLift_map_id
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    explicitTwoFibreProduct_terminalLift_map F G P (𝟙 T) =
      𝟙 (explicitTwoFibreProduct_terminalLift_obj F G P T) := by
  -- Identity is checked on the left and right fibre components.
  apply ExplicitTwoFibreProductHom.ext
  · change P.p.map (𝟙 T) = 𝟙 (P.p.obj T)
    simp
  · change P.q.map (𝟙 T) = 𝟙 (P.q.obj T)
    simp

/-- Helper for Lemma 4.32.3: the textbook factorization preserves composition of morphisms. -/
private theorem explicitTwoFibreProduct_terminalLift_map_comp
    (P : BicategoricalTwoCommutativeSquare F G)
    {T₁ T₂ T₃ : P.obj.obj}
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    explicitTwoFibreProduct_terminalLift_map F G P (f ≫ g) =
      explicitTwoFibreProduct_terminalLift_map F G P f ≫
        explicitTwoFibreProduct_terminalLift_map F G P g := by
  -- Composition is also checked on the left and right fibre components.
  apply ExplicitTwoFibreProductHom.ext
  · change P.p.map (f ≫ g) = P.p.map f ≫ P.p.map g
    simp
  · change P.q.map (f ≫ g) = P.q.map f ≫ P.q.map g
    simp

/-- Helper for Lemma 4.32.3: every competing square factors through the explicit pullback by
sending `T` to the quadruple `(p(T), P.p(T), P.q(T), ψ_T)`. -/
private noncomputable def explicitTwoFibreProduct_terminalLift_hom
    (P : BicategoricalTwoCommutativeSquare F G) :
    P.obj ⥤ᵇ explicitTwoFibreProduct F G :=
  { toFunctor :=
      { obj := explicitTwoFibreProduct_terminalLift_obj F G P
        map := fun f ↦ explicitTwoFibreProduct_terminalLift_map F G P f
        map_id := explicitTwoFibreProduct_terminalLift_map_id F G P
        map_comp := fun f g ↦ explicitTwoFibreProduct_terminalLift_map_comp F G P f g }
    w := rfl }

/-- Helper for Lemma 4.32.3: the canonical factorization square equation reduces objectwise to
the tautological identity on the chosen comparison components. -/
private theorem explicitTwoFibreProduct_terminalLift_comparison_app
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.obj) :
    ((explicitTwoFibreProduct_terminalLift_hom F G P ◁
          (explicitTwoFibreProductSquare F G).ψ.hom).app T) =
      (explicitTwoFibreProduct_terminalLift_obj F G P T).comparison := by
  rfl

/-- Helper for Lemma 4.32.3: the canonical factorization square equation reduces objectwise to
the tautological identity on the chosen comparison components. -/
private theorem explicitTwoFibreProduct_terminalLift_comm
    (P : BicategoricalTwoCommutativeSquare F G) :
    ((𝟙 P.p) ▷ F) ≫ P.ψ.hom =
      (α_ (explicitTwoFibreProduct_terminalLift_hom F G P)
          (explicitTwoFibreProductSquare F G).p F).hom ≫
        explicitTwoFibreProduct_terminalLift_hom F G P ◁
          (explicitTwoFibreProductSquare F G).ψ.hom ≫
        (α_ (explicitTwoFibreProduct_terminalLift_hom F G P)
          (explicitTwoFibreProductSquare F G).q G).inv ≫
        ((𝟙 P.q) ▷ G) :=
by
  -- Normalize both sides objectwise; the associators are strict and the remaining data are the
  -- chosen comparison components `P.ψ.hom.app T`.
  apply basedNatTrans_ext_toNatTrans
  ext T
  simp [explicitTwoFibreProductSquare, explicitTwoFibreProductComparisonIsoOver,
    explicitTwoFibreProductLeftProjection, explicitTwoFibreProductRightProjection,
    explicitTwoFibreProduct_terminalLift_hom, explicitTwoFibreProduct,
    Bicategory.Strict.associator_eqToIso]
  change P.ψ.hom.app T = P.ψ.hom.app T ≫ 𝟙 (G.obj (P.q.obj T))
  simp

/-- Helper for Lemma 4.32.3: the canonical factorization through the explicit pullback square
uses the identity comparisons on both legs. -/
private noncomputable def explicitTwoFibreProduct_terminalLift
    (P : BicategoricalTwoCommutativeSquare F G) :
    P ⟶ explicitTwoFibreProductSquare F G :=
  { hom := explicitTwoFibreProduct_terminalLift_hom F G P
    left := 𝟙 P.p
    right := 𝟙 P.q
    comm := explicitTwoFibreProduct_terminalLift_comm F G P }

/-- Helper for Lemma 4.32.3: the square equation of a morphism into the explicit pullback square,
evaluated at an object, is exactly the commutative-square condition needed for a morphism in the
explicit pullback category. -/
private theorem square_hom_comm_app
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    ((u.left ▷ F) ≫ P.ψ.hom).app T =
      ((α_ u.hom (explicitTwoFibreProductSquare F G).p F).hom ≫
          u.hom ◁ (explicitTwoFibreProductSquare F G).ψ.hom ≫
          (α_ u.hom (explicitTwoFibreProductSquare F G).q G).inv ≫
          (u.right ▷ G)).app T := by
  -- This is just the component of `u.comm` at `T`.
  simpa using congrArg (fun τ => τ.app T) (congrArg BasedNatTrans.toNatTrans u.comm)

/-- Helper for Lemma 4.32.3: the left comparison component of a morphism into the explicit square
can be repackaged over the base arrow `eqToHom (u.hom.w_obj T)`. -/
private theorem vertical_component_isHomLift_eqToHom_left
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    X.p.IsHomLift (eqToHom (u.hom.w_obj T)) (u.left.app T) := by
  let hs :
      X.p.obj ((u.hom ≫ (explicitTwoFibreProductSquare F G).p).obj T) = (u.hom.obj T).U := by
    simpa [explicitTwoFibreProductSquare, explicitTwoFibreProductLeftProjection,
      explicitTwoFibreProduct] using
      (u.hom.obj T).obj.fst.2
  let ht : X.p.obj (P.p.obj T) = P.obj.p.obj T := P.p.w_obj T
  -- Rewrite the already-vertical component of `u.left` into the equality-transport form used by
  -- morphisms in the explicit pullback category.
  refine IsHomLift.of_fac' X.p (eqToHom (u.hom.w_obj T)) (u.left.app T) hs ht ?_
  have hfac := IsHomLift.fac' X.p (𝟙 (P.obj.p.obj T)) (u.left.app T)
  simpa [hs, ht, Category.assoc] using hfac

/-- Helper for Lemma 4.32.3: the right comparison component of a morphism into the explicit
square can be repackaged over the base arrow `eqToHom (u.hom.w_obj T)`. -/
private theorem vertical_component_isHomLift_eqToHom_right
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    Y.p.IsHomLift (eqToHom (u.hom.w_obj T)) (u.right.app T) := by
  let hs :
      Y.p.obj ((u.hom ≫ (explicitTwoFibreProductSquare F G).q).obj T) = (u.hom.obj T).U := by
    simpa [explicitTwoFibreProductSquare, explicitTwoFibreProductRightProjection,
      explicitTwoFibreProduct] using
      (u.hom.obj T).obj.snd.2
  let ht : Y.p.obj (P.q.obj T) = P.obj.p.obj T := P.q.w_obj T
  -- The right component is transported in the same way as the left component.
  refine IsHomLift.of_fac' Y.p (eqToHom (u.hom.w_obj T)) (u.right.app T) hs ht ?_
  have hfac := IsHomLift.fac' Y.p (𝟙 (P.obj.p.obj T)) (u.right.app T)
  simpa [hs, ht, Category.assoc] using hfac

/-- Helper for Lemma 4.32.3: the abstract square-morphism equation into the explicit pullback
square becomes the concrete compatibility equation for an explicit pullback morphism. -/
private theorem square_hom_comm_app_concrete
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    F.map (u.left.app T) ≫
        (explicitTwoFibreProduct_terminalLift_obj F G P T).comparison =
      (u.hom.obj T).comparison ≫ G.map (u.right.app T) := by
  -- Route correction: unfold the target square just enough to identify the right-hand side with
  -- the explicit pullback comparison carried by `u.hom.obj T`.
  have h := square_hom_comm_app (F := F) (G := G) P u T
  have hleft :
      ((u.left ▷ F) ≫ P.ψ.hom).app T =
        F.map (u.left.app T) ≫
          (explicitTwoFibreProduct_terminalLift_obj F G P T).comparison := by
    -- The left-hand side is just whiskering followed by componentwise composition.
    change F.map (u.left.app T) ≫ P.ψ.hom.app T =
      F.map (u.left.app T) ≫ (explicitTwoFibreProduct_terminalLift_obj F G P T).comparison
    rfl
  have hright :
      ((α_ u.hom (explicitTwoFibreProductSquare F G).p F).hom ≫
            u.hom ◁ (explicitTwoFibreProductSquare F G).ψ.hom ≫
            (α_ u.hom (explicitTwoFibreProductSquare F G).q G).inv ≫
            (u.right ▷ G)).app T =
          (u.hom.obj T).comparison ≫ G.map (u.right.app T) := by
    simp [explicitTwoFibreProductSquare, explicitTwoFibreProductComparisonIsoOver,
      explicitTwoFibreProductLeftProjection, explicitTwoFibreProductRightProjection,
      explicitTwoFibreProduct, Bicategory.Strict.associator_eqToIso]
    rfl
  exact hleft.symm.trans (h.trans hright)

/-- Helper for Lemma 4.32.3: the canonical component of the universal `2`-morphism is the
explicit pullback morphism built from the left and right comparison maps of `u`. -/
private noncomputable def hom_to_explicitTwoFibreProduct_terminalLift_component
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    u.hom.obj T ⟶ explicitTwoFibreProduct_terminalLift_obj F G P T :=
  { base := eqToHom (u.hom.w_obj T)
    a := u.left.app T
    a_over := vertical_component_isHomLift_eqToHom_left F G P u T
    b := u.right.app T
    b_over := vertical_component_isHomLift_eqToHom_right F G P u T
    comm := ⟨square_hom_comm_app_concrete F G P u T⟩ }

/-- Helper for Lemma 4.32.3: the components of the universal `2`-morphism are natural because the
left and right comparison maps of `u` are natural. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_component_naturality
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    {T T' : P.obj.obj}
    (f : T ⟶ T') :
    u.hom.map f ≫ hom_to_explicitTwoFibreProduct_terminalLift_component F G P u T' =
      hom_to_explicitTwoFibreProduct_terminalLift_component F G P u T ≫
        explicitTwoFibreProduct_terminalLift_map F G P f := by
  -- The explicit pullback morphism is determined by its left and right components.
  apply ExplicitTwoFibreProductHom.ext
  · simpa [hom_to_explicitTwoFibreProduct_terminalLift_component,
      explicitTwoFibreProduct_terminalLift_map, explicitTwoFibreProductSquare,
      explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
      u.left.toNatTrans.naturality f
  · simpa [hom_to_explicitTwoFibreProduct_terminalLift_component,
      explicitTwoFibreProduct_terminalLift_map, explicitTwoFibreProductSquare,
      explicitTwoFibreProductRightProjection, explicitTwoFibreProduct] using
      u.right.toNatTrans.naturality f

/-- Helper for Lemma 4.32.3: the components of the universal `2`-morphism are vertical over the
identity in the explicit pullback over `C`. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_component_isHomLift
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    (explicitTwoFibreProduct F G).p.IsHomLift (𝟙 (P.obj.p.obj T))
      (hom_to_explicitTwoFibreProduct_terminalLift_component F G P u T) := by
  -- The base projection of the explicit pullback is the stored `base` field of the component
  -- morphism.
  refine IsHomLift.of_fac' (explicitTwoFibreProduct F G).p (𝟙 (P.obj.p.obj T))
    (hom_to_explicitTwoFibreProduct_terminalLift_component F G P u T) (u.hom.w_obj T) rfl ?_
  rw [explicitTwoFibreProduct_base_projection_map]
  change eqToHom (u.hom.w_obj T) = eqToHom (u.hom.w_obj T) ≫ 𝟙 (P.obj.p.obj T) ≫ 𝟙 _
  simp

/-- Helper for Lemma 4.32.3: every morphism into the explicit pullback square has a canonical
`2`-morphism to the terminal factorization, obtained from its left and right comparison maps. -/
private noncomputable def hom_to_explicitTwoFibreProduct_terminalLift_hom
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G) :
    u.hom ⟶ explicitTwoFibreProduct_terminalLift_hom F G P :=
  { toNatTrans :=
      { app := hom_to_explicitTwoFibreProduct_terminalLift_component F G P u
        naturality := fun {_ _} f ↦
          hom_to_explicitTwoFibreProduct_terminalLift_component_naturality F G P u f }
    isHomLift' := hom_to_explicitTwoFibreProduct_terminalLift_component_isHomLift F G P u }

/-- Helper for Lemma 4.32.3: the left projection of the universal apex transformation is the
left comparison map of the original square morphism. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_left_app
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
          (explicitTwoFibreProductSquare F G).p).app T) =
      u.left.app T := by
  rfl

/-- Helper for Lemma 4.32.3: composing the left projection of the universal apex transformation
with the identity comparison on `P.p` does not change its objectwise component. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_left_app_id
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
      ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
          (explicitTwoFibreProductSquare F G).p ≫ 𝟙 P.p).app T) =
      u.left.app T := by
  -- The extra identity on `P.p` does not change the left component.
  change ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
      (explicitTwoFibreProductSquare F G).p).app T) ≫
      ((𝟙 P.p : P.p ⟶ P.p).app T) = u.left.app T
  have hid :
      ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
            (explicitTwoFibreProductSquare F G).p).app T) ≫ 𝟙 (P.p.obj T) =
        ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
            (explicitTwoFibreProductSquare F G).p).app T) := by
    exact Category.comp_id _
  simpa using hid.trans (hom_to_explicitTwoFibreProduct_terminalLift_left_app F G P u T)

/-- Helper for Lemma 4.32.3: the right projection of the universal apex transformation is the
right comparison map of the original square morphism. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_right_app
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
          (explicitTwoFibreProductSquare F G).q).app T) =
      u.right.app T := by
  rfl

/-- Helper for Lemma 4.32.3: composing the right projection of the universal apex transformation
with the identity comparison on `P.q` does not change its objectwise component. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_right_app_id
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
      ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
          (explicitTwoFibreProductSquare F G).q ≫ 𝟙 P.q).app T) =
      u.right.app T := by
  -- The same normalization applies on the right leg.
  change ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
      (explicitTwoFibreProductSquare F G).q).app T) ≫
      ((𝟙 P.q : P.q ⟶ P.q).app T) = u.right.app T
  have hid :
      ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
            (explicitTwoFibreProductSquare F G).q).app T) ≫ 𝟙 (P.q.obj T) =
        ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
            (explicitTwoFibreProductSquare F G).q).app T) := by
    exact Category.comp_id _
  simpa using hid.trans (hom_to_explicitTwoFibreProduct_terminalLift_right_app F G P u T)

/-- Helper for Lemma 4.32.3: on the left leg, the universal `2`-morphism recovers the given left
comparison map of `u`. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_left_comm_app
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
          (explicitTwoFibreProductSquare F G).p ≫
        (explicitTwoFibreProduct_terminalLift F G P).left).app T) =
      u.left.app T := by
  -- The left comparison of the terminal lift is the identity on `P.p`.
  simpa [explicitTwoFibreProduct_terminalLift] using
    hom_to_explicitTwoFibreProduct_terminalLift_left_app_id F G P u T

/-- Helper for Lemma 4.32.3: on the right leg, the universal `2`-morphism recovers the given
right comparison map of `u`. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_right_comm_app
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (T : P.obj.obj) :
    ((hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u ▷
          (explicitTwoFibreProductSquare F G).q ≫
        (explicitTwoFibreProduct_terminalLift F G P).right).app T) =
      u.right.app T := by
  -- The right comparison of the terminal lift is also the identity.
  simpa [explicitTwoFibreProduct_terminalLift] using
    hom_to_explicitTwoFibreProduct_terminalLift_right_app_id F G P u T

/-- Helper for Lemma 4.32.3: the canonical apex transformation from `u` to the textbook
factorization. -/
private noncomputable def hom_to_explicitTwoFibreProduct_terminalLift_twoHom
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G) :
    u ⟶ explicitTwoFibreProduct_terminalLift F G P :=
  { hom := hom_to_explicitTwoFibreProduct_terminalLift_hom F G P u
    left_comm := by
      -- On the left leg, the chosen component was built to be exactly `u.left.app T`.
      apply basedNatTrans_ext_toNatTrans
      ext T
      exact hom_to_explicitTwoFibreProduct_terminalLift_left_comm_app F G P u T
    right_comm := by
      -- On the right leg, the same construction recovers `u.right.app T`.
      apply basedNatTrans_ext_toNatTrans
      ext T
      exact hom_to_explicitTwoFibreProduct_terminalLift_right_comm_app F G P u T }

/-- Helper for Lemma 4.32.3: any `2`-morphism into the textbook factorization is forced by its
left and right projection components. -/
private theorem hom_to_explicitTwoFibreProduct_terminalLift_twoHom_eq
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G)
    (η : u ⟶ explicitTwoFibreProduct_terminalLift F G P) :
    η = hom_to_explicitTwoFibreProduct_terminalLift_twoHom F G P u := by
  -- The apex natural transformation is determined objectwise by its left and right projections.
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  apply basedNatTrans_ext_toNatTrans
  ext T
  apply ExplicitTwoFibreProductHom.ext
  · have hη := congrArg BasedNatTrans.toNatTrans η.left_comm
    have hηT := congrArg (fun τ => τ.app T) hη
    have hηT' :
        ((η.hom ▷ (explicitTwoFibreProductSquare F G).p).app T) = u.left.app T := by
      change ((η.hom ▷ (explicitTwoFibreProductSquare F G).p).app T) ≫
          ((𝟙 P.p : P.p ⟶ P.p).app T) =
        u.left.app T at hηT
      have hid :
          ((η.hom ▷ (explicitTwoFibreProductSquare F G).p).app T) =
            ((η.hom ▷ (explicitTwoFibreProductSquare F G).p).app T) ≫ 𝟙 (P.p.obj T) := by
        exact (Category.comp_id _).symm
      simpa using hid.trans hηT
    -- The left compatibility identifies the `a`-component with `u.left.app T`.
    change ((η.hom ▷ (explicitTwoFibreProductSquare F G).p).app T) =
      ((hom_to_explicitTwoFibreProduct_terminalLift_twoHom F G P u).hom.app T).a
    simpa [explicitTwoFibreProduct_terminalLift, hom_to_explicitTwoFibreProduct_terminalLift_twoHom,
      hom_to_explicitTwoFibreProduct_terminalLift_hom,
      hom_to_explicitTwoFibreProduct_terminalLift_component, explicitTwoFibreProductSquare,
      explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using hηT'
  · have hη := congrArg BasedNatTrans.toNatTrans η.right_comm
    have hηT := congrArg (fun τ => τ.app T) hη
    have hηT' :
        ((η.hom ▷ (explicitTwoFibreProductSquare F G).q).app T) = u.right.app T := by
      change ((η.hom ▷ (explicitTwoFibreProductSquare F G).q).app T) ≫
          ((𝟙 P.q : P.q ⟶ P.q).app T) =
        u.right.app T at hηT
      have hid :
          ((η.hom ▷ (explicitTwoFibreProductSquare F G).q).app T) =
            ((η.hom ▷ (explicitTwoFibreProductSquare F G).q).app T) ≫ 𝟙 (P.q.obj T) := by
        exact (Category.comp_id _).symm
      simpa using hid.trans hηT
    -- The right compatibility identifies the `b`-component with `u.right.app T`.
    change ((η.hom ▷ (explicitTwoFibreProductSquare F G).q).app T) =
      ((hom_to_explicitTwoFibreProduct_terminalLift_twoHom F G P u).hom.app T).b
    simpa [explicitTwoFibreProduct_terminalLift, hom_to_explicitTwoFibreProduct_terminalLift_twoHom,
      hom_to_explicitTwoFibreProduct_terminalLift_hom,
      hom_to_explicitTwoFibreProduct_terminalLift_component, explicitTwoFibreProductSquare,
      explicitTwoFibreProductRightProjection, explicitTwoFibreProduct] using hηT'

/-- Helper for Lemma 4.32.3: every morphism into the explicit pullback square admits a unique
`2`-morphism to the canonical factorization. -/
private noncomputable abbrev hom_to_explicitTwoFibreProduct_terminalLift_unique
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ explicitTwoFibreProductSquare F G) :
    Unique (u ⟶ explicitTwoFibreProduct_terminalLift F G P) := by
  -- Package the canonical `2`-morphism and the uniqueness forced by the two projection legs.
  refine
    { default := hom_to_explicitTwoFibreProduct_terminalLift_twoHom F G P u
      uniq := ?_ }
  intro η
  exact hom_to_explicitTwoFibreProduct_terminalLift_twoHom_eq F G P u η

/-- Helper for Lemma 4.32.3: the textbook factorization is terminal in the fixed hom-category
into the explicit pullback square. -/
private noncomputable def explicitTwoFibreProduct_terminalLift_isTerminal
    (P : BicategoricalTwoCommutativeSquare F G) :
    Limits.IsTerminal
      (explicitTwoFibreProduct_terminalLift F G P :
        P ⟶ explicitTwoFibreProductSquare F G) :=
  -- Package the already-constructed canonical `2`-morphism and its uniqueness at the fixed
  -- hom-category object `explicitTwoFibreProduct_terminalLift F G P`.
  Limits.IsTerminal.ofUniqueHom
    (fun u ↦ hom_to_explicitTwoFibreProduct_terminalLift_twoHom F G P u)
    (fun u η ↦ hom_to_explicitTwoFibreProduct_terminalLift_twoHom_eq F G P u η)

/-- Helper for Lemma 4.32.3: for any competing square, the hom-category into the explicit
pullback square has a terminal object given by the textbook factorization. -/
private theorem explicitTwoFibreProductSquare_hasTerminal
    (P : BicategoricalTwoCommutativeSquare F G) :
    HasTerminal
      (BicategoricalTwoCommutativeSquare.Hom P (explicitTwoFibreProductSquare F G)) := by
  -- Route correction: freeze the hom-category through the typed terminal object first, and only
  -- then pass to `HasTerminal` using `.hasTerminal`.
  change HasTerminal (P ⟶ explicitTwoFibreProductSquare F G)
  exact (explicitTwoFibreProduct_terminalLift_isTerminal F G P).hasTerminal

/-- Lemma 4.32.3: for morphisms `F : X ⟶ S` and `G : Y ⟶ S` in `Cat/C`, the explicit square
constructed from the fibrewise pullback owner is a `2`-fibre product in the bicategory `Cat/C`.
In particular, `Cat/C` has `2`-fibre products. -/
theorem explicitTwoFibreProduct_isTwoFibreProduct :
    Bicategory.IsFinal (explicitTwoFibreProductSquare F G) := by
  -- Route correction: prove the universal property directly in `Cat/C` by the textbook
  -- factorization `T ↦ (p(T), S.p(T), S.q(T), ψ_T)`.
  refine ⟨fun P ↦ ?_⟩
  -- The remaining work is only the terminal-object packaging in the fixed hom-category.
  exact explicitTwoFibreProductSquare_hasTerminal F G P

end

end CategoryOver
end CategoryTheory
