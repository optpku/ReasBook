module

public import stacks_project.Chap04.Definition_4_31_2
public import stacks_project.Chap04.Example_4_31_3
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory.Limits

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped Bicategory CategoricalPullback

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable (F : A ⥤ C) (G : B ⥤ C)

/- Domain-style sampling for Lemma 4.31.4:
- primary domain: bicategorical `2`-fibre products in `Cat`, presented through the categorical
  pullback model of Example `4.31.3`;
- inspected owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `CategoricalPullback.toCatCommSqOver`,
  `CatCommSqOver.toBicategoricalSquare`,
  `CategoricalPullback.functorEquiv`;
- best owner abstraction: the chapter's source-facing owner is
  `Bicategory.IsFinal (categoricalPullbackSquare F G)`, where the square itself is the canonical
  pullback square from Example `4.31.3` viewed in the bicategory of `2`-commutative squares;
- primitive data: the categorical pullback object `F ⊡ G` and its canonical square
  `toCatCommSqOver F G (F ⊡ G)`;
- derived API: the universal property equivalence `CategoricalPullback.functorEquiv F G X`,
  transferred to the chapter's square owner by `CatCommSqOver.toBicategoricalSquare`.

Source/core/bridge triage:
- `source-facing`: the square `categoricalPullbackSquare F G` and its `2`-fibre-product property;
- `core/canonical`: `Bicategory.IsFinal (categoricalPullbackSquare F G)`;
- `bridge/view`: `CategoricalPullback.functorEquiv F G X` and
  `CatCommSqOver.toBicategoricalSquare`. -/

/-- The canonical square from Example 4.31.3, viewed as an object of the chapter's bicategory of
`2`-commutative squares over `F` and `G`. -/
abbrev categoricalPullbackSquare :
    BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom :=
  ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).toBicategoricalSquare

/-- Helper for Lemma 4.31.4: reinterpret a bicategorical square in `Cat` as a categorical
commutative square over `F` and `G`. -/
abbrev as_catCommSqOver
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom) :
    CatCommSqOver F G S.obj :=
  { fst := S.p.toFunctor
    snd := S.q.toFunctor
    iso := Cat.Hom.toNatIso S.ψ }

/-- Helper for Lemma 4.31.4: the compatibility condition of a morphism in `CatCommSqOver`,
evaluated at an object, is exactly the objectwise bicategorical square equation in `Cat`. -/
lemma catCommSqOver_hom_to_square_hom_comm
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (J : S.obj ⥤ F ⊡ G)
    (φ : (toCatCommSqOver F G S.obj).obj J ⟶ as_catCommSqOver F G S)
    (x : S.obj) :
    (Cat.Hom₂.toNatTrans
        ((φ.fst.toCatHom₂ ▷ F.toCatHom) ≫ S.ψ.hom)).app x =
      (Cat.Hom₂.toNatTrans
        ((α_ J.toCatHom (categoricalPullbackSquare F G).p F.toCatHom).hom ≫
          J.toCatHom ◁ (categoricalPullbackSquare F G).ψ.hom ≫
          (α_ J.toCatHom (categoricalPullbackSquare F G).q G.toCatHom).inv ≫
          (φ.snd.toCatHom₂ ▷ G.toCatHom))).app x := by
  let mid := (((toCatCommSqOver F G S.obj).obj J).iso.hom.app x) ≫ G.map (φ.snd.app x)
  -- Route correction: compare both sides with the common `CatCommSqOver` midpoint
  -- `((toCatCommSqOver ...).obj J).iso.hom.app x ≫ G.map (φ.snd.app x)`.
  have hw :
      (Cat.Hom₂.toNatTrans ((φ.fst.toCatHom₂ ▷ F.toCatHom) ≫ S.ψ.hom)).app x = mid := by
    -- This is exactly the objectwise compatibility equation of `φ`.
    simpa [mid, as_catCommSqOver] using
      (CatCommSqOver.w_app
        (F := F) (G := G) (X := S.obj) (S := (toCatCommSqOver F G S.obj).obj J)
        (S' := as_catCommSqOver F G S) φ x)
  have hr :
      (Cat.Hom₂.toNatTrans
        ((α_ J.toCatHom (categoricalPullbackSquare F G).p F.toCatHom).hom ≫
          J.toCatHom ◁ (categoricalPullbackSquare F G).ψ.hom ≫
          (α_ J.toCatHom (categoricalPullbackSquare F G).q G.toCatHom).inv ≫
          (φ.snd.toCatHom₂ ▷ G.toCatHom))).app x = mid := by
    -- The canonical pullback square term reduces to the same midpoint after expanding the
    -- remaining ordinary natural-transformation compositions.
    repeat rw [Cat.Hom₂.comp_app]
    rw [Cat.associator_hom_app]
    have hnat :
        (J.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
            (J.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
            Functor.whiskerRight φ.snd G).app x = mid := by
      repeat rw [NatTrans.comp_app]
      simp [mid]
    have h1 :
        𝟙 (F.obj (J.obj x).fst) ≫
          (J.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
              (J.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
              Functor.whiskerRight φ.snd G).app x =
            (J.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
              (J.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
              Functor.whiskerRight φ.snd G).app x := by
      simp
    exact h1.trans hnat
  exact hw.trans hr.symm

/-- Helper for Lemma 4.31.4: the compatibility field of a bicategorical square morphism into the
canonical pullback square becomes the natural-transformation equation required in
`CatCommSqOver` after applying `toNatTrans` and evaluating at an object. -/
lemma square_hom_comm_to_catCommSqOver_w
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (u : S ⟶ categoricalPullbackSquare F G)
    (x : S.obj) :
    F.map (u.left.toNatTrans.app x) ≫ S.ψ.hom.toNatTrans.app x =
      (((toCatCommSqOver F G S.obj).obj u.hom.toFunctor).iso.hom.app x) ≫
        G.map (u.right.toNatTrans.app x) := by
  -- Route correction: expand `u.comm` to an objectwise equality in `Cat`, then compare its
  -- right-hand side with the pullback object's structural isomorphism.
  have h := congrArg Cat.Hom₂.toNatTrans u.comm
  have h' := congrArg (fun τ ↦ τ.app x) h
  let rhs' :=
    (Cat.Hom₂.toNatTrans
      ((α_ u.hom (categoricalPullbackSquare F G).p F.toCatHom).hom ≫
        u.hom ◁ (categoricalPullbackSquare F G).ψ.hom ≫
        (α_ u.hom (categoricalPullbackSquare F G).q G.toCatHom).inv ≫
        (u.right ▷ G.toCatHom))).app x
  have hr :
      rhs' = (((toCatCommSqOver F G S.obj).obj u.hom.toFunctor).iso.hom.app x) ≫
        G.map (u.right.toNatTrans.app x) := by
    -- The canonical pullback square term collapses to the pullback object's internal `iso.hom`
    -- after expanding the remaining ordinary natural-transformation compositions.
    dsimp [rhs']
    have hnat :
        (u.hom.toFunctor.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
            (u.hom.toFunctor.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
            Functor.whiskerRight u.right.toNatTrans G).app x =
          (((toCatCommSqOver F G S.obj).obj u.hom.toFunctor).iso.hom.app x) ≫
            G.map (u.right.toNatTrans.app x) := by
      repeat rw [NatTrans.comp_app]
      simp
    have h1 :
        𝟙 (F.obj (u.hom.toFunctor.obj x).fst) ≫
          (u.hom.toFunctor.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
              (u.hom.toFunctor.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
              Functor.whiskerRight u.right.toNatTrans G).app x =
            (u.hom.toFunctor.whiskerLeft ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).iso.hom ≫
              (u.hom.toFunctor.associator ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).snd G).inv ≫
              Functor.whiskerRight u.right.toNatTrans G).app x := by
      simp
    exact h1.trans hnat
  -- After the owner-level normalization, `u.comm` becomes the desired `CatCommSqOver` equation.
  simpa [rhs', Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app, Category.assoc] using h'.trans hr

/-- Helper for Lemma 4.31.4: a morphism of categorical squares over `F` and `G` yields a
`1`-morphism from the corresponding bicategorical square to the canonical pullback square. -/
abbrev catCommSqOver_hom_to_square_hom
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (J : S.obj ⥤ F ⊡ G)
    (φ : (toCatCommSqOver F G S.obj).obj J ⟶ as_catCommSqOver F G S) :
    S ⟶ categoricalPullbackSquare F G := by
  refine
    { hom := J.toCatHom
      left := φ.fst.toCatHom₂
      right := φ.snd.toCatHom₂
      comm := ?_ }
  -- The commutativity field is the objectwise square equation transported through `Cat`.
  apply Cat.Hom₂.ext
  ext x
  exact catCommSqOver_hom_to_square_hom_comm F G S J φ x

/-- Helper for Lemma 4.31.4: a morphism into the canonical pullback square is the same data as a
morphism in `CatCommSqOver` from its apex functor to the original square. -/
abbrev hom_to_catCommSqOver_hom
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (u : S ⟶ categoricalPullbackSquare F G) :
    (toCatCommSqOver F G S.obj).obj u.hom.toFunctor ⟶ as_catCommSqOver F G S := by
  refine
    { fst := u.left.toNatTrans
      snd := u.right.toNatTrans
      w := ?_ }
  -- The bicategorical square equation becomes the `CatCommSqOver` compatibility field.
  ext x
  exact square_hom_comm_to_catCommSqOver_w F G S u x

/-- Helper for Lemma 4.31.4: the textbook factorization through `A ×[C] B` obtained by sending an
object `W` to the triple `(a(W), b(W), t_W)`. -/
abbrev terminal_lift
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom) :
    S ⟶ categoricalPullbackSquare F G :=
  catCommSqOver_hom_to_square_hom F G S
    ((CatCommSqOver.toFunctorToCategoricalPullback F G S.obj).obj (as_catCommSqOver F G S))
    (((CategoricalPullback.functorEquiv F G S.obj).counitIso.app (as_catCommSqOver F G S)).hom)

/-- Helper for Lemma 4.31.4: a `2`-morphism between factorizations is equivalent to equality of the
induced morphisms in `CatCommSqOver`. -/
lemma twoHom_to_catCommSqOver_hom
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    {u v : S ⟶ categoricalPullbackSquare F G}
    (η : u ⟶ v) :
    (toCatCommSqOver F G S.obj).map η.hom.toNatTrans ≫ hom_to_catCommSqOver_hom F G S v =
      hom_to_catCommSqOver_hom F G S u := by
  -- The induced equality is detected on the two projection components in `CatCommSqOver`.
  apply CatCommSqOver.hom_ext
  · ext x
    -- The first projection is exactly the left compatibility condition of `η`.
    simpa [hom_to_catCommSqOver_hom, categoricalPullbackSquare] using
      congrArg (fun τ => τ.app x) (congrArg Cat.Hom₂.toNatTrans η.left_comm)
  · ext x
    -- The second projection is exactly the right compatibility condition of `η`.
    simpa [hom_to_catCommSqOver_hom, categoricalPullbackSquare] using
      congrArg (fun τ => τ.app x) (congrArg Cat.Hom₂.toNatTrans η.right_comm)

/-- Helper for Lemma 4.31.4: the `CatCommSqOver` morphism attached to `terminal_lift` is the
counit of the categorical pullback equivalence. -/
lemma hom_to_catCommSqOver_hom_terminal_lift
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom) :
    hom_to_catCommSqOver_hom F G S (terminal_lift F G S) =
      ((CategoricalPullback.functorEquiv F G S.obj).counitIso.app
        (as_catCommSqOver F G S)).hom := by
  -- Both morphisms have the same two projection components, so `hom_ext` closes the comparison.
  apply CatCommSqOver.hom_ext <;> rfl

/-- Helper for Lemma 4.31.4: every morphism into the canonical pullback square admits a unique
`2`-morphism to the canonical factorization `terminal_lift`. -/
noncomputable abbrev hom_to_terminal_unique
    (S : BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom)
    (u : S ⟶ categoricalPullbackSquare F G) :
    Unique (u ⟶ terminal_lift F G S) := by
  let E := (CategoricalPullback.functorEquiv F G S.obj).functor
  let counit := (CategoricalPullback.functorEquiv F G S.obj).counitIso.app
    (as_catCommSqOver F G S)
  let δ := E.preimage (hom_to_catCommSqOver_hom F G S u ≫ counit.inv)
  have hterminal :
      hom_to_catCommSqOver_hom F G S (terminal_lift F G S) = counit.hom := by
    simpa [counit] using hom_to_catCommSqOver_hom_terminal_lift F G S
  have hpre :
      (toCatCommSqOver F G S.obj).map δ =
        hom_to_catCommSqOver_hom F G S u ≫ counit.inv := by
    simpa [E, δ, counit] using
      (E.map_preimage (hom_to_catCommSqOver_hom F G S u ≫ counit.inv))
  have hδ :
      (toCatCommSqOver F G S.obj).map δ ≫ hom_to_catCommSqOver_hom F G S (terminal_lift F G S) =
        hom_to_catCommSqOver_hom F G S u := by
    have hδc :
        (toCatCommSqOver F G S.obj).map δ ≫ counit.hom =
          hom_to_catCommSqOver_hom F G S u := by
      rw [hpre]
      have h :
          (hom_to_catCommSqOver_hom F G S u ≫ counit.inv) ≫ counit.hom =
            hom_to_catCommSqOver_hom F G S u := by
        simp [Category.assoc]
      exact h
    simpa [hterminal] using hδc
  let η0 : u ⟶ terminal_lift F G S :=
    { hom := δ.toCatHom₂
      left_comm := by
        simpa [δ, hom_to_catCommSqOver_hom] using
          congrArg NatTrans.toCatHom₂ (congrArg CatCommSqOver.Hom.fst hδ)
      right_comm := by
        simpa [δ, hom_to_catCommSqOver_hom] using
          congrArg NatTrans.toCatHom₂ (congrArg CatCommSqOver.Hom.snd hδ) }
  refine { default := η0, uniq := ?_ }
  intro η
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  have hη :
      (toCatCommSqOver F G S.obj).map η.hom.toNatTrans ≫
        hom_to_catCommSqOver_hom F G S (terminal_lift F G S) =
      hom_to_catCommSqOver_hom F G S u :=
    twoHom_to_catCommSqOver_hom F G S η
  have hηc :
      (toCatCommSqOver F G S.obj).map η.hom.toNatTrans ≫ counit.hom =
        hom_to_catCommSqOver_hom F G S u := by
    simpa [hterminal] using hη
  have hη' :
      (toCatCommSqOver F G S.obj).map η.hom.toNatTrans =
        hom_to_catCommSqOver_hom F G S u ≫ counit.inv := by
    exact (CategoryTheory.Iso.eq_comp_inv counit).2 hηc
  exact congrArg NatTrans.toCatHom₂ (E.map_injective (hη'.trans hpre.symm))

/-- Lemma 4.31.4: the canonical square carried by the categorical pullback `F ⊡ G` is a
`2`-fibre product square in the bicategory of `2`-commutative squares over `F` and `G`. -/
theorem categoricalPullback_isTwoFibreProduct :
    Bicategory.IsFinal (categoricalPullbackSquare F G) := by
  -- For each source square, the hom-category into the pullback square has a terminal factorization.
  refine ⟨fun S ↦ ?_⟩
  -- The chosen factorization is `terminal_lift`, and uniqueness follows from the pullback
  -- equivalence transported through `CatCommSqOver`.
  let _ : ∀ Y : S ⟶ categoricalPullbackSquare F G, Unique (Y ⟶ terminal_lift F G S) :=
    fun Y ↦ hom_to_terminal_unique F G S Y
  exact Limits.hasTerminal_of_unique (terminal_lift F G S)

/- Companion bridge/view: the universal property above is implemented by the canonical pullback
equivalence between functors into `F ⊡ G` and commutative squares over `F` and `G`. -/
recall CategoricalPullback.functorEquiv

end CategoryTheory.Limits
