/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import AlgebraicTopology_May_1999.Chap03.Construction_3_6_2
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_3
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_7
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_7
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_10
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_3
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_8
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_11
import AlgebraicTopology_May_1999.Chap03.Remark_3_3_13
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]

/-- Groupoid functors over `B`, with varying total groupoid and fixed codomain `B`. This is a
universe-stable owner for the source-facing over-category of groupoid functors to `B`. -/
structure GroupoidFunctorOver (B : Type u) [Groupoid.{v} B] : Type (max u v + 1) where
  left : Type (max u v)
  groupoid_left : Groupoid.{v} left
  hom : left ⥤ B

attribute [instance] GroupoidFunctorOver.groupoid_left

namespace GroupoidFunctorOver

/-- Morphisms over `B` are functors between total groupoids commuting with the structure maps to
`B`. -/
@[ext] structure Hom (X Y : GroupoidFunctorOver B) where
  left : X.left ⥤ Y.left
  comm : left ⋙ Y.hom = X.hom

/-- Constructor for morphisms over `B`. -/
abbrev homMk {X Y : GroupoidFunctorOver B} (F : X.left ⥤ Y.left)
    (hF : F ⋙ Y.hom = X.hom) : Hom X Y :=
  ⟨F, hF⟩

instance : Quiver (GroupoidFunctorOver B) where
  Hom X Y := Hom X Y

instance : Category (GroupoidFunctorOver B) where
  id X := ⟨𝟭 X.left, rfl⟩
  comp {X Y Z} f g := ⟨f.left ⋙ g.left, by
    calc
      (f.left ⋙ g.left) ⋙ Z.hom = f.left ⋙ (g.left ⋙ Z.hom) := rfl
      _ = f.left ⋙ Y.hom := by rw [g.comm]
      _ = X.hom := f.comm⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end GroupoidFunctorOver

/-- The category `Cov(B)` of connected covering functors over the groupoid `B`, realized as the
full subcategory of groupoid functors over `B` on covering functors with connected total
groupoid. -/
abbrev ConnectedCovering (B : Type u) [Groupoid.{v} B] : Type (max u v + 1) :=
  ObjectProperty.FullSubcategory
    (fun X : GroupoidFunctorOver B ↦ Functor.IsCovering X.hom ∧ IsConnected X.left)

namespace ConnectedCovering

/-- The underlying functor of an object of `Cov(B)` is a covering functor over `B`. -/
theorem isCovering (X : ConnectedCovering B) :
    Functor.IsCovering X.obj.hom :=
  X.2.1

/-- The total groupoid of an object of `Cov(B)` is connected. -/
theorem isConnected (X : ConnectedCovering B) :
    IsConnected X.obj.left :=
  X.2.2

end ConnectedCovering

variable (b : B)

variable (S T : Type v) [MulAction (End b) S] [MulAction (End b) T]

/-- The fiber over `x` associated to a `π(B,b)`-set is the orbit quotient of pairs
`(b ⟶ x, s)` for the diagonal action of `π(B,b)`. -/
abbrev associatedActionObj (x : B) : Type v :=
  MulAction.orbitRel.Quotient (End b) ((b ⟶ x) × S)

/-- Transport in the associated `B`-action is induced by postcomposition on the arrow component. -/
def associatedActionMap {x y : B} (f : x ⟶ y) :
    associatedActionObj b S x → associatedActionObj b S y :=
  Quotient.map' (fun p : (b ⟶ x) × S ↦ (p.1 ≫ f, p.2)) <| by
    intro p q hp
    rw [MulAction.orbitRel_apply] at hp ⊢
    rcases hp with ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    ext
    · change g⁻¹ ≫ (q.1 ≫ f) = (g⁻¹ ≫ q.1) ≫ f
      simp [Category.assoc]
    · rfl

/-- The `B`-action associated to a `π(B,b)`-set by the standard twisted-product construction. -/
def associatedAction : B ⥤ Type v where
  obj := associatedActionObj b S
  map f := TypeCat.ofHom (associatedActionMap b S f)
  map_id x := by
    ext q
    refine Quotient.inductionOn' q ?_
    intro p
    change Quotient.mk'' (p.1 ≫ 𝟙 x, p.2) = Quotient.mk'' p
    simp
  map_comp f g := by
    ext q
    refine Quotient.inductionOn' q ?_
    intro p
    change Quotient.mk'' (p.1 ≫ (f ≫ g), p.2) = Quotient.mk'' ((p.1 ≫ f) ≫ g, p.2)
    simp [Category.assoc]

/-- A `π(B,b)`-equivariant map induces a natural transformation of the associated `B`-actions. -/
def associatedActionHom {S T : Type v} [MulAction (End b) S] [MulAction (End b) T]
    (φ : S →[End b] T) :
    associatedAction b S ⟶ associatedAction b T where
  app x := TypeCat.ofHom <| Quotient.map' (fun p : (b ⟶ x) × S ↦ (p.1, φ p.2)) <| by
      intro p q hp
      rw [MulAction.orbitRel_apply] at hp ⊢
      rcases hp with ⟨g, rfl⟩
      refine ⟨g, ?_⟩
      ext
      · rfl
      · simpa using map_smulₛₗ φ g q.2
  naturality {x} {y} f := by
    ext q
    refine Quotient.inductionOn' q ?_
    intro p
    rfl

variable {S}

/-- Helper for Theorem 3.6.1: evaluating the base fiber class `[γ, s]` by the original
`π(B,b)`-action produces a well-defined point of `S`. -/
private abbrev associatedAction_base_eval
    (b : B) (S : Type v) [MulAction (End b) S] (p : (b ⟶ b) × S) : S :=
  (show End b from p.1) • p.2

/-- Helper for Theorem 3.6.1: evaluating the base fiber class `[γ, s]` by the original
`π(B,b)`-action produces a well-defined point of `S`. -/
private theorem associatedAction_base_map_wellDefined
    (b : B) (S : Type v) [MulAction (End b) S] :
    ∀ p q : (b ⟶ b) × S,
      MulAction.orbitRel (End b) ((b ⟶ b) × S) p q →
        associatedAction_base_eval b S p = associatedAction_base_eval b S q := by
  intro p q hp
  rw [MulAction.orbitRel_apply] at hp
  rcases hp with ⟨g, rfl⟩
  -- The diagonal orbit relation exactly preserves the evaluated point `γ • s`.
  change (show End b from g⁻¹ ≫ q.1) • (g • q.2) = (show End b from q.1) • q.2
  simpa [orbitCoveringHomMulAction_smul, CategoryTheory.End.mul_def, Category.assoc] using
    (smul_smul (show End b from g⁻¹ ≫ q.1) g q.2)

/-- Helper for Theorem 3.6.1: the base fiber of the associated action maps to the original
`π(B,b)`-set by evaluation. -/
private noncomputable def associatedAction_base_map
    (b : B) (S : Type v) [MulAction (End b) S] :
    associatedActionObj b S b → S :=
  Quotient.lift (associatedAction_base_eval b S)
    (associatedAction_base_map_wellDefined b S)

/-- Helper for Theorem 3.6.1: evaluating the class of a representative `(γ, s)` in the base
fiber gives `γ • s`. -/
private theorem associatedAction_base_map_mk
    (b : B) (S : Type v) [MulAction (End b) S] (p : (b ⟶ b) × S) :
    associatedAction_base_map b S (Quotient.mk'' p) = associatedAction_base_eval b S p :=
  rfl

/-- Helper for Theorem 3.6.1: the evaluation map identifies the base fiber of the associated
action with the original `π(B,b)`-set. -/
private theorem associatedAction_base_map_bijective
    (b : B) (S : Type v) [MulAction (End b) S] :
    Function.Bijective (associatedAction_base_map b S) := by
  constructor
  · intro q₁ q₂ hq
    -- Each quotient class is represented by an identity-arrow class over its evaluated point.
    have hrepr :
        ∀ q : associatedActionObj b S b,
          Quotient.mk'' (𝟙 b, associatedAction_base_map b S q) = q := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro p
      change Quotient.mk'' (𝟙 b, associatedAction_base_eval b S p) = Quotient.mk'' p
      apply Quotient.sound
      change MulAction.orbitRel (End b) ((b ⟶ b) × S) (𝟙 b, associatedAction_base_eval b S p) p
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
      refine ⟨p.1⁻¹, ?_⟩
      ext
      · change (p.1⁻¹)⁻¹ ≫ 𝟙 b = p.1
        simp
      · simpa [CategoryTheory.End.mul_def] using (smul_smul p.1⁻¹ p.1 p.2).symm
    rw [← hrepr q₁, ← hrepr q₂, hq]
  · intro s
    -- The identity arrow gives a canonical class mapping to the chosen point.
    refine ⟨Quotient.mk'' (𝟙 b, s), ?_⟩
    simpa [associatedAction_base_map, associatedAction_base_eval] using (one_smul (End b) s)

/-- Helper for Theorem 3.6.1: the base fiber of the associated action is canonically equivalent
to the original `π(B,b)`-set. -/
private noncomputable def associatedAction_base_equiv
    (b : B) (S : Type v) [MulAction (End b) S] :
    associatedActionObj b S b ≃ S :=
  Equiv.ofBijective (associatedAction_base_map b S)
    (associatedAction_base_map_bijective b S)

/-- Helper for Theorem 3.6.1: the base-fiber equivalence intertwines the direct `End b`-action on
the associated action with the original action on `S`. -/
private theorem associatedAction_base_equiv_smul
    (b : B) (S : Type v) [MulAction (End b) S] (g : End b)
    (q : associatedActionObj b S b) :
    associatedAction_base_equiv b S ((associatedAction b S).map g q) =
      g • associatedAction_base_equiv b S q := by
  -- Compare both sides on representatives of the quotient.
  refine Quotient.inductionOn' q ?_
  intro p
  simpa [associatedAction_base_equiv, associatedAction_base_map,
    CategoryTheory.End.mul_def, Category.assoc] using
    (smul_smul g p.1 p.2).symm

/-- The associated `B`-action of a transitive `π(B,b)`-set is transitive when `B` is
connected. -/
-- Proof sketch: use connectedness of `B` to move any point of a fiber to the base object `b`,
-- reduce there to the original `π(B,b)`-action, and transport both a chosen point and the orbit
-- relation back to the target fiber.
theorem associatedAction_isTransitive [IsConnected B]
    (hS : MulAction.IsTransitive (End b) S) :
    Functor.IsTransitive (associatedAction b S) := by
  have hb :
      letI := Functor.vertexGroupMulAction (associatedAction b S) b
      MulAction.IsTransitive (End b) ((associatedAction b S).obj b) := by
    letI := Functor.vertexGroupMulAction (associatedAction b S) b
    rcases hS with ⟨hSn, hSpre⟩
    refine ⟨hSn.map (associatedAction_base_equiv b S).symm, ?_⟩
    obtain ⟨s₀⟩ := hSn
    have hSbase : ∀ y : S, ∃ g : End b, g • s₀ = y :=
      (MulAction.isPretransitive_iff_base s₀).mp hSpre
    let q₀ : (associatedAction b S).obj b := (associatedAction_base_equiv b S).symm s₀
    have hbase :
        ∀ q : (associatedAction b S).obj b,
          ∃ g : End b, (associatedAction b S).map g q₀ = q := by
      intro q
      rcases hSbase (associatedAction_base_equiv b S q) with ⟨g, hg⟩
      refine ⟨g, ?_⟩
      apply (associatedAction_base_equiv b S).injective
      -- Move the orbit witness across the base-fiber identification.
      simpa [q₀, associatedAction_base_equiv_smul] using hg
    exact (MulAction.isPretransitive_iff_base q₀).2 hbase
  -- Global transitivity follows once the base vertex-group action is transitive.
  exact
    (Functor.isTransitive_iff_forall_vertexGroupMulAction_isTransitive
      (associatedAction b S)).mpr
      (Functor.forall_vertexGroupMulAction_isTransitive_of_isConnected
        (associatedAction b S) b hb)

/-- The associated action of an orbit-category object is transitive over a connected base
groupoid. -/
-- Proof sketch: combine the general transitivity theorem for associated actions with the
-- transitivity of the orbit `π(B,b) / H`.
theorem orbitCategoryAssociatedAction_isTransitive [IsConnected B]
    (H : O(End b)) :
    Functor.IsTransitive (associatedAction b (End b ⧸ H)) := by
  -- The orbit object `π(B,b) / H` is already a transitive `π(B,b)`-set.
  exact associatedAction_isTransitive b
    (S := End b ⧸ H)
    (orbitCategory_obj_isTransitive (G := End b) H)

/-- Passing to categories of elements turns a `B`-action into a groupoid functor over `B`. -/
abbrev elementsFunctorOver (T : B ⥤ Type v) : GroupoidFunctorOver B :=
  { left := T.Elements
    groupoid_left := inferInstance
    hom := CategoryOfElements.π T }

/-- If every vertex-group action of `T` is transitive, then the projection from its category of
elements to `B` is a covering functor. -/
-- Proof sketch: transitivity makes every fiber nonempty, so the projection is surjective on
-- objects. Morphisms in the category of elements are determined uniquely by their image in `B`,
-- which yields the required bijection on stars.
theorem transitiveAction_elements_isCovering
    (T : B ⥤ Type v) (hT : Functor.IsTransitive T) :
    Functor.IsCovering (CategoryOfElements.π T) := by
  refine ⟨?_, ?_⟩
  · intro b
    -- Use transitivity at `b` to choose a point in the fiber over `b`.
    rcases hT b with ⟨hb, _⟩
    obtain ⟨t⟩ := hb
    exact ⟨⟨b, t⟩, rfl⟩
  · intro e
    -- Route correction: avoid a global left inverse on arbitrary dependent `Under` objects.
    -- Instead, normalize each star object to a literal `Under.mk` representative.
    let lift : Under e.1 → Under e := fun u ↦
      Under.mk (CategoryOfElements.homMk e ⟨u.right, T.map u.hom e.2⟩ u.hom rfl)
    have hlift :
        ∀ u : Under e,
          lift ((Under.post (CategoryOfElements.π T)).obj u) = u := by
      intro u
      obtain ⟨Y, f, rfl⟩ := Under.mk_surjective u
      let Y₀ : T.Elements := ⟨Y.1, T.map f.val e.2⟩
      let m₀ : e ⟶ Y₀ := CategoryOfElements.homMk e Y₀ f.val rfl
      have hY : Y₀ = Y := by
        refine Functor.Elements.ext _ _ rfl ?_
        simp [Y₀, CategoryOfElements.map_snd]
      have hm : m₀ ≫ eqToHom hY = f := by
        -- Compare the two morphisms only on their underlying arrows in `B`.
        apply CategoryOfElements.ext T
        have hmap : (CategoryOfElements.π T).map (eqToHom hY) = 𝟙 Y.1 := by
          simpa [Y₀] using eqToHom_map (CategoryOfElements.π T) hY
        change f.val ≫ (eqToHom hY).val = f.val
        simpa using congrArg (fun k => f.val ≫ k) hmap
      calc
        lift ((Under.post (CategoryOfElements.π T)).obj (Under.mk f)) = Under.mk m₀ := by
          rfl
        _ = Under.mk (m₀ ≫ eqToHom hY) := by
          symm
          exact CategoryTheory.Functor.IsCovering.under_mk_comp_eqToHom m₀ hY
        _ = Under.mk f := by
          rw [hm]
    refine ⟨?_, ?_⟩
    · intro u₁ u₂ h
      -- The normalized lift is a left inverse to the star map, hence injectivity.
      rw [← hlift u₁, ← hlift u₂, h]
    · intro u
      -- On a literal `Under.mk` representative, the chosen lift maps back definitionally.
      refine ⟨lift u, ?_⟩
      obtain ⟨Y, f, rfl⟩ := Under.mk_surjective u
      rfl

variable [IsConnected B]

/-- For a connected base groupoid, the category of elements of a transitive `B`-action is
connected. -/
-- Proof sketch: choose an arrow in `B` joining the underlying base objects and then use
-- transitivity in the target fiber to connect the transported element to the chosen target point.
theorem transitiveAction_elements_isConnected
    (T : B ⥤ Type v) (hT : Functor.IsTransitive T) :
    IsConnected T.Elements := by
  classical
  let b₀ : B := Classical.choice inferInstance
  rcases hT b₀ with ⟨hb₀, _⟩
  obtain ⟨t₀⟩ := hb₀
  let x₀ : T.Elements := ⟨b₀, t₀⟩
  have hAll :
      ∀ x : B,
        letI := Functor.vertexGroupMulAction T x
        MulAction.IsTransitive (End x) (T.obj x) :=
    (Functor.isTransitive_iff_forall_vertexGroupMulAction_isTransitive T).mp hT
  refine CategoryTheory.IsConnected.of_induct (j₀ := x₀) ?_
  intro p hp₀ hstep y
  rcases y with ⟨b', t⟩
  let f : b₀ ⟶ b' := Classical.choice
    (CategoryTheory.nonempty_hom_of_preconnected_groupoid b₀ b')
  letI := Functor.vertexGroupMulAction T b'
  rcases hAll b' with ⟨_, hpre⟩
  rw [MulAction.isPretransitive_iff_base (T.map f t₀)] at hpre
  rcases hpre t with ⟨γ, hγ⟩
  -- The composite `f ≫ γ` carries the chosen base object to the target element.
  let y' : T.Elements := ⟨b', t⟩
  have hmor : x₀ ⟶ y' := by
    refine CategoryOfElements.homMk x₀ y' (f ≫ (γ : b' ⟶ b')) ?_
    simpa [FunctorToTypes.map_comp_apply, hγ]
  exact (hstep hmor).mp hp₀

/-- The orbit category functor sending `H ≤ π(B,b)` to the transitive `B`-action associated to the
orbit `π(B,b) / H`. -/
noncomputable def orbitCategoryToTransitiveGroupoidAction :
    O(End b) ⥤
      CategoryTheory.ObjectProperty.FullSubcategory
        (Functor.IsTransitive : CategoryTheory.ObjectProperty (B ⥤ Type v)) where
  obj H :=
    ⟨associatedAction b (End b ⧸ H),
      orbitCategoryAssociatedAction_isTransitive b H⟩
  map {H K : O(End b)} φ := ObjectProperty.homMk <|
    (associatedActionHom b φ : associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K))
  map_id H := by
    apply ObjectProperty.hom_ext
    ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    rfl
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    rfl

/-- The category-of-elements bridge identifying transitive `B`-actions with connected covering
functors over `B`. -/
noncomputable def transitiveGroupoidActionToConnectedCovering :
    ObjectProperty.FullSubcategory
      (Functor.IsTransitive : ObjectProperty (B ⥤ Type v)) ⥤
        ConnectedCovering B where
  obj T :=
    ⟨elementsFunctorOver T.1,
      ⟨transitiveAction_elements_isCovering T.1 T.2,
        transitiveAction_elements_isConnected T.1 T.2⟩⟩
  map {T U} α := ObjectProperty.homMk <|
    GroupoidFunctorOver.homMk (CategoryOfElements.map α.1) (CategoryOfElements.map_π α.1)
  map_id T := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp α β := by
    apply ObjectProperty.hom_ext
    rfl

/-- The source-facing functor `E(-) : O(π(B,b)) ⥤ Cov(B)` sending an orbit `π(B,b) / H` to its
associated connected covering over `B`. -/
noncomputable abbrev orbitCategoryToConnectedCovering :
    O(End b) ⥤ ConnectedCovering B :=
  orbitCategoryToTransitiveGroupoidAction b ⋙ transitiveGroupoidActionToConnectedCovering

/-- The category of elements of the associated action of `π(B,b) / H` projects to `B` as a
covering functor. -/
-- Proof sketch: the projection from the category of elements is surjective on objects because `B`
-- is connected and the orbit action is transitive, while morphisms in the element category are
-- uniquely determined by their image in `B`, giving the required star bijections.
theorem orbitCategoryAssociatedAction_elements_isCovering
    (H : O(End b)) :
    Functor.IsCovering (CategoryOfElements.π (associatedAction b (End b ⧸ H))) := by
  simpa using transitiveAction_elements_isCovering
    (associatedAction b (End b ⧸ H))
    (orbitCategoryAssociatedAction_isTransitive b H)

/-- The total groupoid of the associated action of `π(B,b) / H` is connected. -/
-- Proof sketch: transitivity of `associatedAction b (End b ⧸ H)`
-- identifies any two
-- objects in the category of elements by a zigzag over a morphism of `B`; since `B` is a
-- groupoid, these zigzags upgrade to actual isomorphisms, yielding connectedness.
theorem orbitCategoryAssociatedAction_elements_isConnected
    (H : O(End b)) :
    IsConnected (Functor.Elements (associatedAction b (End b ⧸ H))) := by
  simpa using transitiveAction_elements_isConnected
    (associatedAction b (End b ⧸ H))
    (orbitCategoryAssociatedAction_isTransitive b H)

/-- Helper for Theorem 3.6.1: a natural transformation between associated actions is already
determined by its component on the base fiber. -/
private noncomputable def associated_action_to_orbit_morphism
    {H K : O(End b)}
    (η : associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K)) :
    H ⟶ K where
  toFun x :=
    associatedAction_base_equiv b (End b ⧸ K)
      (η.app b ((associatedAction_base_equiv b (End b ⧸ H)).symm x))
  map_smul' g x := by
    -- Transport equivariance of `η.app b` through the base-fiber identifications.
    let q := (associatedAction_base_equiv b (End b ⧸ H)).symm x
    have hq :
        (associatedAction b (End b ⧸ H)).map g q =
          (associatedAction_base_equiv b (End b ⧸ H)).symm (g • x) := by
      apply (associatedAction_base_equiv b (End b ⧸ H)).injective
      simpa [q, associatedAction_base_equiv_smul]
    have hnat := congrArg (fun k ↦ k.hom q) (η.naturality g)
    calc
      associatedAction_base_equiv b (End b ⧸ K)
          (η.app b ((associatedAction_base_equiv b (End b ⧸ H)).symm (g • x))) =
        associatedAction_base_equiv b (End b ⧸ K) (η.app b ((associatedAction b (End b ⧸ H)).map g q)) := by
          rw [← hq]
      _ =
        associatedAction_base_equiv b (End b ⧸ K)
          ((associatedAction b (End b ⧸ K)).map g (η.app b q)) := by
          simpa using congrArg (associatedAction_base_equiv b (End b ⧸ K)) hnat
      _ = g • associatedAction_base_equiv b (End b ⧸ K) (η.app b q) := by
          rw [associatedAction_base_equiv_smul]

/-- Helper for Theorem 3.6.1: passing from orbit morphisms to natural transformations of
associated actions is injective. -/
private theorem associatedAction_hom_injective
    (H K : O(End b)) :
    Function.Injective
      (fun φ : H ⟶ K ↦
        (associatedActionHom b φ :
          associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K))) := by
  intro φ ψ hφψ
  apply MulActionHom.ext
  intro x
  have hbase := congrFun (congrArg (fun η ↦ η.app b) hφψ) (Quotient.mk'' (𝟙 b, x))
  simpa [associatedActionHom, associatedAction_base_equiv, associatedAction_base_map,
    associatedAction_base_eval] using
    congrArg (associatedAction_base_equiv b (End b ⧸ K)) hbase

/-- Helper for Theorem 3.6.1: the inverse base-fiber equivalence sends a point of the base fiber
to the identity-arrow class representing it. -/
private theorem associatedAction_base_symm_eq_id_class
    (b : B) (S : Type v) [MulAction (End b) S] (s : S) :
    (associatedAction_base_equiv b S).symm s = Quotient.mk'' (𝟙 b, s) := by
  -- Compare both candidates after applying the explicit base-fiber equivalence.
  apply (associatedAction_base_equiv b S).injective
  simpa [associatedAction_base_equiv, associatedAction_base_map, associatedAction_base_eval] using
    (one_smul (End b) s).symm

/-- Helper for Theorem 3.6.1: every natural transformation between associated orbit actions comes
from a unique morphism in the orbit category. -/
private theorem associatedAction_hom_surjective_to_nattrans
    {H K : O(End b)}
    (η : associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K)) :
    associatedActionHom b (associated_action_to_orbit_morphism (b := b) η) = η := by
  ext x q
  refine Quotient.inductionOn' q ?_
  intro p
  let φ : H ⟶ K := associated_action_to_orbit_morphism (b := b) η
  have hbase :
      η.app b (Quotient.mk'' (𝟙 b, p.2)) = Quotient.mk'' (𝟙 b, φ.toFun p.2) := by
    apply (associatedAction_base_equiv b (End b ⧸ K)).injective
    calc
      associatedAction_base_equiv b (End b ⧸ K) (η.app b (Quotient.mk'' (𝟙 b, p.2))) =
          associatedAction_base_equiv b (End b ⧸ K)
            (η.app b ((associatedAction_base_equiv b (End b ⧸ H)).symm p.2)) := by
              rw [associatedAction_base_symm_eq_id_class]
      _ = φ.toFun p.2 := by
            rfl
      _ = associatedAction_base_equiv b (End b ⧸ K) (Quotient.mk'' (𝟙 b, φ.toFun p.2)) := by
            simpa [associatedAction_base_equiv, associatedAction_base_map,
              associatedAction_base_eval] using
              (one_smul (End b) (φ.toFun p.2)).symm
  -- Every class `[f, s]` is obtained from the base class `[𝟙, s]`, so naturality reduces the
  -- comparison to the canonical base representative.
  calc
    (associatedActionHom b (associated_action_to_orbit_morphism (b := b) η)).app x
        (Quotient.mk'' p) =
      (associatedAction b (End b ⧸ K)).map p.1 (Quotient.mk'' (𝟙 b, φ.toFun p.2)) := by
        change Quotient.mk'' (p.1, φ.toFun p.2) = _
        symm
        change Quotient.mk'' ((𝟙 b) ≫ p.1, φ.toFun p.2) = Quotient.mk'' (p.1, φ.toFun p.2)
        simp
    _ = (associatedAction b (End b ⧸ K)).map p.1 (η.app b (Quotient.mk'' (𝟙 b, p.2))) := by
        rw [hbase.symm]
    _ =
      η.app x
        ((associatedAction b (End b ⧸ H)).map p.1 (Quotient.mk'' (𝟙 b, p.2))) := by
        symm
        exact congrArg (fun k ↦ k.hom (Quotient.mk'' (𝟙 b, p.2))) (η.naturality p.1)
    _ = η.app x (Quotient.mk'' p) := by
        have hrepr :
            (associatedAction b (End b ⧸ H)).map p.1 (Quotient.mk'' (𝟙 b, p.2)) =
              Quotient.mk'' p := by
          change Quotient.mk'' ((𝟙 b) ≫ p.1, p.2) = Quotient.mk'' p
          simp
        rw [hrepr]

/-- Helper for Theorem 3.6.1: normalizing a representative with a chosen path leaves its orbit
class unchanged. -/
private theorem associatedAction_chosen_path_class_eq
    (T : B ⥤ Type v) (a : ∀ x : B, b ⟶ x) {x : B} (f : b ⟶ x) (s : T.obj b) :
    letI := Functor.vertexGroupMulAction T b
    (Quotient.mk'' (a x, T.map (inv (a x)) (T.map f s)) :
      associatedActionObj b (T.obj b) x) =
      Quotient.mk'' (f, s) := by
  letI := Functor.vertexGroupMulAction T b
  -- Compare the two representatives by the loop sending `a x` back to `f`.
  apply Quotient.sound
  change
    MulAction.orbitRel (End b) ((b ⟶ x) × T.obj b)
      (a x, T.map (inv (a x)) (T.map f s)) (f, s)
  rw [MulAction.orbitRel_apply]
  refine ⟨show End b from f ≫ inv (a x), ?_⟩
  ext
  · simp [Category.assoc]
  · simp [FunctorToTypes.map_comp_apply]

/-- Helper for Theorem 3.6.1: over a connected base groupoid, an action is reconstructed from its
base fiber and the corresponding `π(B,b)`-action. -/
private theorem associatedAction_of_vertexGroupMulAction_iso
    (T : B ⥤ Type v) :
    Nonempty (
      letI := Functor.vertexGroupMulAction T b
      associatedAction b (T.obj b) ≅ T) := by
  classical
  letI := Functor.vertexGroupMulAction T b
  let a : ∀ x : B, b ⟶ x := fun x ↦
    Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid b x)
  let forward : associatedAction b (T.obj b) ⟶ T :=
    { app := fun x ↦ TypeCat.ofHom <|
        Quotient.lift
          (fun p : (b ⟶ x) × T.obj b ↦ T.map p.1 p.2)
          (by
            intro p q hp
            change MulAction.orbitRel (End b) ((b ⟶ x) × T.obj b) p q at hp
            rw [MulAction.orbitRel_apply] at hp
            rcases hp with ⟨g, rfl⟩
            -- Orbit-related representatives map to the same point after functorial transport.
            have hg :
                inv (T.map g) (T.map g q.2) = q.2 := by
              simpa using (FunctorToTypes.map_inv_map_hom_apply T (asIso g) q.2)
            simpa [Functor.vertexGroupMulAction_smul_eq_map, FunctorToTypes.map_comp_apply] using
              congrArg (T.map q.1) hg)
      naturality := by
        intro x y f
        apply ConcreteCategory.hom_ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro p
        -- Naturality is exactly compatibility of `T.map` with composition.
        change T.map (p.1 ≫ f) p.2 = T.map f (T.map p.1 p.2)
        simp [FunctorToTypes.map_comp_apply] }
  let inverse : T ⟶ associatedAction b (T.obj b) :=
    { app := fun x ↦ TypeCat.ofHom fun t ↦ Quotient.mk'' (a x, T.map (inv (a x)) t)
      naturality := by
        intro x y f
        apply ConcreteCategory.hom_ext
        intro t
        -- Route correction: use the chosen-path class normalization instead of quotient transport.
        calc
          Quotient.mk'' (a y, T.map (inv (a y)) (T.map f t)) =
              Quotient.mk'' (a x ≫ f, T.map (inv (a x)) t) := by
                have hx : T.map (a x) (inv (T.map (a x)) t) = t := by
                  simpa using (Functor.map_inv_hom_apply T (a x) t)
                have hx' : T.map f (T.map (a x) (inv (T.map (a x)) t)) = T.map f t := by
                  exact congrArg (T.map f) hx
                simpa [hx'] using
                  associatedAction_chosen_path_class_eq (b := b) (T := T) a
                    (f := a x ≫ f) (s := T.map (inv (a x)) t)
          _ = (associatedAction b (T.obj b)).map f (Quotient.mk'' (a x, T.map (inv (a x)) t)) := by
                rfl }
  refine ⟨
    { hom := forward
      inv := inverse
      hom_inv_id := by
        ext x q
        refine Quotient.inductionOn' q ?_
        intro p
        -- The normalization lemma recovers the original orbit class representative.
        simpa [forward, inverse] using
          associatedAction_chosen_path_class_eq (b := b) (T := T) a (f := p.1) (s := p.2)
      inv_hom_id := by
        ext x t
        -- The chosen inverse path cancels immediately under `T.map`.
        simpa [forward, inverse] using
          (Functor.map_inv_hom_apply T (a x) t) }⟩

/-- Helper for Theorem 3.6.1: an equivariant equivalence of `π(B,b)`-sets induces an isomorphism
between the corresponding associated `B`-actions. -/
private noncomputable def associatedAction_iso_of_equivariant_equiv
    {S T : Type v} [MulAction (End b) S] [MulAction (End b) T]
    (e : S ≃ T) (he : ∀ (g : End b) x, e (g • x) = g • e x) :
    associatedAction b S ≅ associatedAction b T where
  hom := associatedActionHom b
    { toFun := e
      map_smul' := he }
  inv := associatedActionHom b
    { toFun := e.symm
      map_smul' := by
        intro g x
        -- The inverse map is equivariant because the forward map intertwines the two actions.
        apply e.injective
        simpa using (he g (e.symm x)).symm }
  hom_inv_id := by
    ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    change Quotient.mk'' (p.1, e.symm (e p.2)) = Quotient.mk'' (p.1, p.2)
    simpa using congrArg (fun s ↦ Quotient.mk'' (p.1, s)) (e.left_inv p.2)
  inv_hom_id := by
    ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    change Quotient.mk'' (p.1, e (e.symm p.2)) = Quotient.mk'' (p.1, p.2)
    simpa using congrArg (fun s ↦ Quotient.mk'' (p.1, s)) (e.right_inv p.2)

/-- Helper for Theorem 3.6.1: every transitive `B`-action is represented by the orbit of the
stabilizer of a chosen point in the base fiber. -/
private theorem transitive_groupoid_action_iso_quotient_stabilizer
    (T : CategoryTheory.ObjectProperty.FullSubcategory
      (Functor.IsTransitive : CategoryTheory.ObjectProperty (B ⥤ Type v))) :
    ∃ H : O(End b), Nonempty ((orbitCategoryToTransitiveGroupoidAction b).obj H ≅ T) := by
  letI := Functor.vertexGroupMulAction T.1 b
  have hTb :
      MulAction.IsTransitive (End b) (T.1.obj b) :=
    (Functor.isTransitive_iff_forall_vertexGroupMulAction_isTransitive T.1).mp T.2 b
  rcases hTb.1 with ⟨s₀⟩
  let H : O(End b) := ⟨MulAction.stabilizer (End b) s₀⟩
  let _ : MulAction.IsPretransitive (End b) (T.1.obj b) := hTb.2
  let e : End b ⧸ H ≃ T.1.obj b :=
    quotientStabilizerEquivOfIsPretransitive (G := End b) (S := T.1.obj b) s₀
  have he : ∀ (g : End b) x, e (g • x) = g • e x := by
    intro g x
    -- Lemma 3.4.3 already supplies the quotient-stabilizer equivariance.
    simpa [e, H] using
      quotientStabilizerEquivOfIsPretransitive_equivariant
        (G := End b) (S := T.1.obj b) s₀ g x
  obtain ⟨eT⟩ := associatedAction_of_vertexGroupMulAction_iso (b := b) T.1
  refine ⟨H, ⟨?_⟩⟩
  -- Lift the underlying `B`-action isomorphism into the full subcategory of transitive actions.
  refine ObjectProperty.isoMk _ ?_
  simpa [orbitCategoryToTransitiveGroupoidAction, H] using
    (associatedAction_iso_of_equivariant_equiv (b := b) e he).trans eT

/-- Helper for Theorem 3.6.1: an over-morphism between categories of elements determines a
natural transformation of the underlying functors. -/
-- The commutativity condition over `B` pins down the first component of each image object, so the
-- second component can be read off as the desired value of the natural transformation.
private theorem elementsFunctorOver_obj_fst_eq
    {T U : B ⥤ Type v} (F : elementsFunctorOver T ⟶ elementsFunctorOver U)
    (x : T.Elements) :
    (F.left.obj x).1 = x.1 := by
  simpa using congrArg (fun G => G.obj x) F.comm

/-- Helper for Theorem 3.6.1: the underlying base arrow of an `eqToHom` in the category of
elements is the corresponding `eqToHom` between base objects. -/
private theorem elements_eqToHom_val
    {T : B ⥤ Type v} {x y : T.Elements} (h : x = y) :
    ((eqToHom h : x ⟶ y).1) = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

/-- Helper for Theorem 3.6.1: an over-morphism of categories of elements preserves the base
object of every element, so its second component defines a natural transformation. -/
private noncomputable def elementsFunctorOver_natTrans_of_over_hom
    {T U : B ⥤ Type v} (F : elementsFunctorOver T ⟶ elementsFunctorOver U) :
    T ⟶ U where
  app x := TypeCat.ofHom fun t ↦
    let h := elementsFunctorOver_obj_fst_eq (F := F) ⟨x, t⟩
    U.map (eqToHom h) (F.left.obj ⟨x, t⟩).2
  naturality {x} {y} f := by
    apply ConcreteCategory.hom_ext
    intro t
    let xt : T.Elements := ⟨x, t⟩
    let yt : T.Elements := ⟨y, T.map f t⟩
    let m : xt ⟶ yt := CategoryOfElements.homMk xt yt f rfl
    let hx := elementsFunctorOver_obj_fst_eq (F := F) xt
    let hy := elementsFunctorOver_obj_fst_eq (F := F) yt
    have hmap :
        U.map (F.left.map m).1 (F.left.obj xt).2 = (F.left.obj yt).2 := by
      exact CategoryOfElements.map_snd (F.left.map m)
    have hval :
        (F.left.map m).1 = eqToHom hx ≫ f ≫ eqToHom hy.symm := by
      simpa [xt, yt, m, hx, hy] using Functor.congr_hom F.comm m
    -- The over condition says the lifted morphism lies over `f`, so the second components satisfy
    -- the ordinary naturality square after rewriting the preserved base objects.
    rw [hval, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply] at hmap
    have hmap' := congrArg (U.map (eqToHom hy)) hmap
    simpa [xt, yt, m, hx, hy, FunctorToTypes.map_comp_apply] using hmap'.symm

/-- Helper for Theorem 3.6.1: reconstructing an over-morphism from the recovered natural
transformation gives back the original over-morphism. -/
-- Compare the two functors on objects and then on morphisms; both comparisons reduce to the fact
-- that `F` already lies over `B`.
private theorem elementsFunctorOver_natTrans_of_over_hom_spec
    {T U : B ⥤ Type v} (F : elementsFunctorOver T ⟶ elementsFunctorOver U) :
    GroupoidFunctorOver.homMk
        (CategoryOfElements.map (elementsFunctorOver_natTrans_of_over_hom F))
        (CategoryOfElements.map_π (elementsFunctorOver_natTrans_of_over_hom F)) = F := by
  ext
  let α := elementsFunctorOver_natTrans_of_over_hom F
  let hObj :
      ∀ z : T.Elements, (CategoryOfElements.map α).obj z = F.left.obj z := by
    intro z
    rcases z with ⟨x, t⟩
    let h := elementsFunctorOver_obj_fst_eq (F := F) ⟨x, t⟩
    apply Functor.Elements.ext _ _ h.symm
    -- On each object, the reconstructed second component is exactly the original one.
    change U.map (eqToHom h.symm)
        (U.map (eqToHom h) (F.left.obj ⟨x, t⟩).2) = (F.left.obj ⟨x, t⟩).2
    rw [← U.map_comp_apply]
    simp
  refine CategoryTheory.Functor.ext hObj ?_
  intro z₁ z₂ k
  apply CategoryOfElements.ext U
  -- Over morphisms in the category of elements are determined by their image in `B`.
  simpa [GroupoidFunctorOver.homMk, CategoryOfElements.map, elements_eqToHom_val] using
    (conj_eqToHom_iff_heq _ _
      (congrArg Sigma.fst (hObj z₁)) (congrArg Sigma.fst (hObj z₂))).2
      ((Functor.hcongr_hom F.comm k).symm)

/-- Helper for Theorem 3.6.1: the category-of-elements construction is faithful on morphisms of
transitive actions. -/
-- Once an over-morphism is reconstructed uniquely from its category-of-elements image, equality of
-- those images forces equality of the original natural transformations objectwise.
private theorem elementsFunctorOver_hom_injective
    (T U : B ⥤ Type v) :
    Function.Injective
      (fun α : T ⟶ U ↦
        (GroupoidFunctorOver.homMk (CategoryOfElements.map α) (CategoryOfElements.map_π α) :
          elementsFunctorOver T ⟶ elementsFunctorOver U)) := by
  intro α β hαβ
  ext x t
  have hobj :
      (CategoryOfElements.map α).obj ⟨x, t⟩ = (CategoryOfElements.map β).obj ⟨x, t⟩ := by
    simpa using congrArg (fun F => F.left.obj ⟨x, t⟩) hαβ
  -- Equality of the induced functors on the element `(x,t)` forces equality of the second
  -- coordinates, hence equality of the original natural transformations.
  injection hobj

/-- Helper for Theorem 3.6.1: the fiber of the projection `CategoryOfElements.π T` over `b`
identifies with the ordinary fiber `T.obj b`. -/
-- A point of the fiber is precisely an element `t : T.obj x` together with an equality `x = b`,
-- so transporting along that equality gives the desired point of `T.obj b`.
private noncomputable def elementsProjectionFiberEquiv
    (T : B ⥤ Type v) (b : B) :
    (CategoryOfElements.π T).Fiber b ≃ T.obj b where
  toFun x := x.2 ▸ x.1.2
  invFun t := ⟨⟨b, t⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨x, t⟩, hx⟩
    subst hx
    rfl
  right_inv t := by
    rfl

/-- Helper for Theorem 3.6.1: the canonical identification of the fiber of
`CategoryOfElements.π T` with `T.obj b` is equivariant for the loop action at `b`. -/
-- In the category of elements, the chosen lift of `γ⁻¹` from `(b,t)` is the explicit morphism
-- whose endpoint is `(b, T.map γ⁻¹ t)`, so the fiber action matches the usual vertex-group
-- action on `T.obj b`.
private theorem elementsProjectionFiberEquiv_smul
    (T : B ⥤ Type v) (b : B) (hp : Functor.IsCovering (CategoryOfElements.π T))
    (γ : b ⟶ b) (x : (CategoryOfElements.π T).Fiber b) :
    letI := Functor.IsCovering.fiberTranslationMulAction hp b
    letI := Functor.vertexGroupAction T b
    elementsProjectionFiberEquiv T b (γ • x) =
      γ • elementsProjectionFiberEquiv T b x := by
  letI := Functor.IsCovering.fiberTranslationMulAction hp b
  letI := Functor.vertexGroupAction T b
  rcases x with ⟨⟨x, t⟩, hx⟩
  cases hx
  let y : T.Elements := ⟨x, T.map γ⁻¹ t⟩
  let m : ⟨x, t⟩ ⟶ y := CategoryOfElements.homMk ⟨x, t⟩ y γ⁻¹ rfl
  have hstar :
      Functor.IsCovering.starLift hp γ⁻¹ ⟨⟨x, t⟩, rfl⟩ = Under.mk m := by
    apply (hp.star_bijective ⟨x, t⟩).injective
    -- The explicit lift already projects to the transported under object `Under.mk γ⁻¹`.
    simpa [m] using Functor.IsCovering.starLift_post_eq hp γ⁻¹ ⟨⟨x, t⟩, rfl⟩
  have hend :
      (Functor.IsCovering.starLift hp γ⁻¹ ⟨⟨x, t⟩, rfl⟩).right = y := by
    simpa [m, y] using congrArg Comma.right hstar
  change
      elementsProjectionFiberEquiv T x
        (⟨(Functor.IsCovering.starLift hp γ⁻¹ ⟨⟨x, t⟩, rfl⟩).right,
          Functor.IsCovering.starLift_obj hp γ⁻¹ ⟨⟨x, t⟩, rfl⟩⟩) =
      T.map γ⁻¹ t
  have hfiber :
      (⟨(Functor.IsCovering.starLift hp γ⁻¹ ⟨⟨x, t⟩, rfl⟩).right,
        Functor.IsCovering.starLift_obj hp γ⁻¹ ⟨⟨x, t⟩, rfl⟩⟩ :
        (CategoryOfElements.π T).Fiber x) = ⟨y, rfl⟩ := by
    apply Subtype.ext
    simpa [y] using hend
  rw [hfiber]
  rfl

/-- Helper for Theorem 3.6.1: the above fiber identification carries the stabilizer of the
distinguished point in the category-of-elements fiber to the stabilizer of the chosen element in
the original fiber. -/
-- The preceding equivariance lemma identifies the fixed-point equations on both sides, so the two
-- stabilizer subgroups coincide elementwise.
private theorem elementsProjectionFiberEquiv_stabilizer
    (T : B ⥤ Type v) (b : B) (hp : Functor.IsCovering (CategoryOfElements.π T))
    (t : T.obj b) :
    letI := Functor.IsCovering.fiberTranslationMulAction hp b
    letI := Functor.vertexGroupAction T b
    MulAction.stabilizer (b ⟶ b) ((elementsProjectionFiberEquiv T b).symm t) =
      MulAction.stabilizer (b ⟶ b) t := by
  letI := Functor.IsCovering.fiberTranslationMulAction hp b
  letI := Functor.vertexGroupAction T b
  ext γ
  constructor
  · intro hγ
    change γ • ((elementsProjectionFiberEquiv T b).symm t) = (elementsProjectionFiberEquiv T b).symm t at hγ
    change γ • t = t
    have hγ' := congrArg (elementsProjectionFiberEquiv T b) hγ
    simpa [elementsProjectionFiberEquiv_smul (T := T) (b := b) (hp := hp)] using hγ'
  · intro hγ
    change γ • ((elementsProjectionFiberEquiv T b).symm t) = (elementsProjectionFiberEquiv T b).symm t
    apply (elementsProjectionFiberEquiv T b).injective
    simpa [elementsProjectionFiberEquiv_smul (T := T) (b := b) (hp := hp)] using hγ

/-- Helper for Theorem 3.6.1: the canonical point of the orbit covering over the base object `b`
is represented by the identity arrow and the identity coset. -/
private abbrev orbitCategoryAssociatedAction_basepoint
    (b : B) (H : O(End b)) :
    (CategoryOfElements.π (associatedAction b (End b ⧸ H))).Fiber b :=
  ⟨⟨b, Quotient.mk'' (𝟙 b, (((1 : End b) : End b ⧸ H)))⟩, rfl⟩

/-- Helper for Theorem 3.6.1: every morphism of connected orbit coverings comes from a unique
orbit-category morphism. -/
-- The category-of-elements owner already lets us reconstruct the underlying natural
-- transformation of associated actions, and the orbit-side classifier then upgrades it back to an
-- actual orbit morphism.
private theorem orbitCategoryToConnectedCovering_map_surjective
    {H K : O(End b)}
    (F : (orbitCategoryToConnectedCovering b).obj H ⟶
      (orbitCategoryToConnectedCovering b).obj K) :
    ∃ φ : H ⟶ K, (orbitCategoryToConnectedCovering b).map φ = F := by
  let η :
      associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K) :=
    elementsFunctorOver_natTrans_of_over_hom F.hom
  -- Recover the orbit morphism from the induced natural transformation on associated actions.
  refine ⟨associated_action_to_orbit_morphism (b := b) η, ?_⟩
  apply ObjectProperty.hom_ext
  change
    GroupoidFunctorOver.homMk
      (CategoryOfElements.map
        (associatedActionHom b (associated_action_to_orbit_morphism (b := b) η)))
      (CategoryOfElements.map_π
        (associatedActionHom b (associated_action_to_orbit_morphism (b := b) η))) =
      F.hom
  rw [associatedAction_hom_surjective_to_nattrans (b := b) η]
  exact elementsFunctorOver_natTrans_of_over_hom_spec F.hom

/-- Helper for Theorem 3.6.1: the orbit-category-to-transitive-action functor is an equivalence. -/
private theorem orbitCategoryToTransitiveGroupoidAction_isEquivalence_aux
    (b : B) :
    Functor.IsEquivalence (orbitCategoryToTransitiveGroupoidAction b) := by
  let _ : (orbitCategoryToTransitiveGroupoidAction b).Faithful :=
    { map_injective := by
        intro H K φ ψ hφψ
        -- Faithfulness reduces to the orbit-side natural-transformation classifier.
        exact associatedAction_hom_injective (b := b) H K (congrArg (fun k => k.hom) hφψ) }
  let _ : (orbitCategoryToTransitiveGroupoidAction b).Full :=
    { map_surjective := by
        intro H K η
        -- Fullness is the explicit reconstruction of an orbit morphism from the base fiber.
        refine ⟨associated_action_to_orbit_morphism (b := b) η.hom, ?_⟩
        apply ObjectProperty.hom_ext
        exact associatedAction_hom_surjective_to_nattrans (b := b) η.hom }
  let _ : (orbitCategoryToTransitiveGroupoidAction b).EssSurj :=
    { mem_essImage := by
        intro T
        -- Choose a point in the base fiber and identify the action with the corresponding orbit.
        rcases transitive_groupoid_action_iso_quotient_stabilizer (b := b) T with ⟨H, ⟨e⟩⟩
        exact ⟨H, ⟨e⟩⟩ }
  -- The orbit-side bridge is faithful, full, and essentially surjective.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- Helper for Theorem 3.6.1: transporting a subgroup inclusion from the literal source and target
objects to the common base object `b` is equivalent to transporting both subgroups separately. -/
private theorem subgroup_transport_le_iff
    {x y : B} (hx : x = b) (hy : y = b)
    (A : Subgroup (x ⟶ x)) (C : Subgroup (y ⟶ y)) :
    A ≤ hy.trans hx.symm ▸ C ↔ hx ▸ A ≤ hy ▸ C := by
  cases hx
  cases hy
  simp

/-- Helper for Theorem 3.6.1: morphisms in `GroupoidFunctorOver B` are classified by the same
vertex-group inclusion criterion as lifts of coverings, but now expressed directly in the
universe-stable owner. -/
private theorem existsUnique_lift_functor_iff_mapVertexGroup_range_le_large
    {X Y : GroupoidFunctorOver B} [IsConnected X.left] (hy : Functor.IsCovering Y.hom)
    (e : X.hom.Fiber b) (e' : Y.hom.Fiber b) :
    (∃! F : X.left ⥤ Y.left, F ⋙ Y.hom = X.hom ∧ F.obj e.1 = e'.1) ↔
      e.2 ▸ (X.hom.mapVertexGroup e.1).range ≤
        e'.2 ▸ (Y.hom.mapVertexGroup e'.1).range := by
  rcases e with ⟨e, rfl⟩
  -- The large-universe statement is exactly Theorem 3.5.1 on the underlying functors.
  simpa using
    (CategoryTheory.Functor.IsCovering.existsUnique_lift_iff_mapVertexGroup_range_le
      (p := Y.hom) (f := X.hom) hy e e')

/-- Helper for Theorem 3.6.1: morphisms in `GroupoidFunctorOver B` are classified by the same
vertex-group inclusion criterion as lifts of coverings, but now expressed directly in the
universe-stable owner. -/
private theorem groupoidFunctorOver_existsUnique_hom_iff_mapVertexGroup_range_le_large
    {X Y : GroupoidFunctorOver B} [IsConnected X.left] (hy : Functor.IsCovering Y.hom)
    (e : X.hom.Fiber b) (e' : Y.hom.Fiber b) :
    (∃! h : X ⟶ Y, h.left.obj e.1 = e'.1) ↔
      e.2 ▸ (X.hom.mapVertexGroup e.1).range ≤
        e'.2 ▸ (Y.hom.mapVertexGroup e'.1).range := by
  rcases e with ⟨e, rfl⟩
  constructor
  · rintro ⟨h, hh, huniq⟩
    -- Forgetting the owner packaging reduces the map classification to a lift classification.
    refine (existsUnique_lift_functor_iff_mapVertexGroup_range_le_large
      (X := X) (Y := Y) (hy := hy) (e := ⟨e, rfl⟩) (e' := e')).1 ?_
    refine ⟨h.left, ?_, ?_⟩
    · refine ⟨h.comm, ?_⟩
      simpa using hh
    · intro F hF
      have hpack :
          GroupoidFunctorOver.homMk F (by simpa using hF.1) = h :=
        huniq (GroupoidFunctorOver.homMk F (by simpa using hF.1))
          (by simpa using hF.2)
      simpa using congrArg GroupoidFunctorOver.Hom.left hpack
  · intro hsub
    -- Conversely, repackage the unique lift functor as the unique owner-level morphism.
    rcases (existsUnique_lift_functor_iff_mapVertexGroup_range_le_large
      (X := X) (Y := Y) (hy := hy) (e := ⟨e, rfl⟩) (e' := e')).2 hsub with
      ⟨F, hF, huniq⟩
    refine ⟨GroupoidFunctorOver.homMk F hF.1, ?_, ?_⟩
    · simpa using hF.2
    · intro h hh
      apply GroupoidFunctorOver.Hom.ext
      simpa using
        huniq h.left ⟨h.comm, by simpa using hh⟩

/-- Helper for Theorem 3.6.1: a morphism in `GroupoidFunctorOver B` is an isomorphism exactly
when it identifies the corresponding basepoint subgroups in `π(B,b)`. -/
private theorem groupoidFunctorOver_isIso_iff_mapVertexGroup_range_eq_large
    {X Y : GroupoidFunctorOver B} [IsConnected X.left] [IsPreconnected Y.left]
    (hx : Functor.IsCovering X.hom) (hy : Functor.IsCovering Y.hom)
    (e : X.hom.Fiber b) (e' : Y.hom.Fiber b)
    (h : X ⟶ Y) (hh : h.left.obj e.1 = e'.1) :
    IsIso h ↔
      e.2 ▸ (X.hom.mapVertexGroup e.1).range =
        e'.2 ▸ (Y.hom.mapVertexGroup e'.1).range := by
  rcases e with ⟨e, rfl⟩
  constructor
  · intro hIso
    letI := hIso
    letI : Nonempty Y.left := ⟨e'.1⟩
    letI : IsConnected Y.left := { toIsPreconnected := inferInstance }
    let hF : X.left ⥤ Y.left := h.left
    let gF : Y.left ⥤ X.left := (CategoryTheory.inv h).left
    have hhF : hF.obj e = e'.1 := by
      simpa [hF] using hh
    -- The inverse fixes the chosen target point because the composite is the identity.
    have hgF : gF.obj e'.1 = e := by
      have hcomp : h ≫ CategoryTheory.inv h = 𝟙 _ := by
        simp
      have hpoint : gF.obj (hF.obj e) = e := by
        exact congrArg
          (fun k : X ⟶ X ↦ k.left.obj e) hcomp
      simpa [hF, gF, hhF] using hpoint
    have hhOver : hF ⋙ Y.hom = X.hom := by
      simpa [hF] using h.comm
    have hle :
        (X.hom.mapVertexGroup e).range ≤
          e'.2 ▸ (Y.hom.mapVertexGroup e'.1).range :=
      Functor.mapVertexGroup_range_le_of_lift
        (p := Y.hom) (f := X.hom) (g := hF) e e' hhOver hhF
    have hgOver : gF ⋙ X.hom = Y.hom := by
      simpa [gF] using (CategoryTheory.inv h).comm
    have hle'₀ :
        (Y.hom.mapVertexGroup e'.1).range ≤
          e'.2.symm ▸ (X.hom.mapVertexGroup e).range :=
      Functor.mapVertexGroup_range_le_of_lift
        (p := X.hom) (f := Y.hom) (g := gF) e'.1 ⟨e, e'.2.symm⟩ hgOver hgF
    have hle' :
        e'.2 ▸ (Y.hom.mapVertexGroup e'.1).range ≤
          (X.hom.mapVertexGroup e).range := by
      intro γ hγ
      have hγ' :
          eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm ∈
            (Y.hom.mapVertexGroup e'.1).range := by
        exact
          (CategoryTheory.Functor.IsCovering.mapVertexGroup_range_transport_iff e'.2 γ).1 hγ
      have hγ'' :
          eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm ∈
            e'.2.symm ▸ (X.hom.mapVertexGroup e).range :=
        hle'₀ hγ'
      have hγ''' :
          eqToHom e'.2.symm ≫
              (eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm) ≫
              eqToHom e'.2 ∈
            (X.hom.mapVertexGroup e).range := by
        exact
          (CategoryTheory.Functor.IsCovering.mapVertexGroup_range_transport_iff e'.2.symm
            (eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm)).1 hγ''
      simpa [Category.assoc] using hγ'''
    exact le_antisymm hle hle'
  · intro hEq
    letI : Nonempty Y.left := ⟨e'.1⟩
    letI : IsConnected Y.left := { toIsPreconnected := inferInstance }
    obtain ⟨g, hg, _huniqg⟩ :=
      (groupoidFunctorOver_existsUnique_hom_iff_mapVertexGroup_range_le_large
        (b := X.hom.obj e) (X := Y) (Y := X) (hy := hx) (e := e') (e' := ⟨e, rfl⟩)).2
        hEq.symm.le
    let hF : X.left ⥤ Y.left := h.left
    let gF : Y.left ⥤ X.left := g.left
    have hhF : hF.obj e = e'.1 := by
      simpa [hF] using hh
    have hgF : gF.obj e'.1 = e := by
      simpa [gF] using hg
    -- The source-side composite fixes the chosen source point, so uniqueness forces identity.
    let hgFcomp : X.left ⥤ X.left := (h ≫ g).left
    have hhg : hgFcomp.obj e = e := by
      change gF.obj (hF.obj e) = e
      simpa [hhF] using hgF
    obtain ⟨_, _, huniqk⟩ :=
      (groupoidFunctorOver_existsUnique_hom_iff_mapVertexGroup_range_le_large
        (X := X) (Y := X) (hy := hx) (e := ⟨e, rfl⟩) (e' := ⟨e, rfl⟩)).2 le_rfl
    have h_comp_g : h ≫ g = 𝟙 _ :=
      (huniqk (h ≫ g) (by simpa [hgFcomp] using hhg)).trans
        (huniqk (𝟙 _) rfl).symm
    -- The target-side composite fixes the chosen target point, so uniqueness gives the other identity.
    let ghFcomp : Y.left ⥤ Y.left := (g ≫ h).left
    have hgh : ghFcomp.obj e'.1 = e'.1 := by
      change hF.obj (gF.obj e'.1) = e'.1
      simpa [hgF] using hhF
    obtain ⟨_, _, huniqk'⟩ :=
      (groupoidFunctorOver_existsUnique_hom_iff_mapVertexGroup_range_le_large
        (X := Y) (Y := Y) (hy := hy) (e := e') (e' := e')).2 le_rfl
    have g_comp_h : g ≫ h = 𝟙 _ :=
      (huniqk' (g ≫ h) (by simpa [ghFcomp] using hgh)).trans
        (huniqk' (𝟙 _) rfl).symm
    exact ⟨⟨g, h_comp_g, g_comp_h⟩⟩

/-- Helper for Theorem 3.6.1: the identity coset in `π(B,b) / H` has stabilizer exactly `H`. -/
private theorem identity_coset_stabilizer_eq_subgroup
    (H : O(End b)) :
    MulAction.stabilizer (End b) (((1 : End b) : End b ⧸ H)) = H := by
  -- The quotient action fixes the identity coset exactly along the subgroup itself.
  simpa using MulAction.stabilizer_quotient (H : Subgroup (End b))

omit [IsConnected B] in
/-- Helper for Theorem 3.6.1: a subgroup of the source-facing loop group can be viewed inside the
reversed endomorphism group `End b` by keeping the same carrier. -/
def loopSubgroupToEndSubgroup (b : B) (K : Subgroup (b ⟶ b)) : Subgroup (End b) where
  carrier := K.carrier
  one_mem' := K.one_mem
  mul_mem' ha hb := by
    simpa [CategoryTheory.End.mul_def] using K.mul_mem hb ha
  inv_mem' := K.inv_mem

/-- Helper for Theorem 3.6.1: comparing subgroup inclusions in the loop group is equivalent to
comparing the same carriers inside `End b`. -/
private theorem loopSubgroupToEndSubgroup_le_iff
    (A C : Subgroup (b ⟶ b)) :
    A ≤ C ↔ loopSubgroupToEndSubgroup b A ≤ loopSubgroupToEndSubgroup b C := by
  rfl

omit [IsConnected B] in
/-- Helper for Theorem 3.6.1: the carrier-preserving passage from loop subgroups to `End`
subgroups is injective. -/
theorem loopSubgroupToEndSubgroup_injective
    (b : B) :
    Function.Injective (loopSubgroupToEndSubgroup b) := by
  intro A C hAC
  ext γ
  exact Iff.of_eq (congrArg (fun K : Subgroup (End b) ↦ γ ∈ K) hAC)

/-- Helper for Theorem 3.6.1: the fiber of a covering over `b` carries the direct `End b`
fiber-translation action. -/
private noncomputable instance fiberTranslationFunctor_base_end_mulAction
    {E : Type w} [Groupoid.{v} E] {p : E ⥤ B} (hp : Functor.IsCovering p) :
    MulAction (End b) (p.Fiber b) :=
  Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b

/-- Helper for Theorem 3.6.1: the base fiber of an associated action carries its direct `End b`
action. -/
private noncomputable instance associatedAction_base_end_mulAction
    (S : Type v) [MulAction (End b) S] :
    MulAction (End b) ((associatedAction b S).obj b) :=
  Functor.vertexGroupMulAction (associatedAction b S) b

/-- Helper for Theorem 3.6.1: the fiber of the elements projection over `b` carries the direct
`End b`-action induced by fiber translation. -/
private noncomputable instance elementsProjection_base_end_mulAction
    (T : B ⥤ Type v) (hp : Functor.IsCovering (CategoryOfElements.π T)) :
    MulAction (End b) ((CategoryOfElements.π T).Fiber b) :=
  Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b

/-- Helper for Theorem 3.6.1: the subgroup attached to a fiber point can be rewritten as the
stabilizer of that point under fiber translation, all inside the single owner `End b`. -/
private theorem fiber_point_stabilizer_eq_mapVertexGroup_range_end
    {E : Type w} [Groupoid.{v} E] {p : E ⥤ B}
    (hp : Functor.IsCovering p) (x : p.Fiber b) :
    by
      let hact : MulAction (End b) (p.Fiber b) := by
        simpa using
          Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b
      letI := hact
      exact MulAction.stabilizer (End b) x =
        loopSubgroupToEndSubgroup b (x.2 ▸ (p.mapVertexGroup x.1).range) := by
  rcases x with ⟨e, rfl⟩
  -- At the distinguished basepoint, Lemma 3.4.11 computes the stabilizer exactly.
  simpa [loopSubgroupToEndSubgroup] using
    (CategoryTheory.Functor.IsCovering.vertexGroupMulAction_basepoint_stabilizer_eq_mapVertexGroup_range
      hp e)

/-- Helper for Theorem 3.6.1: the canonical base class in the associated action has the same
stabilizer as the literal identity coset in `π(B,b) / H`. -/
private theorem associatedAction_identity_class_stabilizer_eq_identity_coset_stabilizer
    (H : O(End b)) :
    by
      let hact : MulAction (End b) ((associatedAction b (End b ⧸ H)).obj b) := by
        simpa using Functor.vertexGroupMulAction (associatedAction b (End b ⧸ H)) b
      letI := hact
      exact @Eq (Subgroup (End b))
        (@MulAction.stabilizer (End b) ((associatedAction b (End b ⧸ H)).obj b) inferInstance hact
          ((Quotient.mk'' (𝟙 b, (((1 : End b) : End b ⧸ H))) :
            (associatedAction b (End b ⧸ H)).obj b)))
        (MulAction.stabilizer (End b) (((1 : End b) : End b ⧸ H))) := by
            letI : MulAction (End b) ((associatedAction b (End b ⧸ H)).obj b) :=
              Functor.vertexGroupMulAction (associatedAction b (End b ⧸ H)) b
            let qbase : (associatedAction b (End b ⧸ H)).obj b :=
              Quotient.mk'' (𝟙 b, (((1 : End b) : End b ⧸ H)))
            let qid : End b ⧸ H := ((1 : End b) : End b ⧸ H)
            have hqbase : associatedAction_base_equiv b (End b ⧸ H) qbase = qid := by
              calc
                associatedAction_base_equiv b (End b ⧸ H) qbase =
                    associatedAction_base_equiv b (End b ⧸ H)
                      ((associatedAction_base_equiv b (End b ⧸ H)).symm qid) := by
                        rw [associatedAction_base_symm_eq_id_class (b := b) (S := End b ⧸ H) qid]
                _ = qid := Equiv.apply_symm_apply (associatedAction_base_equiv b (End b ⧸ H)) qid
            ext γ
            constructor
            · intro hγ
              have hγeq : γ • qbase = qbase := (MulAction.mem_stabilizer_iff).1 hγ
              -- Compare the fixed-point equation after applying the base-fiber equivalence.
              have hγ' : γ • qid = qid := by
                calc
                  γ • qid = γ • associatedAction_base_equiv b (End b ⧸ H) qbase := by
                    rw [hqbase]
                  _ = associatedAction_base_equiv b (End b ⧸ H) (γ • qbase) := by
                    symm
                    exact associatedAction_base_equiv_smul (b := b) (S := End b ⧸ H) γ qbase
                  _ = associatedAction_base_equiv b (End b ⧸ H) qbase := by
                    exact congrArg (associatedAction_base_equiv b (End b ⧸ H)) hγeq
                  _ = qid := hqbase
              exact (MulAction.mem_stabilizer_iff).2 hγ'
            · intro hγ
              have hγeq : γ • qid = qid := (MulAction.mem_stabilizer_iff).1 hγ
              -- Push the fixed-point equation back through the inverse base-fiber equivalence.
              have hγ' :
                  associatedAction_base_equiv b (End b ⧸ H) (γ • qbase) =
                    associatedAction_base_equiv b (End b ⧸ H) qbase := by
                calc
                  associatedAction_base_equiv b (End b ⧸ H) (γ • qbase) =
                      γ • associatedAction_base_equiv b (End b ⧸ H) qbase := by
                        exact associatedAction_base_equiv_smul (b := b) (S := End b ⧸ H) γ qbase
                  _ = γ • qid := by rw [hqbase]
                  _ = qid := hγeq
                  _ = associatedAction_base_equiv b (End b ⧸ H) qbase := hqbase.symm
              exact (MulAction.mem_stabilizer_iff).2 <|
                (associatedAction_base_equiv b (End b ⧸ H)).injective hγ'

/-- Helper for Theorem 3.6.1: the fiber identification for `CategoryOfElements.π T` intertwines
the direct `End b`-actions on the source and target fibers. -/
private theorem elementsProjectionFiberEquiv_smul_end
    (T : B ⥤ Type v) (b : B) (hp : Functor.IsCovering (CategoryOfElements.π T))
    (γ : End b) (x : (CategoryOfElements.π T).Fiber b) :
    by
      let hact₁ : MulAction (End b) ((CategoryOfElements.π T).Fiber b) := by
        simpa using
          Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b
      let hact₂ : MulAction (End b) (T.obj b) := by
        simpa using Functor.vertexGroupMulAction T b
      letI := hact₁
      letI := hact₂
      exact elementsProjectionFiberEquiv T b (γ • x) = γ • elementsProjectionFiberEquiv T b x := by
        dsimp
        letI : MulAction (End b) ((CategoryOfElements.π T).Fiber b) :=
          Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b
        letI : MulAction (End b) (T.obj b) :=
          Functor.vertexGroupMulAction T b
        -- Rewrite the direct `End`-actions as ordinary functor maps before changing owners.
        rw [Functor.vertexGroupMulAction_smul_eq_map]
        letI : MulAction (b ⟶ b) ((CategoryOfElements.π T).Fiber b) :=
          Functor.IsCovering.fiberTranslationMulAction hp b
        letI : MulAction (b ⟶ b) (T.obj b) :=
          Functor.vertexGroupAction T b
        let γloop : b ⟶ b := (γ : b ⟶ b)⁻¹
        have hsource :
            (Functor.IsCovering.fiberTranslationFunctor hp).map γ x =
              (γloop • x : (CategoryOfElements.π T).Fiber b) := by
          -- The loop action by `γ⁻¹` is the same underlying map on the source fiber.
          calc
            (Functor.IsCovering.fiberTranslationFunctor hp).map γ x =
                (Functor.IsCovering.fiberTranslationFunctor hp).map γloop⁻¹ x := by
                  simp [γloop]
            _ = (γloop • x : (CategoryOfElements.π T).Fiber b) := by
                  simpa using
                    (Functor.vertexGroupAction_smul_eq_map_inv
                      (T := Functor.IsCovering.fiberTranslationFunctor hp) (b := b) γloop x).symm
        -- Reduce the direct `End`-equivariance statement to the existing loop-owner lemma.
        calc
          elementsProjectionFiberEquiv T b ((Functor.IsCovering.fiberTranslationFunctor hp).map γ x) =
              elementsProjectionFiberEquiv T b (γloop • x) := by
                rw [hsource]
          _ = (γloop • elementsProjectionFiberEquiv T b x : T.obj b) := by
                exact
                  elementsProjectionFiberEquiv_smul (T := T) (b := b) (hp := hp) γloop x
          _ = T.map γ (elementsProjectionFiberEquiv T b x) := by
                calc
                  (γloop • elementsProjectionFiberEquiv T b x : T.obj b) =
                      T.map γloop⁻¹ (elementsProjectionFiberEquiv T b x) := by
                        simpa using
                          (Functor.vertexGroupAction_smul_eq_map_inv
                            (T := T) (b := b) γloop (elementsProjectionFiberEquiv T b x))
                  _ = T.map γ (elementsProjectionFiberEquiv T b x) := by
                        simp [γloop]

/-- Helper for Theorem 3.6.1: the fiber identification for `CategoryOfElements.π T` carries the
direct `End b`-stabilizer of the distinguished fiber point to the stabilizer of the chosen
element. -/
private theorem elementsProjectionFiberEquiv_stabilizer_end
    (T : B ⥤ Type v) (b : B) (hp : Functor.IsCovering (CategoryOfElements.π T))
    (t : T.obj b) :
    by
      let hact₁ : MulAction (End b) ((CategoryOfElements.π T).Fiber b) := by
        simpa using
          Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b
      let hact₂ : MulAction (End b) (T.obj b) := by
        simpa using Functor.vertexGroupMulAction T b
      letI := hact₁
      letI := hact₂
      exact MulAction.stabilizer (End b) ((elementsProjectionFiberEquiv T b).symm t) =
        MulAction.stabilizer (End b) t := by
          letI : MulAction (End b) ((CategoryOfElements.π T).Fiber b) :=
            Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b
          letI : MulAction (End b) (T.obj b) :=
            Functor.vertexGroupMulAction T b
          ext γ
          constructor
          · intro hγ
            -- Apply the fiber equivalence to the fixed-point equation on the source fiber.
            rw [MulAction.mem_stabilizer_iff] at hγ
            rw [MulAction.mem_stabilizer_iff]
            have hγ' := congrArg (elementsProjectionFiberEquiv T b) hγ
            simpa [elementsProjectionFiberEquiv_smul_end (T := T) (b := b) (hp := hp)] using
              hγ'
          · intro hγ
            -- Injectivity of the fiber equivalence transports the fixed-point equation back.
            rw [MulAction.mem_stabilizer_iff]
            apply (elementsProjectionFiberEquiv T b).injective
            simpa [elementsProjectionFiberEquiv_smul_end (T := T) (b := b) (hp := hp)] using
              hγ

/-- Helper for Theorem 3.6.1: the canonical basepoint of the orbit covering has stabilizer equal
to the subgroup defining that orbit object. -/
private theorem orbitCategoryAssociatedAction_basepoint_stabilizer_eq_subgroup
    (H : O(End b)) :
    by
      let hp : Functor.IsCovering (CategoryOfElements.π (associatedAction b (End b ⧸ H))) :=
        orbitCategoryAssociatedAction_elements_isCovering (b := b) H
      let hact : MulAction (End b) ((CategoryOfElements.π (associatedAction b (End b ⧸ H))).Fiber b) := by
        simpa using
          Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b
      letI := hact
      exact MulAction.stabilizer (End b) (orbitCategoryAssociatedAction_basepoint b H) = H := by
        let hp : Functor.IsCovering (CategoryOfElements.π (associatedAction b (End b ⧸ H))) :=
          orbitCategoryAssociatedAction_elements_isCovering (b := b) H
        letI : MulAction (End b) ((CategoryOfElements.π (associatedAction b (End b ⧸ H))).Fiber b) :=
          Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hp) b
        let t : (associatedAction b (End b ⧸ H)).obj b :=
          Quotient.mk'' (𝟙 b, (((1 : End b) : End b ⧸ H)))
        -- Identify the canonical orbit-cover point with the inverse image of the base class.
        have hbase :
            orbitCategoryAssociatedAction_basepoint b H =
              (elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b).symm t := by
          rfl
        calc
          MulAction.stabilizer (End b) (orbitCategoryAssociatedAction_basepoint b H) =
              MulAction.stabilizer (End b)
                ((elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b).symm t) := by
                  rw [hbase]
          _ = MulAction.stabilizer (End b) t := by
                simpa [t] using
                  elementsProjectionFiberEquiv_stabilizer_end
                    (T := associatedAction b (End b ⧸ H)) (b := b) (hp := hp) t
          _ = MulAction.stabilizer (End b) (((1 : End b) : End b ⧸ H)) := by
                simpa [t] using
                  associatedAction_identity_class_stabilizer_eq_identity_coset_stabilizer
                    (b := b) H
          _ = H.toSubgroup := identity_coset_stabilizer_eq_subgroup (b := b) H

/-- Helper for Theorem 3.6.1: the canonical basepoint of the orbit cover, viewed in the packaged
connected-covering object, is still the literal identity-class point. -/
private noncomputable def orbitCategoryAssociatedAction_packaged_basepoint
    (H : O(End b)) :
    let Ycov : ConnectedCovering B := (orbitCategoryToConnectedCovering b).obj H
    let Y : GroupoidFunctorOver B := Ycov.obj
    Y.hom.Fiber b :=
  orbitCategoryAssociatedAction_basepoint b H

/-- Helper for Theorem 3.6.1: every connected covering is isomorphic to the orbit cover attached
to the subgroup carried by a chosen point in the fiber over `b`. -/
private theorem orbit_covering_iso_of_connected_covering
    (X : ConnectedCovering B) (x0 : X.obj.hom.Fiber b) :
    ∃ H : O(End b), Nonempty (((orbitCategoryToConnectedCovering b).obj H) ≅ X) := by
  let hpX : Functor.IsCovering X.obj.hom := ConnectedCovering.isCovering X
  let hactX : MulAction (End b) (X.obj.hom.Fiber b) :=
    Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hpX) b
  letI := hactX
  let H : O(End b) := ⟨MulAction.stabilizer (End b) x0⟩
  let Ycov : ConnectedCovering B := (orbitCategoryToConnectedCovering b).obj H
  let Y : GroupoidFunctorOver B := Ycov.obj
  let y0 : Y.hom.Fiber b := orbitCategoryAssociatedAction_packaged_basepoint (b := b) H
  let hpY : Functor.IsCovering Y.hom := ConnectedCovering.isCovering Ycov
  let hactY : MulAction (End b) (Y.hom.Fiber b) :=
    Functor.vertexGroupMulAction (Functor.IsCovering.fiberTranslationFunctor hpY) b
  letI := hactY
  -- Compute the orbit-cover basepoint subgroup on the source side inside `End b`.
  have hsource_end :
      loopSubgroupToEndSubgroup b (y0.2 ▸ (Y.hom.mapVertexGroup y0.1).range) =
        H.toSubgroup := by
    calc
      loopSubgroupToEndSubgroup b (y0.2 ▸ (Y.hom.mapVertexGroup y0.1).range) =
          MulAction.stabilizer (End b) y0 := by
            symm
            simpa [Y, y0] using
              fiber_point_stabilizer_eq_mapVertexGroup_range_end
                (b := b) (p := Y.hom) hpY y0
      _ = H.toSubgroup := by
            simpa [Ycov, Y, y0, orbitCategoryAssociatedAction_packaged_basepoint] using
              orbitCategoryAssociatedAction_basepoint_stabilizer_eq_subgroup (b := b) H
  -- Compute the chosen subgroup carried by the target basepoint in the same owner.
  have htarget_end :
      loopSubgroupToEndSubgroup b (x0.2 ▸ (X.obj.hom.mapVertexGroup x0.1).range) =
        H.toSubgroup := by
    change loopSubgroupToEndSubgroup b (x0.2 ▸ (X.obj.hom.mapVertexGroup x0.1).range) =
      MulAction.stabilizer (End b) x0
    symm
    simpa [H, hpX] using
      fiber_point_stabilizer_eq_mapVertexGroup_range_end
        (b := b) (p := X.obj.hom) hpX x0
  have hEq_end :
      loopSubgroupToEndSubgroup b (y0.2 ▸ (Y.hom.mapVertexGroup y0.1).range) =
        loopSubgroupToEndSubgroup b (x0.2 ▸ (X.obj.hom.mapVertexGroup x0.1).range) := by
    calc
      loopSubgroupToEndSubgroup b (y0.2 ▸ (Y.hom.mapVertexGroup y0.1).range) =
          H.toSubgroup := hsource_end
      _ =
          loopSubgroupToEndSubgroup b (x0.2 ▸ (X.obj.hom.mapVertexGroup x0.1).range) := by
            exact htarget_end.symm
  -- Convert the `End`-owner equality back to the loop-owner equality used by the classifiers.
  have hEq :
      y0.2 ▸ (Y.hom.mapVertexGroup y0.1).range =
        x0.2 ▸ (X.obj.hom.mapVertexGroup x0.1).range :=
    (loopSubgroupToEndSubgroup_injective (b := b)) hEq_end
  letI : IsConnected Y.left := ConnectedCovering.isConnected Ycov
  obtain ⟨h, hh, _⟩ :=
    (groupoidFunctorOver_existsUnique_hom_iff_mapVertexGroup_range_le_large
      (b := b) (X := Y) (Y := X.obj) (hy := hpX) (e := y0) (e' := x0)).2 hEq.le
  letI : IsPreconnected X.obj.left := (ConnectedCovering.isConnected X).toIsPreconnected
  have hIso : IsIso h :=
    (groupoidFunctorOver_isIso_iff_mapVertexGroup_range_eq_large
      (b := b) (X := Y) (Y := X.obj) (hx := hpY) (hy := hpX) (e := y0) (e' := x0)
      (h := h) (hh := hh)).2 hEq
  refine ⟨H, ⟨?_⟩⟩
  -- Package the underlying owner-level isomorphism into the full subcategory of coverings.
  letI := hIso
  exact ObjectProperty.isoMk _ (asIso h)

/-- Helper for Theorem 3.6.1: the source-facing functor `E(-)` is essentially surjective because
Theorem 3.5.6 reconstructs every connected covering from the subgroup carried by a basepoint. -/
private theorem orbitCategoryToConnectedCovering_isEquivalence_aux :
    Functor.IsEquivalence (orbitCategoryToConnectedCovering b) := by
  let _ : (orbitCategoryToConnectedCovering b).Faithful :=
    { map_injective := by
        intro H K φ ψ hφψ
        -- First compare the induced over-morphisms of element categories, then descend to orbit maps.
        have hMaps :
            CategoryOfElements.map (associatedActionHom b φ) =
              CategoryOfElements.map (associatedActionHom b ψ) := by
          simpa [orbitCategoryToConnectedCovering, orbitCategoryToTransitiveGroupoidAction,
            transitiveGroupoidActionToConnectedCovering] using
            congrArg (fun k => k.hom.left) hφψ
        have hNat :
            associatedActionHom b φ = associatedActionHom b ψ :=
          by
            ext x t
            have hobj :
                (CategoryOfElements.map (associatedActionHom b φ)).obj ⟨x, t⟩ =
                  (CategoryOfElements.map (associatedActionHom b ψ)).obj ⟨x, t⟩ := by
              simpa using congrArg (fun F => F.obj ⟨x, t⟩) hMaps
            injection hobj
        exact associatedAction_hom_injective (b := b) H K hNat }
  let _ : (orbitCategoryToConnectedCovering b).Full :=
    { map_surjective := by
        intro H K F
        exact orbitCategoryToConnectedCovering_map_surjective (b := b) F }
  let _ : (orbitCategoryToConnectedCovering b).EssSurj :=
    { mem_essImage := by
        intro X
        -- Choose a point in the base fiber and reconstruct the covering from its subgroup.
        rcases (ConnectedCovering.isCovering X).1 b with ⟨x0, hx0⟩
        let x0' : X.obj.hom.Fiber b := ⟨x0, hx0⟩
        rcases orbit_covering_iso_of_connected_covering (b := b) X x0' with ⟨H, ⟨e⟩⟩
        exact ⟨H, ⟨e⟩⟩ }
  -- The composite orbit-to-covering functor is faithful, full, and essentially surjective.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- The category-of-elements bridge from transitive `B`-actions to connected coverings is an
equivalence. -/
-- Proof sketch: the inverse is the fiber-translation functor of a connected covering. Theorem
-- 3.5.6 and Theorem 3.5.8 identify maps of coverings with equivariant maps of the corresponding
-- fibers, while connectedness supplies the transitivity needed to reconstruct the covering from
-- its fiber action.
theorem transitiveGroupoidActionToConnectedCovering_isEquivalence :
    Functor.IsEquivalence
      (transitiveGroupoidActionToConnectedCovering :
        CategoryTheory.ObjectProperty.FullSubcategory
          (Functor.IsTransitive : CategoryTheory.ObjectProperty (B ⥤ Type v)) ⥤
            ConnectedCovering B) := by
  classical
  let b : B := Classical.choice inferInstance
  let _ : Functor.IsEquivalence (orbitCategoryToTransitiveGroupoidAction b) :=
    orbitCategoryToTransitiveGroupoidAction_isEquivalence_aux (B := B) b
  let _ : Functor.IsEquivalence (orbitCategoryToConnectedCovering b) :=
    orbitCategoryToConnectedCovering_isEquivalence_aux (B := B) (b := b)
  -- Route correction: rather than forcing a too-small fiber-translation inverse, recover the
  -- covering-side equivalence from the already reconstructed composite by 2-out-of-3.
  simpa [orbitCategoryToConnectedCovering] using
    (Functor.isEquivalence_of_comp_left
      (orbitCategoryToTransitiveGroupoidAction b)
      transitiveGroupoidActionToConnectedCovering :
        Functor.IsEquivalence transitiveGroupoidActionToConnectedCovering)

/-- The orbit-category-to-transitive-action functor is the core bridge used in the proof of
Theorem 3.6.1. -/
-- Proof sketch: full faithfulness and essential surjectivity reduce to the quotient-stabilizer
-- description of transitive vertex-group actions on a connected groupoid.
theorem orbitCategoryToTransitiveGroupoidAction_isEquivalence :
    Functor.IsEquivalence (orbitCategoryToTransitiveGroupoidAction b) := by
  exact orbitCategoryToTransitiveGroupoidAction_isEquivalence_aux (B := B) b

/-- Theorem 3.6.1: for a connected groupoid `B` with base object `b`, the source-facing functor
`E(-) : O(π(B,b)) ⥤ Cov(B)` sending `π(B,b) / H` to the associated connected covering over `B`
is an equivalence of categories, realizing conjugacy classes of subgroups by connected coverings.
-/
-- Proof sketch: factor `E(-)` through the core bridge `O(π(B,b)) ⥤` transitive `B`-actions and
-- then through the category-of-elements bridge to `Cov(B)`. The first factor is the orbit-action
-- classification, and the second identifies a transitive action with its connected covering of
-- elements.
theorem orbitCategoryToConnectedCovering_isEquivalence :
    Functor.IsEquivalence (orbitCategoryToConnectedCovering b) := by
  exact orbitCategoryToConnectedCovering_isEquivalence_aux (B := B) (b := b)
