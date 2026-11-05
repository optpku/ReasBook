module

public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap04.Definition_4_44_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe wB vB uB

namespace CategoryTheory

open scoped Bicategory

open Limits CategoricalPullback
open CategoricalPullback.CatCommSqOver
open Bicategory

/- Domain sampling for Lemma 4.44.3:
- primary domain: bicategorical dotted-arrow categories and fibred-in-groupoids projections over a
  dotted-arrow base;
- owner abstractions inspected: `BicategoricalTwoCommutativeSquare`,
  `DottedArrow.postcomposeRightFunctor`, `CategoricalPullback.π₁`, and
  `CatCommSqOver.toFunctorToCategoricalPullback`;
- triage:
  `source-facing`: the auxiliary category `D''` and the left-square comparison for a fixed middle
  dotted arrow;
  `core/canonical`: `DottedArrow`, `CategoricalPullback`, and
  `IsFibredInGroupoids`/`FibredInGroupoidsOver`;
  `bridge/view`: the transport from outer dotted arrows to middle ones, the projection
  `D'' ⥤ D'`, and the fiberwise comparison functors;
- primitive data for `D''`: an intermediate dotted arrow, an outer dotted arrow, and a
  comparison `middle.arrow ≅ outer.arrow ≫ f`, exactly the owner data of a categorical pullback in
  the hom-category `Hom(T, Y)`;
- derived API: the projection to the middle dotted-arrow category and the fiberwise equivalence
  with the dotted-arrow category of the corresponding left square. -/

section CompositionAux

variable {B : Type uB} [Bicategory.{wB, vB} B] [Bicategory.IsLocallyGroupoid B]
variable {S T X Y Z : B}
variable (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z) (z : T ⟶ Z)
variable (γ : j ≫ z ≅ x ≫ f ≫ g)

namespace DottedArrowComposition

/-- The outer `2`-commutative square of Lemma 4.44.3. -/
abbrev outerSquare :
    BicategoricalTwoCommutativeSquare z (f ≫ g) :=
  { obj := S
    p := j
    q := x
    ψ := γ }

/-- The source-facing middle square `D'` of Lemma 4.44.3. -/
abbrev middleSquare :
    BicategoricalTwoCommutativeSquare z g :=
  BicategoricalTwoCommutativeSquare.postcomposeRight
    (outerSquare x j f g z γ) (Iso.refl (f ≫ g))

local notation "outerSq" => outerSquare x j f g z γ
local notation "middleSq" => middleSquare x j f g z γ

/-- The left square cut out by an intermediate dotted arrow. -/
noncomputable def leftSquare
    (d : DottedArrow middleSq) :
    BicategoricalTwoCommutativeSquare d.arrow f :=
  { obj := S
    p := j
    q := x
    ψ := d.left }

/-- The base category `D'` of intermediate dotted arrows. -/
private abbrev middleArrow :
    DottedArrow middleSq ⥤ (T ⟶ Y) where
  obj d := d.arrow
  map η := η.right
  map_id := by
    intro d
    rfl
  map_comp := by
    intro d d' d'' η θ
    rfl

/-- The canonical bridge from outer dotted arrows to middle dotted arrows. -/
noncomputable abbrev middleOfOuter :
    DottedArrow outerSq ⥤ DottedArrow middleSq :=
  DottedArrow.postcomposeRightFunctor (outerSquare x j f g z γ) (Iso.refl (f ≫ g))

/-- The arrow functor from outer dotted arrows to the hom-category `Hom(T, Y)`. -/
private noncomputable abbrev outerArrow :
    DottedArrow outerSq ⥤ (T ⟶ Y) :=
  middleOfOuter x j f g z γ ⋙ middleArrow x j f g z γ

/-- Helper for Lemma 4.44.3: the corrected auxiliary category `D''` is the pullback of the
identity of `D'` and the canonical functor from outer dotted arrows to middle dotted arrows. -/
noncomputable abbrev auxCategory :=
  (𝟭 (DottedArrow middleSq)) ⊡ (middleOfOuter x j f g z γ)

/-- Helper for Lemma 4.44.3: the corrected projection `D'' ⥤ D'` forgets the outer dotted-arrow
component and keeps the chosen middle dotted arrow. -/
noncomputable abbrev auxProjection :
    auxCategory x j f g z γ ⥤ DottedArrow middleSq :=
  π₁ (𝟭 (DottedArrow middleSq)) (middleOfOuter x j f g z γ)

/-- Helper for Lemma 4.44.3: forgetting the chosen middle dotted arrow recovers the outer
dotted-arrow component of an auxiliary object. -/
private noncomputable abbrev auxForgetOuter :
    auxCategory x j f g z γ ⥤ DottedArrow outerSq :=
  π₂ (𝟭 (DottedArrow middleSq)) (middleOfOuter x j f g z γ)

/-- The auxiliary projection is fibred in groupoids over the intermediate dotted-arrow category. -/
instance auxProjection_isFibredInGroupoids :
    IsFibredInGroupoids (auxProjection x j f g z γ) := by
  refine
    { toIsFibered := ?_
      isStronglyCartesian_map := ?_ }
  · refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro P d δ
    let Q : auxCategory x j f g z γ :=
      { fst := d
        snd := P.snd
        iso := asIso δ ≪≫ P.iso }
    let φ : Q ⟶ P :=
      { fst := δ
        snd := 𝟙 P.snd
        w := by
          simp [Q] }
    refine ⟨Q, φ, ?_⟩
    letI : IsIso φ :=
      (CategoricalPullback.isIso_iff
        (F := 𝟭 (DottedArrow middleSq))
        (G := middleOfOuter x j f g z γ) φ).2 ⟨inferInstance, inferInstance⟩
    exact
      Functor.IsStronglyCartesian.of_isIso
        (p := auxProjection x j f g z γ)
        ((auxProjection x j f g z γ).map φ) φ
  · intro P Q φ
    letI : IsIso φ :=
      (CategoricalPullback.isIso_iff
        (F := 𝟭 (DottedArrow middleSq))
        (G := middleOfOuter x j f g z γ) φ).2 ⟨inferInstance, inferInstance⟩
    exact
      Functor.IsStronglyCartesian.of_isIso
        (p := auxProjection x j f g z γ)
        ((auxProjection x j f g z γ).map φ) φ

/-- The canonical auxiliary category `D''` of Lemma 4.44.3. -/
noncomputable def auxOver :
    FibredInGroupoidsOver (DottedArrow middleSq) :=
  FibredInGroupoidsOver.ofFunctor (auxProjection x j f g z γ)

/-- The canonical functor from outer dotted arrows to the auxiliary category `D''`. -/
noncomputable def auxFromOuter :
    DottedArrow outerSq ⥤ (auxOver x j f g z γ).S :=
  show DottedArrow outerSq ⥤ auxCategory x j f g z γ from
    { obj := fun A ↦
        { fst := (middleOfOuter x j f g z γ).obj A
          snd := A
          iso := Iso.refl _ }
      map := fun {A B} θ ↦
        { fst := (middleOfOuter x j f g z γ).map θ
          snd := θ
          w := by
            simp }
      map_id := by
        intro A
        apply CategoricalPullback.hom_ext
        · simp
        · simp
      map_comp := by
        intro A B C η θ
        apply CategoricalPullback.hom_ext
        · simp
        · simp }

/-- The canonical functor from outer dotted arrows to the auxiliary category `D''` is an
equivalence. -/
theorem auxFromOuter_isEquivalence :
    (auxFromOuter x j f g z γ).IsEquivalence := by
  -- The outer component is an evident quasi-inverse to the pullback comparison functor.
  refine Functor.IsEquivalence.mk' (auxForgetOuter x j f g z γ) ?_ ?_
  · refine NatIso.ofComponents (fun A ↦ Iso.refl A) ?_
    intro A B θ
    simp [auxFromOuter, auxForgetOuter]
  · refine NatIso.ofComponents (fun P ↦ ?_) ?_
    · -- The counit remembers the stored pullback comparison isomorphism on the first component.
      refine CategoricalPullback.mkIso P.iso.symm (Iso.refl _) ?_
      simp [auxFromOuter, auxForgetOuter]
    · intro P Q φ
      apply CategoricalPullback.hom_ext
      · simpa using (CategoricalPullback.Hom.w' φ)
      · change φ.snd ≫ (Iso.refl Q.snd).hom = (Iso.refl P.snd).hom ≫ φ.snd
        simp

omit [Bicategory.IsLocallyGroupoid B] in
/-- Helper for Lemma 4.44.3: composing the left-square comparison with the fixed middle
comparison produces the outer rectangle comparison. -/
private theorem outer_comparison_of_left_comm
    (d : DottedArrow middleSq)
    (A : DottedArrow (leftSquare x j f g z γ d)) :
    j ◁ d.right.hom ≫
        j ◁ A.right.hom ▷ g ≫
          (α_ j (A.arrow ≫ f) g).inv ≫
            (α_ j A.arrow f).inv ▷ g ≫
              A.left.hom ▷ f ▷ g ≫
                (α_ x f g).hom =
      γ.hom := by
  -- Route correction: first rewrite the whiskered left-square comparison into the shell appearing
  -- in `d.comm`, then cancel the final associator contributed by `middleSquare`.
  have hA :
      j ◁ A.right.hom ▷ g ≫
          (α_ j (A.arrow ≫ f) g).inv ≫
            (α_ j A.arrow f).inv ▷ g ≫
              A.left.hom ▷ f ▷ g =
        (α_ j d.arrow g).inv ≫ d.left.hom ▷ g := by
    -- Whiskering the left-square relation by `g` exposes exactly the shell needed by `d.comm`.
    have hA_whisker :
        (α_ j d.arrow g).hom ≫
            j ◁ A.right.hom ▷ g ≫
              (α_ j (A.arrow ≫ f) g).inv ≫
                (α_ j A.arrow f).inv ▷ g ≫
                  A.left.hom ▷ f ▷ g =
          d.left.hom ▷ g := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ▷ g) (congrArg Iso.hom A.comm)
    simpa [Category.assoc] using
      congrArg (fun k ↦ (α_ j d.arrow g).inv ≫ k) hA_whisker
  have hA' :
      j ◁ d.right.hom ≫
          (j ◁ A.right.hom ▷ g ≫
            (α_ j (A.arrow ≫ f) g).inv ≫
              (α_ j A.arrow f).inv ▷ g ≫
                A.left.hom ▷ f ▷ g) =
        j ◁ d.right.hom ≫ ((α_ j d.arrow g).inv ≫ d.left.hom ▷ g) := by
    exact congrArg (fun k ↦ j ◁ d.right.hom ≫ k) hA
  have hgoal :
      (j ◁ d.right.hom ≫
          j ◁ A.right.hom ▷ g ≫
            (α_ j (A.arrow ≫ f) g).inv ≫
              (α_ j A.arrow f).inv ▷ g ≫
                A.left.hom ▷ f ▷ g) ≫
        (α_ x f g).hom =
      γ.hom := by
    let shell := ((α_ j d.arrow g).inv ≫ d.left.hom ▷ g)
    have hd := by
      simpa [shell, middleSquare, outerSquare, BicategoricalTwoCommutativeSquare.postcomposeRight,
        Category.assoc] using
          (congrArg (fun k ↦ k ≫ (α_ x f g).hom) (congrArg Iso.hom d.comm))
    calc
      (j ◁ d.right.hom ≫
          j ◁ A.right.hom ▷ g ≫
            (α_ j (A.arrow ≫ f) g).inv ≫
              (α_ j A.arrow f).inv ▷ g ≫
                A.left.hom ▷ f ▷ g) ≫
          (α_ x f g).hom =
      (j ◁ d.right.hom ≫ shell) ≫ (α_ x f g).hom := by
            exact congrArg (fun k ↦ k ≫ (α_ x f g).hom) hA'
      _ = γ.hom := hd
  simpa [Category.assoc] using hgoal

omit [Bicategory.IsLocallyGroupoid B] in
/-- Helper for Lemma 4.44.3: morphisms of left-square dotted arrows respect the composed outer
right comparison. -/
private theorem outer_of_left_map_right_comm
    (d : DottedArrow middleSq)
    {A B : DottedArrow (leftSquare x j f g z γ d)}
    (θ : A ⟶ B) :
    (d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g).hom ≫ θ.right ▷ (f ≫ g) =
      (d.right ≪≫ whiskerRightIso B.right g ≪≫ α_ B.arrow f g).hom := by
  -- The morphism compatibility is exactly `θ.right` transported through the same right shell as
  -- in the object-level construction.
  have hα :
      (α_ A.arrow f g).hom ≫ θ.right ▷ (f ≫ g) =
        θ.right ▷ f ▷ g ≫ (α_ B.arrow f g).hom := by
    calc
      (α_ A.arrow f g).hom ≫ θ.right ▷ (f ≫ g) =
          (α_ A.arrow f g).hom ≫ θ.right ▷ (f ≫ g) ≫ 𝟙 (B.arrow ≫ (f ≫ g)) := by
            simp
      _ = θ.right ▷ f ▷ g ≫ (α_ B.arrow f g).hom ≫ 𝟙 (B.arrow ≫ (f ≫ g)) := by
            exact (associator_naturality_left_assoc θ.right f g (𝟙 (B.arrow ≫ (f ≫ g)))).symm
      _ = θ.right ▷ f ▷ g ≫ (α_ B.arrow f g).hom := by
            simp
  calc
    (d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g).hom ≫ θ.right ▷ (f ≫ g)
        = d.right.hom ≫
            A.right.hom ▷ g ≫
              (α_ A.arrow f g).hom ≫
                θ.right ▷ (f ≫ g) := by
            simp [Category.assoc]
    _ = d.right.hom ≫
          A.right.hom ▷ g ≫
            (θ.right ▷ f ▷ g) ≫
              (α_ B.arrow f g).hom := by
          rw [hα]
    _ = d.right.hom ≫
          (A.right.hom ≫ θ.right ▷ f) ▷ g ≫
            (α_ B.arrow f g).hom := by
          rw [← comp_whiskerRight_assoc]
    _ = d.right.hom ≫
          B.right.hom ▷ g ≫
            (α_ B.arrow f g).hom := by
          rw [DottedArrow.Hom.right_comm θ]
    _ = (d.right ≪≫ whiskerRightIso B.right g ≪≫ α_ B.arrow f g).hom := by
      simp

/-- The canonical functor from the left-square dotted-arrow category to the fiber of the
auxiliary projection over a fixed intermediate dotted arrow. -/
noncomputable def outerOfLeft
    (d : DottedArrow middleSq) :
    DottedArrow (leftSquare x j f g z γ d) ⥤ DottedArrow outerSq :=
  { obj := fun A ↦
      let t : LeftLift (f ≫ g) z :=
        LeftLift.mk A.arrow
          ((d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g).hom)
      let _ : IsIso t.unit := by
        change IsIso ((d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g).hom)
        infer_instance
      -- The outer dotted arrow keeps the same dotted morphism and composes the two right
      -- comparison isomorphisms into the outer rectangle comparison.
      { toLeftLift := t
        unit_isIso := inferInstance
        comparison := DottedArrow.comparisonIsoMk t A.left <| by
          simpa [t, Category.assoc] using outer_comparison_of_left_comm x j f g z γ d A }
    map := fun {A B} θ ↦
      ⟨LeftLift.homMk θ.right <| by
          -- The outer right comparison respects morphisms because `θ.right` already commutes
          -- with the fixed middle comparison and the left-square lower-right comparison.
          exact outer_of_left_map_right_comm x j f g z γ d θ,
        by
          -- The upper-left comparison is unchanged, so the original left compatibility suffices.
          apply StructuredArrow.hom_ext
          change j ◁ θ.right ≫ B.left.hom = A.left.hom
          exact DottedArrow.Hom.left_comm θ⟩
    map_id := by
      intro A
      -- The functor acts as the identity on the ambient right `2`-morphism.
      apply DottedArrow.Hom.ext
      rfl
    map_comp := by
      intro A B C η θ
      -- Composition is preserved because the outer map uses the same ambient right component.
      apply DottedArrow.Hom.ext
      rfl }

omit [Bicategory.IsLocallyGroupoid B] in
/-- Helper for Lemma 4.44.3: the outer dotted arrow constructed from a left-square object carries
exactly the composed lower-right comparison used in the textbook tuple model. -/
private theorem outerOfLeft_obj_right_hom
    (d : DottedArrow middleSq)
    (A : DottedArrow (leftSquare x j f g z γ d)) :
    ((outerOfLeft x j f g z γ d).obj A).right.hom =
      (d.right ≪≫ whiskerRightIso A.right g ≪≫ α_ A.arrow f g).hom := by
  -- The constructed outer object is defined with this right comparison as its `LeftLift` unit.
  rfl

omit [Bicategory.IsLocallyGroupoid B] in
/-- Helper for Lemma 4.44.3: a left-square dotted arrow induces a middle dotted-arrow isomorphism
from the fixed middle object to the middle object computed from the associated outer dotted
arrow. -/
private theorem middle_of_outer_of_left_right_comm
    (d : DottedArrow middleSq)
    (A : DottedArrow (leftSquare x j f g z γ d)) :
    d.right.hom ≫ A.right.hom ▷ g =
      ((middleOfOuter x j f g z γ).obj ((outerOfLeft x j f g z γ d).obj A)).toLeftLift.unit := by
  -- Unfolding `middleOfOuter` on the explicit outer object produces the same right shell, and
  -- the postcomposition pair of associators cancels against the chosen outer right comparison.
  have hm :
      ((middleOfOuter x j f g z γ).obj ((outerOfLeft x j f g z γ d).obj A)).right.hom =
        d.right.hom ≫ A.right.hom ▷ g := by
    unfold middleOfOuter DottedArrow.postcomposeRightFunctor
    rw [DottedArrow.right_hom]
    unfold DottedArrow.postcomposeRight
    change
      (((outerOfLeft x j f g z γ d).obj A).right ≪≫
          whiskerLeftIso A.arrow (Iso.refl (f ≫ g)) ≪≫
            (α_ A.arrow f g).symm).hom =
        d.right.hom ≫ A.right.hom ▷ g
    have h_outer :
        ((outerOfLeft x j f g z γ d).obj A).toLeftLift.unit =
          d.right.hom ≫ A.right.hom ▷ g ≫ (α_ A.arrow f g).hom := by
      simpa [DottedArrow.right_hom] using outerOfLeft_obj_right_hom x j f g z γ d A
    have hcancel :
        (d.right.hom ≫ A.right.hom ▷ g ≫ (α_ A.arrow f g).hom) ≫
            𝟙 (A.arrow ≫ f ≫ g) ≫
              (α_ A.arrow f g).inv =
          d.right.hom ≫ A.right.hom ▷ g := by
      simp [Category.assoc]
    calc
      (((outerOfLeft x j f g z γ d).obj A).right ≪≫
          whiskerLeftIso A.arrow (Iso.refl (f ≫ g)) ≪≫
            (α_ A.arrow f g).symm).hom =
        ((outerOfLeft x j f g z γ d).obj A).toLeftLift.unit ≫
          𝟙 (A.arrow ≫ f ≫ g) ≫
            (α_ A.arrow f g).inv := by
              simp [DottedArrow.right_hom]
      _ =
        (d.right.hom ≫ A.right.hom ▷ g ≫ (α_ A.arrow f g).hom) ≫
          𝟙 (A.arrow ≫ f ≫ g) ≫
            (α_ A.arrow f g).inv := by
              rw [h_outer]
              rfl
      _ = d.right.hom ≫ A.right.hom ▷ g := hcancel
  calc
    d.right.hom ≫ A.right.hom ▷ g =
        ((middleOfOuter x j f g z γ).obj ((outerOfLeft x j f g z γ d).obj A)).right.hom := by
          exact hm.symm
    _ = ((middleOfOuter x j f g z γ).obj ((outerOfLeft x j f g z γ d).obj A)).toLeftLift.unit := by
          simp [DottedArrow.right_hom]

/-- Helper for Lemma 4.44.3: a left-square dotted arrow induces a middle dotted-arrow isomorphism
from the fixed middle object to the middle object computed from the associated outer dotted
arrow. -/
noncomputable def middleOfOuter_of_left_hom
    (d : DottedArrow middleSq)
    (A : DottedArrow (leftSquare x j f g z γ d)) :
    d ⟶ (middleOfOuter x j f g z γ).obj ((outerOfLeft x j f g z γ d).obj A) :=
  ⟨LeftLift.homMk A.right.hom <| by
      -- The right component of the bridge is exactly the lower-right comparison of `A`,
      -- and the postcomposition functor computes the target lower-right comparison from it.
      exact middle_of_outer_of_left_right_comm x j f g z γ d A,
    by
      -- The left compatibility is the defining square relation for the left-square dotted arrow.
      apply StructuredArrow.hom_ext
      simpa [middleOfOuter, outerOfLeft, Category.assoc] using congrArg Iso.hom A.comm⟩

omit [Bicategory.IsLocallyGroupoid B] in
/-- Helper for Lemma 4.44.3: `outerOfLeft` preserves the ambient right `2`-morphism literally,
which is the component later reused in the fiber comparison. -/
private theorem outerOfLeft_map_right
    (d : DottedArrow middleSq)
    {A B : DottedArrow (leftSquare x j f g z γ d)}
    (θ : A ⟶ B) :
    ((outerOfLeft x j f g z γ d).map θ).right = θ.right := by
  -- The outer functor was defined by reusing `θ.right` as its ambient component.
  rfl

/-- Helper for Lemma 4.44.3: the map from a left-square dotted arrow to its reconstructed middle
object is invertible because dotted-arrow categories are groupoids in a `(2,1)`-category. -/
noncomputable def middleOfOuter_of_left_iso
    (d : DottedArrow middleSq)
    (A : DottedArrow (leftSquare x j f g z γ d)) :
    d ≅ (middleOfOuter x j f g z γ).obj ((outerOfLeft x j f g z γ d).obj A) :=
  asIso (middleOfOuter_of_left_hom x j f g z γ d A)

/-- Helper for Lemma 4.44.3: the comparison isomorphisms `d ≅ middle(outer(A))` are natural in a
morphism of left-square dotted arrows, exactly in the form needed for a pullback morphism over
`d`. -/
private theorem middleOfOuter_of_left_iso_naturality
    (d : DottedArrow middleSq)
    {A B : DottedArrow (leftSquare x j f g z γ d)}
    (θ : A ⟶ B) :
    (middleOfOuter_of_left_iso x j f g z γ d A).hom ≫
        (middleOfOuter x j f g z γ).map ((outerOfLeft x j f g z γ d).map θ) =
      (middleOfOuter_of_left_iso x j f g z γ d B).hom := by
  -- Route correction: the pullback compatibility is just equality of dotted-arrow morphisms with
  -- the same right component.
  apply DottedArrow.Hom.ext
  change A.right.hom ≫ (((outerOfLeft x j f g z γ d).map θ).right ▷ f) = B.right.hom
  rw [outerOfLeft_map_right]
  exact DottedArrow.Hom.right_comm θ

/-- Helper for Lemma 4.44.3: the pullback object attached to a left-square dotted arrow lies over
the fixed middle dotted arrow `d`. -/
noncomputable def leftToAuxFiberObject
    (d : DottedArrow middleSq)
    (A : DottedArrow (leftSquare x j f g z γ d)) :
    ((auxOver x j f g z γ).p).Fiber d :=
  Functor.Fiber.mk (a := {
    fst := d
    snd := (outerOfLeft x j f g z γ d).obj A
    iso := middleOfOuter_of_left_iso x j f g z γ d A
  }) rfl

/-- Helper for Lemma 4.44.3: a morphism of left-square dotted arrows yields the canonical morphism
between the associated pullback objects over `d`. -/
private theorem leftToAuxFiber_map_w
    (d : DottedArrow middleSq)
    {A B : DottedArrow (leftSquare x j f g z γ d)}
    (θ : A ⟶ B) :
    (𝟭 (DottedArrow middleSq)).map (𝟙 d) ≫
        (middleOfOuter_of_left_iso x j f g z γ d B).hom =
      (middleOfOuter_of_left_iso x j f g z γ d A).hom ≫
        (middleOfOuter x j f g z γ).map ((outerOfLeft x j f g z γ d).map θ) := by
  simpa using (middleOfOuter_of_left_iso_naturality x j f g z γ d θ).symm

/-- Helper for Lemma 4.44.3: the raw pullback morphism attached to a left-square morphism lies
over the identity of `d` for the auxiliary projection. -/
noncomputable def leftToAuxFiberRawHom
    (d : DottedArrow middleSq)
    {A B : DottedArrow (leftSquare x j f g z γ d)}
    (θ : A ⟶ B) :
    (leftToAuxFiberObject x j f g z γ d A).1 ⟶
      (leftToAuxFiberObject x j f g z γ d B).1 :=
  { fst := 𝟙 d
    snd := (outerOfLeft x j f g z γ d).map θ
    w := by
      -- The pullback compatibility is exactly the normalized naturality of the stored bridge.
      change
        (𝟭 (DottedArrow middleSq)).map (𝟙 d) ≫
            (middleOfOuter_of_left_iso x j f g z γ d B).hom =
          (middleOfOuter_of_left_iso x j f g z γ d A).hom ≫
            (middleOfOuter x j f g z γ).map ((outerOfLeft x j f g z γ d).map θ)
      simpa using leftToAuxFiber_map_w x j f g z γ d θ }

/-- Helper for Lemma 4.44.3: the raw pullback morphism attached to a left-square morphism lies
over the identity of `d` for the auxiliary projection. -/
private theorem leftToAuxFiberRawHom_projection_eq_id
    (d : DottedArrow middleSq)
    {A B : DottedArrow (leftSquare x j f g z γ d)}
    (θ : A ⟶ B) :
    ((auxOver x j f g z γ).p).map (leftToAuxFiberRawHom x j f g z γ d θ) = 𝟙 d := by
  -- The auxiliary projection remembers only the first pullback component, which was defined to
  -- be `𝟙 d`.
  change (leftToAuxFiberRawHom x j f g z γ d θ).fst = 𝟙 d
  rfl

/-- Helper for Lemma 4.44.3: the raw pullback morphism attached to a left-square morphism lies
over the identity of `d` for the auxiliary projection. -/
theorem leftToAuxFiberMap_isHomLift
    (d : DottedArrow middleSq)
    {A B : DottedArrow (leftSquare x j f g z γ d)}
    (θ : A ⟶ B) :
    ((auxOver x j f g z γ).p).IsHomLift (𝟙 d) (leftToAuxFiberRawHom x j f g z γ d θ) := by
  -- The projection equation is literal, so the owner-level `IsHomLift.of_fac'` closes the lift.
  refine
    IsHomLift.of_fac' ((auxOver x j f g z γ).p) (𝟙 d)
      (leftToAuxFiberRawHom x j f g z γ d θ) rfl rfl ?_
  simpa using leftToAuxFiberRawHom_projection_eq_id x j f g z γ d θ

/-- Helper for Lemma 4.44.3: a morphism of left-square dotted arrows yields the canonical morphism
between the associated pullback objects over `d`. -/
noncomputable def leftToAuxFiberMap
    (d : DottedArrow middleSq)
    {A B : DottedArrow (leftSquare x j f g z γ d)}
    (θ : A ⟶ B) :
    leftToAuxFiberObject x j f g z γ d A ⟶
      leftToAuxFiberObject x j f g z γ d B :=
  ⟨leftToAuxFiberRawHom x j f g z γ d θ,
    leftToAuxFiberMap_isHomLift x j f g z γ d θ⟩

/-- Helper for Lemma 4.44.3: the forward fiberwise comparison preserves identities. -/
theorem leftToAuxFiber_map_id
    (d : DottedArrow middleSq)
    (A : DottedArrow (leftSquare x j f g z γ d)) :
    leftToAuxFiberMap x j f g z γ d (𝟙 A) =
      𝟙 (leftToAuxFiberObject x j f g z γ d A) := by
  -- Equality in the fiber reduces to equality of the underlying pullback morphisms.
  apply Functor.Fiber.hom_ext
  apply CategoricalPullback.hom_ext
  · rfl
  · change (outerOfLeft x j f g z γ d).map (𝟙 A) =
        𝟙 ((outerOfLeft x j f g z γ d).obj A)
    exact Functor.map_id (outerOfLeft x j f g z γ d) A

/-- Helper for Lemma 4.44.3: the forward fiberwise comparison preserves composition. -/
theorem leftToAuxFiber_map_comp
    (d : DottedArrow middleSq)
    {A B C : DottedArrow (leftSquare x j f g z γ d)}
    (η : A ⟶ B) (θ : B ⟶ C) :
    leftToAuxFiberMap x j f g z γ d (η ≫ θ) =
      leftToAuxFiberMap x j f g z γ d η ≫
        leftToAuxFiberMap x j f g z γ d θ := by
  -- Equality in the fiber again reduces to the outer dotted-arrow functoriality on the second
  -- pullback component.
  apply Functor.Fiber.hom_ext
  apply CategoricalPullback.hom_ext
  · change 𝟙 d = (𝟙 d ≫ 𝟙 d)
    simp
  · change
      (outerOfLeft x j f g z γ d).map (η ≫ θ) =
        (outerOfLeft x j f g z γ d).map η ≫ (outerOfLeft x j f g z γ d).map θ
    exact Functor.map_comp (outerOfLeft x j f g z γ d) η θ

/-- The fiberwise comparison functor from left-square dotted arrows to the auxiliary fiber. -/
noncomputable def leftToAuxFiber
    (d : DottedArrow middleSq) :
    DottedArrow (leftSquare x j f g z γ d) ⥤ ((auxOver x j f g z γ).p).Fiber d where
  obj A := leftToAuxFiberObject x j f g z γ d A
  map θ := leftToAuxFiberMap x j f g z γ d θ
  map_id A := leftToAuxFiber_map_id x j f g z γ d A
  map_comp η θ := leftToAuxFiber_map_comp x j f g z γ d η θ

omit [Bicategory.IsLocallyGroupoid B] in
/-- Helper for Lemma 4.44.3: once an auxiliary object is normalized so that its first pullback
component is the fixed middle dotted arrow `d`, its stored bridge to `middle(outer)` is exactly
the left-square compatibility needed to recover a dotted arrow for the left square. -/
private theorem fiber_object_to_left_square_comm
    (d : DottedArrow middleSq)
    (Qsnd : DottedArrow outerSq)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd) :
    j ◁ Qiso.hom.right ≫ (α_ j Qsnd.arrow f).inv ≫ Qsnd.left.hom ▷ f =
      d.left.hom := by
  -- This is precisely the left compatibility of the normalized morphism
  -- `Qiso.hom : d ⟶ middle(Qsnd)`.
  have hleft :
      j ◁ DottedArrow.Hom.right Qiso.hom ≫ ((middleOfOuter x j f g z γ).obj Qsnd).left.hom =
        d.left.hom :=
    DottedArrow.Hom.left_comm Qiso.hom
  simpa [middleOfOuter, DottedArrow.postcomposeRightFunctor, DottedArrow.postcomposeRight,
    leftSquare, Category.assoc] using hleft

/-- Helper for Lemma 4.44.3: the normalized auxiliary data `(Qsnd, Qiso)` defines the
corresponding dotted arrow for the left square over `d`. -/
private noncomputable def fiberToLeftSquareNormalized
    (d : DottedArrow middleSq)
    (Qsnd : DottedArrow outerSq)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd) :
    DottedArrow (leftSquare x j f g z γ d) := by
  let t : LeftLift f d.arrow := LeftLift.mk Qsnd.arrow Qiso.hom.right
  let leftIso : j ≫ t.lift ≅ x := Qsnd.left
  let comm : j ◁ t.unit ≫ (α_ j t.lift f).inv ≫ leftIso.hom ▷ f = d.left.hom :=
    fiber_object_to_left_square_comm x j f g z γ d Qsnd Qiso
  let _ : IsIso t.unit := by
    change IsIso Qiso.hom.right
    infer_instance
  exact
    { toLeftLift := t
      unit_isIso := inferInstance
      comparison := DottedArrow.comparisonIsoMk t leftIso comm }

/-- Helper for Lemma 4.44.3: a normalized fiber object over `d` determines the corresponding
left-square dotted arrow. -/
private noncomputable def fiberToLeftSquareObject
    (d : DottedArrow middleSq)
    (P : ((auxOver x j f g z γ).p).Fiber d) :
    DottedArrow (leftSquare x j f g z γ d) := by
  rcases P with ⟨⟨d, Qsnd, Qiso⟩, rfl⟩
  exact fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso

/-- Helper for Lemma 4.44.3: after normalizing a fiber morphism over `d`, its pullback
compatibility is exactly the lower-right compatibility needed for the reconstructed left-square
morphism. -/
private theorem normalized_fiber_morphism_fst_eq_id
    (d : DottedArrow middleSq)
    {Psnd Qsnd : DottedArrow outerSq}
    (Piso : d ≅ (middleOfOuter x j f g z γ).obj Psnd)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd)
    (φ :
      Functor.Fiber.mk
          (a := ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ))
          (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ) = d from rfl) ⟶
        Functor.Fiber.mk
          (a := ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ))
    (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ) = d from rfl)) :
    φ.1.fst = 𝟙 d := by
  -- The fiber lift data says that the pullback morphism lies over the identity of `d`.
  have hmap :
      ((auxOver x j f g z γ).p).map (Functor.Fiber.fiberInclusion.map φ) = 𝟙 d := by
    simpa using
      (CategoryTheory.IsHomLift.fac'
        ((auxOver x j f g z γ).p) (𝟙 d) (Functor.Fiber.fiberInclusion.map φ))
  simpa using hmap

/-- Helper for Lemma 4.44.3: after normalizing a fiber morphism over `d`, its pullback
compatibility is exactly the lower-right compatibility needed for the reconstructed left-square
morphism. -/
private theorem normalized_fiber_morphism_middle_bridge
    (d : DottedArrow middleSq)
    {Psnd Qsnd : DottedArrow outerSq}
    (Piso : d ≅ (middleOfOuter x j f g z γ).obj Psnd)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd)
    (φ :
      Functor.Fiber.mk
          (a := ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ))
          (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ) = d from rfl) ⟶
        Functor.Fiber.mk
          (a := ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ))
    (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ) = d from rfl)) :
    Piso.hom ≫ (middleOfOuter x j f g z γ).map φ.1.snd = Qiso.hom := by
  -- The fiber condition forces the first pullback component to be `𝟙 d`, so the pullback
  -- relation collapses to the textbook compatibility between the two middle comparisons.
  have hfst :
      φ.1.fst = 𝟙 d :=
    normalized_fiber_morphism_fst_eq_id x j f g z γ d Piso Qiso φ
  have hw :
      φ.1.fst ≫ Qiso.hom =
        Piso.hom ≫ (middleOfOuter x j f g z γ).map φ.1.snd := by
    simpa using CategoricalPullback.Hom.w φ.1
  have hmain :
      Piso.hom ≫ (middleOfOuter x j f g z γ).map φ.1.snd =
        φ.1.fst ≫ Qiso.hom := by
    simpa using hw.symm
  rw [hmain]
  rw [hfst]
  exact Category.id_comp Qiso.hom

/-- Helper for Lemma 4.44.3: the outer dotted-arrow component of a normalized fiber morphism
already satisfies the upper-left compatibility for the reconstructed left square. -/
private theorem normalized_fiber_morphism_left_comm
    (d : DottedArrow middleSq)
    {Psnd Qsnd : DottedArrow outerSq}
    (Piso : d ≅ (middleOfOuter x j f g z γ).obj Psnd)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd)
    (φ :
      Functor.Fiber.mk
          (a := ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ))
          (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ) = d from rfl) ⟶
        Functor.Fiber.mk
          (a := ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ))
          (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ) = d from rfl)) :
    j ◁ φ.1.snd.right ≫ Qsnd.left.hom = Psnd.left.hom := by
  -- The left comparison for the reconstructed left square is exactly the left comparison of the
  -- outer dotted-arrow component.
  simpa using DottedArrow.Hom.left_comm φ.1.snd

/-- Helper for Lemma 4.44.3: after normalizing a fiber morphism over `d`, its pullback
compatibility is exactly the lower-right compatibility needed for the reconstructed left-square
morphism. -/
private theorem fiberToLeftSquareMap_right_comm
    (d : DottedArrow middleSq)
    {Psnd Qsnd : DottedArrow outerSq}
    (Piso : d ≅ (middleOfOuter x j f g z γ).obj Psnd)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd)
    (φ :
      Functor.Fiber.mk
          (a := ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ))
          (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ) = d from rfl) ⟶
        Functor.Fiber.mk
          (a := ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ))
    (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ) = d from rfl)) :
    Piso.hom.right ≫ φ.1.snd.right ▷ f = Qiso.hom.right := by
  -- The normalized bridge is an equality of middle dotted-arrow morphisms, so taking right
  -- components gives exactly the lower-right compatibility of the reconstructed left square.
  have hbridge :=
    congrArg DottedArrow.Hom.right
      (normalized_fiber_morphism_middle_bridge x j f g z γ d Piso Qiso φ)
  simpa [middleOfOuter, DottedArrow.postcomposeRightFunctor, DottedArrow.postcomposeRight,
    Category.assoc] using hbridge

/-- Helper for Lemma 4.44.3: a normalized fiber morphism over `d` induces the corresponding
morphism of reconstructed left-square dotted arrows. -/
private noncomputable def normalized_fiber_morphism_to_left_square_hom
    (d : DottedArrow middleSq)
    {Psnd Qsnd : DottedArrow outerSq}
    (Piso : d ≅ (middleOfOuter x j f g z γ).obj Psnd)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd)
    (φ :
      Functor.Fiber.mk
          (a := ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ))
          (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Psnd, iso := Piso } : auxCategory x j f g z γ) = d from rfl) ⟶
        Functor.Fiber.mk
          (a := ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ))
          (show (auxOver x j f g z γ).p.obj
              ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ) = d from rfl)) :
    fiberToLeftSquareNormalized x j f g z γ d Psnd Piso ⟶
      fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso :=
  ⟨show
      (fiberToLeftSquareNormalized x j f g z γ d Psnd Piso).toLeftLift ⟶
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso).toLeftLift from
        LeftLift.homMk φ.1.snd.right (fiberToLeftSquareMap_right_comm x j f g z γ d Piso Qiso φ),
    by
      -- The reconstructed left comparison is inherited unchanged from the outer dotted-arrow
      -- component.
      apply StructuredArrow.hom_ext
      simpa using normalized_fiber_morphism_left_comm x j f g z γ d Piso Qiso φ⟩

/-- Helper for Lemma 4.44.3: the backward fiberwise comparison acts on morphisms by keeping only
the outer dotted-arrow component. -/
private noncomputable def fiberToLeftSquareMap
    (d : DottedArrow middleSq)
    {P Q : ((auxOver x j f g z γ).p).Fiber d}
    (φ : P ⟶ Q) :
    fiberToLeftSquareObject x j f g z γ d P ⟶
      fiberToLeftSquareObject x j f g z γ d Q :=
  match P, Q, φ with
  | ⟨⟨_, _, Piso⟩, rfl⟩, ⟨⟨_, _, Qiso⟩, rfl⟩, φ =>
      normalized_fiber_morphism_to_left_square_hom x j f g z γ d Piso Qiso φ

/-- Helper for Lemma 4.44.3: the backward fiberwise comparison preserves identities. -/
private theorem fiberToLeftSquare_map_id
    (d : DottedArrow middleSq)
    (P : ((auxOver x j f g z γ).p).Fiber d) :
    fiberToLeftSquareMap x j f g z γ d (𝟙 P) =
      𝟙 (fiberToLeftSquareObject x j f g z γ d P) := by
  -- Normalize the fiber object, then read the identity map off from the outer dotted-arrow
  -- component.
  match P with
  | ⟨⟨_, Psnd, Piso⟩, rfl⟩ =>
      apply DottedArrow.Hom.ext
      change (𝟙 Psnd : Psnd ⟶ Psnd).right = 𝟙 (Psnd.arrow)
      simp

/-- Helper for Lemma 4.44.3: the backward fiberwise comparison preserves composition. -/
private theorem fiberToLeftSquare_map_comp
    (d : DottedArrow middleSq)
    {P Q R : ((auxOver x j f g z γ).p).Fiber d}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    fiberToLeftSquareMap x j f g z γ d (φ ≫ ψ) =
      fiberToLeftSquareMap x j f g z γ d φ ≫
        fiberToLeftSquareMap x j f g z γ d ψ := by
  -- Normalize the three fiber objects, then the composite is governed entirely by composition in
  -- the outer dotted-arrow category.
  revert φ ψ
  match P, Q, R with
  | ⟨⟨_, Psnd, Piso⟩, rfl⟩, ⟨⟨_, Qsnd, Qiso⟩, rfl⟩, ⟨⟨_, Rsnd, Riso⟩, rfl⟩ =>
      intro φ ψ
      apply DottedArrow.Hom.ext
      change (φ.1.snd ≫ ψ.1.snd).right = φ.1.snd.right ≫ ψ.1.snd.right
      simp

/-- Helper for Lemma 4.44.3: unpacking a fiber object over `d` produces the corresponding
left-square dotted arrow, with upper-left comparison taken from the outer object and lower-right
comparison taken from the stored bridge to `d`. -/
private noncomputable def fiberToLeftSquare
    (d : DottedArrow middleSq) :
    ((auxOver x j f g z γ).p).Fiber d ⥤ DottedArrow (leftSquare x j f g z γ d) where
  obj P := fiberToLeftSquareObject x j f g z γ d P
  map φ := fiberToLeftSquareMap x j f g z γ d φ
  map_id P := fiberToLeftSquare_map_id x j f g z γ d P
  map_comp φ ψ := fiberToLeftSquare_map_comp x j f g z γ d φ ψ

/-- Helper for Lemma 4.44.3: reconstructing the left square from normalized fiber data and then
returning to the outer rectangle preserves the lower-right comparison morphism. -/
private theorem outerOfLeft_fiberToLeftSquareNormalized_right_hom
    (d : DottedArrow middleSq)
    (Qsnd : DottedArrow outerSq)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd) :
    ((outerOfLeft x j f g z γ d).obj
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).right.hom =
      Qsnd.right.hom := by
  -- The reconstructed outer object uses the normalized left-square lower-right comparison, and
  -- `Qiso.hom` identifies that comparison with the one stored in `Qsnd`.
  have hRight :
      ((outerOfLeft x j f g z γ d).obj
          (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).right.hom =
        ((middleOfOuter x j f g z γ).obj Qsnd).right.hom ≫ (α_ Qsnd.arrow f g).hom := by
    rw [outerOfLeft_obj_right_hom]
    change d.right.hom ≫ Qiso.hom.right ▷ g ≫ (α_ Qsnd.arrow f g).hom =
      ((middleOfOuter x j f g z γ).obj Qsnd).right.hom ≫ (α_ Qsnd.arrow f g).hom
    calc
      d.right.hom ≫ Qiso.hom.right ▷ g ≫ (α_ Qsnd.arrow f g).hom =
          (d.right.hom ≫ Qiso.hom.right ▷ g) ≫ (α_ Qsnd.arrow f g).hom := by
            simp
      _ = ((middleOfOuter x j f g z γ).obj Qsnd).right.hom ≫ (α_ Qsnd.arrow f g).hom := by
            rw [DottedArrow.Hom.right_comm Qiso.hom]
  calc
    ((outerOfLeft x j f g z γ d).obj
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).right.hom =
        ((middleOfOuter x j f g z γ).obj Qsnd).right.hom ≫ (α_ Qsnd.arrow f g).hom := hRight
    _ = Qsnd.right.hom := by
      change
        (Qsnd.right.hom ≫ Qsnd.arrow ◁ (Iso.refl (f ≫ g)).hom ≫ (α_ Qsnd.arrow f g).inv) ≫
            (α_ Qsnd.arrow f g).hom =
          Qsnd.toLeftLift.unit
      simp [Category.assoc]

/-- Helper for Lemma 4.44.3: the reconstructed outer object maps canonically back to the
normalized outer object by the identity right component. -/
private noncomputable def outerOfLeft_fiberToLeftSquareNormalized_hom
    (d : DottedArrow middleSq)
    (Qsnd : DottedArrow outerSq)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd) :
    ((outerOfLeft x j f g z γ d).obj
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)) ⟶
      Qsnd := by
  -- The canonical outer morphism keeps the dotted arrow fixed and only forgets the redundant
  -- reconstruction shell around the lower-right comparison.
  refine ⟨LeftLift.homMk (𝟙 Qsnd.arrow) ?_, ?_⟩
  · -- On the lower-right edge the normalization lemma reduces the compatibility to a right unit.
    change ((outerOfLeft x j f g z γ d).obj
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).right.hom ≫
          (𝟙 Qsnd.arrow ▷ (f ≫ g)) = Qsnd.right.hom
    rw [outerOfLeft_fiberToLeftSquareNormalized_right_hom, id_whiskerRight]
    exact Category.comp_id Qsnd.right.hom
  · -- The upper-left comparison is literally the reused `Qsnd.left`.
    apply StructuredArrow.hom_ext
    change j ◁ (𝟙 Qsnd.arrow) ≫ Qsnd.left.hom =
      ((outerOfLeft x j f g z γ d).obj
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).left.hom
    simp [outerOfLeft, fiberToLeftSquareNormalized, DottedArrow.left, DottedArrow.comparisonIsoMk]

/-- Helper for Lemma 4.44.3: the canonical normalized outer morphism really has identity right
component. -/
private theorem outerOfLeft_fiberToLeftSquareNormalized_hom_right
    (d : DottedArrow middleSq)
    (Qsnd : DottedArrow outerSq)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd) :
    (outerOfLeft_fiberToLeftSquareNormalized_hom x j f g z γ d Qsnd Qiso).right =
      𝟙 Qsnd.arrow :=
  by
    -- The canonical normalized outer morphism was defined with right component `𝟙`.
    rfl

/-- Helper for Lemma 4.44.3: the reconstructed outer object is isomorphic to the normalized
outer object. -/
private noncomputable def outerOfLeft_fiberToLeftSquareNormalized_iso
    (d : DottedArrow middleSq)
    (Qsnd : DottedArrow outerSq)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd) :
    ((outerOfLeft x j f g z γ d).obj
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)) ≅
      Qsnd :=
  asIso (outerOfLeft_fiberToLeftSquareNormalized_hom x j f g z γ d Qsnd Qiso)

omit [Bicategory.IsLocallyGroupoid B] in
/-- Helper for Lemma 4.44.3: whiskering the identity on the reconstructed outer arrow by `f`
stays the identity. -/
private theorem whiskerRight_id_reconstructed
    (Qsnd : DottedArrow outerSq) :
    𝟙 Qsnd.arrow ▷ f = 𝟙 (Qsnd.arrow ≫ f) := by
  simp

/-- Helper for Lemma 4.44.3: after applying the canonical outer isomorphism, the middle bridge
stored in the pullback object becomes exactly the normalized comparison `Qiso`. -/
private theorem outerOfLeft_fiberToLeftSquareNormalized_middle_bridge
    (d : DottedArrow middleSq)
    (Qsnd : DottedArrow outerSq)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd) :
    (middleOfOuter_of_left_iso x j f g z γ d
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).hom ≫
      (middleOfOuter x j f g z γ).map
        (outerOfLeft_fiberToLeftSquareNormalized_iso x j f g z γ d Qsnd Qiso).hom =
      Qiso.hom := by
  -- Route correction: both bridges are morphisms out of `d`, so it is enough to compare the
  -- ambient lower-right `2`-morphism after postcomposing the canonical normalized outer map.
  apply DottedArrow.Hom.ext
  change
    (middleOfOuter_of_left_hom x j f g z γ d
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).right ≫
      (((outerOfLeft_fiberToLeftSquareNormalized_hom x j f g z γ d Qsnd Qiso).right) ▷ f) =
    Qiso.hom.right
  rw [outerOfLeft_fiberToLeftSquareNormalized_hom_right]
  change DottedArrow.Hom.right Qiso.hom ≫ (𝟙 Qsnd.arrow ▷ f) = DottedArrow.Hom.right Qiso.hom
  rw [whiskerRight_id_reconstructed]
  exact Category.comp_id (DottedArrow.Hom.right Qiso.hom)

/-- Helper for Lemma 4.44.3: the normalized reconstructed left-square object maps back to the
given fiber object by a canonical isomorphism in the fiber over `d`. -/
private noncomputable def fiber_counit_normalized
    (d : DottedArrow middleSq)
    (Qsnd : DottedArrow outerSq)
    (Qiso : d ≅ (middleOfOuter x j f g z γ).obj Qsnd) :
    leftToAuxFiberObject x j f g z γ d
        (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso) ≅
      Functor.Fiber.mk
        (a := ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ))
        rfl := by
  -- First package the normalized outer isomorphism in the auxiliary pullback category.
  have heAux_w :
      (𝟭 (DottedArrow middleSq)).map (Iso.refl d).hom ≫ Qiso.hom =
        ((leftToAuxFiberObject x j f g z γ d
          (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).1).iso.hom ≫
          (middleOfOuter x j f g z γ).map
            (outerOfLeft_fiberToLeftSquareNormalized_iso x j f g z γ d Qsnd Qiso).hom := by
    simpa using
      (outerOfLeft_fiberToLeftSquareNormalized_middle_bridge x j f g z γ d Qsnd Qiso).symm
  let eAux :
      (leftToAuxFiberObject x j f g z γ d
          (fiberToLeftSquareNormalized x j f g z γ d Qsnd Qiso)).1 ≅
        ({ fst := d, snd := Qsnd, iso := Qiso } : auxCategory x j f g z γ) :=
    CategoricalPullback.mkIso (Iso.refl d)
      (outerOfLeft_fiberToLeftSquareNormalized_iso x j f g z γ d Qsnd Qiso) heAux_w
  have hhom : ((auxOver x j f g z γ).p).map eAux.hom = 𝟙 d := by
    change (Iso.refl d).hom = 𝟙 d
    simp
  have hinv : ((auxOver x j f g z γ).p).map eAux.inv = 𝟙 d := by
    change (Iso.refl d).inv = 𝟙 d
    simp
  letI : ((auxOver x j f g z γ).p).IsHomLift (𝟙 d) eAux.hom :=
    IsHomLift.of_fac' ((auxOver x j f g z γ).p) (𝟙 d) eAux.hom rfl rfl (by simpa using hhom)
  letI : ((auxOver x j f g z γ).p).IsHomLift (𝟙 d) eAux.inv :=
    IsHomLift.of_fac' ((auxOver x j f g z γ).p) (𝟙 d) eAux.inv rfl rfl (by simpa using hinv)
  -- Then lift that auxiliary isomorphism into the fiber over `d`.
  refine
    { hom := Functor.Fiber.homMk ((auxOver x j f g z γ).p) d eAux.hom
      inv := Functor.Fiber.homMk ((auxOver x j f g z γ).p) d eAux.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact eAux.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact eAux.inv_hom_id }

/-- The canonical comparison functor from the dotted arrows of the left square to the fiber of
`D'' ⥤ D'` over a fixed middle dotted arrow. -/
theorem leftToAuxFiber_isEquivalence
    (d : DottedArrow middleSq) :
    (leftToAuxFiber x j f g z γ d).IsEquivalence := by
  -- Route correction: instead of packaging a full unit/counit naturality proof, it is enough
  -- here to prove that the fiberwise comparison is faithful, full, and essentially surjective.
  refine Functor.IsEquivalence.mk ?_ ?_ ?_
  · -- Faithfulness follows because the functor records the ambient right `2`-morphism literally.
    refine Functor.Faithful.mk ?_
    intro A B θ η hθη
    apply DottedArrow.Hom.ext
    have hright :
        (leftToAuxFiberMap x j f g z γ d θ).1.snd.right =
          (leftToAuxFiberMap x j f g z γ d η).1.snd.right := by
      simpa using congrArg (fun κ ↦ κ.1.snd.right) hθη
    simpa [leftToAuxFiberMap, leftToAuxFiberRawHom, outerOfLeft_map_right] using hright
  · -- Fullness is obtained by reconstructing the left-square morphism from the outer component of
    -- any morphism in the fiber over `d`.
    refine Functor.Full.mk ?_
    intro A B φ
    refine ⟨normalized_fiber_morphism_to_left_square_hom x j f g z γ d
        (middleOfOuter_of_left_iso x j f g z γ d A)
        (middleOfOuter_of_left_iso x j f g z γ d B) φ, ?_⟩
    apply Functor.Fiber.hom_ext
    apply CategoricalPullback.hom_ext
    · -- The first pullback component of a fiber morphism is forced to be `𝟙 d`.
      change 𝟙 d = φ.1.fst
      symm
      exact normalized_fiber_morphism_fst_eq_id x j f g z γ d
        (middleOfOuter_of_left_iso x j f g z γ d A)
        (middleOfOuter_of_left_iso x j f g z γ d B) φ
    · -- The second pullback component is recovered from the same ambient right `2`-morphism.
      apply DottedArrow.Hom.ext
      change
        (normalized_fiber_morphism_to_left_square_hom x j f g z γ d
          (middleOfOuter_of_left_iso x j f g z γ d A)
          (middleOfOuter_of_left_iso x j f g z γ d B) φ).right =
          φ.1.snd.right
      rfl
  · -- Every object in the fiber over `d` is represented by the reconstructed left-square dotted
    -- arrow associated to its normalized outer component.
    refine Functor.EssSurj.mk ?_
    intro P
    -- Normalize `P` to the literal pullback object over `d`; the previously constructed counit
    -- iso then gives the essential-surjectivity witness directly.
    cases P with
    | mk Q hQ =>
        cases Q with
        | mk fst snd iso =>
            cases hQ
            refine ⟨fiberToLeftSquareNormalized x j f g z γ fst snd iso, ?_⟩
            exact ⟨fiber_counit_normalized x j f g z γ fst snd iso⟩

/-- Lemma 4.44.3, fiberwise form: the fiber of `D'' ⥤ D'` over a middle dotted arrow is
canonically equivalent to the dotted-arrow category of the corresponding left square. -/
noncomputable def auxFiberEquivLeftSquare
    (d : DottedArrow middleSq) :
    ((auxOver x j f g z γ).p).Fiber d ≌ DottedArrow (leftSquare x j f g z γ d) :=
  let H := leftToAuxFiber x j f g z γ d
  letI : H.IsEquivalence := leftToAuxFiber_isEquivalence x j f g z γ d
  H.asEquivalence.symm

end DottedArrowComposition

-- Proof sketch: the explicit auxiliary category `D''` above is the one constructed in the
-- textbook proof, now expressed canonically as a categorical pullback in `Hom(T, Y)`. Its
-- projection to the middle dotted-arrow category is fibred in groupoids, the functor from outer
-- dotted arrows is the canonical pullback comparison `a ↦ (middle(a), a, 𝟙)`, and the fiber over
-- a fixed middle dotted arrow is the left-square dotted-arrow category corresponding to that
-- middle object.
/- Lemma 4.44.3: for a `2`-commutative rectangle in a `(2,1)`-category with chosen
`2`-isomorphism `γ : j ≫ z ≅ x ≫ f ≫ g`, the source-facing intermediate category `D'` is the
dotted-arrow category of the direct middle square
`DottedArrowComposition.middleSquare x j f g z γ : BicategoricalTwoCommutativeSquare z g`, and
the auxiliary category `D''` is `DottedArrowComposition.auxOver x j f g z γ`. Its projection to
`D'` is fibred in groupoids by construction, the canonical comparison functor from outer dotted
arrows is `DottedArrowComposition.auxFromOuter x j f g z γ`, and for each middle dotted arrow
`d : DottedArrow (DottedArrowComposition.middleSquare x j f g z γ)` the fiber of `D'' ⥤ D'` over
`d` is canonically equivalent to the dotted-arrow category of the corresponding left square via
`DottedArrowComposition.auxFiberEquivLeftSquare x j f g z γ d`. -/

end CompositionAux

end CategoryTheory
