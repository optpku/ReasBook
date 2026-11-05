module

public import stacks_project.Chap04.Definition_4_44_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

/- Domain-style sampling for Lemma 4.44.2:
- primary domain: dotted-arrow categories attached to bicategorical `2`-commutative squares;
- owner abstractions inspected: `BicategoricalTwoCommutativeSquare`, `Bicategory.IsFinal`,
  `LeftLift.whiskering`, and `DottedArrow.postcomposeFunctor`;
- source/core/bridge triage:
  `source-facing`: postcomposition on dotted-arrow categories along a right square,
  `core/canonical`: `Functor.IsEquivalence (DottedArrow.postcomposeFunctor S φ)` under the
  owner hypothesis that the right square is bicategorically final,
  `bridge/view`: the underlying `LeftLift` whiskering picture from which dotted arrows are the
  source-facing refinement;
- primitive data: a source square `S : BicategoricalTwoCommutativeSquare y p` and a right-square
  comparison `φ : p ≫ g ≅ q ≫ f`;
- derived API: the outer square `S.postcompose φ`, the induced functor
  `DottedArrow.postcomposeFunctor S φ`, and its equivalence property under
  `[Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]`. -/

namespace DottedArrow

section

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable (S : BicategoricalTwoCommutativeSquare y p)
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}

/-- Helper for Lemma 4.44.2: an outer dotted arrow determines the canonical triangle square over
`f` and `y ≫ g`. -/
private noncomputable abbrev outer_triangle_square
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow (S.postcompose φ)) :
    BicategoricalTwoCommutativeSquare f (y ≫ g) :=
  { obj := T
    p := A.arrow
    q := 𝟙 T
    ψ := A.right.symm ≪≫ (λ_ (y ≫ g)).symm }

/-- Helper for Lemma 4.44.2: the dotted-arrow compatibility for an outer object is exactly the
square-morphism compatibility for the canonical map from the fixed outer square to its associated
triangle square. -/
private theorem source_to_outer_triangle_comm
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow (S.postcompose φ)) :
    (A.left.hom ▷ f) ≫ ((S.postcompose φ).symm).ψ.hom =
      (α_ S.p A.arrow f).hom ≫
        S.p ◁ (outer_triangle_square S φ A).ψ.hom ≫
          (α_ S.p (𝟙 T) (y ≫ g)).inv ≫
            ((ρ_ S.p).hom ▷ (y ≫ g)) := by
  -- The outer dotted-arrow coherence is already the required square-morphism identity after
  -- rewriting the target triangle square with the right unitor on `S.p`.
  have h :
      A.left.inv ▷ f ≫ (α_ S.p A.arrow f).hom ≫ S.p ◁ A.right.inv =
        ((S.postcompose φ).symm).ψ.hom := by
    simpa [Category.assoc] using congrArg
      (fun I : S.p ≫ y ≫ g ≅ (S.postcompose φ).q ≫ f => I.symm.hom)
      A.comm
  rw [← h]
  simp [outer_triangle_square, Category.assoc]
  rfl

/-- Helper for Lemma 4.44.2: every outer dotted arrow yields the canonical square morphism from
the fixed outer source square to its associated triangle square. -/
private noncomputable def source_to_outer_triangle
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow (S.postcompose φ)) :
    (S.postcompose φ).symm ⟶ outer_triangle_square S φ A :=
  { hom := S.p
    left := A.left.hom
    right := (ρ_ S.p).hom
    comm := source_to_outer_triangle_comm S φ A }

/-- Helper for Lemma 4.44.2: an outer dotted arrow determines the square over the right-hand
cospan `f, g` whose lower edge is the original map `y`. -/
private noncomputable abbrev outer_dotted_arrow_square
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow (S.postcompose φ)) :
    BicategoricalTwoCommutativeSquare f g :=
  { obj := T
    p := A.arrow
    q := y
    ψ := A.right.symm }

/-- Helper for Lemma 4.44.2: a morphism of outer dotted arrows induces the corresponding morphism
of the associated right-hand squares. -/
private noncomputable def outer_dotted_arrow_square_hom
    (φ : p ≫ g ≅ q ≫ f)
    {A B : DottedArrow (S.postcompose φ)}
    (θ : A ⟶ B) :
    outer_dotted_arrow_square S φ B ⟶ outer_dotted_arrow_square S φ A :=
  { hom := 𝟙 T
    left := (λ_ A.arrow).hom ≫ θ.right
    right := (λ_ y).hom
    comm := by
      -- The square compatibility is the inverse form of the dotted-arrow lower-right
      -- compatibility, after the identity apex-map coherence collapses.
      simp [outer_dotted_arrow_square, Category.assoc]
      -- Postcompose `Hom.right_comm θ` with the inverse target comparison, then cancel the
      -- source comparison on the left.
      exact
        (cancel_epi A.right.hom).1 <| by
          calc
            A.right.hom ≫ θ.right ▷ f ≫ B.right.inv = B.right.hom ≫ B.right.inv := by
              simpa [Category.assoc] using
                congrArg (fun k => k ≫ B.right.inv) (Hom.right_comm θ)
            _ = A.right.hom ≫ A.right.inv := by
              simpa [DottedArrow.right, Category.assoc] }

/-- Helper for Lemma 4.44.2: finality of the right square supplies the canonical comparison from
the square encoded by an outer dotted arrow to the chosen `2`-cartesian square. -/
private noncomputable abbrev outer_dotted_arrow_terminal_hom
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    outer_dotted_arrow_square S φ A ⟶
      (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g) :=
  ⊤_ _

/-- Helper for Lemma 4.44.2: as soon as the terminal square morphism has invertible lower-right
component, it already determines the candidate left lift over `p` and `y`. -/
private noncomputable def outer_dotted_arrow_terminal_toLeftLift_of_right_isIso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ))
    [IsIso ((outer_dotted_arrow_terminal_hom S φ A).right)] :
    LeftLift p y :=
  LeftLift.mk (outer_dotted_arrow_terminal_hom S φ A).hom
    (inv ((outer_dotted_arrow_terminal_hom S φ A).right))

/-- Helper for Lemma 4.44.2: under the same invertibility hypothesis, the induced unit of the
reconstructed left lift is invertible. -/
private theorem outer_dotted_arrow_terminal_toLeftLift_of_right_isIso_unit_isIso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ))
    [IsIso ((outer_dotted_arrow_terminal_hom S φ A).right)] :
    IsIso (outer_dotted_arrow_terminal_toLeftLift_of_right_isIso S φ A).unit := by
  -- The reconstructed unit is definitionally the inverse of the terminal morphism's right
  -- component.
  change IsIso (inv ((outer_dotted_arrow_terminal_hom S φ A).right))
  infer_instance

/-- Helper for Lemma 4.44.2: in a `(2,1)`-category, the lower-right comparison extracted from the
terminal square morphism is automatically invertible. -/
private theorem outer_dotted_arrow_terminal_right_isIso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    IsIso ((outer_dotted_arrow_terminal_hom S φ A).right) := by
  -- The missing `(2,1)` input is exactly what upgrades the terminal square morphism into
  -- dotted-arrow data on the right triangle.
  infer_instance

/-- Helper for Lemma 4.44.2: in a `(2,1)`-category, the upper-left comparison extracted from the
terminal square morphism is also automatically invertible. -/
private theorem outer_dotted_arrow_terminal_left_isIso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    IsIso ((outer_dotted_arrow_terminal_hom S φ A).left) := by
  -- The same local-groupoid hypothesis turns the left comparison into an isomorphism.
  infer_instance

/-- Helper for Lemma 4.44.2: in a `(2,1)`-category, the terminal square morphism attached to an
outer dotted arrow already determines the lower-right left-lift data of the desired preimage
dotted arrow. -/
private noncomputable def outer_dotted_arrow_terminal_toLeftLift
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    LeftLift p y :=
  let _ : IsIso ((outer_dotted_arrow_terminal_hom S φ A).right) :=
    outer_dotted_arrow_terminal_right_isIso S φ A
  -- The `(2,1)` input is only used to invert the terminal lower-right comparison.
  outer_dotted_arrow_terminal_toLeftLift_of_right_isIso S φ A

/-- Helper for Lemma 4.44.2: the lower-right comparison recovered from the terminal square
morphism is invertible, so the constructed left lift satisfies the dotted-arrow unit condition. -/
private theorem outer_dotted_arrow_terminal_toLeftLift_unit_isIso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    IsIso (outer_dotted_arrow_terminal_toLeftLift S φ A).unit := by
  let _ : IsIso ((outer_dotted_arrow_terminal_hom S φ A).right) :=
    outer_dotted_arrow_terminal_right_isIso S φ A
  -- The local-groupoid hypothesis is only used through the isolated right-component inversion.
  simpa [outer_dotted_arrow_terminal_toLeftLift] using
    outer_dotted_arrow_terminal_toLeftLift_of_right_isIso_unit_isIso S φ A

/-- Helper for Lemma 4.44.2: the source-facing lower-right comparison for the reconstructed
preimage left lift is the inverse of the terminal square morphism's right component. -/
private noncomputable def outer_dotted_arrow_terminal_rightIso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    y ≅ (outer_dotted_arrow_terminal_toLeftLift S φ A).lift ≫ p :=
  asIso (inv ((outer_dotted_arrow_terminal_hom S φ A).right))

/-- Helper for Lemma 4.44.2: the hom part of the reconstructed lower-right comparison is exactly
the inverse of the terminal square morphism's right component. -/
@[simp] private theorem outer_dotted_arrow_terminal_rightIso_hom
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    (outer_dotted_arrow_terminal_rightIso S φ A).hom =
      inv ((outer_dotted_arrow_terminal_hom S φ A).right) := by
  -- The comparison is defined by applying `asIso` to the inverse right component.
  rfl

/-- Helper for Lemma 4.44.2: in a `(2,1)`-category, the upper-left comparison extracted from the
terminal square morphism is an explicit isomorphism from the reconstructed lift, after
postcomposition by `q`, to the original outer dotted-arrow lift. -/
private noncomputable def outer_dotted_arrow_terminal_leftIso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    (outer_dotted_arrow_terminal_toLeftLift S φ A).lift ≫ q ≅ A.arrow :=
  asIso ((outer_dotted_arrow_terminal_hom S φ A).left)

/-- Helper for Lemma 4.44.2: the hom part of the reconstructed upper-left comparison is exactly
the left component of the terminal square morphism. -/
@[simp] private theorem outer_dotted_arrow_terminal_leftIso_hom
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    (outer_dotted_arrow_terminal_leftIso S φ A).hom =
      (outer_dotted_arrow_terminal_hom S φ A).left := by
  -- The comparison is defined by applying `asIso` to the terminal left component.
  rfl

/-- Helper for Lemma 4.44.2: after postcomposing by `q`, the upper-left comparison for the
reconstructed preimage is already determined by the terminal square morphism and the given outer
dotted-arrow comparison. -/
private noncomputable def outer_dotted_arrow_terminal_left_whiskeredIso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    S.p ≫ (outer_dotted_arrow_terminal_toLeftLift S φ A).lift ≫ q ≅ S.q ≫ q :=
  -- The terminal left comparison lands in `A.arrow`, and the existing upper-left dotted-arrow
  -- isomorphism for `A` finishes the `q`-whiskered comparison.
  whiskerLeftIso S.p (outer_dotted_arrow_terminal_leftIso S φ A) ≪≫ A.left

/-- Helper for Lemma 4.44.2: the `q`-whiskered upper-left comparison recovered from the terminal
square morphism has the expected explicit source-facing form. -/
@[simp] private theorem outer_dotted_arrow_terminal_left_whiskeredIso_hom
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    (outer_dotted_arrow_terminal_left_whiskeredIso S φ A).hom =
      S.p ◁ (outer_dotted_arrow_terminal_hom S φ A).left ≫ A.left.hom := by
  -- Unfold the composite of the whiskered terminal comparison with the original upper-left
  -- comparison; only the two explicit source-facing morphisms remain.
  rfl

/-- Helper for Lemma 4.44.2: the owner square over `f, g` obtained by composing the source square
with the right square has apex `S.obj`, left leg `S.q ≫ q`, and right leg `S.p ≫ y`. -/
private noncomputable def outer_dotted_arrow_owner_square
    (φ : p ≫ g ≅ q ≫ f) :
    BicategoricalTwoCommutativeSquare f g :=
  { obj := S.obj
    p := S.q ≫ q
    q := S.p ≫ y
    ψ := (S.postcompose φ).ψ.symm ≪≫ (α_ S.p y g).symm }

/-- Helper for Lemma 4.44.2: the owner square maps to the outer square by transporting the
source-to-outer compatibility through the final associator shell. -/
private theorem outer_dotted_arrow_owner_to_outer_square_comm
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow (S.postcompose φ)) :
    (A.left.hom ▷ f) ≫ (outer_dotted_arrow_owner_square S φ).ψ.hom =
      (α_ S.p (outer_dotted_arrow_square S φ A).p f).hom ≫
        S.p ◁ (outer_dotted_arrow_square S φ A).ψ.hom ≫
          (α_ S.p (outer_dotted_arrow_square S φ A).q g).inv ≫ 𝟙 (S.p ≫ y) ▷ g := by
  -- Transport the already-normalized source-to-outer triangle comparison through the final
  -- associator shell defining the owner square.
  simp only [outer_dotted_arrow_owner_square, outer_dotted_arrow_square, Category.assoc]
  have h :
      (A.left.hom ▷ f) ≫ ((S.postcompose φ).symm).ψ.hom =
        (α_ S.p A.arrow f).hom ≫ S.p ◁ A.right.inv := by
    simpa [outer_triangle_square, Category.assoc] using
      source_to_outer_triangle_comm (S := S) φ A
  have h' :
      (A.left.hom ▷ f ≫ ((S.postcompose φ).symm).ψ.hom) ≫ (α_ S.p y g).inv =
        ((α_ S.p A.arrow f).hom ≫ S.p ◁ A.right.inv) ≫ (α_ S.p y g).inv := by
    rw [h]
    rfl
  simpa [Category.assoc] using h'

/-- Helper for Lemma 4.44.2: the original upper-left comparison and the trivial right leg together
assemble the canonical square morphism from the owner square to the outer square of `A`. -/
private noncomputable def outer_dotted_arrow_owner_to_outer_square
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow (S.postcompose φ)) :
    outer_dotted_arrow_owner_square S φ ⟶ outer_dotted_arrow_square S φ A :=
  { hom := S.p
    left := A.left.hom
    right := 𝟙 (S.p ≫ y)
    comm := outer_dotted_arrow_owner_to_outer_square_comm (S := S) φ A }

/-- Helper for Lemma 4.44.2: the source square itself gives the comparison morphism from the owner
square to the chosen final right square. -/
private noncomputable def outer_dotted_arrow_owner_terminal_source_hom
    (φ : p ≫ g ≅ q ≫ f) :
    outer_dotted_arrow_owner_square S φ ⟶
      (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g) :=
  { hom := S.q
    left := 𝟙 (S.q ≫ q)
    right := S.ψ.inv
    comm := by
      -- Expanding the owner square shows that this is the defining outer-rectangle shell of
      -- `S.postcompose φ`, written in the source-facing direction.
      calc
        𝟙 (S.q ≫ q) ▷ f ≫ (outer_dotted_arrow_owner_square S φ).ψ.hom =
            𝟙 ((S.q ≫ q) ≫ f) ≫
              ((α_ S.q q f).hom ≫ S.q ◁ φ.inv ≫ (α_ S.q p g).inv ≫ S.ψ.inv ▷ g) := by
                simp [outer_dotted_arrow_owner_square, BicategoricalTwoCommutativeSquare.postcompose,
                  Category.assoc]
        _ =
            (α_ S.q q f).hom ≫ S.q ◁ φ.inv ≫ (α_ S.q p g).inv ≫ S.ψ.inv ▷ g := by
              simp [Category.assoc] }

/-- Helper for Lemma 4.44.2: uniqueness of the map from the owner square to the final square
produces the owner-level upper-left comparison from the reconstructed terminal lift to `S`. -/
private noncomputable def outer_dotted_arrow_owner_descent_hom
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    S.p ≫ (outer_dotted_arrow_terminal_toLeftLift S φ A).lift ⟶ S.q := by
  let leftHom :=
    outer_dotted_arrow_owner_to_outer_square S φ A ≫ outer_dotted_arrow_terminal_hom S φ A
  let rightHom := outer_dotted_arrow_owner_terminal_source_hom (S := S) φ
  let _ : Unique (leftHom ⟶ rightHom) := inferInstance
  -- The unique `TwoHom` into the final square is the owner-level comparison we need.
  exact (default : leftHom ⟶ rightHom).hom

/-- Helper for Lemma 4.44.2: the owner-level comparison coming from the terminal square has the
expected `q`-whiskered form on the upper-left leg. -/
private theorem outer_dotted_arrow_owner_descent_hom_whisker_q
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    outer_dotted_arrow_owner_descent_hom (S := S) φ A ▷ q ≫
        𝟙 (S.q ≫ q) =
      (α_ S.p (outer_dotted_arrow_terminal_hom S φ A).hom q).hom ≫
        S.p ◁ (outer_dotted_arrow_terminal_hom S φ A).left ≫
          A.left.hom := by
  let leftHom :=
    outer_dotted_arrow_owner_to_outer_square S φ A ≫ outer_dotted_arrow_terminal_hom S φ A
  let rightHom := outer_dotted_arrow_owner_terminal_source_hom (S := S) φ
  let _ : Unique (leftHom ⟶ rightHom) := inferInstance
  let τ : leftHom ⟶ rightHom := default
  -- The upper-left owner comparison is the left component of the unique square `TwoHom`.
  change τ.hom ▷ q ≫ 𝟙 (S.q ≫ q) =
      (α_ S.p (outer_dotted_arrow_terminal_hom S φ A).hom q).hom ≫
        S.p ◁ (outer_dotted_arrow_terminal_hom S φ A).left ≫ A.left.hom
  simpa [leftHom, rightHom, outer_dotted_arrow_owner_terminal_source_hom,
    outer_dotted_arrow_owner_to_outer_square, outer_dotted_arrow_owner_to_outer_square_comm,
    outer_dotted_arrow_owner_descent_hom,
    Category.assoc] using τ.left_comm

/-- Helper for Lemma 4.44.2: the same owner-level comparison also satisfies the lower-right
compatibility needed by `DottedArrow.comparisonIsoMk`. -/
private theorem outer_dotted_arrow_owner_descent_hom_whisker_p
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    outer_dotted_arrow_owner_descent_hom (S := S) φ A ▷ p ≫ S.ψ.inv =
      (α_ S.p (outer_dotted_arrow_terminal_hom S φ A).hom p).hom ≫
        S.p ◁ (outer_dotted_arrow_terminal_hom S φ A).right ≫
          𝟙 (S.p ≫ y) := by
  let leftHom :=
    outer_dotted_arrow_owner_to_outer_square S φ A ≫ outer_dotted_arrow_terminal_hom S φ A
  let rightHom := outer_dotted_arrow_owner_terminal_source_hom (S := S) φ
  let _ : Unique (leftHom ⟶ rightHom) := inferInstance
  let τ : leftHom ⟶ rightHom := default
  -- The lower-right owner comparison is the right component of the same unique square `TwoHom`.
  change τ.hom ▷ p ≫ (outer_dotted_arrow_owner_terminal_source_hom (S := S) φ).right =
      (outer_dotted_arrow_owner_to_outer_square S φ A ≫ outer_dotted_arrow_terminal_hom S φ A).right
  simpa [leftHom, rightHom, outer_dotted_arrow_owner_terminal_source_hom,
    outer_dotted_arrow_owner_to_outer_square, outer_dotted_arrow_owner_to_outer_square_comm,
    outer_dotted_arrow_owner_descent_hom,
    Category.assoc] using τ.right_comm

/-- Helper for Lemma 4.44.2: a left lift with invertible unit and an owner-level whiskered
comparison packages directly into a dotted arrow. -/
private noncomputable def dotted_arrow_of_whiskered_comparison
    (t : LeftLift p y) [IsIso t.unit]
    (comparison : (LeftLift.whiskering S.p).obj t ≅ S.symm.toLeftLift) :
    DottedArrow S :=
  { toLeftLift := t
    unit_isIso := inferInstance
    comparison := comparison }

/-- Helper for Lemma 4.44.2: once the terminally reconstructed left lift carries the correct
owner-level whiskered comparison, it packages into the desired preimage dotted arrow. -/
private noncomputable def outer_dotted_arrow_preimage
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ))
    (comparison :
      (LeftLift.whiskering S.p).obj (outer_dotted_arrow_terminal_toLeftLift S φ A) ≅
        S.symm.toLeftLift) :
    DottedArrow S :=
  let t := outer_dotted_arrow_terminal_toLeftLift S φ A
  let _ : IsIso t.unit := outer_dotted_arrow_terminal_toLeftLift_unit_isIso S φ A
  -- Route correction: the genuine source-facing datum is the whiskered owner comparison itself,
  -- not an artificially unwhiskered `S.p ≫ lift ≅ S.q`.
  dotted_arrow_of_whiskered_comparison (S := S) t comparison

/-- Helper for Lemma 4.44.2: once every outer dotted arrow is isomorphic to the postcomposition of
some source dotted arrow, the postcomposition functor is essentially surjective. -/
private theorem postcomposeFunctor_essSurj_of_objectwise_preimage
    (φ : p ≫ g ≅ q ≫ f)
    (hpre :
      ∀ A : DottedArrow (S.postcompose φ),
        ∃ A' : DottedArrow S, Nonempty (postcompose φ A' ≅ A)) :
    (postcomposeFunctor S φ).EssSurj := by
  refine ⟨fun A ↦ ?_⟩
  -- The assumed objectwise preimage data is exactly the essential-image witness.
  rcases hpre A with ⟨A', hA'⟩
  exact ⟨A', hA'⟩

/-- Helper for Lemma 4.44.2: full faithfulness together with explicit objectwise preimages already
packages the postcomposition functor into an equivalence. -/
private theorem postcomposeFunctor_isEquivalence_of_data
    (φ : p ≫ g ≅ q ≫ f)
    [Functor.Full (postcomposeFunctor S φ)]
    [Functor.Faithful (postcomposeFunctor S φ)]
    (hpre :
      ∀ A : DottedArrow (S.postcompose φ),
        ∃ A' : DottedArrow S, Nonempty (postcompose φ A' ≅ A)) :
    (postcomposeFunctor S φ).IsEquivalence := by
  let _ : (postcomposeFunctor S φ).EssSurj :=
    postcomposeFunctor_essSurj_of_objectwise_preimage (S := S) φ hpre
  -- Once full faithfulness and essential surjectivity are available, the standard equivalence
  -- constructor applies.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- Helper for Lemma 4.44.2: the terminal square comparison on an outer dotted arrow is the
owner-level whiskered comparison required to reconstruct a source dotted arrow. -/
private noncomputable def outer_dotted_arrow_terminal_comparison
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    (LeftLift.whiskering S.p).obj (outer_dotted_arrow_terminal_toLeftLift S φ A) ≅
      S.symm.toLeftLift := by
  -- Package the owner-level comparison extracted from the unique square `TwoHom` into the
  -- source-facing dotted-arrow comparison isomorphism.
  refine
    DottedArrow.comparisonIsoMk (sq := S)
      (t := outer_dotted_arrow_terminal_toLeftLift S φ A)
      (asIso (outer_dotted_arrow_owner_descent_hom (S := S) φ A)) ?_
  have h :
      outer_dotted_arrow_owner_descent_hom (S := S) φ A ▷ p ≫ S.ψ.inv =
        (α_ S.p (outer_dotted_arrow_terminal_hom S φ A).hom p).hom ≫
          S.p ◁ (outer_dotted_arrow_terminal_hom S φ A).right := by
    simpa [Category.assoc] using outer_dotted_arrow_owner_descent_hom_whisker_p (S := S) φ A
  -- Postcompose the desired owner comparison by `S.ψ.inv`, rewrite with the descended
  -- lower-right compatibility, and cancel the explicit shell.
  apply (cancel_mono S.ψ.inv).1
  simpa [outer_dotted_arrow_terminal_toLeftLift,
    outer_dotted_arrow_terminal_toLeftLift_of_right_isIso, Category.assoc] using
    congrArg
      (fun k ↦
        S.p ◁ inv ((outer_dotted_arrow_terminal_hom S φ A).right) ≫
          (α_ S.p (outer_dotted_arrow_terminal_hom S φ A).hom p).inv ≫ k)
      h

/-- Helper for Lemma 4.44.2: the terminally reconstructed source dotted arrow maps back to the
given outer dotted arrow after postcomposition. -/
private theorem outer_dotted_arrow_postcompose_lower_right_cancel
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    (postcompose φ
        (outer_dotted_arrow_preimage S φ A
          (outer_dotted_arrow_terminal_comparison S φ A))).toLeftLift.unit ≫
      (outer_dotted_arrow_terminal_leftIso S φ A).hom ▷ f =
    A.toLeftLift.unit := by
  have hcomm :
      (outer_dotted_arrow_terminal_leftIso S φ A).hom ▷ f ≫ A.right.inv =
        (α_ (outer_dotted_arrow_terminal_hom S φ A).hom q f).hom ≫
          (outer_dotted_arrow_terminal_hom S φ A).hom ◁ φ.inv ≫
            (α_ (outer_dotted_arrow_terminal_hom S φ A).hom p g).inv ≫
              (outer_dotted_arrow_terminal_hom S φ A).right ▷ g := by
    -- The terminal square commutativity is exactly the missing lower-right shell.
    simpa [outer_dotted_arrow_terminal_leftIso_hom, outer_dotted_arrow_square, Category.assoc] using
      (outer_dotted_arrow_terminal_hom S φ A).comm
  let shell :=
    inv ((outer_dotted_arrow_terminal_hom S φ A).right) ▷ g ≫
      (α_ (outer_dotted_arrow_terminal_hom S φ A).hom p g).hom ≫
        (outer_dotted_arrow_terminal_hom S φ A).hom ◁ φ.hom ≫
          (α_ (outer_dotted_arrow_terminal_hom S φ A).hom q f).inv
  have hunit :
      (postcompose φ
          (outer_dotted_arrow_preimage S φ A
            (outer_dotted_arrow_terminal_comparison S φ A))).toLeftLift.unit = shell := by
    change
      inv ((outer_dotted_arrow_terminal_hom S φ A).right) ▷ g ≫
          (α_ (outer_dotted_arrow_terminal_hom S φ A).hom p g).hom ≫
            (outer_dotted_arrow_terminal_hom S φ A).hom ◁ φ.hom ≫
              (α_ (outer_dotted_arrow_terminal_hom S φ A).hom q f).inv = shell
    rfl
  apply (cancel_mono A.right.inv).1
  change
    ((postcompose φ
          (outer_dotted_arrow_preimage S φ A
            (outer_dotted_arrow_terminal_comparison S φ A))).toLeftLift.unit ≫
        (outer_dotted_arrow_terminal_leftIso S φ A).hom ▷ f) ≫ A.right.inv =
      A.toLeftLift.unit ≫ A.right.inv
  calc
    ((postcompose φ
          (outer_dotted_arrow_preimage S φ A
            (outer_dotted_arrow_terminal_comparison S φ A))).toLeftLift.unit ≫
        (outer_dotted_arrow_terminal_leftIso S φ A).hom ▷ f) ≫ A.right.inv =
      shell ≫ ((outer_dotted_arrow_terminal_leftIso S φ A).hom ▷ f ≫ A.right.inv) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ (outer_dotted_arrow_terminal_leftIso S φ A).hom ▷ f ≫ A.right.inv)
              hunit
    _ =
      shell ≫
        ((α_ (outer_dotted_arrow_terminal_hom S φ A).hom q f).hom ≫
            (outer_dotted_arrow_terminal_hom S φ A).hom ◁ φ.inv ≫
              (α_ (outer_dotted_arrow_terminal_hom S φ A).hom p g).inv ≫
                (outer_dotted_arrow_terminal_hom S φ A).right ▷ g) := by
          simpa [shell, Category.assoc] using
            congrArg (fun k ↦ shell ≫ k) hcomm
    _ = A.toLeftLift.unit ≫ A.right.inv := by
          simp [shell, DottedArrow.right, Category.assoc]

/-- Helper for Lemma 4.44.2: the terminally reconstructed source dotted arrow maps back to the
given outer dotted arrow after postcomposition. -/
private theorem outer_dotted_arrow_postcompose_iso
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow (S.postcompose φ)) :
    Nonempty
      (postcompose φ
          (outer_dotted_arrow_preimage S φ A
            (outer_dotted_arrow_terminal_comparison S φ A)) ≅
        A) := by
  classical
  -- The ambient component of the desired isomorphism is the terminal upper-left comparison.
  refine ⟨asIso ⟨LeftLift.homMk (outer_dotted_arrow_terminal_leftIso (S := S) φ A).hom ?_, ?_⟩⟩
  · -- The remaining lower-right condition is exactly the shell cancellation isolated above.
    simpa using outer_dotted_arrow_postcompose_lower_right_cancel (S := S) φ A
  · -- The upper-left comparison is exactly the owner descent, whiskered by `q` and normalized by
    -- the associator shell of `postcompose`.
    apply StructuredArrow.hom_ext
    change S.p ◁ (outer_dotted_arrow_terminal_hom S φ A).left ≫ A.left.hom =
      (α_ S.p (outer_dotted_arrow_terminal_hom S φ A).hom q).inv ≫
        (outer_dotted_arrow_owner_descent_hom (S := S) φ A ▷ q)
    have h := outer_dotted_arrow_owner_descent_hom_whisker_q (S := S) φ A
    exact Eq.symm <| by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ (α_ S.p (outer_dotted_arrow_terminal_hom S φ A).hom q).inv ≫ k)
          h

/-- Helper for Lemma 4.44.2: a source dotted arrow already defines an explicit morphism from its
postcomposed outer square to the chosen right square. -/
private noncomputable def postcompose_source_square_hom
    (φ : p ≫ g ≅ q ≫ f)
    (A : DottedArrow S) :
    outer_dotted_arrow_square S φ (postcompose φ A) ⟶
      (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g) :=
  { hom := A.arrow
    left := 𝟙 (A.arrow ≫ q)
    right := A.right.inv
    comm := by
      -- The square identity is exactly the inverse form of the postcomposition lower-right
      -- comparison.
      have h_inv : (postcompose φ A).right.inv =
        (α_ A.arrow q f).hom ≫ A.arrow ◁ φ.inv ≫
          (α_ A.arrow p g).inv ≫ A.right.inv ▷ g := by
        apply IsIso.inv_eq_of_hom_inv_id
        rw [show (postcompose φ A).toLeftLift.unit =
            A.right.hom ▷ g ≫ (α_ A.arrow p g).hom ≫
              A.arrow ◁ φ.hom ≫ (α_ A.arrow q f).inv by
          rfl]
        calc
          (A.toLeftLift.unit ▷ g ≫ (α_ A.arrow p g).hom ≫
                A.arrow ◁ φ.hom ≫ (α_ A.arrow q f).inv) ≫
              (α_ A.arrow q f).hom ≫ A.arrow ◁ φ.inv ≫
                (α_ A.arrow p g).inv ≫ A.right.inv ▷ g =
              A.toLeftLift.unit ▷ g ≫ A.right.inv ▷ g := by
                simp [Category.assoc]
          _ = 𝟙 (y ≫ g) := by
                simpa [DottedArrow.right, Category.assoc] using
                  congrArg (fun k => k ▷ g) (Iso.hom_inv_id A.right)
      simp [outer_dotted_arrow_square]
      have hstep₁ :
          𝟙 (A.arrow ≫ q) ▷ f ≫ (postcompose φ A).right.inv =
            𝟙 ((A.arrow ≫ q) ≫ f) ≫ (postcompose φ A).right.inv := by
        simpa [Category.assoc] using
          congrArg (fun k => k ≫ (postcompose φ A).right.inv)
            (Bicategory.id_whiskerRight (A.arrow ≫ q) f)
      have hstep₂ :
          𝟙 ((A.arrow ≫ q) ≫ f) ≫ (postcompose φ A).right.inv =
            (α_ A.arrow q f).hom ≫ A.arrow ◁ φ.inv ≫
              (α_ A.arrow p g).inv ≫ A.right.inv ▷ g := by
        simpa using h_inv
      exact hstep₁.trans hstep₂ }

/-- Helper for Lemma 4.44.2: postcomposition acts on the ambient `2`-morphism component by
whiskering with `q`. -/
private theorem postcomposeFunctor_map_right
    (φ : p ≫ g ≅ q ≫ f)
    {A B : DottedArrow S}
    (η : A ⟶ B) :
    ((postcomposeFunctor S φ).map η).right = η.right ▷ q := by
  -- The functor was defined by whiskering the source ambient `2`-morphism with `q`.
  rfl

/-- Helper for Lemma 4.44.2: composing the square morphism induced by `η` with the canonical
source-square morphism only inserts the expected left-unitor before `η.right`. -/
private theorem outer_dotted_arrow_square_hom_comp_postcompose_source_left
    (φ : p ≫ g ≅ q ≫ f)
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    (outer_dotted_arrow_square_hom S φ η ≫ postcompose_source_square_hom S φ A).left =
      (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ η.right := by
  -- The composite only inserts unitors around `η.right`, so bicategorical coherence collapses it.
  change
    (α_ (𝟙 T) A.arrow q).hom ≫ (𝟙 T ◁ 𝟙 (A.arrow ≫ q)) ≫
        (((λ_ (A.arrow ≫ q)).hom ≫ η.right)) =
      (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ η.right
  simp

/-- Helper for Lemma 4.44.2: the same composite keeps the lower-right component equal to the
inverse lower-right comparison of the source dotted arrow, up to the expected left unitor. -/
private theorem outer_dotted_arrow_square_hom_comp_postcompose_source_right
    (φ : p ≫ g ≅ q ≫ f)
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    (outer_dotted_arrow_square_hom S φ η ≫ postcompose_source_square_hom S φ A).right =
      (α_ (𝟙 T) A.arrow p).hom ≫ (λ_ (A.arrow ≫ p)).hom ≫ A.right.inv := by
  -- The identity apex map in `outer_dotted_arrow_square_hom` means the right leg is unchanged.
  change
    (α_ (𝟙 T) A.arrow p).hom ≫ (𝟙 T ◁ A.right.inv) ≫ (λ_ y).hom =
      (α_ (𝟙 T) A.arrow p).hom ≫ (λ_ (A.arrow ≫ p)).hom ≫ A.right.inv
  simp

/-- Helper for Lemma 4.44.2: terminality of the right square produces the unique `2`-morphism
from the square induced by `η` to the canonical source square morphism of the target. -/
private noncomputable abbrev postcomposeFunctor_terminal_twohom
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    outer_dotted_arrow_square_hom S φ η ≫ postcompose_source_square_hom S φ A ⟶
      postcompose_source_square_hom S φ B := by
  -- Finality identifies the hom-category into the chosen `2`-cartesian square with a singleton.
  let _ :
      Unique
        (outer_dotted_arrow_square_hom S φ η ≫ postcompose_source_square_hom S φ A ⟶
          postcompose_source_square_hom S φ B) := inferInstance
  exact default

/-- Helper for Lemma 4.44.2: the candidate source ambient `2`-cell is the apex `2`-cell of the
terminal comparison, normalized by the left unitor. -/
private noncomputable def postcomposeFunctor_preimage_right
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    A.arrow ⟶ B.arrow :=
  (λ_ A.arrow).inv ≫ (postcomposeFunctor_terminal_twohom (S := S) φ η).hom

/-- Helper for Lemma 4.44.2: the normalized candidate ambient `2`-cell is definitionally the
left-unitor inverse followed by the apex `2`-cell of the terminal comparison. -/
@[simp] private theorem postcomposeFunctor_preimage_right_def
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    postcomposeFunctor_preimage_right (S := S) φ η =
      (λ_ A.arrow).inv ≫ (postcomposeFunctor_terminal_twohom (S := S) φ η).hom := by
  rfl

/-- Helper for Lemma 4.44.2: the left-leg compatibility of the terminal `TwoHom` rewrites to the
explicit source-square normalization formula before the final left-unitor shell is removed. -/
private theorem postcomposeFunctor_terminal_twohom_left_leg
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    (postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q ≫ 𝟙 (B.arrow ≫ q) =
      (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ η.right := by
  let τ := postcomposeFunctor_terminal_twohom (S := S) φ η
  have hτ := τ.left_comm
  -- The target source square has identity left comparison, so `τ.left_comm` already has the
  -- desired source-facing shape once the composite left leg is expanded.
  rw [outer_dotted_arrow_square_hom_comp_postcompose_source_left (S := S) φ η] at hτ
  exact hτ

/-- Helper for Lemma 4.44.2: the right-leg compatibility of the terminal `TwoHom` rewrites to the
explicit source-square normalization formula before the final lower-right cancellation. -/
private theorem postcomposeFunctor_terminal_twohom_right_leg
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    (postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ p ≫ B.right.inv =
      (α_ (𝟙 T) A.arrow p).hom ≫ (λ_ (A.arrow ≫ p)).hom ≫ A.right.inv := by
  let τ := postcomposeFunctor_terminal_twohom (S := S) φ η
  have hτ := τ.right_comm
  -- The target source square keeps the inverse lower-right comparison of `B`, so expanding the
  -- composite right leg exposes the desired normalization formula.
  rw [outer_dotted_arrow_square_hom_comp_postcompose_source_right (S := S) φ η] at hτ
  simpa [postcompose_source_square_hom] using hτ

/-- Helper for Lemma 4.44.2: after canceling the left unitor, the ambient `2`-cell of the
terminal square comparison becomes the given outer morphism after whiskering by `q`. -/
private theorem postcomposeFunctor_preimage_right_whisker_q_expansion
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    postcomposeFunctor_preimage_right (S := S) φ η ▷ q =
      (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫
        ((postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q ≫ 𝟙 (B.arrow ≫ q)) := by
  -- Expand the candidate ambient `2`-cell and then insert the identity target object produced by
  -- the terminal source-square morphism for `B`.
  change (((λ_ A.arrow).inv ≫ (postcomposeFunctor_terminal_twohom (S := S) φ η).hom) ▷ q) = _
  rw [comp_whiskerRight]
  calc
    (λ_ A.arrow).inv ▷ q ≫ (postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q =
        (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫
          (postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q := by
          simp [Category.assoc]
    _ =
      (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫
        (postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q ≫ 𝟙 (B.arrow ≫ q) := by
          exact
            congrArg
              (fun k ↦ (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫ k)
              (Category.comp_id ((postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q)).symm

/-- Helper for Lemma 4.44.2: composing the normalized preimage candidate with the source and
target lower-right comparisons exposes the terminal square's right-leg shell. -/
private theorem postcomposeFunctor_preimage_right_whisker_p_expansion
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    A.right.hom ≫ (postcomposeFunctor_preimage_right (S := S) φ η ▷ p) ≫ B.right.inv =
      A.right.hom ≫ (λ_ (A.arrow ≫ p)).inv ≫ (α_ (𝟙 T) A.arrow p).inv ≫
        ((postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ p ≫ B.right.inv) := by
  -- The same expansion on the right-hand leg exposes the shell governed by the terminal square's
  -- right-leg `TwoHom`.
  change
    A.right.hom ≫
        (((λ_ A.arrow).inv ≫ (postcomposeFunctor_terminal_twohom (S := S) φ η).hom) ▷ p) ≫
          B.right.inv = _
  rw [comp_whiskerRight]
  simp [Category.assoc]
  rfl

/-- Helper for Lemma 4.44.2: after canceling the left unitor, the ambient `2`-cell of the
terminal square comparison becomes the given outer morphism after whiskering by `q`. -/
private theorem postcompose_left_shell_cancel
    {A B : DottedArrow S}
    (β : A.arrow ≫ q ⟶ B.arrow ≫ q) :
    (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫
        ((α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ β) =
      β := by
  -- The exposed associator and left-unitor shell is inverse to itself, so only `β` remains.
  simp

/-- Helper for Lemma 4.44.2: after canceling the left unitor, the ambient `2`-cell of the
terminal square comparison becomes the given outer morphism after whiskering by `q`. -/
private theorem postcomposeFunctor_terminal_twohom_normalized_whisker
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    postcomposeFunctor_preimage_right (S := S) φ η ▷ q = η.right := by
  -- First expose the terminal `TwoHom` shell on the left leg, then rewrite that shell by the
  -- explicit left-leg compatibility of the chosen terminal `TwoHom`.
  let β : A.arrow ≫ q ⟶ B.arrow ≫ q := η.right
  have h₁ :
      postcomposeFunctor_preimage_right (S := S) φ η ▷ q =
        (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫
          ((postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q ≫ 𝟙 (B.arrow ≫ q)) := by
    simpa using postcomposeFunctor_preimage_right_whisker_q_expansion (S := S) φ η
  have hleg :
      (postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q ≫ 𝟙 (B.arrow ≫ q) =
        (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ β := by
    simpa [β] using postcomposeFunctor_terminal_twohom_left_leg (S := S) φ η
  have h₂ :
      (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫
          ((postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ q ≫ 𝟙 (B.arrow ≫ q)) =
        (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫
          ((α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ β) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫ k)
        hleg
  have h₃ :
      (λ_ (A.arrow ≫ q)).inv ≫ (α_ (𝟙 T) A.arrow q).inv ≫
          ((α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ β) =
        η.right := by
    simpa [β] using postcompose_left_shell_cancel (S := S) (A := A) (B := B) β
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 4.44.2: when the target morphism already comes from a source dotted-arrow
morphism, the terminally reconstructed ambient `2`-cell is exactly that source component. -/
private theorem postcomposeFunctor_preimage_right_of_map
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (θ : A ⟶ B) :
    postcomposeFunctor_preimage_right (S := S) φ ((postcomposeFunctor S φ).map θ) = θ.right := by
  -- Route correction: identify the terminal `TwoHom` with the explicit source-side witness before
  -- reading off the normalized ambient `2`-morphism.
  let τExplicit :
      outer_dotted_arrow_square_hom S φ ((postcomposeFunctor S φ).map θ) ≫
          postcompose_source_square_hom S φ A ⟶
        postcompose_source_square_hom S φ B :=
    { hom := (λ_ A.arrow).hom ≫ θ.right
      left_comm := by
        -- The left leg is exactly the whiskered source compatibility of `θ`.
        have hleft_shell :
            ((λ_ A.arrow).hom ≫ θ.right) ▷ q ≫ (postcompose_source_square_hom S φ B).left =
              (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ (θ.right ▷ q) := by
          have h_shell_with_id :
              (λ_ A.arrow).hom ▷ q ≫ θ.right ▷ q ≫ (postcompose_source_square_hom S φ B).left =
                (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ (θ.right ▷ q) ≫
                  𝟙 (B.arrow ≫ q) := by
            have hlu :
                (λ_ A.arrow).hom ▷ q =
                  (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom := by
              simpa [Category.assoc] using
                (congrArg
                  (fun k ↦ (α_ (𝟙 T) A.arrow q).hom ≫ k)
                  (leftUnitor_comp (f := A.arrow) (g := q))).symm
            have hleftB :
                (postcompose_source_square_hom S φ B).left = 𝟙 (B.arrow ≫ q) := by
              rfl
            rw [hlu]
            rw [hleftB]
            rw [Category.assoc]
            rfl
          have h_id :
              (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ (θ.right ▷ q) ≫
                  𝟙 (B.arrow ≫ q) =
                (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ (θ.right ▷ q) := by
            simpa [Category.assoc] using
              Category.comp_id
                ((α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ (θ.right ▷ q))
          calc
            ((λ_ A.arrow).hom ≫ θ.right) ▷ q ≫ (postcompose_source_square_hom S φ B).left =
                (λ_ A.arrow).hom ▷ q ≫ θ.right ▷ q ≫ (postcompose_source_square_hom S φ B).left := by
                    rw [comp_whiskerRight, Category.assoc]
            _ =
                (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ (θ.right ▷ q) ≫
                  𝟙 (B.arrow ≫ q) := h_shell_with_id
            _ =
                (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ (θ.right ▷ q) := h_id
        have hleft_target :
            (outer_dotted_arrow_square_hom S φ ((postcomposeFunctor S φ).map θ) ≫
                postcompose_source_square_hom S φ A).left =
              (α_ (𝟙 T) A.arrow q).hom ≫ (λ_ (A.arrow ≫ q)).hom ≫ (θ.right ▷ q) := by
          simpa [postcomposeFunctor_map_right, Category.assoc] using
            outer_dotted_arrow_square_hom_comp_postcompose_source_left
              (S := S) (φ := φ) (η := (postcomposeFunctor S φ).map θ)
        exact hleft_shell.trans hleft_target.symm
      right_comm := by
        -- The right leg is unchanged by the identity apex map and then reduces to `θ`'s
        -- lower-right compatibility.
        have hθinv :
            θ.right ▷ p ≫ B.right.inv = A.right.inv := by
          have hcomp :
              A.right.hom ≫ (θ.right ▷ p ≫ B.right.inv) = A.right.hom ≫ A.right.inv := by
            calc
              A.right.hom ≫ (θ.right ▷ p ≫ B.right.inv) =
                  (A.right.hom ≫ θ.right ▷ p) ≫ B.right.inv := by
                    simp
              _ = B.right.hom ≫ B.right.inv := by
                    rw [Hom.right_comm θ]
              _ = A.right.hom ≫ A.right.inv := by
                    simp [DottedArrow.right]
          exact (cancel_epi A.right.hom).1 hcomp
        have hright_shell :
            ((λ_ A.arrow).hom ≫ θ.right) ▷ p ≫ (postcompose_source_square_hom S φ B).right =
              (α_ (𝟙 T) A.arrow p).hom ≫ (λ_ (A.arrow ≫ p)).hom ≫ A.right.inv := by
          rw [comp_whiskerRight]
          simp [postcompose_source_square_hom, hθinv, Category.assoc]
        have hright_target :
            (outer_dotted_arrow_square_hom S φ ((postcomposeFunctor S φ).map θ) ≫
                postcompose_source_square_hom S φ A).right =
              (α_ (𝟙 T) A.arrow p).hom ≫ (λ_ (A.arrow ≫ p)).hom ≫ A.right.inv := by
          simpa [postcomposeFunctor_map_right, Category.assoc] using
            outer_dotted_arrow_square_hom_comp_postcompose_source_right
              (S := S) (φ := φ) (η := (postcomposeFunctor S φ).map θ)
        exact hright_shell.trans hright_target.symm }
  let _ :
      Unique
        (outer_dotted_arrow_square_hom S φ ((postcomposeFunctor S φ).map θ) ≫
            postcompose_source_square_hom S φ A ⟶
          postcompose_source_square_hom S φ B) := inferInstance
  have hτ :
      postcomposeFunctor_terminal_twohom (S := S) φ ((postcomposeFunctor S φ).map θ) = τExplicit :=
    Subsingleton.elim _ _
  -- Substitute the explicit witness and cancel the left-unitor shell in the definition.
  simp [postcomposeFunctor_preimage_right, hτ, τExplicit]

/-- Helper for Lemma 4.44.2: the same normalized ambient `2`-cell already satisfies the
lower-right dotted-arrow compatibility before the missing upper-left unwhiskering step. -/
private theorem postcomposeFunctor_terminal_twohom_normalized_right_comm
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    A.right.hom ≫ (postcomposeFunctor_preimage_right (S := S) φ η ▷ p) =
      B.right.hom := by
  -- Postcompose by the inverse target comparison so that the terminal right-leg shell applies
  -- directly.
  apply (cancel_mono B.right.inv).1
  calc
    (A.right.hom ≫ postcomposeFunctor_preimage_right (S := S) φ η ▷ p) ≫ B.right.inv =
        A.right.hom ≫ (λ_ (A.arrow ≫ p)).inv ≫ (α_ (𝟙 T) A.arrow p).inv ≫
          ((postcomposeFunctor_terminal_twohom (S := S) φ η).hom ▷ p ≫ B.right.inv) := by
            simpa [Category.assoc] using
              postcomposeFunctor_preimage_right_whisker_p_expansion (S := S) φ η
    _ = A.right.hom ≫ (λ_ (A.arrow ≫ p)).inv ≫ (α_ (𝟙 T) A.arrow p).inv ≫
          ((α_ (𝟙 T) A.arrow p).hom ≫ (λ_ (A.arrow ≫ p)).hom ≫ A.right.inv) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ A.right.hom ≫ (λ_ (A.arrow ≫ p)).inv ≫
                  (α_ (𝟙 T) A.arrow p).inv ≫ k)
                (postcomposeFunctor_terminal_twohom_right_leg (S := S) φ η)
    _ = A.right.hom ≫ A.right.inv := by
          simp
    _ = B.right.hom ≫ B.right.inv := by
          simp [DottedArrow.right]

/-- Helper for Lemma 4.44.2: the descended ambient `2`-cell defines the owner-level source
comparison obtained by composing the owner square of `A` with its source-square map. -/
private theorem postcompose_owner_source_hom_left
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow S) :
    (outer_dotted_arrow_owner_to_outer_square S φ (postcompose φ A) ≫
        postcompose_source_square_hom S φ A).left =
      A.left.hom ▷ q := by
  -- Expanding the composite owner map leaves only the whiskered upper-left comparison of `A`.
  change
    (α_ S.p A.arrow q).hom ≫ (S.p ◁ 𝟙 (A.arrow ≫ q)) ≫ (postcompose φ A).left.hom =
      A.left.hom ▷ q
  rw [show (postcompose φ A).left.hom = (α_ S.p A.arrow q).inv ≫ A.left.hom ▷ q by rfl]
  simp [Category.assoc]

/-- Helper for Lemma 4.44.2: the same composite owner map has the expected explicit lower-right
comparison shell. -/
private theorem postcompose_owner_source_hom_right
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    (A : DottedArrow S) :
    (outer_dotted_arrow_owner_to_outer_square S φ (postcompose φ A) ≫
        postcompose_source_square_hom S φ A).right =
      (α_ S.p A.arrow p).hom ≫ S.p ◁ A.right.inv := by
  -- The right leg is the unchanged source lower-right comparison, with the outer identity shell
  -- collapsed.
  change
    (α_ S.p A.arrow p).hom ≫ (S.p ◁ A.right.inv) ≫ 𝟙 (S.p ≫ y) =
      (α_ S.p A.arrow p).hom ≫ S.p ◁ A.right.inv
  simp

/-- Helper for Lemma 4.44.2: any morphism from the whiskered source lift to the canonical owner
lift yields the matching owner-level lower-right compatibility after normalization. -/
private theorem whiskered_comparison_right_comm
    {A : DottedArrow S}
    (μ : (LeftLift.whiskering S.p).obj A.toLeftLift ⟶ S.symm.toLeftLift) :
    μ.right ▷ p ≫ S.ψ.inv =
      (α_ S.p A.arrow p).hom ≫ S.p ◁ inv A.toLeftLift.unit := by
  -- Rewrite the `LeftLift` morphism relation in the owner-square coordinates by cancelling the
  -- terminal comparison shell on the right.
  apply (cancel_mono S.ψ.hom).1
  simpa [DottedArrow.right, LeftLift.whiskering, Category.assoc] using
    congrArg (fun k ↦ (α_ S.p A.arrow p).hom ≫ S.p ◁ inv A.toLeftLift.unit ≫ k)
      (LeftLift.w μ)

/-- Helper for Lemma 4.44.2: the descended ambient `2`-cell defines the owner-level source
comparison witness into the final square whenever its `q`-whiskering matches the expected
upper-left source comparison. -/
private noncomputable def owner_terminal_twohom_of_whiskered_comparison
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A : DottedArrow S}
    (μ : (LeftLift.whiskering S.p).obj A.toLeftLift ⟶ S.symm.toLeftLift)
    (hq : μ.right ▷ q = (α_ S.p A.arrow q).hom ≫ (postcompose φ A).left.hom) :
    (outer_dotted_arrow_owner_to_outer_square S φ (postcompose φ A) ≫
        postcompose_source_square_hom S φ A) ⟶
      outer_dotted_arrow_owner_terminal_source_hom (S := S) φ := by
  refine
    { hom := μ.right
      left_comm := ?_
      right_comm := ?_ }
  · -- The hypothesized `q`-whiskered formula is already the left leg of the owner-level square.
    rw [postcompose_owner_source_hom_left (S := S) (φ := φ) (A := A)]
    have hleft_id :
        μ.right ▷ q ≫ (outer_dotted_arrow_owner_terminal_source_hom (S := S) φ).left =
          μ.right ▷ q := by
      change μ.right ▷ q ≫ 𝟙 (S.q ≫ q) = μ.right ▷ q
      exact Category.comp_id (μ.right ▷ q)
    have hq' : μ.right ▷ q = A.comparison.hom.right ▷ q := by
      have hq'' :
          μ.right ▷ q = (α_ S.p A.arrow q).hom ≫ (postcompose φ A).comparison.hom.right := by
        simpa [DottedArrow.left] using hq
      have hpostA :
          (α_ S.p A.arrow q).hom ≫ (postcompose φ A).comparison.hom.right =
            A.comparison.hom.right ▷ q := by
        change
          (α_ S.p A.arrow q).hom ≫
              ((α_ S.p A.arrow q).inv ≫ A.comparison.hom.right ▷ q) =
            A.comparison.hom.right ▷ q
        simp [Category.assoc]
      exact hq''.trans hpostA
    simpa [DottedArrow.left] using hleft_id.trans hq'
  · -- The `LeftLift` compatibility of `μ` is the normalized lower-right owner relation.
    simpa [postcompose_owner_source_hom_right, DottedArrow.right, Category.assoc] using
      whiskered_comparison_right_comm (S := S) (A := A) μ

/-- Helper for Lemma 4.44.2: the descended ambient `2`-cell defines the owner-level source
comparison required for a morphism before postcomposition. -/
private theorem postcomposeFunctor_preimage_owner_descent
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    (LeftLift.whiskering S.p).map
        (LeftLift.homMk (postcomposeFunctor_preimage_right (S := S) φ η)
          (postcomposeFunctor_terminal_twohom_normalized_right_comm (S := S) φ η)) ≫
      B.comparison.hom = A.comparison.hom := by
  let θLift : A.toLeftLift ⟶ B.toLeftLift :=
    LeftLift.homMk (postcomposeFunctor_preimage_right (S := S) φ η)
      (postcomposeFunctor_terminal_twohom_normalized_right_comm (S := S) φ η)
  let μ₁ :
      (LeftLift.whiskering S.p).obj A.toLeftLift ⟶ S.symm.toLeftLift :=
    (LeftLift.whiskering S.p).map θLift ≫ B.comparison.hom
  let μ₂ :
      (LeftLift.whiskering S.p).obj A.toLeftLift ⟶ S.symm.toLeftLift :=
    A.comparison.hom
  have hμ₁ :
      μ₁.right ▷ q = (α_ S.p A.arrow q).hom ≫ (postcompose φ A).left.hom := by
    -- Normalize the `q`-whiskered upper-left comparison through `η`.
    have hpostB :
        (α_ S.p B.arrow q).inv ≫ B.comparison.hom.right ▷ q =
          (postcompose φ B).left.hom := by
      rfl
    calc
      μ₁.right ▷ q =
          (α_ S.p A.arrow q).hom ≫
            (S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q)) ≫
              (postcompose φ B).left.hom := by
                have hμ₁_expand :
                    μ₁.right ▷ q =
                      (α_ S.p A.arrow q).hom ≫
                        S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q) ≫
                          (α_ S.p B.arrow q).inv ≫ B.comparison.hom.right ▷ q := by
                  simp [μ₁, θLift, Category.assoc]
                have hμ₁_post :
                    (α_ S.p A.arrow q).hom ≫
                        S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q) ≫
                          (α_ S.p B.arrow q).inv ≫ B.comparison.hom.right ▷ q =
                      (α_ S.p A.arrow q).hom ≫
                        S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q) ≫
                          (postcompose φ B).left.hom := by
                  have hμ₁_post_base :
                      S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q) ≫
                          (α_ S.p B.arrow q).inv ≫ B.comparison.hom.right ▷ q =
                        S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q) ≫
                          (postcompose φ B).left.hom := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦
                          S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q) ≫ k)
                        hpostB
                  exact congrArg
                      (fun k ↦
                        (α_ S.p A.arrow q).hom ≫ k)
                      hμ₁_post_base
                exact hμ₁_expand.trans hμ₁_post
      _ =
          (α_ S.p A.arrow q).hom ≫
            (S.p ◁ η.right) ≫
              (postcompose φ B).left.hom := by
                have hηq_base :
                    S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q) =
                      S.p ◁ η.right := by
                  simpa using
                    congrArg
                      (fun k ↦ S.p ◁ k)
                      (postcomposeFunctor_terminal_twohom_normalized_whisker (S := S) φ η)
                have hηq :
                    S.p ◁ (postcomposeFunctor_preimage_right (S := S) φ η ▷ q) ≫
                        (postcompose φ B).left.hom =
                      S.p ◁ η.right ≫ (postcompose φ B).left.hom := by
                  exact congrArg (fun k ↦ k ≫ (postcompose φ B).left.hom) hηq_base
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ (α_ S.p A.arrow q).hom ≫ k)
                    hηq
      _ = (α_ S.p A.arrow q).hom ≫ (postcompose φ A).left.hom := by
            calc
              (α_ S.p A.arrow q).hom ≫ (S.p ◁ η.right) ≫ (postcompose φ B).left.hom =
                  (α_ S.p A.arrow q).hom ≫
                    (S.p ◁ η.right ≫ (postcompose φ B).left.hom) := by
                      simp [Category.assoc]
              _ = (α_ S.p A.arrow q).hom ≫ (postcompose φ A).left.hom := by
                    exact congrArg
                      (fun k ↦ (α_ S.p A.arrow q).hom ≫ k)
                      (DottedArrow.Hom.left_comm η)
  have hμ₂ :
      μ₂.right ▷ q = (α_ S.p A.arrow q).hom ≫ (postcompose φ A).left.hom := by
    -- The original comparison is already the owner witness for `A`.
    change A.comparison.hom.right ▷ q =
      (α_ S.p A.arrow q).hom ≫ ((α_ S.p A.arrow q).inv ≫ A.comparison.hom.right ▷ q)
    simp [Category.assoc]
  let τ₁ :
      (outer_dotted_arrow_owner_to_outer_square S φ (postcompose φ A) ≫
          postcompose_source_square_hom S φ A) ⟶
        outer_dotted_arrow_owner_terminal_source_hom (S := S) φ :=
    owner_terminal_twohom_of_whiskered_comparison (S := S) (φ := φ) μ₁ hμ₁
  let τ₂ :
      (outer_dotted_arrow_owner_to_outer_square S φ (postcompose φ A) ≫
          postcompose_source_square_hom S φ A) ⟶
        outer_dotted_arrow_owner_terminal_source_hom (S := S) φ :=
    owner_terminal_twohom_of_whiskered_comparison (S := S) (φ := φ) μ₂ hμ₂
  let _ :
      Unique
        ((outer_dotted_arrow_owner_to_outer_square S φ (postcompose φ A) ≫
            postcompose_source_square_hom S φ A) ⟶
          outer_dotted_arrow_owner_terminal_source_hom (S := S) φ) := inferInstance
  have hτ : τ₁ = τ₂ := Subsingleton.elim _ _
  -- Equality of the owner-level terminal witnesses identifies the source comparison itself.
  apply StructuredArrow.hom_ext
  simpa [τ₁, τ₂, μ₁, μ₂] using
    congrArg BicategoricalTwoCommutativeSquare.TwoHom.hom hτ

/-- Helper for Lemma 4.44.2: every morphism between postcomposed dotted arrows descends uniquely
to a morphism before postcomposition. -/
private theorem postcomposeFunctor_preimage_hom
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]
    {A B : DottedArrow S}
    (η : postcompose φ A ⟶ postcompose φ B) :
    ∃ θ : A ⟶ B, (postcomposeFunctor S φ).map θ = η := by
  let θLift : A.toLeftLift ⟶ B.toLeftLift :=
    LeftLift.homMk (postcomposeFunctor_preimage_right (S := S) φ η)
      (postcomposeFunctor_terminal_twohom_normalized_right_comm (S := S) φ η)
  have hθLift :
      (LeftLift.whiskering S.p).map θLift ≫ B.comparison.hom = A.comparison.hom := by
    -- The only genuinely source-level input is the owner descent for `θLift`.
    simpa [θLift] using
      postcomposeFunctor_preimage_owner_descent (S := S) (φ := φ) (η := η)
  let θ : A ⟶ B := ⟨θLift, hθLift⟩
  refine ⟨θ, ?_⟩
  -- Equality after postcomposition is detected on the ambient `2`-morphism component.
  apply DottedArrow.Hom.ext
  simpa [θ, θLift, postcomposeFunctor_map_right] using
    postcomposeFunctor_terminal_twohom_normalized_whisker (S := S) φ η

/-- Helper for Lemma 4.44.2: the postcomposition functor is full and faithful once morphisms are
descended through the terminal right square. -/
private theorem postcomposeFunctor_full_faithful
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)] :
    Functor.Full (postcomposeFunctor S φ) ∧ Functor.Faithful (postcomposeFunctor S φ) := by
  constructor
  · refine ⟨?_⟩
    intro A B η
    -- The descended source morphism is the required preimage.
    let h := postcomposeFunctor_preimage_hom (S := S) φ η
    exact ⟨h.choose, h.choose_spec⟩
  · refine ⟨?_⟩
    intro A B η θ hηθ
    -- Equality is detected on the ambient `2`-morphism component, and for actual source
    -- morphisms terminality reconstructs that component without any separate `q`-cancellation.
    apply DottedArrow.Hom.ext
    have hpre :=
      congrArg (postcomposeFunctor_preimage_right (S := S) φ) hηθ
    calc
      η.right = postcomposeFunctor_preimage_right (S := S) φ ((postcomposeFunctor S φ).map η) := by
        symm
        exact postcomposeFunctor_preimage_right_of_map (S := S) φ η
      _ = postcomposeFunctor_preimage_right (S := S) φ ((postcomposeFunctor S φ).map θ) := hpre
      _ = θ.right := postcomposeFunctor_preimage_right_of_map (S := S) φ θ

/-- Lemma 4.44.2: if the right square `⟨X', q, p, φ.symm⟩` is `2`-cartesian, then
postcomposition with that square induces an equivalence on dotted-arrow categories. -/
noncomputable instance postcomposeFunctor_isEquivalence
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)] :
    (postcomposeFunctor S φ).IsEquivalence := by
  -- Route correction: the failed route tried to unwhisker the `q`-postcomposed upper-left
  -- comparison into a bare isomorphism `S.p ≫ lift ≅ S.q`.
  -- The verified frontier is now factored through the formal helper
  -- `postcomposeFunctor_isEquivalence_of_data`.
  let hff := postcomposeFunctor_full_faithful (S := S) φ
  let _ : Functor.Full (postcomposeFunctor S φ) := hff.1
  let _ : Functor.Faithful (postcomposeFunctor S φ) := hff.2
  -- The remaining input is essential surjectivity, provided by the terminally reconstructed
  -- source dotted arrow on each outer object.
  refine postcomposeFunctor_isEquivalence_of_data (S := S) φ ?_
  intro A
  refine ⟨outer_dotted_arrow_preimage S φ A (outer_dotted_arrow_terminal_comparison S φ A), ?_⟩
  exact outer_dotted_arrow_postcompose_iso (S := S) φ A

end

end DottedArrow

end CategoryTheory
