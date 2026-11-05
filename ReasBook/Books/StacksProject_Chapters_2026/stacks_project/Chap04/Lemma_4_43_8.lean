module

public import stacks_project.Chap04.Remark_4_43_7
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MonoidalCategory

noncomputable section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: rigid monoidal category theory.
- Core/canonical declarations inspected:
  - `CategoryTheory.ExactPairing`
  - `CategoryTheory.tensorRightAdjunction`
  - `CategoryTheory.tensorRightTensor`
  - `CategoryTheory.Adjunction.toExactPairing`
- Owner abstraction: `ExactPairing Y X`.
- Layer triage:
  - `source-facing`: the fixed-pair statement that if `Y₁` is a left dual of `A` and `Y₂` is a
    left dual of `B`, then `Y₂ ⊗ Y₁` is a left dual of `A ⊗ B`;
  - `core/canonical`: `ExactPairing Y X`;
  - `bridge/view`: the tensor-right adjunctions `tensorRightAdjunction`, their tensor-product
    comparison isomorphisms `tensorRightTensor`, and the canonical reconstruction
    `Adjunction.toExactPairing`.
- Primitive vs. derived:
  - primitive data: the exact pairings `ExactPairing Y₁ A` and `ExactPairing Y₂ B`;
  - derived API: the composite tensor-right adjunction on `tensorRight (Y₂ ⊗ Y₁)` and the
    resulting exact pairing on `(Y₂ ⊗ Y₁, A ⊗ B)`, together with the induced
    `HasLeftDual (A ⊗ B)` instance for chosen duals.
-/

section

variable {A B Y₁ Y₂ : C} [ExactPairing Y₁ A] [ExactPairing Y₂ B]

namespace ExactPairing

def tensorAdjunction :
    tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight (A ⊗ B) :=
  let adjComp : tensorRight Y₂ ⋙ tensorRight Y₁ ⊣ tensorRight A ⋙ tensorRight B :=
    (tensorRightAdjunction Y₂ B).comp (tensorRightAdjunction Y₁ A)
  let adjLeft : tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight A ⋙ tensorRight B :=
    adjComp.ofNatIsoLeft (tensorRightTensor Y₂ Y₁).symm
  adjLeft.ofNatIsoRight (tensorRightTensor A B).symm

/-- Helper for Lemma 4.43.8: expanding the transported composite adjunction rewrites its
hom-equivalence as the nested tensor-right hom-equivalences for the two input exact pairings. -/
private theorem tensorAdjunction_homEquiv_apply {Z Z' : C} (f : Z' ⊗ (Y₂ ⊗ Y₁) ⟶ Z) :
    tensorAdjunction.homEquiv Z' Z f =
      (tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A)
        ((tensorRightAdjunction Y₁ A).homEquiv (Z' ⊗ Y₂) Z ((α_ Z' Y₂ Y₁).hom ≫ f)) ≫
          (α_ Z A B).hom := by
  -- Expand the transported adjunction so the two underlying tensor-right adjunctions are visible.
  simp only [tensorAdjunction]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  rw [Adjunction.comp_homEquiv]
  rfl

/-- Helper for Lemma 4.43.8: the left-tensored input to the transported adjunction reassociates to
the exact shape needed to apply the compatibility of `tensorRightAdjunction Y₁ A`. -/
private theorem tensorAdjunction_input_reassociation {W Z Z' : C}
    (f : Z' ⊗ (Y₂ ⊗ Y₁) ⟶ Z) :
    (α_ (W ⊗ Z') Y₂ Y₁).hom ≫ (α_ W Z' (Y₂ ⊗ Y₁)).hom ≫ W ◁ f =
      ((α_ W Z' Y₂).hom ▷ Y₁) ≫ (α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f := by
  -- This is pure monoidal coherence: both sides are the canonical reassociation of `W ◁ f`.
  monoidal

/-- Helper for Lemma 4.43.8: after applying the two compatibility theorems, the remaining
associators combine to the target associator for `A ⊗ B`. -/
private theorem tensorAdjunction_output_reassociation {W Z Z' : C}
    (g : Z' ⟶ (Z ⊗ A) ⊗ B) :
    W ◁ g ≫ (α_ W (Z ⊗ A) B).inv ≫ ((α_ W Z A).inv ▷ B) ≫ (α_ (W ⊗ Z) A B).hom =
      W ◁ (g ≫ (α_ Z A B).hom) ≫ (α_ W Z (A ⊗ B)).inv := by
  -- This is the associator coherence relating the iterated tensor-right output to `A ⊗ B`.
  monoidal

theorem tensorAdjunction_compatible :
    (tensorAdjunction : tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight (A ⊗ B)).CompatibleWithLeftTensoring := by
  -- Route correction: keep the source-faithful transported-composite adjunction and prove
  -- compatibility by expanding its `homEquiv`, then applying the two basic tensor-right
  -- compatibility theorems in sequence.
  intro W Z Z' f
  -- Rewrite both sides into the nested hom-equivalences for the two tensor-right adjunctions.
  rw [tensorAdjunction_homEquiv_apply]
  rw [tensorAdjunction_homEquiv_apply]
  let inner₀ : Z' ⊗ Y₂ ⟶ Z ⊗ A :=
    (tensorRightAdjunction Y₁ A).homEquiv (Z' ⊗ Y₂) Z ((α_ Z' Y₂ Y₁).hom ≫ f)
  have hinput :
      (α_ (W ⊗ Z') Y₂ Y₁).hom ≫ (α_ W Z' (Y₂ ⊗ Y₁)).hom ≫ W ◁ f =
        ((α_ W Z' Y₂).hom ▷ Y₁) ≫ (α_ W (Z' ⊗ Y₂) Y₁).hom ≫
          W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f := by
    -- Normalize the left-tensored source so the first compatibility theorem can be used.
    exact tensorAdjunction_input_reassociation (W := W) (Z := Z) (Z' := Z') (f := f)
  have hinner_reassoc :
      ((tensorRightAdjunction Y₁ A).homEquiv ((W ⊗ Z') ⊗ Y₂) (W ⊗ Z))
          (((α_ W Z' Y₂).hom ▷ Y₁) ≫ (α_ W (Z' ⊗ Y₂) Y₁).hom ≫
            W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f) =
        (α_ W Z' Y₂).hom ≫
          (tensorRightAdjunction Y₁ A).homEquiv (W ⊗ (Z' ⊗ Y₂)) (W ⊗ Z)
            ((α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f) := by
    -- Move the outer associator across the inner hom-equivalence via naturality in the source.
    simpa [Category.assoc] using
      (Adjunction.homEquiv_naturality_left (adj := tensorRightAdjunction Y₁ A)
        ((α_ W Z' Y₂).hom)
        ((α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f))
  have hinner_compat :
      (tensorRightAdjunction Y₁ A).homEquiv (W ⊗ (Z' ⊗ Y₂)) (W ⊗ Z)
          ((α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f) =
        W ◁ inner₀ ≫ (α_ W Z A).inv := by
    -- Apply the compatibility theorem for the first tensor-right adjunction.
    simpa [inner₀] using
      ((tensorRightAdjunction_compatibleWithLeftTensoring Y₁ A)
        (W := W) (Z := Z) (Z' := Z' ⊗ Y₂) ((α_ Z' Y₂ Y₁).hom ≫ f))
  have houter_naturality :
      (tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A)
          (((α_ W Z' Y₂).hom ≫ W ◁ inner₀) ≫ (α_ W Z A).inv) =
        (tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') (W ⊗ (Z ⊗ A))
            ((α_ W Z' Y₂).hom ≫ W ◁ inner₀) ≫
          ((α_ W Z A).inv ▷ B) := by
    -- Move the right-side associator through the outer hom-equivalence via naturality in the target.
    simpa [Category.assoc] using
      (Adjunction.homEquiv_naturality_right (adj := tensorRightAdjunction Y₂ B)
        ((α_ W Z' Y₂).hom ≫ W ◁ inner₀) (α_ W Z A).inv)
  have houter_compat :
      (tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') (W ⊗ (Z ⊗ A))
          ((α_ W Z' Y₂).hom ≫ W ◁ inner₀) =
        W ◁ ((tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A) inner₀) ≫
          (α_ W (Z ⊗ A) B).inv := by
    -- Apply the compatibility theorem for the second tensor-right adjunction.
    simpa [inner₀] using
      ((tensorRightAdjunction_compatibleWithLeftTensoring Y₂ B)
        (W := W) (Z := Z ⊗ A) (Z' := Z') inner₀)
  calc
    ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
          (((tensorRightAdjunction Y₁ A).homEquiv ((W ⊗ Z') ⊗ Y₂) (W ⊗ Z))
            ((α_ (W ⊗ Z') Y₂ Y₁).hom ≫ (α_ W Z' (Y₂ ⊗ Y₁)).hom ≫ W ◁ f)) ≫
        (α_ (W ⊗ Z) A B).hom
        =
      ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
          (((tensorRightAdjunction Y₁ A).homEquiv ((W ⊗ Z') ⊗ Y₂) (W ⊗ Z))
            (((α_ W Z' Y₂).hom ▷ Y₁) ≫ (α_ W (Z' ⊗ Y₂) Y₁).hom ≫
              W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Replace the inner source morphism by its reassociated form.
          exact congrArg
            (fun k =>
              ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
                (((tensorRightAdjunction Y₁ A).homEquiv ((W ⊗ Z') ⊗ Y₂) (W ⊗ Z)) k) ≫
                  (α_ (W ⊗ Z) A B).hom)
            hinput
    _ =
      ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
          ((α_ W Z' Y₂).hom ≫
            (tensorRightAdjunction Y₁ A).homEquiv (W ⊗ (Z' ⊗ Y₂)) (W ⊗ Z)
              ((α_ W (Z' ⊗ Y₂) Y₁).hom ≫ W ◁ (α_ Z' Y₂ Y₁).hom ≫ W ◁ f)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Move the outer associator across the inner hom-equivalence.
          exact congrArg
            (fun k =>
              ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A)) k ≫
                (α_ (W ⊗ Z) A B).hom)
            hinner_reassoc
    _ =
      ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
          ((α_ W Z' Y₂).hom ≫ (W ◁ inner₀ ≫ (α_ W Z A).inv)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Substitute the first compatibility theorem.
          exact congrArg
            (fun k =>
              ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') ((W ⊗ Z) ⊗ A))
                ((α_ W Z' Y₂).hom ≫ k) ≫ (α_ (W ⊗ Z) A B).hom)
            hinner_compat
    _ =
      ((tensorRightAdjunction Y₂ B).homEquiv (W ⊗ Z') (W ⊗ (Z ⊗ A))
          ((α_ W Z' Y₂).hom ≫ W ◁ inner₀) ≫
        ((α_ W Z A).inv ▷ B)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Move the remaining target associator through the outer hom-equivalence.
          simpa [Category.assoc] using
            congrArg (fun k => k ≫ (α_ (W ⊗ Z) A B).hom) houter_naturality
    _ =
      (W ◁ ((tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A) inner₀) ≫
          (α_ W (Z ⊗ A) B).inv ≫ ((α_ W Z A).inv ▷ B)) ≫
        (α_ (W ⊗ Z) A B).hom := by
          -- Substitute the second compatibility theorem.
          simpa [Category.assoc] using
            congrArg
              (fun k => k ≫ ((α_ W Z A).inv ▷ B) ≫ (α_ (W ⊗ Z) A B).hom)
              houter_compat
    _ =
      W ◁
          (((tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A) inner₀) ≫
            (α_ Z A B).hom) ≫
        (α_ W Z (A ⊗ B)).inv := by
          -- Finish with the associator coherence relating the iterated right adjoints to `A ⊗ B`.
          simpa [inner₀, Category.assoc] using
            tensorAdjunction_output_reassociation (W := W) (Z := Z) (Z' := Z')
              ((tensorRightAdjunction Y₂ B).homEquiv Z' (Z ⊗ A) inner₀)

/-- Lemma 4.43.8: if `Y₁` is a left dual of `A` and `Y₂` is a left dual of `B`, then
`Y₂ ⊗ Y₁` is a left dual of `A ⊗ B`. This exact pairing is canonically reconstructed from the
tensor-right adjunction of the two input pairings. -/
instance tensor : ExactPairing (Y₂ ⊗ Y₁) (A ⊗ B) :=
  tensorAdjunction.toExactPairing tensorAdjunction_compatible

end ExactPairing

end

section

variable {A B : C} [HasLeftDual A] [HasLeftDual B]

namespace HasLeftDual

/-- If two objects admit chosen left duals, then their tensor product admits the tensor product of
those duals, in reverse order, as a chosen left dual. -/
instance tensor : HasLeftDual (A ⊗ B) where
  leftDual := (ᘁB : C) ⊗ (ᘁA : C)
  exact := inferInstance

end HasLeftDual

end

end CategoryTheory
