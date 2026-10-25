module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MonoidalCategory

noncomputable section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: rigid monoidal category theory, with `ExactPairing X Y` as the owner object for
  an object `X` together with a chosen right dual `Y`.
- Core/canonical declarations inspected:
  - `ExactPairing`
  - `tensorRightAdjunction`
  - `tensorRightHomEquiv_tensor`
  - `rightDualIso`
- Owner abstraction: `ExactPairing X Y` for the core rigid datum, and `Adjunction` for the
  bridge/view property imposed on an adjunction `tensorRight X ⊣ tensorRight Y`.
- Layer triage:
  - `core/canonical`: `ExactPairing`, `tensorRightAdjunction`, and `rightDualIso`;
  - `bridge/view`: `Adjunction.CompatibleWithLeftTensoring`, which expresses the source remark's
    extra compatibility condition on an adjunction `tensorRight X ⊣ tensorRight Y`, together with
    `Adjunction.toExactPairing` as the canonical bridge back to the owner exact pairing.
- Primitive vs. derived:
  - primitive data: the exact pairing `ExactPairing X Y`;
  - derived API: `tensorRightHomEquiv`, the induced adjunction `tensorRightAdjunction`,
    compatibility via `tensorRightHomEquiv_tensor`, uniqueness via `rightDualIso`, and the
    adjunction-to-pairing bridge `Adjunction.toExactPairing` used by the source-facing existence
    theorem `nonempty_exactPairing_iff_exists_compatible_tensorRightAdjunction`.
-/

/- Remark 4.43.7 first observes that a right dual `Y` of `X` makes `tensorRight Y` a right adjoint
to `tensorRight X`. This is the canonical adjunction `tensorRightAdjunction X Y`. -/
recall tensorRightAdjunction

/- Remark 4.43.7 also records that a right dual, if it exists, is unique up to unique isomorphism.
This is the canonical isomorphism `rightDualIso`. -/
recall rightDualIso

namespace Adjunction

variable {X Y : C}

/-- An adjunction `tensorRight X ⊣ tensorRight Y` is compatible with left tensoring when its
hom-set equivalence commutes with tensoring on the left by any object, up to the associators of
the ambient monoidal category. -/
def CompatibleWithLeftTensoring (adj : tensorRight X ⊣ tensorRight Y) : Prop :=
  ∀ ⦃W Z Z' : C⦄ (f : Z' ⊗ X ⟶ Z),
    adj.homEquiv (W ⊗ Z') (W ⊗ Z) ((α_ W Z' X).hom ≫ W ◁ f) =
      W ◁ adj.homEquiv Z' Z f ≫ (α_ W Z Y).inv

/-- An adjunction `tensorRight X ⊣ tensorRight Y` whose hom-set equivalence is compatible with
left tensoring determines the exact pairing exhibiting `Y` as a right dual of `X`. -/
@[implicit_reducible] def toExactPairing (adj : tensorRight X ⊣ tensorRight Y)
    (hcompat : adj.CompatibleWithLeftTensoring) : ExactPairing X Y where
  coevaluation' := adj.homEquiv (𝟙_ C) X (λ_ X).hom
  evaluation' := (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv
  coevaluation_evaluation' := by
    let η : 𝟙_ C ⟶ X ⊗ Y := adj.homEquiv (𝟙_ C) X (λ_ X).hom
    let ε : Y ⊗ X ⟶ 𝟙_ C := (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv
    apply (adj.homEquiv (Y ⊗ 𝟙_ C) (𝟙_ C)).symm.injective
    have hη :
        adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X) ((ρ_ Y).hom ▷ X) =
          Y ◁ η ≫ (α_ Y X Y).inv := by
      simpa [η] using hcompat ((λ_ X).hom : (𝟙_ C) ⊗ X ⟶ X)
    have hη' :
        (adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)).symm (Y ◁ η ≫ (α_ Y X Y).inv) =
          (ρ_ Y).hom ▷ X := by
      apply (adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)).injective
      rw [(adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)).apply_symm_apply]
      exact hη.symm
    have hρ :
        (adj.homEquiv (Y ⊗ 𝟙_ C) (𝟙_ C)).symm ((ρ_ Y).hom ≫ (λ_ Y).inv) =
          (ρ_ Y).hom ▷ X ≫ ε := by
      simpa [ε] using
        (adj.homEquiv_naturality_left_symm (ρ_ Y).hom (λ_ Y).inv)
    trans (adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)).symm (Y ◁ η ≫ (α_ Y X Y).inv) ≫ ε
    · simpa [ε] using
        (adj.homEquiv_naturality_right_symm (Y ◁ η ≫ (α_ Y X Y).inv) ε)
    trans (ρ_ Y).hom ▷ X ≫ ε
    · rw [hη']
    · exact hρ.symm
  evaluation_coevaluation' := by
    let η : 𝟙_ C ⟶ X ⊗ Y := adj.homEquiv (𝟙_ C) X (λ_ X).hom
    let ε : Y ⊗ X ⟶ 𝟙_ C := (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv
    apply (adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C)).injective
    have hε :
        adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C) ((α_ X Y X).hom ≫ X ◁ ε) =
          (ρ_ X).inv ▷ Y := by
      calc
        adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C) ((α_ X Y X).hom ≫ X ◁ ε)
          = X ◁ adj.homEquiv Y (𝟙_ C) ε ≫ (α_ X (𝟙_ C) Y).inv := by
              simpa using hcompat ε
        _ = X ◁ (λ_ Y).inv ≫ (α_ X (𝟙_ C) Y).inv := by
            simpa using
              congrArg (fun g ↦ X ◁ g ≫ (α_ X (𝟙_ C) Y).inv)
                ((adj.homEquiv Y (𝟙_ C)).apply_symm_apply (λ_ Y).inv)
        _ = (ρ_ X).inv ▷ Y := by monoidal
    have hLambda :
        adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C) ((λ_ X).hom ≫ (ρ_ X).inv) =
          η ≫ (ρ_ X).inv ▷ Y := by
      simpa [η] using
        (adj.homEquiv_naturality_right (λ_ X).hom (ρ_ X).inv)
    trans η ≫ adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C) ((α_ X Y X).hom ≫ X ◁ ε)
    · simpa [η] using
        (adj.homEquiv_naturality_left η ((α_ X Y X).hom ≫ X ◁ ε))
    trans η ≫ (ρ_ X).inv ▷ Y
    · rw [hε]
    · exact hLambda.symm

end Adjunction

/-- The canonical adjunction attached to an exact pairing is compatible with left tensoring. -/
theorem tensorRightAdjunction_compatibleWithLeftTensoring (X Y : C) [ExactPairing X Y] :
    (tensorRightAdjunction X Y).CompatibleWithLeftTensoring := by
  intro W Z Z' f
  simp only [tensorRightAdjunction]
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  have h :
      (tensorRightHomEquiv (W ⊗ Z') X Y (W ⊗ Z)).symm
          (((𝟙 W) ⊗ₘ (tensorRightHomEquiv Z' X Y Z) f) ≫ (α_ W Z Y).inv) =
        (α_ W Z' X).hom ≫
          ((𝟙 W) ⊗ₘ (tensorRightHomEquiv Z' X Y Z).symm ((tensorRightHomEquiv Z' X Y Z) f)) := by
    exact tensorRightHomEquiv_tensor ((tensorRightHomEquiv Z' X Y Z) f) (𝟙 W)
  simpa using h.symm

/-- Remark 4.43.7: an object `Y` is a right dual of `X` exactly when the functor
`Z' ↦ Z' ⊗ Y` is a right adjoint of `Z ↦ Z ⊗ X` via an adjunction whose hom-set equivalence is
compatible with tensoring on the left. This is the source-facing existence bridge, with
`Adjunction.toExactPairing` as its canonical reconstruction map. -/
theorem nonempty_exactPairing_iff_exists_compatible_tensorRightAdjunction (X Y : C) :
    Nonempty (ExactPairing X Y) ↔
      ∃ adj : tensorRight X ⊣ tensorRight Y,
        adj.CompatibleWithLeftTensoring := by
  constructor
  · rintro ⟨_⟩
    exact ⟨tensorRightAdjunction X Y, tensorRightAdjunction_compatibleWithLeftTensoring X Y⟩
  · rintro ⟨adj, hcompat⟩
    exact ⟨adj.toExactPairing hcompat⟩

end

end CategoryTheory
