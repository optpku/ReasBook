module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

noncomputable section

/-- A chosen two-sided tensor inverse for `X` makes left tensoring by `X` an equivalence. -/
private theorem tensorLeft_isEquivalence_of_exists_tensor_inverse
    {X : C}
    (hX : ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C)) :
    (tensorLeft X).IsEquivalence := by
  rcases hX with ⟨X', ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩
  exact Functor.IsEquivalence.mk' (tensorLeft X')
    ((leftUnitorNatIso C).symm ≪≫ (tensoringLeft C).mapIso e₂.symm ≪≫ tensorLeftTensor X' X)
    ((tensorLeftTensor X X').symm ≪≫ (tensoringLeft C).mapIso e₁ ≪≫ leftUnitorNatIso C)

/-- A chosen two-sided tensor inverse for `X` also makes right tensoring by `X` an equivalence. -/
private theorem tensorRight_isEquivalence_of_exists_tensor_inverse
    {X : C}
    (hX : ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C)) :
    (tensorRight X).IsEquivalence := by
  rcases hX with ⟨X', ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩
  exact Functor.IsEquivalence.mk' (tensorRight X')
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso e₁.symm ≪≫
      tensorRightTensor X X')
    ((tensorRightTensor X' X).symm ≪≫ (tensoringRight C).mapIso e₂ ≪≫ rightUnitorNatIso C)

/-- If left tensoring by `X` is an equivalence, applying a quasi-inverse to the tensor unit
produces a two-sided tensor inverse for `X`. -/
private theorem exists_tensor_inverse_of_tensorLeft_isEquivalence
    (X : C) (hX : (tensorLeft X).IsEquivalence) :
    ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) := by
  letI := hX
  let F : C ⥤ C := tensorLeft X
  let e : C ≌ C := F.asEquivalence
  let X' : C := F.inv.obj (𝟙_ C)
  let e₁ : X ⊗ X' ≅ 𝟙_ C := e.counitIso.app (𝟙_ C)
  let e₂ : X' ⊗ X ≅ 𝟙_ C :=
    F.preimageIso <|
      (tensorLeftTensor X X').symm.app X ≪≫
        whiskerRightIso e₁ X ≪≫ leftUnitor X ≪≫ (rightUnitor X).symm
  exact ⟨X', ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩

/-- The right-tensor analogue of `exists_tensor_inverse_of_tensorLeft_isEquivalence`. -/
private theorem exists_tensor_inverse_of_tensorRight_isEquivalence
    (X : C) (hX : (tensorRight X).IsEquivalence) :
    ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) := by
  letI := hX
  let F : C ⥤ C := tensorRight X
  let e : C ≌ C := F.asEquivalence
  let X' : C := F.inv.obj (𝟙_ C)
  let e₂ : X' ⊗ X ≅ 𝟙_ C := e.counitIso.app (𝟙_ C)
  let e₁ : X ⊗ X' ≅ 𝟙_ C :=
    F.preimageIso <|
      (tensorRightTensor X' X).symm.app X ≪≫
        whiskerLeftIso X e₂ ≪≫ rightUnitor X ≪≫ (leftUnitor X).symm
  exact ⟨X', ⟨⟨e₁⟩, ⟨e₂⟩⟩⟩

/- Domain sampling:
- Primary domain: monoidal category theory, specifically invertibility of an object detected by
  tensoring endofunctors, with the two-sided inverse data organized upstream through
  `ExactPairing`.
- Core/canonical declarations inspected:
  - `ExactPairing`
  - `tensorLeftAdjunction`
  - `tensorRightAdjunction`
  - `Functor.IsEquivalence`
- Best owner abstraction: `(tensorLeft X).IsEquivalence`, later adopted in Definition `4.43.4`.
- Layer triage:
  - `source-facing`: the three equivalent textbook conditions in Lemma `4.43.3`;
  - `core/canonical`: `(tensorLeft X).IsEquivalence`;
  - `bridge/view`: the `ExactPairing`/adjunction route from two-sided inverse data to the tensor
    equivalence criteria.
- Primitive vs. derived:
  - primitive data: the source-facing two-sided tensor inverse data
    `∃ X', X ⊗ X' ≅ 𝟙_ C` and `X' ⊗ X ≅ 𝟙_ C`;
  - derived API: the source-facing `TFAE` statement, its atomic `↔` projections below, and the
    induced exact pairing/adjunction package.
-/

-- Proof sketch: if left tensoring by `X` is an equivalence, apply a quasi-inverse to the tensor
-- unit to obtain an object `X'` with `X ⊗ X' ≅ 𝟙_ C`, then compare that quasi-inverse with
-- tensoring by `X'` to obtain `X' ⊗ X ≅ 𝟙_ C`; the argument for right tensoring is dual.
-- Conversely, a two-sided tensor inverse for `X` gives the source-facing inverse data, from which
-- one obtains the corresponding exact-pairing/adjunction package and hence equivalences of both
-- `tensorLeft X` and `tensorRight X`.
/-- Lemma 4.43.3: for an object `X` of a monoidal category, the following are equivalent:
left tensoring by `X` is an equivalence, right tensoring by `X` is an equivalence, and there
exists an object `X'` such that `X ⊗ X' ≅ 𝟙_ C` and `X' ⊗ X ≅ 𝟙_ C`. -/
theorem tensor_left_right_equivalence_tfae (X : C) :
    List.TFAE [
      (tensorLeft X).IsEquivalence,
      (tensorRight X).IsEquivalence,
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C)
    ] := by
  tfae_have 1 → 3 := by
    intro hX
    exact exists_tensor_inverse_of_tensorLeft_isEquivalence X hX
  tfae_have 3 → 2 := by
    intro hX
    exact tensorRight_isEquivalence_of_exists_tensor_inverse hX
  tfae_have 2 → 1 := by
    intro hX
    exact tensorLeft_isEquivalence_of_exists_tensor_inverse <|
      exists_tensor_inverse_of_tensorRight_isEquivalence X hX
  tfae_finish

/-- Left tensoring by `X` is an equivalence exactly when right tensoring by `X` is. -/
theorem tensorLeft_isEquivalence_iff_tensorRight_isEquivalence (X : C) :
    (tensorLeft X).IsEquivalence ↔ (tensorRight X).IsEquivalence :=
  (tensor_left_right_equivalence_tfae X).out 0 1

/-- Left tensoring by `X` is an equivalence exactly when `X` admits a two-sided tensor inverse. -/
theorem tensorLeft_isEquivalence_iff_exists_tensor_inverse (X : C) :
    (tensorLeft X).IsEquivalence ↔
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) :=
  (tensor_left_right_equivalence_tfae X).out 0 2

/-- Right tensoring by `X` is an equivalence exactly when `X` admits a two-sided tensor inverse. -/
theorem tensorRight_isEquivalence_iff_exists_tensor_inverse (X : C) :
    (tensorRight X).IsEquivalence ↔
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) :=
  (tensor_left_right_equivalence_tfae X).out 1 2

end

end CategoryTheory
