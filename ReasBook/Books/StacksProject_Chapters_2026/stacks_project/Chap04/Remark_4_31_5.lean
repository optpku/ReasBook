module

public import stacks_project.Chap04.Lemma_4_31_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory.Limits

open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/- Domain-style sampling for Remark 4.31.5:
- primary domain: categorical pullbacks of functors between categories;
- sampled owner-level declarations:
  `CategoricalPullback`,
  `CategoricalPullback.toCatCommSqOver`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `CategoricalPullback.functorEquiv`,
  `Functor.prod`,
  `Functor.diag`;
- best owner abstraction for the source model: the diagonal pullback
  `(F.prod G) ⊡ (Functor.diag C)`;
- core/canonical owner abstraction for the ordinary `2`-fibre product: `F ⊡ G`.

Primitive-vs-derived split:
- primitive data of the source-facing symmetric model: the canonical diagonal square
  `toCatCommSqOver (F.prod G) (Functor.diag C) ((F.prod G) ⊡ (Functor.diag C))`
  applied to `𝟭 _`;
- derived API: the projected square over `F` and `G`, the comparison functor to `F ⊡ G`, and the
  resulting equivalence.

Source/core/bridge triage:
- `source-facing`: `(F.prod G) ⊡ (Functor.diag C)`;
- `core/canonical`: `F ⊡ G`;
- `bridge/view`: `symmetricTwoFibreProductComparison` and
  `symmetricTwoFibreProductEquivalence`. -/

abbrev SymmetricModel (F : A ⥤ C) (G : B ⥤ C) :=
  (F.prod G) ⊡ (Functor.diag C)

abbrev diagonalSourceSquare (F : A ⥤ C) (G : B ⥤ C) :
    CatCommSqOver (F.prod G) (Functor.diag C) (SymmetricModel F G) :=
  (toCatCommSqOver (F.prod G) (Functor.diag C) (SymmetricModel F G)).obj (𝟭 _)

def leftComponentIso
    (F : A ⥤ C) (G : B ⥤ C)
    {X : Type*} [Category X]
    {Φ : X ⥤ A × B} {Λ : X ⥤ C}
    (σ : Φ ⋙ (F.prod G) ≅ Λ ⋙ Functor.diag C) :
    Φ ⋙ fst A B ⋙ F ≅ Λ :=
  NatIso.ofComponents
    (fun X ↦ by simpa using (fst C C).mapIso (σ.app X))
    (fun {_ _} f ↦ by
      simpa using congrArg _root_.Prod.fst (σ.hom.naturality f))

def rightComponentIso
    (F : A ⥤ C) (G : B ⥤ C)
    {X : Type*} [Category X]
    {Φ : X ⥤ A × B} {Λ : X ⥤ C}
    (σ : Φ ⋙ (F.prod G) ≅ Λ ⋙ Functor.diag C) :
    Φ ⋙ snd A B ⋙ G ≅ Λ :=
  NatIso.ofComponents
    (fun X ↦ by simpa using (snd C C).mapIso (σ.app X))
    (fun {_ _} f ↦ by
      simpa using congrArg _root_.Prod.snd (σ.hom.naturality f))

abbrev ordinarySquare
    (F : A ⥤ C) (G : B ⥤ C)
    {X : Type*} [Category X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) :
    CatCommSqOver F G X where
  fst := P.fst ⋙ fst A B
  snd := P.fst ⋙ snd A B
  iso := leftComponentIso F G P.iso ≪≫ (rightComponentIso F G P.iso).symm

/-- Remark 4.31.5: the symmetric quintuple model
`(A, B, C, F(A) ≅ C, G(B) ≅ C)` is the canonical diagonal pullback
`(F.prod G) ⊡ (Functor.diag C)`. The functor below is its canonical comparison
to the standard pullback owner `F ⊡ G`; the `IsEquivalence` instance below expresses that this
comparison is an equivalence. -/
abbrev symmetricTwoFibreProductComparison (F : A ⥤ C) (G : B ⥤ C) :
    (F.prod G) ⊡ (Functor.diag C) ⥤ F ⊡ G :=
  (toFunctorToCategoricalPullback F G (SymmetricModel F G)).obj
    (ordinarySquare F G (diagonalSourceSquare F G))

-- Proof sketch: use the explicit quasi-inverse `symmetricInverse F G` together with the unit and
-- counit isomorphisms `symmetricUnitIso F G` and `symmetricCounitIso F G`, then apply
-- `Functor.IsEquivalence.mk'`.
private def symmetricInverse (F : A ⥤ C) (G : B ⥤ C) :
    F ⊡ G ⥤ SymmetricModel F G where
  obj X :=
    { fst := (X.fst, X.snd)
      snd := G.obj X.snd
      iso := Iso.prod X.iso (.refl _) }
  map {X Y} f :=
    { fst := f.fst ×ₘ f.snd
      snd := G.map f.snd
      w := by
        ext <;> simp [f.w] }

private def symmetricUnitIso (F : A ⥤ C) (G : B ⥤ C) :
    𝟭 (SymmetricModel F G) ≅ symmetricTwoFibreProductComparison F G ⋙ symmetricInverse F G :=
  CategoricalPullback.mkNatIso
    (NatIso.ofComponents
      (fun X ↦ (prod.etaIso X.fst).symm)
      (fun {_ _} f ↦ by
        ext <;> simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso]))
    (NatIso.ofComponents
      (fun X ↦ ((rightComponentIso F G (diagonalSourceSquare F G).iso).app X).symm)
      (fun {_ _} f ↦ by
        simpa [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso] using
          congrArg _root_.Prod.snd f.w'))
    (by
      ext X
      · simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso]
      · suffices 𝟙 (G.obj X.fst.2) = X.iso.hom.2 ≫ X.iso.inv.2 by
          simpa [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
            diagonalSourceSquare, leftComponentIso, rightComponentIso] using this
        exact (congrArg _root_.Prod.snd X.iso.hom_inv_id).symm)

private def symmetricCounitIso (F : A ⥤ C) (G : B ⥤ C) :
    symmetricInverse F G ⋙ symmetricTwoFibreProductComparison F G ≅ 𝟭 (F ⊡ G) :=
  CategoricalPullback.mkNatIso
    (NatIso.ofComponents
      (fun X ↦ .refl _)
      (fun {_ _} f ↦ by
        simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso]))
    (NatIso.ofComponents
      (fun X ↦ .refl _)
      (fun {_ _} f ↦ by
        simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
          diagonalSourceSquare, leftComponentIso, rightComponentIso]))
    (by
      ext X
      simp [symmetricTwoFibreProductComparison, symmetricInverse, ordinarySquare,
        diagonalSourceSquare, leftComponentIso, rightComponentIso])

/-- The canonical comparison from the symmetric diagonal pullback model to the ordinary pullback
owner is an equivalence of categories. -/
theorem symmetricTwoFibreProductComparison_isEquivalence
    (F : A ⥤ C) (G : B ⥤ C) :
    (symmetricTwoFibreProductComparison F G).IsEquivalence := by
  -- The explicit inverse and the unit/counit isomorphisms already realize the comparison as an
  -- equivalence, so it remains only to package that data with `Functor.IsEquivalence.mk'`.
  exact
    Functor.IsEquivalence.mk'
      (symmetricInverse F G)
      (symmetricUnitIso F G)
      (symmetricCounitIso F G)

noncomputable instance
    (F : A ⥤ C) (G : B ⥤ C) :
    (symmetricTwoFibreProductComparison F G).IsEquivalence :=
  symmetricTwoFibreProductComparison_isEquivalence F G

end

end CategoryTheory.Limits
