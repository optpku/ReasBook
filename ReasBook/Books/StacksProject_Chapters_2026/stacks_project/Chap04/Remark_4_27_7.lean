module

public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

open Limits
open LeftFraction
open MorphismProperty

scoped[MorphismPropertyUnder] notation:80 Y " / " W =>
  CategoryTheory.MorphismProperty.Under W ⊤ Y

open scoped MorphismPropertyUnder

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (Y : C)

/- Domain-style sampling for Remark 4.27.7:
- primary domain: left calculus of fractions and the canonical denominator category `Y / W`;
- inspected owner declarations:
  `MorphismProperty.Under.mk`,
  `MorphismProperty.Under.homMk`,
  `MorphismProperty.RightFraction.leftFraction`,
  `MorphismProperty.RightFraction.leftFraction_fac`,
  `MorphismProperty.HasLeftCalculusOfFractions.ext`;
- best owner abstraction: the source-facing denominator category is already the owner object
  `Y / W`, realized by `MorphismProperty.Under W ⊤ Y`, so refinement should reuse its
  constructors instead of rebuilding objects by hand.

Primitive-vs-derived split:
- primitive data: an arrow `s : Y ⟶ Y'` together with `W s`;
- derived API: the corresponding object of `Y / W` via `Under.mk`, and its comparison morphisms
  via `Under.homMk`/`Under.Hom.ext`. -/

/- Source/core/bridge triage:
- `source-facing`: `localizationTargetArrows_isFiltered`;
- `core/canonical`: the denominator category owner `Y / W = MorphismProperty.Under W ⊤ Y`;
- `bridge/view`: the `Under.mk` / `Under.homMk` constructors expressing the textbook arrows and
  commutative triangles inside that owner category. -/

-- Proof sketch: use the identity arrow `𝟙 Y` for nonemptiness; apply the left Ore condition to
-- produce a common successor of two arrows out of `Y`; and use the left-cancellation axiom to
-- equalize parallel morphisms in the canonical denominator category `Y / W`.
/-- Remark 4.27.7: for a left multiplicative system `W`, the category `Y / W` of arrows
`s : Y ⟶ Y'` lying in `W`, with morphisms given by commutative triangles under `Y`, is filtered.
Equivalently, the canonical denominator category `Y / W`, i.e. `W.Under ⊤ Y`, is filtered. -/
instance localizationTargetArrows_isFiltered :
    IsFiltered (Y / W) where
  nonempty := ⟨Under.mk (⊤ : MorphismProperty C) (𝟙 Y) (W.id_mem Y)⟩
  cocone_objs s t := by
    let φ : W.RightFraction s.right t.right := RightFraction.mk s.hom s.prop t.hom
    let ψ := φ.leftFraction
    let u : Y / W := Under.mk (⊤ : MorphismProperty C) (t.hom ≫ ψ.s)
      (W.comp_mem _ _ t.prop ψ.hs)
    refine ⟨u, Under.homMk ψ.f (by simpa [u] using φ.leftFraction_fac.symm), Under.homMk ψ.s rfl,
      trivial⟩
  cocone_maps {s t} f g := by
    have hfg : s.hom ≫ f.right = s.hom ≫ g.right := by
      rw [Under.w f, Under.w g]
    obtain ⟨Z, h, hh, heq⟩ :=
      (inferInstance : W.HasLeftCalculusOfFractions).ext f.right g.right s.hom s.prop hfg
    let u : Y / W := Under.mk (⊤ : MorphismProperty C) (t.hom ≫ h) (W.comp_mem _ _ t.prop hh)
    refine ⟨u, Under.homMk h rfl, ?_⟩
    apply Under.Hom.ext
    exact heq

variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C)

/- Domain-style sampling for `4.27.7.1`:
- primary domain: calculus of left fractions and localized Hom-sets.
- inspected owner-level declarations:
  `localizationTargetArrows_isFiltered`,
  `MorphismProperty.Under.forget`,
  `uliftCoyoneda.obj`,
  `MorphismProperty.Q`,
  `Localization.exists_leftFraction`,
  `LeftFraction.Localization.homMk`,
  `LeftFraction.Localization.homMk_eq_iff_leftFractionRel`,
  `Functor.CoconeTypes.isColimit_iff`.
- best owner abstraction: the indexed Hom-diagram is owned by
  `uliftCoyoneda.obj (Opposite.op X)` on the canonical denominator category `Y / W`, while the
  localized target morphisms are owned by the canonical left-fraction localization model via
  `LeftFraction.Localization.homMk : W.LeftFraction X Y → (W.Q.obj X ⟶ W.Q.obj Y)`.

Primitive-vs-derived split:
- primitive data: the diagram on `Y / W` and its canonical cocone into
  `Hom_{W^{-1} C}(X, Y)`.
- derived API: the `Type`-colimit witness and the resulting colimit isomorphism.

Source/core/bridge triage:
- `source-facing`: `left_localization_hom_colimit`.
- `core/canonical`: `uliftCoyoneda.obj (Opposite.op X)` together with the left-fraction owner
  morphism `LeftFraction.Localization.homMk` in the canonical localization `W.Q`.
- `bridge/view`: the cocone identifying the source diagram with the localized Hom-set. -/

abbrev leftLocalizationHomDiagram (W : MorphismProperty C) (X Y : C) :
    (Y / W) ⥤ Type (max u v) :=
  Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
    uliftCoyoneda.{u}.obj (Opposite.op X)

/-- The cocone leg at `s : Y / W` sends `f : Hom_C(X, Y')` to the roof
`X ⟶ Y' ← Y` in the localized category. -/
noncomputable def leftLocalizationHomCoconeApp
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) (s : Y / W) :
    (leftLocalizationHomDiagram W X Y).obj s →
      ((Localization.Q W).obj X ⟶ (Localization.Q W).obj Y) :=
  fun f ↦
    let g : X ⟶ s.right := by
      simpa using f.down
    let hs : Y ⟶ s.right := by
      simpa using s.hom
    have hhs : W hs := by
      simpa [hs] using s.prop
    LeftFraction.Localization.homMk (LeftFraction.mk g hs hhs)

/- Naturality of the canonical cocone from the `Y/S` hom diagram to the localized hom-set. -/
-- Proof sketch: if `f : s ⟶ t` in `Y/S`, then `t.hom = s.hom ≫ f.right`; after localizing,
-- `W.Q.map f.right` is invertible, so the two corresponding roofs represent the same morphism.
theorem leftLocalizationHomCocone_naturality
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C)
    {s t : Y / W} (f : s ⟶ t) :
    (leftLocalizationHomDiagram W X Y).map f ≫ leftLocalizationHomCoconeApp W X Y t =
      leftLocalizationHomCoconeApp W X Y s := by
  funext g
  let ht : Y ⟶ t.right := by
    simpa using t.hom
  have hht : W ht := by
    simpa [ht] using t.prop
  let hs : Y ⟶ s.right := by
    simpa using s.hom
  have hhs : W hs := by
    simpa [hs] using s.prop
  let φ : W.LeftFraction X Y :=
    LeftFraction.mk (g.down ≫ f.right) ht hht
  let ψ : W.LeftFraction X Y :=
    LeftFraction.mk g.down hs hhs
  suffices hφψ : LeftFraction.Localization.homMk φ = LeftFraction.Localization.homMk ψ by
    simpa [leftLocalizationHomDiagram, leftLocalizationHomCoconeApp, φ, ψ] using hφψ
  rw [LeftFraction.Localization.homMk_eq_iff_leftFractionRel]
  refine ⟨t.right, 𝟙 _, f.right, ?_, ?_, ?_⟩
  · simpa [φ, ψ, ht, hs] using (Under.w f).symm
  · simp [φ, ψ]
  · simpa [φ, ht] using hht

/-- The cocone over the `Y / W` hom diagram whose point is the localized hom-set
`Hom_{W^{-1} C}(X, Y)`. -/
noncomputable def leftLocalizationHomCocone
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    Cocone (leftLocalizationHomDiagram W X Y) where
  pt := (Localization.Q W).obj X ⟶ (Localization.Q W).obj Y
  ι :=
    { app := leftLocalizationHomCoconeApp W X Y
      naturality := fun _ _ f ↦ leftLocalizationHomCocone_naturality W X Y f }

theorem leftLocalizationHomCoconeTypes_isColimit
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    let F : (Y / W) ⥤ Type (max u v) := leftLocalizationHomDiagram W X Y
    let c : F.CoconeTypes := F.coconeTypesEquiv.symm (leftLocalizationHomCocone W X Y)
    c.IsColimit := by
  let F : (Y / W) ⥤ Type (max u v) := leftLocalizationHomDiagram W X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (leftLocalizationHomCocone W X Y)
  refine ⟨?_⟩
  constructor
  · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered]
    intro s t f g hfg
    let hs : Y ⟶ s.right := by
      simpa using s.hom
    have hhs : W hs := by
      simpa [hs] using s.prop
    let ht : Y ⟶ t.right := by
      simpa using t.hom
    have hht : W ht := by
      simpa [ht] using t.prop
    let φ : W.LeftFraction X Y := LeftFraction.mk f.down hs hhs
    let ψ : W.LeftFraction X Y := LeftFraction.mk g.down ht hht
    change leftLocalizationHomCoconeApp W X Y s f = leftLocalizationHomCoconeApp W X Y t g at hfg
    dsimp [leftLocalizationHomCoconeApp, φ, ψ] at hfg
    obtain ⟨Z, a, b, hab, hfg', hW⟩ :=
      (LeftFraction.Localization.homMk_eq_iff_leftFractionRel φ ψ).mp hfg
    let u : Y / W := Under.mk (⊤ : MorphismProperty C) (s.hom ≫ a) hW
    refine ⟨u, ?_, ?_, ?_⟩
    · exact Under.homMk a rfl
    · exact Under.homMk b (by simpa [u] using hab.symm)
    change ULift.up (f.down ≫ a) = ULift.up (g.down ≫ b)
    simpa using hfg'
  · rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    change ∀ z : ((Localization.Q W).obj X ⟶ (Localization.Q W).obj Y),
      ∃ s x, leftLocalizationHomCoconeApp W X Y s x = z
    intro z
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction (Localization.Q W) W z
    let s : Y / W := Under.mk (⊤ : MorphismProperty C) φ.s φ.hs
    refine ⟨s, ULift.up φ.f, ?_⟩
    change LeftFraction.Localization.homMk (LeftFraction.mk φ.f φ.s φ.hs) = z
    rw [LeftFraction.Localization.homMk_eq]
    simpa using hφ.symm

/-- The cocone `leftLocalizationHomCocone W X Y` is a colimit cocone. -/
noncomputable def leftLocalizationHomCocone_isColimit
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    IsColimit (leftLocalizationHomCocone W X Y) := by
  let F : (Y / W) ⥤ Type (max u v) := leftLocalizationHomDiagram W X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (leftLocalizationHomCocone W X Y)
  have hc : c.IsColimit := by
    simpa [F, c] using leftLocalizationHomCoconeTypes_isColimit W X Y
  exact Nonempty.some <| by
    simpa [c] using (Functor.CoconeTypes.isColimit_iff c).mp hc

/-- Remark 4.27.7, formula 4.27.7.1: for a left multiplicative system `W`, the localized
Hom-set `Hom_{W^{-1} C}(X, Y)` is canonically isomorphic to the colimit over `Y / W` of the
Hom-sets `Hom_C(X, Y')`, where `s : Y ⟶ Y'` ranges over arrows of `W`. -/
noncomputable def left_localization_hom_colimit
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    let F : (Y / W) ⥤ Type (max u v) :=
      Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
        uliftCoyoneda.{u}.obj (Opposite.op X)
    colimit F ≅ ((Localization.Q W).obj X ⟶ (Localization.Q W).obj Y) := by
  let F : (Y / W) ⥤ Type (max u v) := leftLocalizationHomDiagram W X Y
  let c : ColimitCocone F :=
    ⟨leftLocalizationHomCocone W X Y, leftLocalizationHomCocone_isColimit W X Y⟩
  let _ : HasColimit F := HasColimit.mk c
  change colimit F ≅ c.cocone.pt
  simpa [F, leftLocalizationHomDiagram] using colimit.isoColimitCocone c

end MorphismProperty
end CategoryTheory
