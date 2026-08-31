module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/- Domain-style sampling for Lemma 4.33.3:
- primary domain: strongly cartesian morphisms for functors and their behavior under composition;
- sampled owner declarations:
  `IsStronglyCartesian`,
  `comp`,
  `of_comp`,
  `map_comp_map`;
- best owner abstraction: `Functor.IsStronglyCartesian`;
- primitive data: a functor pair `F : A ⥤ B`, `G : B ⥤ C`, a morphism `φ : x ⟶ y`, and the two
  strongly cartesian hypotheses for `φ` over `F` and `F.map φ` over `G`;
- derived API: the induced strongly cartesian structure for `φ` over the composite functor
  `F ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that strong cartesianness is stable under functor
  composition;
- `core/canonical`: the owner predicate `Functor.IsStronglyCartesian`;
- `bridge/view`: none; this file supplies the source-facing functor-composition theorem directly in
  the owner namespace so downstream files reuse one public result instead of carrying private
  duplicates. -/

-- Proof sketch: given a lift `τ` over `g ≫ G.map (F.map φ)`, first use the strong cartesianness
-- of `F.map φ` for `G` to obtain a lift `δ : F.obj a' ⟶ F.obj a` of `g`, then use the strong
-- cartesianness of `φ` for `F` to lift `δ` to `χ : a' ⟶ a`. The universal properties for `G` and
-- `F` then identify `χ` as the unique lift over `g` for the composite functor `F ⋙ G`.
/-- Helper for Lemma 4.33.3: a lift for the composite functor yields a lift for `G` after applying
`F`. -/
private lemma mapped_isHomLift_of_comp_isHomLift
    (F : A ⥤ B) (G : B ⥤ C) {a a' : A}
    {g : G.obj (F.obj a') ⟶ G.obj (F.obj a)} {π : a' ⟶ a}
    (hπ : (F ⋙ G).IsHomLift g π) :
    G.IsHomLift g (F.map π) := by
  -- Rewriting the composite-functor lift equation exposes the outer lift directly.
  refine IsHomLift.of_fac G g (F.map π) rfl rfl ?_
  simpa [Functor.comp_map] using
    (@IsHomLift.fac' _ _ _ _ (F ⋙ G) _ _ _ _ g π hπ).symm

/-- Helper for Lemma 4.33.3: composing the lifts through `F` and `G` gives a lift for `F ⋙ G`. -/
private lemma comp_isHomLift_of_component_lifts
    (F : A ⥤ B) (G : B ⥤ C) {a a' : A}
    {g : G.obj (F.obj a') ⟶ G.obj (F.obj a)}
    {δ : F.obj a' ⟶ F.obj a} {χ : a' ⟶ a}
    (hδ : G.IsHomLift g δ) (hχ : F.IsHomLift δ χ) :
    (F ⋙ G).IsHomLift g χ := by
  -- The base map of the composite lift is the composite of the two component base maps.
  refine IsHomLift.of_fac (F ⋙ G) g χ rfl rfl ?_
  have hδ' : G.map δ = g := by
    simpa using (@IsHomLift.fac' _ _ _ _ G _ _ _ _ g δ hδ)
  have hχ' : F.map χ = δ := by
    simpa using (@IsHomLift.fac' _ _ _ _ F _ _ _ _ δ χ hχ)
  simpa using
    calc
      g = G.map δ := hδ'.symm
      _ = G.map (F.map χ) := by rw [hχ'.symm]

/-- Lemma 4.33.3: if `φ : a ⟶ b` is strongly cartesian for `F : A ⥤ B` and `F.map φ` is strongly
cartesian for `G : B ⥤ C`, then `φ` is strongly cartesian for the composite functor `F ⋙ G`. -/
theorem isStronglyCartesian_map_comp
    (F : A ⥤ B) (G : B ⥤ C) {a b : A} (φ : a ⟶ b)
    [F.IsStronglyCartesian (F.map φ) φ]
    [G.IsStronglyCartesian (G.map (F.map φ)) (F.map φ)] :
    (F ⋙ G).IsStronglyCartesian ((F ⋙ G).map φ) φ := by
  refine
    { toIsHomLift := by
        exact IsHomLift.map φ
      universal_property' := ?_ }
  intro a' g τ hτ
  have hτG :
      G.IsHomLift (g ≫ G.map (F.map φ)) (F.map τ) :=
    mapped_isHomLift_of_comp_isHomLift F G hτ
  have hτfac : G.map (F.map τ) = g ≫ G.map (F.map φ) := by
    simpa using
      (@IsHomLift.fac' _ _ _ _ G _ _ _ _ (g ≫ G.map (F.map φ)) (F.map τ) hτG)
  -- First lift `F.map τ` through `G` to produce the middle-stage base morphism.
  let δ : F.obj a' ⟶ F.obj a :=
    IsStronglyCartesian.map G (G.map (F.map φ)) (F.map φ) hτfac (F.map τ)
  have hδlift : G.IsHomLift g δ := by
    dsimp [δ]
    infer_instance
  have hδ : δ ≫ F.map φ = F.map τ := by
    dsimp [δ]
    exact IsStronglyCartesian.fac G (G.map (F.map φ)) (F.map φ) hτfac (F.map τ)
  -- Then lift `δ` through `F` to obtain the desired composite lift upstairs.
  let χ : a' ⟶ a :=
    IsStronglyCartesian.map F (F.map φ) φ hδ.symm τ
  have hχlift : F.IsHomLift δ χ := by
    dsimp [χ]
    infer_instance
  have hχ : χ ≫ φ = τ := by
    dsimp [χ]
    exact IsStronglyCartesian.fac F (F.map φ) φ hδ.symm τ
  have hχcomp : (F ⋙ G).IsHomLift g χ :=
    comp_isHomLift_of_component_lifts F G hδlift hχlift
  refine ⟨χ, ⟨hχcomp, hχ⟩, ?_⟩
  intro π hπ
  -- Uniqueness follows by comparing first after applying `F`, then upstairs over `A`.
  have hπG : G.IsHomLift g (F.map π) :=
    mapped_isHomLift_of_comp_isHomLift F G hπ.1
  have hFπ : F.map π = δ := by
    -- The two candidate `G`-lifts agree because they have the same composite with `F.map φ`.
    exact
      @IsStronglyCartesian.ext _ _ _ _ G _ _ _ _
        (G.map (F.map φ)) (F.map φ) inferInstance _ _ g (F.map π) δ hπG hδlift <| by
          calc
            F.map π ≫ F.map φ = F.map (π ≫ φ) := by
              simp
            _ = F.map τ := by
              rw [hπ.2]
            _ = δ ≫ F.map φ := hδ.symm
  have hπF : F.IsHomLift δ π := by
    refine IsHomLift.of_fac F δ π rfl rfl ?_
    simpa using hFπ.symm
  -- Comparing the two lifts through `F` proves uniqueness in `A`.
  exact
    @IsStronglyCartesian.ext _ _ _ _ F _ _ _ _
      (F.map φ) φ inferInstance _ _ δ π χ hπF hχlift <| by
        rw [hπ.2, hχ]

end CategoryTheory.Functor
