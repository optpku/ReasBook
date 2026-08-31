module

public import stacks_project.Chap04.Definition_4_22_2
public import Mathlib.CategoryTheory.Filtered.Final

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor.Final

universe uI vI uJ vJ uC vC

/- Domain-style sampling for Lemma 4.22.11:
- primary domain: filtered diagrams, essential constancy, and invariance under pullback along a
  final functor.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredDiagram`,
  `isEssentiallyConstantFilteredCocone_iff`,
  `Functor.Final.extendCocone`,
  `Functor.Final.final_iff_of_isFiltered`.
- best owner abstraction for the main proposition:
  `IsEssentiallyConstantFilteredDiagram M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cocone with a distinguished split leg and the
  eventual factorization data from `isEssentiallyConstantFilteredCocone_iff`.
- derived API: pullback of cocones by `Cocone.whisker`, extension along a final functor by
  `Functor.Final.extendCocone`, and the final-functor lifting/equalization data supplied by
  `Functor.Final.final_iff_of_isFiltered` and `Functor.Final.exists_coeq`.

Source/core/bridge triage:
- `source-facing`: the textbook claim that essential constancy is preserved and reflected by
  pullback along a cofinal functor.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram`.
- `bridge/view`: `Functor.Final.extendCocone`, `Functor.Final.extendCocone_obj_ι_app'`,
  `Functor.Final.colimit_cocone_comp_aux`, and the filtered-form finality criteria. -/

private theorem essentiallyConstantFilteredCocone_whisker_final
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] {M : J ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) :
    IsEssentiallyConstantFilteredCocone (c.whisker H) := by
  let _ : IsFiltered J := IsFiltered.of_final H
  rcases (isEssentiallyConstantFilteredCocone_iff c).mp hc with ⟨j₀, s, hs, hfac⟩
  obtain ⟨i₀, ⟨f₀⟩⟩ := ((Functor.final_iff_of_isFiltered H).mp
    (show H.Final from inferInstance)).1 j₀
  rw [isEssentiallyConstantFilteredCocone_iff]
  refine ⟨i₀, s ≫ M.map f₀, ?_, ?_⟩
  · change (s ≫ M.map f₀) ≫ c.ι.app (H.obj i₀) = 𝟙 c.pt
    have hw₀ : s ≫ M.map f₀ ≫ c.ι.app (H.obj i₀) = s ≫ c.ι.app j₀ := by
      have hw := congrArg (fun g ↦ s ≫ g) (c.w f₀)
      simpa only [Category.assoc] using hw
    simpa [Category.assoc] using hw₀.trans hs
  · intro j
    rcases hfac (H.obj j) with ⟨k, α, β, hβ⟩
    obtain ⟨i, ⟨u⟩⟩ := ((Functor.final_iff_of_isFiltered H).mp
      (show H.Final from inferInstance)).1 k
    let m := IsFiltered.max i₀ i
    let p : i₀ ⟶ m := IsFiltered.leftToMax i₀ i
    let q : i ⟶ m := IsFiltered.rightToMax i₀ i
    obtain ⟨n, r, hr⟩ := Functor.Final.exists_coeq H (f₀ ≫ H.map p) (α ≫ u ≫ H.map q)
    let m' := IsFiltered.max j n
    let a : j ⟶ m' := IsFiltered.leftToMax j n
    let b : n ⟶ m' := IsFiltered.rightToMax j n
    obtain ⟨n', r', hr'⟩ := Functor.Final.exists_coeq H (H.map a)
      (β ≫ u ≫ H.map q ≫ H.map r ≫ H.map b)
    refine ⟨n', p ≫ r ≫ b ≫ r', a ≫ r', ?_⟩
    change M.map (H.map (a ≫ r')) =
      c.ι.app (H.obj j) ≫ (s ≫ M.map f₀) ≫ M.map (H.map (p ≫ r ≫ b ≫ r'))
    calc
      M.map (H.map (a ≫ r')) = M.map (H.map a ≫ H.map r') := by
        simp [Functor.map_comp]
      _ = M.map (β ≫ u ≫ H.map q ≫ H.map r ≫ H.map b ≫ H.map r') := by
        simpa [Functor.map_comp, Category.assoc] using congrArg (fun f ↦ M.map f) hr'
      _ = M.map β ≫ M.map u ≫ M.map (H.map q) ≫ M.map (H.map r) ≫
          M.map (H.map b) ≫ M.map (H.map r') := by
        simp [Functor.map_comp]
      _ = c.ι.app (H.obj j) ≫ s ≫ M.map α ≫ M.map u ≫ M.map (H.map q) ≫
          M.map (H.map r) ≫ M.map (H.map b) ≫ M.map (H.map r') := by
        simpa [Functor.map_comp, Category.assoc] using congrArg
          (fun f ↦ f ≫ M.map u ≫ M.map (H.map q) ≫ M.map (H.map r) ≫
            M.map (H.map b) ≫ M.map (H.map r')) hβ
      _ = c.ι.app (H.obj j) ≫ (s ≫ M.map f₀) ≫ M.map (H.map (p ≫ r ≫ b ≫ r')) := by
        have hfr := congrArg (fun f ↦ M.map f ≫ M.map (H.map b) ≫ M.map (H.map r')) hr.symm
        simp only [Functor.const_obj_obj, Functor.map_comp, Category.assoc] at hfr ⊢
        rw [hfr]

private theorem essentiallyConstantFilteredCocone_of_whisker_final
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] {M : J ⥤ C} {c : Cocone (H ⋙ M)}
    (hc : IsEssentiallyConstantFilteredCocone c) :
    IsEssentiallyConstantFilteredCocone (extendCocone.obj c) := by
  rw [isEssentiallyConstantFilteredCocone_iff] at hc ⊢
  rcases hc with ⟨i₀, s, hs, hfac⟩
  refine ⟨H.obj i₀, s, ?_, ?_⟩
  · have hw₀ : s ≫ (extendCocone.obj c).ι.app (H.obj i₀) = s ≫ c.ι.app i₀ := by
      simpa using congrArg (fun g ↦ s ≫ g) (colimit_cocone_comp_aux c i₀)
    simpa [hs] using hw₀.trans hs
  · intro j
    obtain ⟨i, ⟨f⟩⟩ := ((Functor.final_iff_of_isFiltered H).mp
      (show H.Final from inferInstance)).1 j
    rcases hfac i with ⟨k, α, β, hβ⟩
    refine ⟨H.obj k, H.map α, f ≫ H.map β, ?_⟩
    change M.map (f ≫ H.map β) =
      (extendCocone.obj c).ι.app j ≫ s ≫ M.map (H.map α)
    rw [extendCocone_obj_ι_app' c f]
    simpa [Functor.map_comp, Category.assoc] using congrArg (fun g ↦ M.map f ≫ g) hβ

-- Proof sketch: the source-facing data for an essentially constant cocone transport directly
-- along `Cocone.whisker` and `Functor.Final.extendCocone`. The only extra work is that, on the
-- whiskered side, the distinguished stage and the eventual factorization data must be moved into
-- the image of the final functor using the filtered-form criteria `Functor.final_iff_of_isFiltered`
-- and `Functor.Final.exists_coeq`.
/-- Lemma 4.22.11: for a cofinal functor `H : I ⥤ J` between filtered index categories, a diagram
`M : J ⥤ C` is essentially constant if and only if its pullback `H ⋙ M` is essentially constant. -/
theorem essentiallyConstantFilteredDiagram_iff_comp_final
    {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] (M : J ⥤ C) :
    IsEssentiallyConstantFilteredDiagram M ↔
      IsEssentiallyConstantFilteredDiagram (H ⋙ M) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.whisker H, essentiallyConstantFilteredCocone_whisker_final H hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨extendCocone.obj c, essentiallyConstantFilteredCocone_of_whisker_final H hc⟩
