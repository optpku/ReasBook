module

public import stacks_project.Chap04.Definition_4_22_2
public import Mathlib.CategoryTheory.Limits.HasLimits

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory

universe uI vI uC vC

section

/- Domain-style sampling for Lemma 4.22.3:
- primary domain: essentially constant filtered/cofiltered diagrams and the resulting actual
  colimit/limit data.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredCocone.isColimit`,
  `IsEssentiallyConstantCofilteredCone.isLimit`,
  `IsEssentiallyConstantFilteredCocone`,
  `IsEssentiallyConstantFilteredDiagram`,
  `CategoryTheory.Limits.ColimitCocone`,
  `CategoryTheory.Limits.LimitCone`.
- best owner abstraction for the hypothesis: the chapter source-facing owners
  `IsEssentiallyConstantFilteredDiagram M` and `IsEssentiallyConstantCofilteredDiagram M`.
- best owner abstraction for the conclusion: `ColimitCocone M` / `LimitCone M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cocone/cone as in Definition 4.22.1.
- derived owner API: `IsEssentiallyConstantFilteredCocone.isColimit` and
  `IsEssentiallyConstantCofilteredCone.isLimit`.
- derived actual-colimit data: a colimit cocone or limit cone for `M`.
- derived duality bridge: `IsColimit.unop`, transporting the filtered cocone owner theorem to the
  cofiltered cone owner theorem.
- later bridge/view formulations via representability/corepresentability of the associated
  ind/pro-object belong to Lemmas 4.22.9 and 4.22.10, not to the main statements here.

Source/core/bridge triage:
- source-facing: the two theorems below, whose hypotheses are exactly the diagram-level notions
  from Definition 4.22.2.
- core/canonical: `ColimitCocone M` and `LimitCone M`.
- bridge/view: representability of `colimit (M ⋙ uliftYoneda)` and corepresentability of
  `limit (M.op ⋙ uliftCoyoneda)`. -/

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]

/-- Helper for Lemma 4.22.3: package an essentially constant filtered cocone as a genuine
colimit cocone without changing its underlying cocone. -/
noncomputable def filteredCoconeToColimitCocone {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) : ColimitCocone M :=
  ⟨c, hc.isColimit⟩

/-- Helper for Lemma 4.22.3: the colimit-cocone packaging preserves essential constancy of the
underlying cocone. -/
theorem filteredCoconeToColimitCocone_isEssentiallyConstant {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) :
    IsEssentiallyConstantFilteredCocone (filteredCoconeToColimitCocone hc).cocone := by
  -- Unfold the adapter: only the universal-property field was added.
  simpa [filteredCoconeToColimitCocone] using hc

/-- Helper for Lemma 4.22.3: package an essentially constant cofiltered cone as a genuine limit
cone without changing its underlying cone. -/
noncomputable def cofilteredConeToLimitCone {M : I ⥤ C} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) : LimitCone M :=
  ⟨c, hc.isLimit⟩

/-- Helper for Lemma 4.22.3: the limit-cone packaging preserves essential constancy of the
underlying cone. -/
theorem cofilteredConeToLimitCone_isEssentiallyConstant {M : I ⥤ C} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) :
    IsEssentiallyConstantCofilteredCone (cofilteredConeToLimitCone hc).cone := by
  -- Unfold the adapter: only the universal-property field was added.
  simpa [cofilteredConeToLimitCone] using hc

-- Proof sketch: choose an essentially constant cocone from Definition 4.22.2; its distinguished
-- split leg and eventual factorization data already make it colimiting.
/-- Lemma 4.22.3 (1): a diagram satisfying
`IsEssentiallyConstantFilteredDiagram` admits an essentially constant colimit cocone. -/
theorem essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone
    (M : I ⥤ C) (hM : IsEssentiallyConstantFilteredDiagram M) :
    ∃ c : ColimitCocone M, IsEssentiallyConstantFilteredCocone c.cocone := by
  -- Extract the essentially constant cocone already supplied by the definition.
  rcases hM with ⟨c, hc⟩
  -- The adapter adds only the colimit universal property.
  exact ⟨filteredCoconeToColimitCocone hc, filteredCoconeToColimitCocone_isEssentiallyConstant hc⟩

-- Proof sketch: Definition 4.22.2 already identifies cofiltered essential constancy with the
-- existence of an essentially constant cone by direct unfolding; the canonical duality bridge
-- `IsColimit.unop` then transports the filtered cocone owner theorem to a genuine limit cone.
/-- Lemma 4.22.3 (2): a diagram satisfying
`IsEssentiallyConstantCofilteredDiagram` admits an essentially constant limit cone. -/
theorem essentiallyConstantCofilteredDiagram_exists_essentiallyConstant_limitCone
    (M : I ⥤ C) (hM : IsEssentiallyConstantCofilteredDiagram M) :
    ∃ c : LimitCone M, IsEssentiallyConstantCofilteredCone c.cone := by
  -- Unpack the cone witness from the definition-level iff.
  rcases (isEssentiallyConstantCofilteredDiagram_iff_exists_essentiallyConstantCone M).1 hM with
    ⟨c, hc⟩
  -- The adapter adds only the limit universal property.
  exact ⟨cofilteredConeToLimitCone hc, cofilteredConeToLimitCone_isEssentiallyConstant hc⟩

end
