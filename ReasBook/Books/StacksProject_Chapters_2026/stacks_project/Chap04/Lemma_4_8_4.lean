module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap04.Definition_4_8_2
import Mathlib.Tactic.TFAE
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Opposite Limits Functor.relativelyRepresentable
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasPullbacks C]

/-
Source/core/bridge triage for Lemma 4.8.4:
- domain-style sampling in the presheaf representability layer:
  `Functor.relativelyRepresentable.diag_iff`,
  `yoneda.relativelyRepresentable`,
  `Limits.pullback`,
  `relativelyRepresentable_iff_isRepresentable_pullback_yoneda`,
  `yoneda.obj`;
- source-facing owner: `presheaf_diagonal_representability_tfae`;
- core/canonical owner: `Functor.relativelyRepresentable.diag_iff`;
- bridge/view API: specialize the owner-level diagonal criterion to Yoneda sections
  `ξ : h[U] ⟶ F`, then translate relative representability of each section to representability of
  the associated pullback by Definition 4.8.2.
- primitive data: only the presheaf `F`;
- derived API: relative representability of `diag F`, relative representability of each Yoneda
  section, and representability of the associated Yoneda pullbacks.
-/

/-- Helper for Lemma 4.8.4: the diagonal of a presheaf is relatively representable exactly when
every Yoneda section is relatively representable. -/
lemma diag_relativelyRepresentable_iff_forall_yoneda_section (F : Presheaf.{v} C) :
    yoneda.relativelyRepresentable (diag F) ↔
      ∀ (U : C) (ξ : h[U] ⟶ F), yoneda.relativelyRepresentable ξ := by
  -- This is the owner-level diagonal criterion specialized to presheaves.
  simpa using
    (diag_iff :
      yoneda.relativelyRepresentable (diag F) ↔
        ∀ ⦃U : C⦄ (ξ : yoneda.obj U ⟶ F), yoneda.relativelyRepresentable ξ)

omit [HasBinaryProducts C] [HasPullbacks C] in
/-- Helper for Lemma 4.8.4: a Yoneda section is relatively representable exactly when all of its
Yoneda pullbacks are representable. -/
lemma yoneda_section_relativelyRepresentable_iff_forall_pullback_isRepresentable
    {F : Presheaf.{v} C} {U : C} (ξ : h[U] ⟶ F) :
    yoneda.relativelyRepresentable ξ ↔
      ∀ (V : C) (ξ' : h[V] ⟶ F), (pullback ξ ξ').IsRepresentable := by
  -- This is Definition 4.8.2 in the special case of a section from a representable presheaf.
  simpa using relativelyRepresentable_iff_isRepresentable_pullback_yoneda ξ

/-- Lemma 4.8.4: for a presheaf `F` on a category with binary products and pullbacks, the
relative representability of the diagonal `Δ : F ⟶ F × F`, the relative representability of every
section `h_U ⟶ F`, and the representability of every fibre product `h_U ×[F] h_V` cut out by two
sections are equivalent. -/
theorem presheaf_diagonal_representability_tfae (F : Presheaf.{v} C) :
    [yoneda.relativelyRepresentable (diag F),
      ∀ (U : C) (ξ : h[U] ⟶ F), yoneda.relativelyRepresentable ξ,
      ∀ (U V : C) (ξ : h[U] ⟶ F) (ξ' : h[V] ⟶ F), (pullback ξ ξ').IsRepresentable].TFAE := by
  -- First package the diagonal criterion as the representability of every Yoneda section.
  tfae_have 1 ↔ 2 := by
    simpa using diag_relativelyRepresentable_iff_forall_yoneda_section F
  -- Next translate each relatively representable section into representable Yoneda pullbacks.
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h U V ξ ξ'
      exact (yoneda_section_relativelyRepresentable_iff_forall_pullback_isRepresentable ξ).1
        (h U ξ) V ξ'
    · intro h U ξ
      exact (yoneda_section_relativelyRepresentable_iff_forall_pullback_isRepresentable ξ).2
        (fun V ξ' ↦ h U V ξ ξ')
  -- The two equivalences assemble into the required TFAE statement.
  tfae_finish

end CategoryTheory
