module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_21_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w vC vD uC uD

noncomputable section

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D)
variable [u.Full] [u.Faithful]

/- Domain-style sampling for Lemma 7.21.8:
- primary domain: adjunction criteria for fully faithful lower-shriek functors on sheaf
  categories induced by fully faithful continuous functors of sites;
- sampled owner API:
  `Functor.sheafAdjunctionContinuous`,
  `NatIso.isIso_of_isIso_app`,
  `Adjunction.fullyFaithfulLOfIsIsoUnit`,
  `Functor.FullyFaithful`;
- source-facing layer: the Stacks statement that the unit `𝟭 ⟶ g⁻¹ g_!` is an isomorphism and
  therefore `g_!` is full and faithful for a fully faithful continuous functor of sites;
- core/canonical owner: the adjunction `u.sheafAdjunctionContinuous (Type w) J K` and the bundled
  functor property `(u.sheafPullback (Type w) J K).FullyFaithful`;
- bridge/view: Lemma 7.21.7 gives the componentwise `IsIso` owner data on the unit, which this
  file promotes to an `IsIso` statement on the whole unit and then to the bundled full-faithfulness
  owner of the left adjoint.

Primitive data are the site functor `u`, its full faithfulness, continuity, and the lower-shriek
construction data `HasWeakSheafify K (Type w)` together with
`∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P`. The chosen
right-adjoint structure on `u.sheafPushforwardContinuous (Type w) J K`, the unit `IsIso`, and the
bundled `FullyFaithful` fact are derived API of that owner, so the public surface should center the
adjunction and functor owners rather than a parallel proposition-level `Full ∧ Faithful` package.
-/

section

variable [u.IsContinuous J K]
variable [u.IsCocontinuous J K]
variable [HasWeakSheafify K (Type w)]
variable [HasWeakSheafify J (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]

-- Proof sketch: by Lemma 7.21.5, `u.sheafPullback (Type w) J K` is the source-facing lower
-- shriek `g_!`, while `u.sheafPushforwardContinuous (Type w) J K` is the inverse-image `g⁻¹`.
-- Lemma 7.21.7 makes each component of the unit `𝟭 ⟶ g⁻¹ g_!` an isomorphism, and
-- `NatIso.isIso_of_isIso_app` upgrades this to an isomorphism of natural transformations.
/-- Lemma 7.21.8 (1): for a fully faithful continuous functor of sites, the canonical map
`ℱ ⟶ g⁻¹(g_! ℱ)`, i.e. the unit of
`u.sheafPullback (Type w) J K ⊣ u.sheafPushforwardContinuous (Type w) J K`, is an isomorphism. -/
instance isIso_unit_sheafAdjunctionContinuous_of_fullyFaithful :
    IsIso (u.sheafAdjunctionContinuous (Type w) J K).unit :=
  NatIso.isIso_of_isIso_app _

-- Proof sketch: apply the standard adjunction criterion that a left adjoint is fully faithful as
-- soon as the unit is an isomorphism.
/-- Lemma 7.21.8 (2): under the same hypotheses, the lower shriek functor
`g_!`, realized by `u.sheafPullback (Type w) J K`, is fully faithful. -/
instance fullyFaithful_sheafPullback_of_fullyFaithful :
    (u.sheafPullback (Type w) J K).FullyFaithful :=
  (u.sheafAdjunctionContinuous (Type w) J K).fullyFaithfulLOfIsIsoUnit

end
