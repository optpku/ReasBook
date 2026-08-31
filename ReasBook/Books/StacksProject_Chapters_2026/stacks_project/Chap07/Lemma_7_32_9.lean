module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_32_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace MorphismOfTopoiIn

/- Source/core/bridge triage for Lemma 7.32.9:
- source-facing item: the canonical section of the counit map `(p_* E)_p → E`
- core/canonical owner: the derived adjunction `p.typeAdjunction`
- derived API used here: terminality of `Type` together with preservation of terminal objects by the
  left adjoint `p.typeInverseImage`
-/

-- Proof sketch: the backward map is the canonical counit `p.typeAdjunction.counit.app E`. For the
-- forward map, send `e : E` through the morphism `PUnit ⟶ E` picking out `e`, apply the
-- endofunctor `p_* ⋙ p⁻¹`, and use that the counit is an isomorphism on the terminal object.
-- Naturality of the counit and the triangle identity then show that the composite back to `E` is
-- the identity.
variable (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w})

/-- Helper for Lemma 7.32.9: the endofunctor on `Type` given by first pushing forward along the
point and then taking the fiber at that point. -/
abbrev pointPushforwardFiberEndofunctor : Type w ⥤ Type w :=
  p.typePushforward ⋙ p.typeInverseImage

/-- Helper for Lemma 7.32.9: the `Type`-valued inverse image of a point preserves finite limits,
transporting the left exactness of the underlying inverse image functor. -/
instance typeInverseImagePreservesFiniteLimits :
    PreservesFiniteLimits p.typeInverseImage := by
  -- Expose the bundled left exactness of `p⁻¹` through the `Type`-valued presentation.
  letI : PreservesFiniteLimits (p⁻¹) := by
    simpa using MorphismOfTopoiIn.inverseImage_preservesFiniteLimits p
  letI : PreservesFiniteLimits typeEquiv.{w}.inverse := by
    letI : PreservesLimits typeEquiv.{w}.inverse :=
      typeEquiv.{w}.toAdjunction.rightAdjoint_preservesLimits
    infer_instance
  change PreservesFiniteLimits ((p⁻¹) ⋙ typeEquiv.{w}.inverse)
  exact comp_preservesFiniteLimits (p⁻¹) typeEquiv.{w}.inverse

/-- Helper for Lemma 7.32.9: the composite `p_* ⋙ p⁻¹` preserves finite limits, so it sends the
terminal object to a terminal object. -/
instance pointPushforwardFiberEndofunctorPreservesFiniteLimits :
    PreservesFiniteLimits (pointPushforwardFiberEndofunctor p) := by
  -- The pushforward preserves limits as a right adjoint, and the inverse image is left exact.
  letI : PreservesLimits p.typePushforward :=
    p.typeAdjunction.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits p.typePushforward := by infer_instance
  letI : PreservesFiniteLimits p.typeInverseImage := typeInverseImagePreservesFiniteLimits p
  change PreservesFiniteLimits (p.typePushforward ⋙ p.typeInverseImage)
  exact comp_preservesFiniteLimits p.typePushforward p.typeInverseImage

/-- Helper for Lemma 7.32.9: the terminal object remains terminal after applying
`p_* ⋙ p⁻¹` to `PUnit`. -/
noncomputable def pointPushforwardFiberTerminalIso :
    (pointPushforwardFiberEndofunctor p).obj PUnit.{w + 1} ≅ PUnit.{w + 1} :=
  ((pointPushforwardFiberEndofunctor p).mapIso Types.terminalIso).symm ≪≫
    PreservesTerminal.iso (pointPushforwardFiberEndofunctor p) ≪≫
    Types.terminalIso

/-- Helper for Lemma 7.32.9: the distinguished point of `(p_* PUnit)_p`, obtained from terminality.
-/
noncomputable def pointPushforwardFiberTerminalPoint :
    (pointPushforwardFiberEndofunctor p).obj PUnit.{w + 1} :=
  (pointPushforwardFiberTerminalIso p).inv PUnit.unit

/-- Helper for Lemma 7.32.9: the counit of the transported adjunction
`p.typeInverseImage ⊣ p.typePushforward`. -/
abbrev pointPushforwardFiberCounit :
    pointPushforwardFiberEndofunctor p ⟶ 𝟭 (Type w) :=
  p.typeAdjunction.counit

/-- The canonical section `E → (p_* E)_p = p^{-1}(p_* E)` from Lemma 7.32.9. -/
def pointPushforwardFiberSection (E : Type w) :
    E → p.typeInverseImage.obj (p.typePushforward.obj E) :=
  fun e ↦
    (pointPushforwardFiberEndofunctor p).map (fun _ : PUnit.{w + 1} ↦ e)
      (pointPushforwardFiberTerminalPoint p)

/-- Lemma 7.32.9: for a point `p` of the topos `Sh(C)` and a set `E`, the canonical counit map
`(p_* E)_p = p^{-1} p_* E → E` admits the canonical section
`pointPushforwardFiberSection p E`. -/
theorem pointPushforwardFiber_counit_leftInverse (E : Type w) :
    Function.LeftInverse ((pointPushforwardFiberCounit p).app E) (pointPushforwardFiberSection p E) := by
  intro e
  -- Evaluate counit naturality on the constant map `PUnit ⟶ E` picking out `e`.
  simpa [pointPushforwardFiberSection] using
    congrFun
      ((pointPushforwardFiberCounit p).naturality (fun _ : PUnit.{w + 1} ↦ e))
      (pointPushforwardFiberTerminalPoint p)

/-- The counit map `p^{-1}(p_* E) → E` from Lemma 7.32.9 is split epic, with section
`pointPushforwardFiberSection p E`. -/
theorem pointPushforwardFiber_counit_isSplitEpi (E : Type w) :
    IsSplitEpi ((pointPushforwardFiberCounit p).app E) := by
  -- A morphism with a left inverse is surjective, hence split epic in `Type`.
  exact (CategoryTheory.isSplitEpi_iff_surjective _).2 <|
    Function.LeftInverse.surjective (pointPushforwardFiber_counit_leftInverse p E)

end MorphismOfTopoiIn

end CategoryTheory

end
