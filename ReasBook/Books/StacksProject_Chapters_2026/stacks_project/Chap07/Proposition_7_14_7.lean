module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import stacks_project.Chap07.Definition_7_14_1
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Proposition 7.14.7:
- primary domain: Grothendieck topologies, continuous functors, finite-limit preservation, and
  morphisms of sites;
- sampled owner API:
  `preservesTerminal_of_iso`,
  `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`,
  `flat_of_preservesFiniteLimits`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`;
- source/core/bridge triage:
  `source-facing`: the explicit final-object and pullback hypotheses from the Stacks statement;
  `core/canonical`: `PreservesFiniteLimits u`;
  `bridge/view`: the theorems below transferring the source hypotheses first to finite-limit
    preservation, then onward to `RepresentablyFlat u` and `IsMorphismOfSites J K u`.

Primitive data here are only continuity together with terminal-object and pullback preservation.
Terminal preservation, finite-limit preservation, representable flatness, and the site-morphism
structure are derived owner API, so the file should expose only the source-facing bridges to those
canonical owners. -/

-- Proof sketch: choose `X` as the terminal object of `C` and `u.obj X` as the terminal object of
-- `D`; the induced comparison `u.obj (⊤_ C) ≅ ⊤_ D` then gives preservation of the empty-diagram
-- limit via `preservesTerminal_of_iso`.
/-- An explicit terminal object whose image is terminal induces terminal-object preservation. -/
theorem preservesTerminal_of_terminal_and_image_terminal
    (u : C ⥤ D) (X : C) (hX : IsTerminal X) (huX : IsTerminal (u.obj X)) :
    PreservesLimit (Functor.empty.{0} C) u := by
  let _ : HasTerminal C := hX.hasTerminal
  let _ : HasTerminal D := huX.hasTerminal
  exact preservesTerminal_of_iso u <|
    u.mapIso (terminalIsoIsTerminal hX) ≪≫ (terminalIsoIsTerminal huX).symm

-- Proof sketch: terminal-object preservation upgrades to preservation of `Discrete PEmpty`-shaped
-- limits, and together with pullback preservation this is exactly the canonical theorem
-- `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`.
private theorem preservesFiniteLimits_of_terminal_and_pullbacks
    (u : C ⥤ D) [HasTerminal C] [HasPullbacks C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    PreservesFiniteLimits u := by
  let _ : PreservesLimitsOfShape (Discrete PEmpty) u :=
    preservesLimitsOfShape_pempty_of_preservesTerminal u
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks u

-- Proof sketch: terminal preservation and pullback preservation yield finite-limit preservation,
-- hence `u` is representably flat. For a continuous functor,
-- this is exactly the extra hypothesis needed for the canonical instance
-- `isMorphismOfSites_of_isContinuous_representablyFlat`.
/-- Proposition 7.14.7 in canonical form: a continuous functor that preserves terminal objects and
pullbacks defines a morphism of sites `(\mathcal D, K) ⟶ (\mathcal C, J)`. -/
theorem isMorphismOfSites_of_preservesTerminal_and_pullbacks
    (u : C ⥤ D) [u.IsContinuous J K]
    [HasTerminal C] [HasPullbacks C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := by
  let _ : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let _ : PreservesFiniteLimits u := preservesFiniteLimits_of_terminal_and_pullbacks u
  let _ : RepresentablyFlat u :=
    flat_of_preservesFiniteLimits u
  exact isMorphismOfSites_of_isContinuous_representablyFlat J K u

-- Proof sketch: the textbook hypotheses imply preservation of the terminal object, so the
-- canonical finite-limit-preservation theorem applies and hence `flat_of_preservesFiniteLimits`
-- yields representable flatness.
/-- Textbook-form bridge from an explicit final object and pullback preservation to representable
flatness. -/
theorem representablyFlat_of_terminal_and_pullbacks
    (u : C ⥤ D) (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    RepresentablyFlat u := by
  let _ : HasTerminal C := hX.hasTerminal
  let _ : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let _ : PreservesLimit (Functor.empty.{0} C) u :=
    preservesTerminal_of_terminal_and_image_terminal u X hX huX
  let _ : PreservesFiniteLimits u := preservesFiniteLimits_of_terminal_and_pullbacks u
  exact flat_of_preservesFiniteLimits u

-- Proof sketch: a chosen terminal object `X` equips `C` with a terminal object, and `u.obj X`
-- equips `D` with one. The induced isomorphism `u.obj (⊤_ C) ≅ ⊤_ D` gives preservation of the
-- terminal object, so the canonical proposition above applies.
/-- Textbook-form bridge for Proposition 7.14.7, using an explicit final object `X` whose image is
final. -/
theorem isMorphismOfSites_of_terminal_and_pullbacks
    (u : C ⥤ D) [u.IsContinuous J K] (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := by
  let _ : HasTerminal C := hX.hasTerminal
  let _ : PreservesLimit (Functor.empty.{0} C) u :=
    preservesTerminal_of_terminal_and_image_terminal u X hX huX
  exact isMorphismOfSites_of_preservesTerminal_and_pullbacks u

end
