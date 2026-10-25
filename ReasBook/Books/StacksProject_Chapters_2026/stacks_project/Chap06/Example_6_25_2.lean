module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import stacks_project.Chap06.Example_6_9_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open TopCat.Sheaf

noncomputable section

/- Domain-style sampling for Example 6.25.2:
- primary domain: morphisms of sheaves of continuous real-valued functions along a continuous map;
- sampled owner declarations:
  `continuousRealFunctionsSheaf`,
  `TopCat.Sheaf.pushforward`,
  `ContinuousMap.compRightAlgHom`,
  `ObjectProperty.homMk`;
- best owner abstraction: the canonical `f`-map is a morphism in the sheaf category
  `continuousRealFunctionsSheaf Y ⟶
    (pushforward (CommAlgCat ℝ) f).obj (continuousRealFunctionsSheaf X)`;
- primitive data: for each open `V ⊆ Y`, the pullback algebra homomorphism
  `C⁰(V, ℝ) → C⁰(f ⁻¹' V, ℝ)` induced by `ContinuousMap.compRightAlgHom`;
- derived API: the naturality of these sectionwise maps and the resulting packaged sheaf morphism.

Source/core/bridge triage:
- `source-facing`: the induced `f^\sharp` on the sheaf of continuous real-valued functions;
- `core/canonical`: a presheaf morphism into the canonical sheaf pushforward owner;
- `bridge/view`: `ObjectProperty.homMk`, packaging the underlying presheaf morphism as a morphism
  of sheaves. -/

/-- The sectionwise pullback homomorphism on continuous real-valued functions over an open subset
of the target. -/
public def continuousRealFunctionsSheafPullbackApp {X Y : TopCat} (f : X ⟶ Y)
    (V : (Opens Y)ᵒᵖ) :
    (continuousRealFunctionsSheaf Y).presheaf.obj V ⟶
      ((pushforward (CommAlgCat ℝ) f).obj (continuousRealFunctionsSheaf X)).presheaf.obj V :=
  CommAlgCat.ofHom <|
    ContinuousMap.compRightAlgHom ℝ ℝ (f.hom.restrictPreimage (V.unop : Set Y))

public def continuousRealFunctionsPresheafFMap {X Y : TopCat} (f : X ⟶ Y) :
    (continuousRealFunctionsSheaf Y).presheaf ⟶
      ((pushforward (CommAlgCat ℝ) f).obj (continuousRealFunctionsSheaf X)).presheaf where
  app := continuousRealFunctionsSheafPullbackApp f
  naturality := fun {_ _} i ↦ by
    ext h
    rfl

/-- Example 6.25.2: a continuous map `f : X → Y` induces the canonical `f`-map
`f^\sharp : \mathcal{C}^0_Y → \mathcal{C}^0_X` of sheaves of `ℝ`-algebras, whose component on an
open `V ⊆ Y` sends a continuous function `h : V → ℝ` to the pullback `h ∘ f|_{f^{-1}(V)}`. -/
def continuous_real_functions_sheaf_f_map {X Y : TopCat} (f : X ⟶ Y) :
    continuousRealFunctionsSheaf Y ⟶
      (pushforward (CommAlgCat ℝ) f).obj (continuousRealFunctionsSheaf X) :=
  ObjectProperty.homMk (continuousRealFunctionsPresheafFMap f)

/-- The component of `continuous_real_functions_sheaf_f_map` over an open subset `V ⊆ Y` is the
sectionwise pullback homomorphism `h ↦ h ∘ f|_{f^{-1}(V)}`. -/
theorem continuous_real_functions_sheaf_f_map_app {X Y : TopCat} (f : X ⟶ Y)
    (V : (Opens Y)ᵒᵖ) :
    (continuous_real_functions_sheaf_f_map f).1.app V =
      CommAlgCat.ofHom
        (ContinuousMap.compRightAlgHom ℝ ℝ (f.hom.restrictPreimage (V.unop : Set Y))) :=
  rfl
