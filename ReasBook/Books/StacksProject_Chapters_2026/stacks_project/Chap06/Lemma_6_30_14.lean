module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import stacks_project.Chap06.Definition_6_30_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe w v u

section

variable {C : Type u} [Category.{v} C]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable {ℱ : TopCat.Sheaf C X} {𝒢 : TopCat.Sheaf C Y}
variable {B : Set (Opens Y)} (hB : Opens.IsBasis B)

/-
Domain-style sampling for Lemma 6.30.14:
- primary domain: dense-subsite comparison for sheaves on a topological basis, specialized to the
  basis restriction of a pushforward sheaf;
- sampled owner declarations:
  `Functor.sheafPushforwardContinuous`,
  `basisOpenInclusion_isCoverDense`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`,
  `Functor.Full.map_surjective`,
  `Functor.Faithful.map_injective`;
- best owner abstraction: the canonical basis-restriction functor
  `(basisOpenInclusion B).sheafPushforwardContinuous C
    (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y)`;
- primitive data: the sheaves `𝒢`, `(Sheaf.pushforward C f).obj ℱ`, and the basis-restriction
  functor itself;
- derived API: bijectivity of the functorial map on morphisms, equivalently the canonical Hom
  equivalence between global morphisms and basis-restriction morphisms, with the unique-extension
  statement as a companion corollary.

Source/core/bridge triage:
- `source-facing`: the unique extension of a compatible basis morphism to a global `f`-map;
- `core/canonical`: the dense-subsite restriction functor above and its full/faithful morphism
  map;
- `bridge/view`: the basis-site morphism `φB`.
-/
public instance :
    Functor.IsContinuous (basisOpenInclusion B)
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y) := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology Y) :=
    basisOpenInclusion_isCoverDense hB
  exact
    Functor.IsCoverDense.isContinuous
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y) (basisOpenInclusion B)
      (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
        (Opens.grothendieckTopology Y))

/- Lemma 6.30.14, owner form: restriction to a basis `B` of `Y` identifies morphisms
`𝒢 ⟶ f_* ℱ` with morphisms between the basis restrictions of `𝒢` and `f_* ℱ` through the
canonical Hom equivalence induced by the basis-restriction functor. -/
#check
  (by
    let H := (Sheaf.pushforward C f).obj ℱ
    let G := (basisOpenInclusion B).sheafPushforwardContinuous C
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y)
    letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology Y) :=
      basisOpenInclusion_isCoverDense hB
    exact
      (show (G.obj 𝒢 ⟶ G.obj H) ≃ (𝒢 ⟶ H) from
        (Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm))

/-- Lemma 6.30.14 companion: a morphism between the basis restrictions of `𝒢` and `f_* ℱ`
extends uniquely to a global morphism `𝒢 ⟶ f_* ℱ`. Unpacked sectionwise, this is the Stacks
Project formulation by a compatible family of morphisms `𝒢(V) ⟶ ℱ(f⁻¹ V)` on the basis opens. -/
theorem existsUnique_pushforward_hom_of_basis_restriction
    (φB :
      ((basisOpenInclusion B).sheafPushforwardContinuous C
          (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y)).obj 𝒢 ⟶
        ((basisOpenInclusion B).sheafPushforwardContinuous C
          (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y)).obj
          ((Sheaf.pushforward C f).obj ℱ)) :
    ∃! Φ : 𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ,
      ((basisOpenInclusion B).sheafPushforwardContinuous C
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y)).map Φ = φB := by
  let H := (Sheaf.pushforward C f).obj ℱ
  let G := (basisOpenInclusion B).sheafPushforwardContinuous C
    (basisGrothendieckTopology B hB) (Opens.grothendieckTopology Y)
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology Y) :=
    basisOpenInclusion_isCoverDense hB
  change ∃! Φ : 𝒢 ⟶ H, G.map Φ = φB
  refine ⟨G.preimage φB, G.map_preimage φB, ?_⟩
  intro Φ hΦ
  exact G.map_injective (hΦ.trans (G.map_preimage φB).symm)

end
